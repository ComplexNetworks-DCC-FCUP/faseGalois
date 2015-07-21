#include "Galois/Statistic.h"
#include "Galois/Accumulator.h"
#include "Galois/Galois.h"
#include "Galois/Graph/Graph.h"
#include "llvm/Support/CommandLine.h"
#include "Lonestar/BoilerPlate.h"
#include "Isomorphism.h"

typedef Galois::Graph::FirstGraph<int, int, false> Graph;
typedef Graph::GraphNode GNode;
typedef std::vector<GNode> list;
typedef std::pair<list, list> LPair;
typedef std::pair<LPair, long long int> WNode;

Galois::GMapElementAccumulator<std::map<long long int, int> > isoCount;
Galois::GAccumulator<int> occs;
Graph graph;
int K;

#include <string>
std::map <std::string, int> freqs;

void expand(list vsub, list vext, long long int clabel, Galois::UserContext<WNode>& ctx) {
  list nvsub;
  for (auto n : vsub)
    nvsub.push_back(n);

  list nvext;
  for (auto n : vext)
    nvext.push_back(n);

  while (!vext.empty()) {
    GNode nx = vext.back();
    vext.pop_back();
    nvext.pop_back();
    nvsub.push_back(nx);

    long long int label = clabel;

    int added = 0;
    for (auto edge : graph.out_edges(nx, Galois::MethodFlag::NONE)) {
      GNode dst = graph.getEdgeDst(edge);
      if (graph.getData(dst, Galois::MethodFlag::NONE) <= graph.getData(vsub[0], Galois::MethodFlag::NONE) || find(vsub.begin(), vsub.end(), dst) != vsub.end())
        continue;

      int fl = 0;
      for (auto edge2 : graph.out_edges(dst, Galois::MethodFlag::NONE))
        if (find(vsub.begin(), vsub.end(), graph.getEdgeDst(edge2)) != vsub.end()) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      added++;
      nvext.push_back(dst);
    }

    if (nvsub.size() >= 3) {
      int st = vsub.size() * (vsub.size() - 1) / 2 - 1;

      for (auto edge : graph.out_edges(nx, Galois::MethodFlag::NONE))
        for (int i = 0; i < (int)vsub.size(); i++)
          if (vsub[i] == graph.getEdgeDst(edge)) {
            label |= (1LL << (st + i));
            break;
          }
    }

    ctx.push(WNode(LPair(nvsub, nvext), label));
    nvsub.pop_back();
    while (added) {
      added--;
      nvext.pop_back();
    }
  }
}

struct FaSE {
  void operator()(WNode& req, Galois::UserContext<WNode>& ctx) const {
    if (req.first.first.size() == K) {
      occs += 1;
      isoCount.update(req.second, 1);

/*      printf("Found: ");
      for (auto a : req.first)
        printf("%d ", graph.getData(a).first);
        printf("\n");*/
    }
    else {
/*      for (auto a : req.first)
        printf("%d ", graph.getData(a).first);
      printf("|");
      for (auto a : req.second)
        printf("%d ", graph.getData(a).first);
        printf("\n");*/

      expand(req.first.first, req.first.second, req.second, ctx);
    }
  }
};

std::vector<Graph::GraphNode> createGraph(int n, int m){
  std::vector<Graph::GraphNode> nodes(n);

  for (int i = 0; i < n; i++) {
    Graph::GraphNode a = graph.createNode(i);
    graph.addNode(a);
    nodes[i] = a;
  }

  for (int i = 0; i < m; i++) {
    int a, b;
    scanf("%d %d", &a, &b);
    a--, b--;
    graph.addEdge(nodes[a], nodes[b]);
    //graph.addEdge(nodes[b], nodes[a]);
  }

  return nodes;
}

void getSubgraphFrequencies(){
  std::map<long long int, int> isoIt = isoCount.reduce();
  for (auto element : isoIt) {
    char s[K * K + 1];
    for(int i = 0; i < K*K; i++) s[i] = '0';
    s[K*K] = '\0';

    // Rebuild Graph (Matrix) Representation
    s[1] = '1'; s[1*K] = '1';
    for (int nodex = 2, nodey = 0, i = 0; ; nodey++, i++){
      if(nodey == nodex) {
        nodex++;
        nodey = 0;
        if(nodex == K) break;
      }

      int conn = element.first & (1LL << i) ? 1 : 0;

      if(conn){
        s[nodex*K + nodey] = '1';
        s[nodey*K + nodex] = '1';
      }
    }

    /*printf("Matrix: ");for(int i = 0; i < K; i++){
      for(int j = 0; j < K; j++){
        printf("%c", s[i*K + j]);
      }
      printf("|");
    }*/

    // Compute Canonical Types
    char nauty_s[K * K + 1];
    nauty_s[0] = '\0';
    Isomorphism::canonicalStrNauty(s, nauty_s);
    std::string str = std::string(nauty_s);
    freqs[str] += element.second;

    /*printf("==> Type: : ");
    for(int i = 0; i < K; i++){
      for(int j = 0; j < K; j++){
        printf("%c", nauty_s[i*K + j]);
      }
      printf("|");
    }
    printf("\n");*/
  }
}

int main(int argc, char **argv) {
  Galois::StatManager statManager;

  int th = 1;
  if (argc > 1) th = atoi(argv[1]);

  K = 3;
  if (argc > 2) K = atoi(argv[2]);

  Galois::setActiveThreads(th);

  Isomorphism::initNauty(K, false);
  //LonestarSntart(argc, argv, 0,0,0);

  int n, m;
  scanf("%d %d", &n, &m);

  std::vector<Graph::GraphNode> nodes = createGraph(n, m);

  using namespace Galois::WorkList;
  typedef dChunkedFIFO<64> dChunk;

  Galois::StatTimer T;
  T.start();

  for (int i = 0; i < n; i++) {
    list vsub, vext;
    vsub.push_back(nodes[i]);
    for (auto edge : graph.out_edges(nodes[i])) {
      GNode dst = graph.getEdgeDst(edge);
      if (graph.getData(dst) <= graph.getData(nodes[i]))
        continue;

      vext.push_back(dst);
    }

    Galois::for_each(WNode(LPair(vsub, vext), 0LL), FaSE(), Galois::wl<dChunk>());
  }

  T.stop();

  getSubgraphFrequencies();

  for(auto kv : freqs)
    printf("%s has %d occurrences\n",(kv.first).c_str(), kv.second);

  Isomorphism::finishNauty();

  return 0;
}
