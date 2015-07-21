#include "Galois/Statistic.h"
#include "Galois/Accumulator.h"
#include "Galois/Galois.h"
#include "Galois/Graph/Graph.h"
#include "llvm/Support/CommandLine.h"
#include "Lonestar/BoilerPlate.h"
#include "Isomorphism.h"
#include <string>
#include <unordered_map>

typedef Galois::Graph::FirstGraph<int, int, false> Graph;
typedef Graph::GraphNode GNode;
typedef std::vector<GNode> list;
typedef std::pair<list, list> LPair;
typedef std::pair<LPair, long long int> WNode;

Galois::GMapElementAccumulator<std::unordered_map<std::string, int> > freqs;
Galois::GMapElementAccumulator<std::unordered_map<long long int, int> > isoCount;
Graph graph;
int K;

void expand(list& vsub, list& vext, long long int clabel, Galois::UserContext<WNode>& ctx) {
  std::sort(vsub.begin(), vsub.end());

  while (!vext.empty()) {
    GNode nx = vext.back();
    vext.pop_back();

    long long int label = clabel;
    int added = 0;

    for (auto edge : graph.out_edges(nx, Galois::MethodFlag::NONE)) {
      GNode dst = graph.getEdgeDst(edge);
      if (graph.getData(dst, Galois::MethodFlag::NONE) <= graph.getData(vsub[0], Galois::MethodFlag::NONE) || std::binary_search(vsub.begin(), vsub.end(), dst))
        continue;

      int fl = 0;
      for (auto edge2 : graph.out_edges(dst, Galois::MethodFlag::NONE))
        if (std::binary_search(vsub.begin(), vsub.end(), graph.getEdgeDst(edge2))) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      added++;
      vext.push_back(dst);
    }


    if (1 + vsub.size() >= 3) {
      int st = vsub.size() * (vsub.size() - 1) / 2 - 1;

      for (int i = 0; i < (int)vsub.size(); i++) {
        GNode dst = vsub[i];
        
        if (graph.findEdge(nx, dst, Galois::MethodFlag::NONE) != graph.edge_end(nx, Galois::MethodFlag::NONE))
          label |= (1LL << (st + i));
      }
    }

    vsub.push_back(nx);
    ctx.push(WNode(LPair(vsub, vext), label));
    vsub.pop_back();

    while (added) {
      added--;
      vext.pop_back();
    }
  }
}

struct FaSE {
  void operator()(WNode& req, Galois::UserContext<WNode>& ctx) const {
    if (req.first.first.size() == K)
      isoCount.update(req.second, 1);
    else
      expand(req.first.first, req.first.second, req.second, ctx);
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

void getSubgraphFrequencies(std::pair<long long int, int> element) {
  Isomorphism *iso = new Isomorphism();
  iso->initNauty(K, false);

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
  iso->canonicalStrNauty(s, nauty_s);
  std::string str = std::string(nauty_s);
  freqs.update(str, element.second);

  /*printf("==> Type: : ");
    for(int i = 0; i < K; i++){
    for(int j = 0; j < K; j++){
    printf("%c", nauty_s[i*K + j]);
    }
    printf("|");
    }
    printf("\n");*/
  iso->finishNauty();
}

int main(int argc, char **argv) {
  Galois::StatManager statManager;

  int th = 1;
  if (argc > 1) th = atoi(argv[1]);

  K = 3;
  if (argc > 2) K = atoi(argv[2]);

  Galois::setActiveThreads(th);

  //LonestarSntart(argc, argv, 0,0,0);

  int n, m;
  scanf("%d %d", &n, &m);

  std::vector<Graph::GraphNode> nodes = createGraph(n, m);

  using namespace Galois::WorkList;
  typedef ChunkedLIFO<1> dChunk;

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

  std::unordered_map<long long int, int> isoIt = isoCount.reduce();
  Galois::do_all(isoIt.begin(), isoIt.end(), getSubgraphFrequencies);

  std::unordered_map<std::string, int> freqsReduced = freqs.reduce();

//  for(auto kv : freqsReduced)
//    printf("%s has %d occurrences\n",(kv.first).c_str(), kv.second);

  int tot = 0;
  for(auto kv : freqsReduced)
    tot += kv.second;
  printf("Total subgraphs: %d\n", tot);

  T.stop();

  return 0;
}
