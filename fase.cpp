#include "Galois/Statistic.h"
#include "Galois/Accumulator.h"
#include "Galois/Galois.h"
#include "Galois/Graph/Graph.h"
#include "Galois/Graph/LCGraph.h"
#include "Galois/Graph/LC_InOut_Graph.h"
#include "llvm/Support/CommandLine.h"
#include "Lonestar/BoilerPlate.h"
#include "Isomorphism.h"
#include <string>
#include <unordered_map>

typedef Galois::Graph::LC_CSR_Graph<int, void>
::with_no_lockable<true>::type
::with_numa_alloc<true>::type InnerGraph;
typedef Galois::Graph::LC_InOut_Graph<InnerGraph> Graph;
typedef Graph::GraphNode GNode;
typedef std::vector<size_t> list;
typedef std::pair<list, list> LPair;
typedef std::pair<LPair, long long int> WNode;

Galois::GMapElementAccumulator<std::unordered_map<std::string, int> > freqs;
Galois::GMapElementAccumulator<std::unordered_map<long long int, int> > isoCount;
Graph graph;

namespace cll = llvm::cl;
static cll::opt<std::string> filename(cll::Positional, cll::desc("<input file>"), cll::Required);
static cll::opt<std::string> transposeGraphName(cll::Positional, cll::desc("<transpose file>"), cll::Required);
static cll::opt<int> K(cll::Positional, cll::desc("<subgraph size>"), cll::Required);

void expand(list vsub, list vext, long long int clabel, Galois::UserContext<WNode>& ctx) {
  if (vsub.size() == K - 1) {
    while (!vext.empty()) {
      size_t nx = vext.back();
      vext.pop_back();
      long long int label = clabel;

      if (1 + vsub.size() >= 3) {
        int st = vsub.size() * (vsub.size() - 1) / 2 - 1;

        for (int i = 0; i < (int)vsub.size(); i++) {
          size_t dst = vsub[i];

          for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
                 ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
            if (graph.idFromNode(graph.getEdgeDst(ii)) == dst)
              label |= (1LL << (st + i));

          for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
                 ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
            if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
              label |= (1LL << (st + i));
        }
      }
      isoCount.update(label, 1);
    }
    return;
  }

  list nvsub;
  for (auto n : vsub)
    nvsub.push_back(n);

  std::sort(vsub.begin(), vsub.end());

  while (!vext.empty()) {
    size_t nx = vext.back();
    vext.pop_back();

    long long int label = clabel;
    int added = 0;

    for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getEdgeDst(ii));
      if (graph.idFromNode(dst) <= graph.idFromNode(nvsub[0]) || std::binary_search(vsub.begin(), vsub.end(), dst))
        continue;

      int fl = 0;
      for (auto ii2 = graph.edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::binary_search(vsub.begin(), vsub.end(), graph.idFromNode(graph.getEdgeDst(ii2)))) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      for (auto ii2 = graph.in_edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.in_edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::binary_search(vsub.begin(), vsub.end(), graph.idFromNode(graph.getInEdgeDst(ii2)))) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      added++;
      vext.push_back(dst);
    }

    for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));

      if (std::find(vext.begin(), vext.end(), dst) != vext.end())
        continue;

      if (graph.idFromNode(dst) <= graph.idFromNode(nvsub[0]) || std::binary_search(vsub.begin(), vsub.end(), dst))
        continue;

      int fl = 0;
      for (auto ii2 = graph.edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::binary_search(vsub.begin(), vsub.end(), graph.idFromNode(graph.getEdgeDst(ii2)))) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      for (auto ii2 = graph.in_edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.in_edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::binary_search(vsub.begin(), vsub.end(), graph.idFromNode(graph.getInEdgeDst(ii2)))) {
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

      for (int i = 0; i < (int)nvsub.size(); i++) {
        size_t dst = nvsub[i];

        for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
               ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
          if (graph.idFromNode(graph.getEdgeDst(ii)) == dst)
            label |= (1LL << (st + i));

        for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
               ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
          if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
            label |= (1LL << (st + i));
      }
    }

    nvsub.push_back(nx);

    if (nvsub.size() >= K - 1 /*|| vext.size() < graph.size() / 80*/)
      expand(nvsub, vext, label, ctx);
    else
      ctx.push(WNode(LPair(nvsub, vext), label));
    nvsub.pop_back();

    while (added) {
      added--;
      vext.pop_back();
    }
  }
}

struct FaSE {
  void operator()(WNode& req, Galois::UserContext<WNode>& ctx) const {
    if(req.first.first.size() == 1){
      for (auto ii = graph.edge_begin(req.first.first[0]), ee = graph.edge_end(req.first.first[0]); ii != ee; ++ii) {
        size_t dst = graph.idFromNode(graph.getEdgeDst(ii));
        if (graph.idFromNode(dst) <= graph.idFromNode(req.first.first[0]))
          continue;

        req.first.second.push_back(dst);
      }

      for (auto ii = graph.in_edge_begin(req.first.first[0]), ee = graph.in_edge_end(req.first.first[0]); ii != ee; ++ii) {
        size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));
        if (graph.idFromNode(dst) <= graph.idFromNode(req.first.first[0]) ||
                std::find(req.first.second.begin(), req.first.second.end(), dst) != req.first.second.end())
          continue;

        req.first.first.push_back(dst);
      }
    }
    expand(req.first.first, req.first.second, req.second, ctx);
  }
};

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
  LonestarStart(argc, argv, 0,0,0);
  Galois::Graph::readGraph(graph, filename, transposeGraphName);
  //int n, m;
  //scanf("%d %d", &n, &m);

  //std::vector<Graph::GraphNode> nodes = createGraph(n, m);

  using namespace Galois::WorkList;
  typedef ChunkedLIFO<1> dChunk;

  Galois::StatTimer T;
  T.start();

  int lb = 0;
  for (auto v : graph)
    graph.getData(v) = lb++;

  for (auto v : graph) {
    list vsub, vext;
    vsub.push_back(graph.idFromNode(v));

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
