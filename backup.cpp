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

Galois::Runtime::PerThreadStorage<size_t*> perThreadVsub;
Galois::Runtime::PerThreadStorage<size_t*> perThreadVextSz;
Galois::Runtime::PerThreadStorage<size_t**> perThreadVext;

void serialExpand(int lk, long long int clabel, size_t *vsub, size_t *vextSz, size_t **vext) {
  if (lk == K - 1) {
    while (vextSz[lk]) {
      size_t nx = vext[lk][--vextSz[lk]];
      long long int label = clabel;

      int st = lk * (lk - 1) / 2 - 1;

      for (int i = 0; i < lk; i++) {
        size_t dst = vsub[i];

        if(std::binary_search(graph.edge_begin(nx, Galois::MethodFlag::NONE),
                           graph.edge_end(nx, Galois::MethodFlag::NONE),
                           graph.nodeFromId(dst)))
            label |= (1LL << (st + i));

        for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
               ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
          if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
            label |= (1LL << (st + i));
      }

      isoCount.update(label, 1);
    }

    return;
  }

  while (vextSz[lk]) {
    size_t nx = vext[lk][--vextSz[lk]];

    for (int i = 0; i < vextSz[lk]; i++)
      vext[lk + 1][i] = vext[lk][i];
    vextSz[lk + 1] = vextSz[lk];

    long long int label = clabel;
    int added = 0;

    for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getEdgeDst(ii));
      if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) || std::find(vsub, vsub + lk, dst) != vsub + lk)
        continue;

      bool fl = 0;
      for (auto ii2 = graph.edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getEdgeDst(ii2))) != vsub + lk) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      for (auto ii2 = graph.in_edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.in_edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getInEdgeDst(ii2))) != vsub + lk) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      vext[lk + 1][vextSz[lk + 1]++] = dst;
    }

    for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));

      if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) ||
              std::find(vsub, vsub + lk, dst) != vsub + lk   ||
              std::find(vext[lk], vext[lk] + vextSz[lk], dst) != vext[lk] + vextSz[lk])
        continue;

      bool fl = 0;
      for (auto ii2 = graph.edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getEdgeDst(ii2))) != vsub + lk) {
          fl = 1;
          break;
        }

      if (fl)
        continue;

      for (auto ii2 = graph.in_edge_begin(dst, Galois::MethodFlag::NONE),
           ee2 = graph.in_edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
        if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getInEdgeDst(ii2))) != vsub + lk) {
          fl = 1;
          break;
        }


      if (fl)
        continue;

      vext[lk + 1][vextSz[lk + 1]++] = dst;
    }

    if (1 + lk >= 3) {
      int st = lk * (lk - 1) / 2 - 1;

      for (int i = 0; i < (int)lk; i++) {
        size_t dst = vsub[i];

        if(std::binary_search(graph.edge_begin(nx, Galois::MethodFlag::NONE),
                           graph.edge_end(nx, Galois::MethodFlag::NONE),
                           graph.nodeFromId(dst)))
            label |= (1LL << (st + i));

        for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
               ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
          if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
            label |= (1LL << (st + i));
      }
    }

    vsub[lk] = nx;

    serialExpand(lk + 1, label, vsub, vextSz, vext);
  }
}

void prepareAndCallSerial(WNode nd) {
  size_t* vsub = *perThreadVsub.getLocal();
  size_t* vextSz = *perThreadVextSz.getLocal();
  size_t** vext = *perThreadVext.getLocal();;

  if (vsub == NULL)
    vsub = new size_t[K];

  if (vextSz == NULL)
    vextSz = new size_t[K];

  if (vext == NULL) {
    vext = new size_t*[K];

    for (int i = 0; i < K; i++)
      vext[i] = new size_t[graph.size() + 1];
  }

  if(nd.first.first.size() == 1){
    for (auto ii = graph.edge_begin(nd.first.first[0]), ee = graph.edge_end(nd.first.first[0]); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getEdgeDst(ii));
      if (graph.idFromNode(dst) <= graph.idFromNode(nd.first.first[0]))
        continue;

      nd.first.second.push_back(dst);
    }

    for (auto ii = graph.in_edge_begin(nd.first.first[0]), ee = graph.in_edge_end(nd.first.first[0]); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));
      if (graph.idFromNode(dst) <= graph.idFromNode(nd.first.first[0]) ||
          std::find(nd.first.second.begin(), nd.first.second.end(), dst) != nd.first.second.end())
        continue;

      nd.first.second.push_back(dst);
    }
  }

  for (int i = 0; i < nd.first.first.size(); i++)
    vsub[i] = nd.first.first[i];

  memset(vextSz, 0, sizeof vextSz);
  vextSz[nd.first.first.size()] = nd.first.second.size();
  for (int i = 0; i < nd.first.second.size(); i++)
    vext[nd.first.first.size()][i] = nd.first.second[i];

  serialExpand(nd.first.first.size(), nd.second, vsub, vextSz, vext);
}

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

        req.first.second.push_back(dst);
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
  typedef ChunkedLIFO<16> dChunk;

  Galois::StatTimer T;
  T.start();

  std::vector<WNode> initialWork;

  for (auto v : graph) {
    list vsub, vext;
    vsub.push_back(graph.idFromNode(v));

    initialWork.push_back(WNode(LPair(vsub, vext), 0LL));
  }

  Galois::for_each(initialWork.begin(), initialWork.end(), FaSE(), Galois::wl<dChunk>());

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
