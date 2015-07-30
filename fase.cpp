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

const int chunkSize   = 10;
bool bigIncrease      = true;
const int bigSizeMult = 10;

Galois::GMapElementAccumulator<std::unordered_map<std::string, int> > freqs;
Galois::GMapElementAccumulator<std::unordered_map<long long int, int> > isoCount;
Galois::GAccumulator<int> wlSize;
Graph graph;

Galois::GAccumulator<int> bigListAddWork;
Galois::GAccumulator<int> bigListSequential;
Galois::GAccumulator<int> smallListAddWork;
Galois::GAccumulator<int> smallListSequential;

namespace cll = llvm::cl;
static cll::opt<std::string> filename(cll::Positional, cll::desc("<input file>"), cll::Required);
static cll::opt<std::string> transposeGraphName(cll::Positional, cll::desc("<transpose file>"), cll::Required);
static cll::opt<int> K(cll::Positional, cll::desc("<subgraph size>"), cll::Required);
static cll::opt<bool> printTypes("pr", cll::desc("Print occurrences by type"), cll::init(false));
static cll::opt<bool> directed("d", cll::desc("Directed"), cll::init(false));

Galois::Runtime::PerThreadStorage<size_t*> perThreadVsub;
Galois::Runtime::PerThreadStorage<size_t*> perThreadVextSz;
Galois::Runtime::PerThreadStorage<size_t**> perThreadVext;

long long int updateLabel(size_t* vsub, int lk, size_t nx, long long int clabel){
  long long int label = clabel;

  if (1 + lk >= 3) {
    int st = (lk * (lk - 1) / 2 - 1) * (directed + 1);

    for (int i = 0; i < (int)lk; i++) {
      size_t dst = vsub[i];

      for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
             ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
        if (graph.idFromNode(graph.getEdgeDst(ii)) == dst)
          label |= (1LL << (st + i + (lk - 1) * directed));

      for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
             ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
        if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
          label |= (1LL << (st + i + (lk - 1) * directed));
    }
  }
  return label;
}

bool alreadyInMotif(size_t* vsub, int lk, size_t dst){
  bool fl = 0;

  for (auto ii2 = graph.edge_begin(dst, Galois::MethodFlag::NONE),
       ee2 = graph.edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
    if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getEdgeDst(ii2))) != vsub + lk) {
      fl = 1;
      break;
    }

  if (fl) return 1;

  for (auto ii2 = graph.in_edge_begin(dst, Galois::MethodFlag::NONE),
       ee2 = graph.in_edge_end(dst, Galois::MethodFlag::NONE); ii2 != ee2; ++ii2)
    if (std::find(vsub, vsub + lk, graph.idFromNode(graph.getInEdgeDst(ii2))) != vsub + lk) {
      fl = 1;
      break;
    }

  if (fl) return 1;

  return 0;
}

void serialExpand(int lk, long long int clabel, size_t *vsub, size_t *vextSz, size_t **vext, Galois::UserContext<WNode>& ctx) {
  long long int label;
  size_t nx;

  if (lk == K - 1) {
    while (vextSz[lk]) {
      nx = vext[lk][--vextSz[lk]];

      long long int label = updateLabel(&vsub[0], lk, nx, clabel);

      isoCount.update(label, 1);
    }

    return;
  }

  while (vextSz[lk]) {
    nx = vext[lk][--vextSz[lk]];

    for (int i = 0; i < vextSz[lk]; i++)
      vext[lk + 1][i] = vext[lk][i];
    vextSz[lk + 1] = vextSz[lk];

    label = clabel;

    for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getEdgeDst(ii));

      if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) ||
              std::find(vsub, vsub + lk, dst) != vsub + lk)
        continue;

      if(!alreadyInMotif(vsub, lk, dst))
        vext[lk + 1][vextSz[lk + 1]++] = dst;
    }

    for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));

      if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) ||
              std::find(vsub, vsub + lk, dst) != vsub + lk   ||
              std::find(vext[lk], vext[lk] + vextSz[lk], dst) != vext[lk] + vextSz[lk])
        continue;

      if(!alreadyInMotif(vsub, lk, dst))
        vext[lk + 1][vextSz[lk + 1]++] = dst;
    }

    label = updateLabel(vsub, lk, nx, clabel);

    vsub[lk] = nx;

    /*if (wlSize.unsafeRead() > numThreads * chunkSize || lk >= K - 2)
      serialExpand(lk + 1, label, vsub, vextSz, vext, ctx);
    else {
      list lvsub, lvext;
      for (int i = 0; i < vextSz[lk + 1]; i++)
        lvext.push_back(vext[lk + 1][i]);

      for (int i = 0; i < lk + 1; i++)
        lvsub.push_back(vsub[i]);

      ctx.push(WNode(LPair(lvsub, lvext), label));
    }*/

    // Big Worklist Phase
    if(bigIncrease){
      if (wlSize.unsafeRead() >= (numThreads - 1) * chunkSize * bigSizeMult || lk >= K - 2){
        bigListSequential.update(1);
        serialExpand(lk + 1, label, vsub, vextSz, vext, ctx);

        bigIncrease = false;
      }
      else {
        bigListAddWork.update(1);
        list lvsub, lvext;
        for (int i = 0; i < vextSz[lk + 1]; i++)
          lvext.push_back(vext[lk + 1][i]);

        for (int i = 0; i < lk + 1; i++)
          lvsub.push_back(vsub[i]);

        ctx.push(WNode(LPair(lvsub, lvext), label));
      }
    }
    // Small Worklist Phase
    else{
      if (wlSize.unsafeRead() >= numThreads * chunkSize || lk >= K - 2){
        serialExpand(lk + 1, label, vsub, vextSz, vext, ctx);
        smallListSequential.update(1);
      }
      else {
        bigIncrease = true;
        smallListAddWork.update(1);

        list lvsub, lvext;
        for (int i = 0; i < vextSz[lk + 1]; i++)
          lvext.push_back(vext[lk + 1][i]);

        for (int i = 0; i < lk + 1; i++)
          lvsub.push_back(vsub[i]);

        ctx.push(WNode(LPair(lvsub, lvext), label));
      }
    }
  }
}

void prepareAndCallSerial(WNode nd, Galois::UserContext<WNode>& ctx) {
  size_t*  vsub   = *perThreadVsub.getLocal();
  size_t*  vextSz = *perThreadVextSz.getLocal();
  size_t** vext   = *perThreadVext.getLocal();

  list vsubReq = nd.first.first;
  list vextReq = nd.first.second;
  long long int label = nd.second;

  for (int i = 0; i < vsubReq.size(); i++)
    vsub[i] = vsubReq[i];

  memset(vextSz, 0, sizeof vextSz);
  vextSz[vsubReq.size()] = vextReq.size();
  for (int i = 0; i < vextReq.size(); i++)
    vext[vsubReq.size()][i] = vextReq[i];

  serialExpand(vsubReq.size(), label, vsub, vextSz, vext, ctx);
}

struct FaSE {
  void operator()(WNode& req, Galois::UserContext<WNode>& ctx) const {
    wlSize.update(-1);

    list vsub = req.first.first;
    list vext = req.first.second;
    long long int label = req.second;

    if(vsub.size() == 1){
      for (auto ii = graph.edge_begin(vsub[0]), ee = graph.edge_end(vsub[0]); ii != ee; ++ii) {
        size_t dst = graph.idFromNode(graph.getEdgeDst(ii));
        if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]))
          continue;

        vext.push_back(dst);
      }

      for (auto ii = graph.in_edge_begin(vsub[0]), ee = graph.in_edge_end(vsub[0]); ii != ee; ++ii) {
        size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));
        if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) ||
                std::find(vext.begin(), vext.end(), dst) != vext.end())
          continue;

        vext.push_back(dst);
      }
    }

    prepareAndCallSerial(WNode(LPair(vsub, vext), label), ctx);
//    expand(vsub, vext, label, ctx);
  }
};

void getSubgraphFrequencies(std::pair<long long int, int> element) {
  Isomorphism *iso = new Isomorphism();
  iso->initNauty(K, directed);

  char s[K * K + 1];
  for(int i = 0; i < K*K; i++) s[i] = '0';
  s[K*K] = '\0';

  // Rebuild Graph (Matrix) Representation

  if(!directed){
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
  }
  else{

  }

  // Compute Canonical Types
  char nauty_s[K * K + 1];
  nauty_s[0] = '\0';
  iso->canonicalStrNauty(s, nauty_s);
  std::string str = std::string(nauty_s);
  freqs.update(str, element.second);

  iso->finishNauty();
}

struct InitializeLocal {
  void operator()(unsigned, unsigned) {
    size_t* a = new size_t[K];
    *perThreadVsub.getLocal() = a;

    size_t* b = new size_t[K];
    *perThreadVextSz.getLocal() = b;

    size_t** c = new size_t*[K];
    for (int i = 0; i < K; i++)
      c[i] = new size_t[graph.size() + 1];

    *perThreadVext.getLocal() = c;
  }
};

struct DeleteLocal {
  void operator()(unsigned, unsigned) {
    delete [] *perThreadVsub.getLocal();
    delete [] *perThreadVextSz.getLocal();
    for (int i = 0; i < K; i++)
      delete [] (*perThreadVext.getLocal())[i];
  }
};

int main(int argc, char **argv) {
  Galois::StatManager statManager;
  LonestarStart(argc, argv, 0,0,0);
  Galois::Graph::readGraph(graph, filename, transposeGraphName);

  using namespace Galois::WorkList;
  typedef ChunkedLIFO<chunkSize> dChunk;

  Galois::StatTimer T;
  T.start();

  std::vector<WNode> initialWork;
  Galois::on_each(InitializeLocal());

  for (auto v : graph) {
    list lvsub, lvext;
    lvsub.push_back(graph.idFromNode(v));

    initialWork.push_back(WNode(LPair(lvsub, lvext), 0LL));
    wlSize.update(1);
  }

  Galois::for_each(initialWork.begin(), initialWork.end(), FaSE(), Galois::wl<dChunk>());

  std::unordered_map<long long int, int> isoIt = isoCount.reduce();
  Galois::do_all(isoIt.begin(), isoIt.end(), getSubgraphFrequencies);

  std::unordered_map<std::string, int> freqsReduced = freqs.reduce();

  if (printTypes)
    for(auto kv : freqsReduced)
      printf("%s has %d occurrences\n",(kv.first).c_str(), kv.second);

  int tot = 0;
  for(auto kv : freqsReduced)
    tot += kv.second;
  printf("Total subgraphs: %d\n", tot);

  Galois::on_each(DeleteLocal());

  int blAdds = bigListAddWork.reduce();
  int blSeq  = bigListSequential.reduce();
  int slAdds = smallListAddWork.reduce();
  int slSeq  = smallListSequential.reduce();

  int all = blAdds + blSeq + slAdds + slSeq;

  if (directed)
    printf("Directed graph\n");
  printf("-------------------------------------------\n");
  printf("Adds to Big List:       %d (%.2f%%)\n", blAdds, (float)blAdds/(float)all * 100);
  printf("Seq Runs to Big List:   %d (%.2f%%)\n", bigListSequential.reduce(), (float)blSeq/(float)all * 100);
  printf("Adds to Small List:     %d (%.2f%%)\n", smallListAddWork.reduce(), (float)slAdds/(float)all * 100);
  printf("Seq Runs on Small List: %d (%.2f%%)\n", smallListSequential.reduce(), (float)slSeq/(float)all * 100);
  printf("-------------------------------------------\n");

  T.stop();

  return 0;
}
