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

typedef Galois::Graph::LC_CSR_Graph<int, int>
::with_no_lockable<true>::type
::with_numa_alloc<true>::type InnerGraph;
typedef Galois::Graph::LC_InOut_Graph<InnerGraph> Graph;
typedef Graph::GraphNode GNode;
typedef std::vector<size_t> list;
typedef std::pair<list, list> LPair;
typedef std::pair<LPair, long long int> WNode;

const int chunkSize     = 10;
bool bigIncrease        = true;
const int smallSizeMult = 1;
const long long int bigSizeMult   = 8 * smallSizeMult;

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

  if (1 + lk >= 3 || (1 + lk >= 2 && directed)) {
    int st = (lk * (lk - 1) / 2 - 1);

    if (directed)
      st = lk * (lk - 1);

    for (int i = 0; i < (int)lk; i++) {
      size_t dst = vsub[i];

      for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
             ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
        if (graph.idFromNode(graph.getEdgeDst(ii)) == dst)
          label |= (1LL << (st + directed * 2 * i + (1 - directed) * i));

      for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
             ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii)
        if (graph.idFromNode(graph.getInEdgeDst(ii)) == dst)
          label |= (1LL << (st + directed * (2 * (i + 1) - 1) + (1 - directed) * i));
    }
  }
  return label;
}

bool findcmp (Graph::edge_iterator i, Graph::edge_iterator j) {
  return graph.getEdgeDst(i) < graph.getEdgeDst(j);
}

bool connected(size_t a, size_t b) {
/*  return (std::binary_search(graph.edge_begin(a, Galois::MethodFlag::NONE), graph.edge_end(a, Galois::MethodFlag::NONE), b, findcmp) ||
          std::binary_search(graph.edge_begin(b, Galois::MethodFlag::NONE), graph.edge_end(b, Galois::MethodFlag::NONE), a, findcmp));*/

  for (auto ii = graph.edge_begin(a, Galois::MethodFlag::NONE),
         ee = graph.edge_end(a, Galois::MethodFlag::NONE); ii != ee; ++ii)
    if (graph.idFromNode(graph.getEdgeDst(ii)) == b)
      return 1;

  for (auto ii = graph.edge_begin(b, Galois::MethodFlag::NONE),
         ee = graph.edge_end(b, Galois::MethodFlag::NONE); ii != ee; ++ii)
    if (graph.idFromNode(graph.getEdgeDst(ii)) == a)
      return 1;

  return 0;
}

void serialExpand(int lk, long long int clabel, size_t *vsub, size_t *vextSz, size_t **vext, Galois::UserContext<WNode>& ctx) {
  long long int label;
  size_t nx;

  /*printf("Vsub: ");
  for(int aa = 0; aa < lk; aa++) printf("%d ", vsub[aa]);
  printf("\n");

  printf("Vext: ");
  for(int aa = 0; aa < vextSz[lk]; aa++) printf("%d ", vext[lk][aa]);
  printf("\n");*/

  if (lk == K - 1) {
    while (vextSz[lk]) {
      nx = vext[lk][--vextSz[lk]];
      vsub[K-1] = nx;

      label = updateLabel(&vsub[0], lk, nx, clabel);

      isoCount.update(label, 1);

      /*printf("Found: ");
      for (int aaa =0; aaa < K; aaa++)printf("%d ", vsub[aaa]);
      printf("\n");*/
    }

    return;
  }

  //printf("\n");

  int estimateSize = wlSize.unsafeRead(), localUpdates = 0, iter = 0;

  while (vextSz[lk]) {
    nx = vext[lk][--vextSz[lk]];

    for (int i = 0; i < vextSz[lk]; i++)
      vext[lk + 1][i] = vext[lk][i];
    vextSz[lk + 1] = vextSz[lk];

    label = clabel;

//  std::vector<size_t, ctx.getPerIterAlloc()> added;
    std::vector<size_t> added;

    for (auto ii = graph.edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getEdgeDst(ii));

      if (dst <= vsub[0])
        continue;

      int i;
      for (i = 0; i < lk; i++)
        if (dst == vsub[i] || connected(dst, vsub[i]))
          break;

      if (i == lk) {
        vext[lk + 1][vextSz[lk + 1]++] = dst;
        added.push_back(dst);
      }
    }

    std::sort(added.begin(), added.end());

    for (auto ii = graph.in_edge_begin(nx, Galois::MethodFlag::NONE),
           ee = graph.in_edge_end(nx, Galois::MethodFlag::NONE); ii != ee; ++ii) {
      size_t dst = graph.idFromNode(graph.getInEdgeDst(ii));

      if (dst <= vsub[0])
        continue;

      if (std::binary_search(added.begin(), added.end(), dst))
        continue;

      int i;
      for (i = 0; i < lk; i++)
        if (dst == vsub[i] || connected(dst, vsub[i]))
          break;

      if(i == lk)
        vext[lk + 1][vextSz[lk + 1]++] = dst;
    }

    label = updateLabel(vsub, lk, nx, clabel);

    vsub[lk] = nx;

    if (numThreads > 1 && iter++ % ((numThreads - 1) * chunkSize * smallSizeMult) == 0) {
      wlSize.update(localUpdates);
      localUpdates = 0;
      estimateSize = wlSize.unsafeRead();
    }
    //estimateSize = wlSize.unsafeRead();

    // Big Worklist Phase
    if(bigIncrease){
      if (estimateSize + localUpdates >= (numThreads - 1) * chunkSize * bigSizeMult || lk >= K - 2){
      //if (estimateSize  >= (numThreads - 1) * chunkSize * bigSizeMult){
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

        localUpdates++;
        //wlSize.update(1);
        ctx.push(WNode(LPair(lvsub, lvext), label));
      }
    }
    // Small Worklist Phase
    else{
      if (estimateSize + localUpdates >= (numThreads - 1) * chunkSize * smallSizeMult || lk >= K - 2){
      //if (estimateSize >= (numThreads - 1) * chunkSize * smallSizeMult){
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

        localUpdates++;
        //wlSize.update(1);
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
        if (graph.idFromNode(dst) <= graph.idFromNode(vsub[0]) ||
                std::find(vext.begin(), vext.end(), dst) != vext.end())
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
  }
};

void getSubgraphFrequencies(std::pair<long long int, int> element) {
  Isomorphism *iso = new Isomorphism();
  iso->initNauty(K, directed);

  char s[K * K + 1];
  for(int i = 0; i < K*K; i++) s[i] = '0';
  s[K*K] = '\0';

  int conn, connIn, connOut;

  // Rebuild Graph (Matrix) Representation

  if(!directed){
    s[1] = '1'; s[1*K] = '1';
    for (int nodex = 2, nodey = 0, i = 0; ; nodey++, i++){
      if(nodey == nodex) {
        nodex++;
        nodey = 0;
        if(nodex == K) break;
      }

      conn = element.first & (1LL << i) ? 1 : 0;

      if(conn){
        s[nodex*K + nodey] = '1';
        s[nodey*K + nodex] = '1';
      }
    }
  }
  else{
    for (int nodex = 1, nodey = 0, i = 0; ; nodey++, i+=2){
      if(nodey == nodex) {
        nodex++;
        nodey = 0;
        if(nodex == K) break;
      }

      connIn = element.first & (1LL << i) ? 1 : 0;
      connOut = element.first & (1LL << (i+1)) ? 1 : 0;

      if(connIn)  s[nodex*K + nodey] = '1';
      if(connOut) s[nodey*K + nodex] = '1';
    }
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

struct InitializeGraph {
  void operator()(GNode& n, Galois::UserContext<GNode>& ctx) const {
//    graph.sortEdges(n, cmp, Galois::MethodFlag::NONE);
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
  typedef dChunkedLIFO<chunkSize> dChunk;

  Galois::StatTimer T;
  T.start();

  std::vector<WNode> initialWork;
  Galois::on_each(InitializeLocal());
  Galois::for_each(graph.begin(), graph.end(), InitializeGraph());

  //int c = 0;

  for (auto v : graph) {
    //if (c != 12) { c++; continue; }

    list lvsub, lvext;
    lvsub.push_back(graph.idFromNode(v));

    initialWork.push_back(WNode(LPair(lvsub, lvext), 0LL));
    wlSize.update(1);

    //c++;
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

  printf("-------------------------------------------\n");
  printf("Total subgraphs      : %d\n", tot);
  printf("Total subgraph types : %d\n", (int)freqsReduced.size());

  Galois::on_each(DeleteLocal());

  int blAdds = bigListAddWork.reduce();
  int blSeq  = bigListSequential.reduce();
  int slAdds = smallListAddWork.reduce();
  int slSeq  = smallListSequential.reduce();

  int all = blAdds + blSeq + slAdds + slSeq;

  printf("-------------------------------------------\n");
  printf("Adds to Big List:       %d (%.2f%%)\n", blAdds, (float)blAdds/(float)all * 100);
  printf("Seq Runs to Big List:   %d (%.2f%%)\n", bigListSequential.reduce(), (float)blSeq/(float)all * 100);
  printf("Adds to Small List:     %d (%.2f%%)\n", smallListAddWork.reduce(), (float)slAdds/(float)all * 100);
  printf("Seq Runs on Small List: %d (%.2f%%)\n", smallListSequential.reduce(), (float)slSeq/(float)all * 100);
  printf("-------------------------------------------\n");

  T.stop();

  return 0;
}
