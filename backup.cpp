void prepareAndCallSerial(WNode nd) {
  size_t* vsub = *perThreadVsub.getLocal();
  size_t* vextSz = *perThreadVextSz.getLocal();
  size_t** vext = *perThreadVext.getLocal();;

  if(nd.first.first.size() == 1) {
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

void serialExpand(int lk, long long int clabel, size_t *vsub, size_t *vextSz, size_t **vext) {
  if (lk == K - 1) {
    while (vextSz[lk]) {
      size_t nx = vext[lk][--vextSz[lk]];
      long long int label = clabel;

      int st = lk * (lk - 1) / 2 - 1;

      for (int i = 0; i < lk; i++) {
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

    vsub[lk] = nx;

    serialExpand(lk + 1, label, vsub, vextSz, vext);
  }
}
