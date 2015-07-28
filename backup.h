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

      bool fl = 0;
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

      if (graph.idFromNode(dst) <= graph.idFromNode(nvsub[0])   ||
              std::binary_search(vsub.begin(), vsub.end(), dst) ||
              std::find(vext.begin(), vext.end(), dst) != vext.end())
        continue;

      bool fl = 0;
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

    nvsub.push_back(nx);

    //if (nvsub.size() >= K - 2 /*|| vext.size() < graph.size() / 80*/)
      prepareAndCallSerial(WNode(LPair(nvsub, vext), label));
    //else
      //ctx.push(WNode(LPair(nvsub, vext), label));

    nvsub.pop_back();

    while (added) {
      added--;
      vext.pop_back();
    }
  }
}

