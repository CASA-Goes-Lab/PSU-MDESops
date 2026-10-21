def prob_trans(g):
    # returns the avg probability of a transition (v1, e, v2) for any v1, v2 & particular e
    total = 0
    num_trans = 0
    for e in g.events:
        for v1 in range(g.vcount()):
            for v2 in range(g.vcount()):
                try:
                    trans = g.es.find(_between=((v1,), (v2,)))
                except:
                    total += 1
                    continue

                if trans["label"] == e:
                    num_trans += 1

                total += 1

    """
    Do this with an adjacency matrix instead:
    idk how though, tomorrow problem

    """
    return num_trans / total
