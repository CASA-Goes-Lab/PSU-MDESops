import DESops.automata as automata
from DESops import error


def compare_language(g1, g2):
    # https://cs.stackexchange.com/questions/48136/testing-two-dfas-generate-the-same-language-by-trying-all-strings-upto-a-certain
    # https://cs.stackexchange.com/questions/81813/is-the-equality-of-two-dfas-a-decidable-problem/81815#81815
    """
    Returns a bool for language equivalence
    L(g1) == L(g2)

    Slight modification of the product composition:
        computes product of g1, g2 with transition function

        f ((x1, x2), e) := { (f1(x1, e), f2(x2, e))     if e in R1(x1) and e in R2(x2)
                           { "dead"                     if e in only one of R1(x1) or R2(x2)
                           { undefined                  o.w.
    "dead" states are noted as accepting states in the stack exchange links above.

    Returns False if a "dead" state is reached in the search (the full product need not be computed)

    TODO: - update for marked language equivalence
          - NFA equivalence
    """
    if not g1.type == "DFA" or not g2.type == "DFA":
        raise error.InvalidAutomataTypeError(
            "Expected inputs g1, g2 to be type DFA, got: {}, {}".format(
                g1.type, g2.type
            )
        )

    if g1.vcount() == 0 and g2.vcount() == 0:
        # both empty, so equivalent
        return True

    elif g1.vcount() == 0 or g2.vcount() == 0:
        return False

    vertice_names = list()  # list of vertex names for igraph construction
    vertice_number = dict()  # dictionary vertex_names -> vertex_id

    # BFS queue that holds states that must be visited
    queue = list()

    # index tracks the current number of vertices in the graph
    index = 0

    # inseting initial state to the graph
    vertice_names.insert(index, (g1.vs["name"][0], g2.vs["name"][0]))
    vertice_number[(g1.vs["name"][0], g2.vs["name"][0])] = index

    index = index + 1
    queue.append((g1.vs[0], g2.vs[0]))

    common_events = g1.events.intersection(g2.events)
    while queue:
        (v1, v2) = queue.pop(0)

        active_v1 = {e[1]: e[0] for e in v1["out"]}
        active_v2 = {e[1]: e[0] for e in v2["out"]}
        # Check for equivalence:
        if active_v1.keys() != active_v2.keys():
            # This transition would lead to a "dead" state: there is an event defined by one automata at this v
            # which is not possible in the other, i.e. languages are not equivalent
            return False

        active_events = set(active_v1.keys()).union(active_v2.keys())

        for e in active_events:
            if e in common_events and e in active_v1.keys() and e in active_v2.keys():
                nx_v1 = g1.vs[active_v1[e]]
                nx_v2 = g2.vs[active_v2[e]]
                (n, t, index, m, q) = composition(
                    v1, v2, nx_v1, nx_v2, index, vertice_number
                )
            else:
                continue

            # print(index)
            if q:
                vertice_names.insert(vertice_number[n], n)
                queue.append((nx_v1, nx_v2))

    return True
    # print(vertice_names)


def composition(v1, v2, nx_v1, nx_v2, index, vertice_number):
    name = (nx_v1["name"], nx_v2["name"])
    if name in vertice_number.keys():
        transition = (vertice_number[(v1["name"], v2["name"])], vertice_number[name])
        new = False
    else:
        transition = (vertice_number[(v1["name"], v2["name"])], index)
        vertice_number[name] = index
        new = True
        index = index + 1
    marking = nx_v1["marked"] and nx_v2["marked"]
    return name, transition, index, marking, new
