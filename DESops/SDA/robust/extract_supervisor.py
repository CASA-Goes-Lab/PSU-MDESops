from DESops.automata.DFA import DFA
from DESops.basic_operations.observer_comp import observer_comp
from DESops.basic_operations.parallel_comp import parallel_comp
from DESops.supervisory_control.VLPPO import offline_VLPPO


def select_supervisor(arena, Euo, Euc):
    S = DFA()

    Q = list()
    trans = list()
    trans_labels = list()
    vertex = list()
    Q.append(0)
    vertex.append(0)
    while Q:
        q = Q.pop(0)

        transitions = [e[1] for e in arena.vs["out"][q]]
        # max_control_action = max(transitions, key=len)
        index_max_ctr_dec = max(range(len(transitions)), key=transitions.__getitem__)
        # print(transitions[index_max_ctr_dec])
        q2 = arena.vs["out"][q][index_max_ctr_dec]

        for e in max_control_action:
            if e in Euo:
                trans_labels.append(e)
                trans.append((vertex.index(q), vertex.index(q)))
            else:
                # print(e)
                transq2 = [v[0] for v in arena.vs["out"][q2] if v[1] == e]
                # print(transq2)
                if transq2:
                    add_vertex(vertex, Q, transq2[0])
                    trans_labels.append(e)
                    trans.append((vertex.index(q), vertex.index(transq2[0])))

                else:
                    trans_labels.append(e)
                    trans.append((vertex.index(q), vertex.index(q)))

    # Construct graph
    # print(vertex)
    # g.vs["name"] = range(len(vertex))
    # print(trans)
    R.add_vertices(len(vertex))
    R.vs["name"] = [i for i in range(0, g.vcount())]
    R.add_edges(trans, trans_labels)
    return R


def add_vertex(vertex, Q, v):
    if v not in vertex:
        vertex.append(v)
        Q.append(v)


def Q1_state(state, graph=None):
    if isinstance(state, int):
        return len(graph.vs[state]["name"]) == 2
    return len(state["name"]) == 2


def Q2_state(state, graph=None):
    if isinstance(state, int):
        return len(graph.vs[state]["name"]) > 2
    return len(state["name"]) > 2
