import igraph as ig
import DESops.SDA.event_extensions as ee
from DESops.automata.event import Event
from DESops.automata.PFA import PFA
from DESops.error import InvalidAutomataTypeError


def construct_MDP(G, H, Ea, X_crit):
    # 1. Construct MDP style graph
    # 2. eliminate zero-cost cycles
    # 3. convert to desired type(?) repeated game/finite cost/infinite cost
    # ~4. Use LP solution or value iteration to generate an optimal attack strategy (outside this file)

    if not isinstance(G, PFA):
        raise InvalidAutomataTypeError(
            "Expected G as PFA, instead got {}".format(type(G))
        )

    A = ig.Graph(directed=True)
    Q = list()
    X = set()
    if G.vcount() == 0 or H.vcount() == 0:
        return A
    init_state = (0, 0, "eps")
    Q.append(init_state)
    X.add(init_state)
    E = list()
    P = list()
    while Q:
        q = Q.pop(0)
        if unsafe(G, X_crit, q):
            if q[2] == "eps":
                if (q, "tau", q) not in E:
                    E.append((q, "tau", q))
                    P.append(1)
            else:
                v = (q[0], q[1], "eps")
                X.add(v)
                if (q, "tau", v) not in E:
                    E.append((q, "tau", v))
                    P.append(1)

                if (v, "tau", v) not in E:
                    E.append((v, "tau", v))
                    P.append(1)
            continue

        for e in H.vs["out"][q[1]]:
            e_label = e[1]

            if e_label in Ea:
                xH_i = e[0]
                v_i = (q[0], xH_i, "eps")
                if (q, ee.inserted_event(e_label), v_i) not in E:
                    E.append((q, ee.inserted_event(e_label), v_i))
                    P.append(1)
                add_state(X, v_i, Q)

            # Assumed here that the system G is deterministic (is a DFA)
            G_transitions = [t for t in G.vs["out"][q[0]] if t[1] == e_label]

            if not G_transitions:
                continue

            xG = G_transitions[0][0]
            if e_label in Ea:
                xH = q[1]
                xHe = e[0]
                vd = (xG, xH, e_label)

                prob = MDP_prob(G, H, q[0], q[1], e_label)
                if vd not in X:
                    X.add(vd)
                if (q, "tau", vd) not in E:
                    E.append((q, "tau", vd))
                    P.append(prob)

                vd2 = (xG, xH, "eps")
                add_state(X, vd2, Q)

                if (vd, ee.deleted_event(e_label), vd2) not in E:
                    E.append((vd, ee.deleted_event(e_label), vd2))
                    P.append(1)

                vd3 = (xG, xHe, "eps")
                if (vd, "nd", vd3) not in E:
                    E.append((vd, "nd", vd3))
                    P.append(1)

                add_state(X, vd3, Q)
            else:
                xH = e[0]
                v = (xG, xH, e_label)
                prob = MDP_prob(G, H, q[0], q[1], e_label)
                if (q, "tau", v) not in E:
                    E.append((q, "tau", v))
                    P.append(prob)

                add_state(X, v, Q)

    for x in X:
        if not [y[2] for y in E if y[0] == x]:
            # print(x)
            if x[2] == "eps":
                if (x, "tau", x) not in E:
                    E.append((x, "tau", x))
                    P.append(1)
            else:
                v = (x[0], x[1], "eps")
                X.add(v)
                if (x, "tau", v) not in E:
                    E.append((x, "tau", v))
                    P.append(1)
                if (v, "tau", v) not in E:
                    E.append((v, "tau", v))
                    P.append(1)

    # Convert X,E into graph A
    A.add_vertices(len(X))
    X.remove(init_state)
    states = list()
    states.append(init_state)
    states.extend(X)
    trans_labels = [l[1] for l in E]

    trans = [(states.index(l[0]), states.index(l[2])) for l in E]

    A.vs["name"] = states
    A.add_edges(trans)
    A.es["label"] = trans_labels
    A.es["prob"] = P
    A.es["cost"] = [0 if e == "tau" else 1 for e in trans_labels]

    A.vs["name"] = [
        (G.vs["name"][v[0]], H.vs["name"][v[1]], v[2]) for v in A.vs["name"]
    ]

    return A


# Calculates the Probability of generating e from state xG in G (plant) and state xH in H (sup)
def MDP_prob(G, H, xG, xH, e):
    # edge = G.es(_source = xG)
    G_out = G.vs["out"][xG]
    H_out = H.vs["out"][xH]
    intersection = set(i[1] for i in G_out).intersection(j[1] for j in H_out)
    prob_e = float([ev[2] for ev in G_out if ev[1] == e][0])
    prob_t = sum([float(ev[2]) for ev in G_out if ev[1] in intersection])
    # assert(prob_t > 0)
    return prob_e / prob_t


def add_state(X, v, Q):
    if v not in X:
        X.add(v)
        Q.append(v)


def unsafe(G, X_crit, v):
    if isinstance(v, tuple):
        return G.vs["name"][v[0]] in X_crit
    else:
        return False


def edited(v):
    # edited vertices are of the form (xG,xH,<edited>)
    # whereas other vertices are (xG,xH)
    return len(v) == 3
