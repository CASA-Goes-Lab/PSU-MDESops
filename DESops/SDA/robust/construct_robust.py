import itertools

from DESops.automata.DFA import DFA
from DESops.basic_operations.ureach import unobservable_reach
from DESops.SDA.event_extensions import deleted_event, inserted_event

# from DESops.Event.Event import Event


def construct_arena_opt_with_attacker(
    G, A, Ea, Euo, Euc, X_crit, arena=None, reduced=False, debug=False
):
    # G: input system automata, igraph graph object
    # Ea: set of compromised events
    # Euo:set of unobservable events
    # Euc: set of uncontrollable events
    # reduced: True: use reduced arena construction method (much faster, less states),
    #          False: use full arena construction method (slower, more states)
    #          default: False
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False
    if debug:
        import time

        start_time = time.process_time()

    # TODO: is arena always a DFA?
    if arena is not None:
        arena_provided = False
        arena = DFA()
    else:
        arena_provided = True

    E = set(G.es["label"])
    Eo = set([e for e in E if e not in Euo])
    A1 = set()
    find_A1_sets(A1, G, Euc)
    Ea_e = find_Ea_e_events(G, E, Ea)
    A2 = Ea_e | Eo
    queue = list()
    init_state = (frozenset({0}), 0)
    queue.append(init_state)
    Q1, Q2, h1, h2 = set(), set(), list(), list()
    Q1.add(init_state)
    adj_dict = dict()

    search_opt_with_att(
        G, A, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug
    )
    # print(adj_dict)
    # print(Q1)
    # print(len(Q2))
    convert_to_graph_opt_with_att(arena, G, A, Q1, Q2, h1, h2, init_state, adj_dict)

    Euc_new = Ea_e.union(E)
    Euc_new.add(frozenset(Euc))

    Euo_new = Ea_e.copy()

    if debug:
        print("-----")
        print("Final Vcount: {0}".format(str(arena.vcount())))
        print("Time elapsed: {0}".format(str(time.process_time() - start_time)))
        print("-----")

    if arena_provided:
        return [Euc_new, Euo_new]
    else:
        return [Euc_new, Euo_new, arena]


def convert_to_graph_opt_with_att(arena, G, A, Q1, Q2, h1, h2, init_state, adj_dict):

    # Convert Q1, Q2 states and h1, h2 edges to arena, an Automata
    arena.add_vertices(len(Q1) + len(Q2))
    Q1.remove(init_state)
    V_names = list()
    V_names.append("{" + G.vs["name"][0] + "," + A.vs["name"][0] + "}")
    E_list = list()
    E_events = list()
    # Convert Q1 and Q2 into a dict with name : index
    adj_list = list()
    Q_dict = dict()
    Q_dict[init_state] = 0
    Q = list()
    for i, q in enumerate(Q1, 1):
        q0_names = (
            "{"
            + ",".join([G.vs["name"][l] for l in q[0]])
            + ","
            + A.vs["name"][q[1]]
            + "}"
        )
        t = q0_names
        V_names.append(t)
        Q_dict[q] = i
        Q.append(q)
    for j, q in enumerate(Q2, i + 1):
        q0_names = (
            "{"
            + ",".join([G.vs["name"][l] for l in q[0]])
            + ","
            + A.vs["name"][q[1]]
            + "}"
        )
        q1 = "{" + ",".join({u for u in q[2]}) + "}"
        t = "(" + ",".join([q0_names, q1, str(q[3])]) + ")"
        V_names.append(t)
        Q_dict[q] = j
        Q.append(q)

    adj_list.append([(Q_dict[v[0]], v[1]) for v in adj_dict[init_state]])
    adj_list.extend(
        [[(Q_dict[v[0]], v[1]) for v in adj_dict[Q[i]]] for i, x in enumerate(Q)]
    )
    # print(adj_list)
    # [print(key, value) for key, value in Q_dict.items()]
    # print(V_names)
    # print(len(Q1)+len(Q2))

    for h in h1:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])

    for h in h2:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])

    # print(V_names)
    arena.vs["name"] = V_names
    arena.add_edges(E_list)
    arena.es["label"] = E_events
    arena.vs["out"] = adj_list


def search_opt_with_att(
    G, A, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug
):
    X_crit = set([v.index for v in G.vs.select(name_in=X_crit)])

    while queue:
        # print(len(queue))
        q = queue.pop(0)
        if Q1_state(q):
            # Q1 to Q2 transitions
            # events = gamma_feasible(G, q, Euc)
            events = A1
            adj = list()
            for e in events:
                next_state_set = UR(q[0], G, e, Euo)
                target = (next_state_set, q[1], frozenset(e), None)
                h1.append((q, e, target))
                adj.append((target, e))
                add_to_arena_opt_with_att(
                    Q1, Q2, target, queue, X_crit, adj_dict, debug
                )
            adj_dict[q] = adj

        elif Q2_state(q):
            # Various types of Q2 transitions
            # print(q)
            adj = list()
            for e in A2:
                if q[3] == e and e in Ea:
                    # 2nd type, Q2->Q1
                    target = (q[0], q[1])
                    h2.append((q, e, target))
                    add_to_arena_opt_with_att(
                        Q1, Q2, target, queue, X_crit, adj_dict, debug
                    )
                    adj.append((target, e))

                if q[3] == None:
                    if (
                        e in Eo
                        and e in G.es(_source_in=q[0])["label"]
                        and e in A.es(_source=q[1])["label"]
                        and e in q[2]
                    ):
                        # 1st type, Q2->Q1
                        stA = [ad[0] for ad in A.vs["out"][q[1]] if ad[1] == e]
                        if stA:
                            stA = stA[0]

                        next_state_set = NX(e, q[0], G)
                        target = (next_state_set, stA)
                        h2.append((q, e, target))
                        add_to_arena_opt_with_att(
                            Q1, Q2, target, queue, X_crit, adj_dict, debug
                        )
                        adj.append((target, e))

                    if isinstance(e, Event) and e.inserted and e.label in q[2]:
                        if (
                            "(" + ", ".join(e.name()) + ")"
                            in A.es(_source=q[1])["label"]
                        ):
                            # 3rd type, Q2->Q2
                            # print('_'.join(e.name()))
                            stA = [
                                ad[0]
                                for ad in A.vs["out"][q[1]]
                                if ad[1] == "(" + ", ".join(e.name()) + ")"
                            ]
                            if stA:
                                stA = stA[0]
                            target = (q[0], stA, q[2], M(e))
                            h2.append((q, e.name(), target))
                            add_to_arena_opt_with_att(
                                Q1, Q2, target, queue, X_crit, adj_dict, debug
                            )
                            adj.append((target, e.name()))

                    if (
                        isinstance(e, Event)
                        and e.deleted
                        and e.label in G.es(_source_in=q[0])["label"]
                        and e.label in q[2]
                    ):
                        if (
                            "(" + ", ".join(e.name()) + ")"
                            in A.es(_source=q[1])["label"]
                        ):
                            # 4th type, Q2->Q2
                            # proj is just M(e) since e is in Ead (not in Eai)
                            stA = [
                                ad[0]
                                for ad in A.vs["out"][q[1]]
                                if ad[1] == "(" + ", ".join(e.name()) + ")"
                            ]
                            if stA:
                                stA = stA[0]
                            nx = NX(e.label, q[0], G)
                            next_state_set = UR(nx, G, q[2], Euo)
                            target = (next_state_set, stA, q[2], None)
                            # print(target)
                            # if target[0] == frozenset():
                            # print(q[1])
                            # print(UR(frozenset({3}),G,q[1],Euo))
                            # print(e.label)
                            h2.append((q, e.name(), target))
                            add_to_arena_opt_with_att(
                                Q1, Q2, target, queue, X_crit, adj_dict, debug
                            )
                            adj.append((target, e.name()))
            # print(q)
            adj_dict[q] = adj


def construct_arena_opt(
    G, Ea, Euo, Euc, X_crit, arena=None, reduced=False, debug=False
):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata, igraph graph object
    # Ea: set of compromised events
    # Euo:set of unobservable events
    # Euc: set of uncontrollable events
    # reduced: True: use reduced arena construction method (much faster, less states),
    #          False: use full arena construction method (slower, more states)
    #          default: False
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False

    if arena is not None:
        arena_provided = False
        arena = DFA()
    else:
        arena_provided = True

    if debug:
        import time

        start_time = time.process_time()
    E = set(G.es["label"])
    Eo = set([e for e in E if e not in Euo])
    A1 = set()
    # find_A1_sets(A1, G, Euc)
    singleton_A1_set(A1, G, E, Euc)
    print(A1)
    Ea_e = find_Ea_e_events(G, E, Ea)
    A2 = Ea_e | Eo
    queue = list()
    init_state = frozenset({0})
    queue.append(init_state)
    Q1, Q2, h1, h2 = set(), set(), list(), list()
    Q1.add(init_state)
    adj_dict = dict()

    search_opt(
        G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug
    )
    # print(adj_dict)
    # print(Q1)
    # print(len(Q2))
    convert_to_graph_opt(arena, G, Q1, Q2, h1, h2, init_state, adj_dict)
    Euc_new = {e.name() for e in Ea_e}
    Euc_new = Euc_new.union(E)
    Euc_new.add(frozenset(Euc))
    Euo_new = {e.name() for e in Ea_e}
    if debug:
        print("-----")
        print("Final Vcount: {0}".format(str(arena.vcount())))
        print("Time elapsed: {0}".format(str(time.process_time() - start_time)))
        print("-----")

    if arena_provided:
        return [Euc_new, Euo_new]
    else:
        return [Euc_new, Euo_new, arena]


def search_opt(
    G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, X_crit, adj_dict, debug
):
    X_crit = set([v.index for v in G.vs.select(name_in=X_crit)])

    while queue:
        # print(len(queue))
        q = queue.pop(0)
        if Q1_state_opt(q):
            # Q1 to Q2 transitions
            # events = gamma_feasible(G, q, Euc)
            events = A1
            adj = list()
            for e in events:
                next_state_set = UR(q, G, e, Euo)
                target = (next_state_set, frozenset(e), None)
                h1.append((q, e, target))
                adj.append((target, e))
                add_to_arena_opt(Q1, Q2, target, queue, X_crit, adj_dict, debug)
            adj_dict[q] = adj

        elif Q2_state_opt(q):
            # Various types of Q2 transitions
            # print(q)
            # print(type(q))
            adj = list()
            for e in A2:
                if q[2] == e and e in Ea:
                    # 2nd type, Q2->Q1
                    target = q[0]
                    h2.append((q, e, target))
                    add_to_arena_opt(Q1, Q2, target, queue, X_crit, adj_dict, debug)
                    adj.append((target, e))

                if q[2] == None:
                    trans_set = {t[1]["label"] for v in q[0] for t in G.vs["out"][v]}
                    # Why is this {e in trans_set} and then 13 lines down {e.label in trans_set} ?
                    # Some e aren't Event objects?
                    if e in Eo and e in trans_set and e in q[1]:
                        # 1st type, Q2->Q1
                        target = NX(e, q[0], G)
                        h2.append((q, e, target))
                        add_to_arena_opt(Q1, Q2, target, queue, X_crit, adj_dict, debug)
                        adj.append((target, e))
                    if isinstance(e, Event) and e.inserted and e.label in q[1]:
                        # 3rd type, Q2->Q2
                        # print('_'.join(e.name()))
                        target = (q[0], q[1], M(e))
                        h2.append((q, e.name(), target))
                        add_to_arena_opt(Q1, Q2, target, queue, X_crit, adj_dict, debug)
                        adj.append((target, e.name()))
                    if (
                        isinstance(e, Event)
                        and e.deleted
                        and e.label in trans_set
                        and e.label in q[1]
                    ):
                        # 4th type, Q2->Q2
                        # proj is just M(e) since e is in Ead (not in Eai)
                        nx = NX(e.label, q[0], G)
                        next_state_set = UR(nx, G, q[1], Euo)
                        target = (next_state_set, q[1], None)
                        # if target[0] == frozenset():
                        # print(q[1])
                        # print(UR(frozenset({3}),G,q[1],Euo))
                        # print(e.label)
                        h2.append((q, e.name(), target))
                        add_to_arena_opt(Q1, Q2, target, queue, X_crit, adj_dict, debug)
                        adj.append((target, e.name()))
            # print(q)
            adj_dict[q] = adj


def convert_to_graph_opt(arena, G, Q1, Q2, h1, h2, init_state, adj_dict):
    # Convert Q1, Q2 states and h1, h2 edges to arena, an igraph Graph
    arena.add_vertices(len(Q1) + len(Q2))
    # [print(key, value) for key, value in adj_dict.items()]
    Q1.remove(init_state)
    V_names = list()
    V_names.append("{" + G.vs["name"][0] + "}")
    E_list = list()
    E_events = list()
    # Convert Q1 and Q2 into a dict with name : index
    adj_list = list()
    Q_dict = dict()
    Q_dict[init_state] = 0
    Q = list()
    for i, q in enumerate(Q1, 1):
        q0_names = "{" + ",".join([G.vs["name"][l] for l in q]) + "}"
        t = q0_names
        V_names.append(t)
        Q_dict[q] = i
        Q.append(q)
    for j, q in enumerate(Q2, i + 1):
        q0_names = "{" + ",".join([G.vs["name"][l] for l in q[0]]) + "}"
        q1 = "{" + ",".join({u for u in q[1]}) + "}"
        t = "(" + ",".join([q0_names, q1, str(q[2])]) + ")"
        V_names.append(t)
        Q_dict[q] = j
        Q.append(q)

    adj_list.append([(Q_dict[v[0]], v[1]) for v in adj_dict[init_state]])
    adj_list.extend(
        [[(Q_dict[v[0]], v[1]) for v in adj_dict[Q[i]]] for i, x in enumerate(Q)]
    )
    # print(adj_list)
    # [print(key, value) for key, value in Q_dict.items()]
    # print(V_names)
    # print(len(Q1)+len(Q2))

    for h in h1:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])
    for h in h2:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])

    # print(V_names)
    arena.vs["name"] = V_names
    arena.add_edges(E_list)
    arena.es["label"] = E_events
    arena.vs["out"] = adj_list


def construct_arena(arena, G, Ea, Euo, Euc, reduced=False, debug=False):
    """
    Need this still?
    Or will be deleted

    """
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata, igraph graph object
    # Ea: set of compromised events
    # Euo:set of unobservable events
    # Euc: set of uncontrollable events
    # reduced: True: use reduced arena construction method (much faster, less states),
    #          False: use full arena construction method (slower, more states)
    #          default: False
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False
    if debug:
        import time

        start_time = time.process_time()
    E = set(G.es["label"])
    Eo = set([e for e in E if e not in Euo])
    A1 = set()
    find_A1_sets(A1, G, Euc)
    Ea_e = find_Ea_e_events(G, E, Ea)
    A2 = Ea_e | Eo
    queue = list()
    init_state = (frozenset({0}), frozenset({0}))
    queue.append(init_state)
    Q1, Q2, h1, h2 = set(), set(), list(), list()
    Q1.add(init_state)

    search(G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, reduced, debug)

    convert_to_graph(arena, G, Q1, Q2, h1, h2, init_state)
    Euc_new = Ea_e.union(Euc)
    Euo_new = Ea_e
    if debug:
        print("-----")
        print("Final Vcount: {0}".format(str(arena.vcount())))
        print("Time elapsed: {0}".format(str(time.process_time() - start_time)))
        print("-----")

    return [Euc_new, Euo_new]


def search(G, Q1, Q2, h1, h2, queue, Eo, Euo, Euc, Ea, A1, A2, reduced, debug):
    """
    Need this still?
    Or will be deleted

    """
    while queue:
        q = queue.pop(0)
        if Q1_state(q):
            # Q1 to Q2 transitions
            if not reduced:
                events = A1
            if reduced:
                events = gamma_feasible(G, q, Euc)
            for e in events:
                target = (UR(q[0], G, e, Euo), UR(q[1], G, e, Euo), frozenset(e), None)
                h1.append((q, e, target))
                add_to_arena(Q1, Q2, target, queue, debug)
        elif Q2_state(q):
            # Various types of Q2 transitions
            for e in A2:
                if M(e) not in q[2]:
                    continue
                if q[3] == e and e in Ea:
                    # 2nd type, Q2->Q1
                    target = (q[0], NX(e, q[1], G))
                    h2.append((q, e, target))
                    add_to_arena(Q1, Q2, target, queue, debug)
                if q[3] == None:
                    if e in Eo and e in G.es(_source_in=q[0])["label"]:
                        # 1st type, Q2->Q1
                        target = (NX(e, q[0], G), NX(e, q[1], G))
                        h2.append((q, e, target))
                        add_to_arena(Q1, Q2, target, queue, debug)
                    if isinstance(e, Event) and e.inserted:
                        # 3rd type, Q2->Q2
                        target = (q[0], q[1], q[2], M(e))
                        h2.append((q, e, target))
                        add_to_arena(Q1, Q2, target, queue, debug)
                    if (
                        isinstance(e, Event)
                        and e.deleted
                        and e.label in G.es(_source_in=q[0])["label"]
                    ):
                        # 4th type, Q2->Q2
                        # proj is just M(e) since e is in Ead (not in Eai)
                        target = (
                            UR(NX(e.label, q[0], G), G, q[2], Euo),
                            q[1],
                            q[2],
                            None,
                        )
                        h2.append((q, e, target))
                        add_to_arena(Q1, Q2, target, queue, debug)


def add_to_arena(Q1, Q2, x, queue, debug):
    if Q1_state(x):
        if x not in Q1:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))
            Q1.add(x)
            queue.append(x)
    if Q2_state(x):
        if x not in Q2:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))
            Q2.add(x)
            queue.append(x)


def add_to_arena_opt(Q1, Q2, x, queue, X_crit, adj_list, debug):
    if Q1_state_opt(x):
        if x not in Q1:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))

            Q1.add(x)
            # print(set(x).intersection(X_crit))
            if X_crit.intersection(x):
                # print(set(x),X_crit)
                queue.append(x)
            else:
                adj_list[x] = list()

    if Q2_state_opt(x):
        if x not in Q2:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))

            Q2.add(x)

            if not X_crit.intersection(x[0]):
                # print(set(x[0]),X_crit)
                queue.append(x)
            else:
                adj_list[x] = list()


def add_to_arena_opt_with_att(Q1, Q2, x, queue, X_crit, adj_list, debug):
    """
    This appears to be redundant, identical to add_to_arena_opt
    """
    if Q1_state(x):
        if x not in Q1:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))

            Q1.add(x)
            # print(set(x).intersection(X_crit))
            if not X_crit.intersection(x):
                # print(set(x),X_crit)
                queue.append(x)
            else:
                adj_list[x] = list()

    if Q2_state(x):
        if x not in Q2:
            if debug and ((len(Q1) + len(Q2)) % 10000 == 0):
                print("Vcount: {0}".format(len(Q1) + len(Q2)))

            Q2.add(x)

            if not X_crit.intersection(x[0]):
                # print(set(x[0]),X_crit)
                queue.append(x)
            else:
                adj_list[x] = list()


def NX(event, S, G):
    # NX defined in (4) in paper.
    # Observable reach (or next set of states)
    # Given event in Eo and a set of states in G (and the graph G)
    # Returns a frozen set of states in X that are reached by event from states in S
    # Assuming event is in Eo:
    next_states = set()
    for u in S:
        # TODO: test this with a set for performance.
        #   Less construction time for list but also longer
        #   search for event in event_list
        event_list = [e[1] for e in G.vs[u]["out"]]
        if event in event_list:
            next_states.add(edges[0].target)
    if not next_states:
        # If event is infeasible at all states in S, set NX to X (all states in G)
        return frozenset(i for i in range(G.vcount()))
    return frozenset(next_states)


def convert_to_graph(arena, G, Q1, Q2, h1, h2, init_state):
    # Convert Q1, Q2 states and h1, h2 edges to arena, an igraph Graph
    arena.add_vertices(len(Q1) + len(Q2))
    Q1.remove(init_state)
    V_names = list()
    V_names.append(([G.vs["name"][0]], [G.vs["name"][0]]))
    E_list = list()
    E_events = list()
    # Convert Q1 and Q2 into a dict with name : index
    Q_dict = dict()
    Q_dict[init_state] = 0
    for i, q in enumerate(Q1, 1):
        q0_names = [G.vs["name"][l] for l in q[0]]
        q1_names = [G.vs["name"][l] for l in q[1]]
        t = (q0_names, q1_names)
        V_names.append(t)
        Q_dict[q] = i
    for j, q in enumerate(Q2, i + 1):
        q0_names = [G.vs["name"][l] for l in q[0]]
        q1_names = [G.vs["name"][l] for l in q[1]]
        q2 = {u for u in q[2]}
        t = (q0_names, q1_names, q2, q[3])
        V_names.append(t)
        Q_dict[q] = j
    for h in h1:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])
    for h in h2:
        source = Q_dict[h[0]]
        target = Q_dict[h[2]]
        E_list.append((source, target))
        E_events.append(h[1])

    arena.vs["name"] = V_names
    arena.add_edges(E_list)
    arena.es["label"] = E_events


def Q1_state(c):
    return len(c) == 2


def Q2_state(c):
    return len(c) > 2


def Q1_state_opt(c):
    return isinstance(c, frozenset)


def Q2_state_opt(c):
    return isinstance(c, tuple)


def UR(set_of_states, graph, event, Euo):
    Euo_inter = event.intersection(Euo)
    return frozenset(ureach_from_set_adj(set_of_states, graph, Euo_inter))


def find_A1_sets(A1, G, Euc):
    # A1 is the set of admissable control decisions
    E = set(G.es["label"])
    for l in range(len(E) + 1):
        A1.update(frozenset(Euc.union(comb)) for comb in itertools.combinations(E, l))


def singleton_A1_set(A1, G, E, Euc):

    A1.add(frozenset())
    print(A1)
    for l in E.difference(Euc):
        # print(l)
        A1.add(frozenset(Euc.union({l})))


def find_Ea_e_events(G, E, Ea):
    Ea_i = [inserted_event(e) for e in Ea]
    Ea_d = [deleted_event(e) for e in Ea]
    return set(Ea_i) | set(Ea_d)


def M(e):
    if isinstance(e, Event):
        return e.label
    return e


def gamma_feasible(G, q, Euc):
    # possible_events = set(G.es(_source_in = q[1])["label"])
    possible_events = set(G.es(_source_in=q)["label"])
    all_sets = set()
    for l in range(len(possible_events) + 1):
        all_sets.update(
            frozenset(Euc.union(comb))
            for comb in itertools.combinations(possible_events, l)
        )
    return all_sets
