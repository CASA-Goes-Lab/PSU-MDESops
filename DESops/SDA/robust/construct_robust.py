import itertools

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.SDA.event_extensions import (
    deleted_event,
    inserted_event,
    is_deleted,
    is_inserted,
    is_unedited,
    unedited_event,
)


def construct_robust_arena(G, X_crit, Ea, A=None):
    # G: input system automata, igraph graph object
    # X_crit: critical state names
    # Ea: set of compromised events
    # A: optionally provide attack specification

    arena = DFA()
    if G.vcount() == 0:
        return arena

    E = G.events
    Euo = G.Euo
    Euc = G.Euc

    Ea_e = find_Ea_e_events(G, E, Ea)

    queue = list()
    if A is not None:
        init_state = (frozenset({0}), 0)
    else:
        init_state = frozenset({0})
    queue.append((init_state, 0))
    # Q1, Q2 dict maps vertex names to index
    Q1, Q2 = dict(), dict()
    h1_pairs, h1_labels, h2_pairs, h2_labels = list(), list(), list(), list()

    Q1[init_state] = 0

    # List of Q1 & Q2 states in order (to be used for naming)
    state_list = list()
    state_list.append(init_state)
    if A is not None:
        X_crit_vert = search_w_att(
            G,
            A,
            Q1,
            Q2,
            state_list,
            h1_pairs,
            h1_labels,
            h2_pairs,
            h2_labels,
            queue,
            Ea,
            X_crit,
        )
    else:
        X_crit_vert = search(
            G,
            Q1,
            Q2,
            state_list,
            h1_pairs,
            h1_labels,
            h2_pairs,
            h2_labels,
            queue,
            Ea,
            X_crit,
        )

    Qname = state2str(state_list, G, A)
    arena.add_vertices(len(Q1) + len(Q2), Qname)

    arena.add_edges(h1_pairs, h1_labels)
    arena.add_edges(h2_pairs, h2_labels)

    arena.events.update(G.events)

    arena.X_crit = {Qname[i] for i in X_crit_vert}

    # The Euc for meta SCP = A2 U {Euc}
    Euc_new = Ea_e.union(E)
    Euc_new.add(Event(frozenset(Euc)))

    # Euo for meta SCP = Ea_e, i.e. set of modified events
    Euo_new = Ea_e.copy()

    arena.Euc.update(Euc_new)
    arena.Euo.update(Euo_new)
    return arena


def search_w_att(
    G,
    A,
    Q1,
    Q2,
    state_list,
    h1_pairs,
    h1_labels,
    h2_pairs,
    h2_labels,
    queue,
    Ea,
    X_crit,
):
    Euo = G.Euo
    Euc = G.Euc

    X_crit_vert = set()
    X_crit = set([v.index for v in G.vs.select(name_in=X_crit)])

    vertex_counter = 1
    A1 = set()
    find_A1_sets(A1, G, Euc)

    Ea_e = find_Ea_e_events(G, G.events, Ea)
    Eo = {e for e in G.events if e not in Euo}
    # A2: set edited or observable events (sigma_m in paper)
    A2 = Ea_e.union(Eo)

    while queue:
        q, source_ind = queue.pop(0)

        if Q1_state(q):
            # Q1 to Q2 transitions

            for ctr_dec in A1:
                uo_ctr_dec = frozenset(Euo.intersection(ctr_dec.label))
                next_S1 = G.UR.from_set(q[0], uo_ctr_dec, freeze_result=True)

                target = (next_S1, ctr_dec.label, None, q[-1])

                vertex_counter = add_Q2_state(
                    Q2,
                    target,
                    ctr_dec,
                    queue,
                    X_crit,
                    X_crit_vert,
                    vertex_counter,
                    source_ind,
                    h1_pairs,
                    h1_labels,
                    state_list,
                )

        elif Q2_state(q):
            # Various types of Q2 transitions
            G_out_labels = {t[1] for v in q[0] for t in G.vs[v]["out"]}

            A_out_labels = {v[1] for v in A.vs[q[-1]]["out"]}
            for e in A2:
                if q[2] == e and e in Ea:
                    # 2nd type, Q2->Q1
                    target = (q[0], q[-1])

                    vertex_counter = add_Q1_state(
                        Q1,
                        target,
                        e,
                        queue,
                        X_crit,
                        X_crit_vert,
                        vertex_counter,
                        source_ind,
                        h2_pairs,
                        h2_labels,
                        state_list,
                    )

                if q[2] is None:
                    if (
                        e not in Euo
                        and e in G_out_labels
                        and e in A_out_labels
                        and e in q[1]
                    ):
                        # 1st type, Q2->Q1
                        stA = [ad[0] for ad in A.vs["out"][q[-1]] if ad[1] == e]
                        if stA:
                            stA = stA[0]

                        next_state_set = NX(e, q[0], G)
                        target = (next_state_set, stA)

                        vertex_counter = add_Q1_state(
                            Q1,
                            target,
                            e,
                            queue,
                            X_crit,
                            X_crit_vert,
                            vertex_counter,
                            source_ind,
                            h2_pairs,
                            h2_labels,
                            state_list,
                        )

                    if is_inserted(e) and unedited_event(e) in q[1]:
                        if e in A_out_labels:
                            # 3rd type, Q2->Q2
                            stA = [ad[0] for ad in A.vs["out"][q[-1]] if ad[1] == e]
                            if stA:
                                stA = stA[0]
                            target = (q[0], q[1], unedited_event(e), stA)

                            vertex_counter = add_Q2_state(
                                Q2,
                                target,
                                e,
                                queue,
                                X_crit,
                                X_crit_vert,
                                vertex_counter,
                                source_ind,
                                h2_pairs,
                                h2_labels,
                                state_list,
                            )

                if (
                    is_deleted(e)
                    and unedited_event(e) in G_out_labels
                    and unedited_event(e) in q[1]
                ):
                    if e in A_out_labels:
                        # 4th type, Q2->Q2
                        # proj is just M(e) since e is in Ead (not in Eai)
                        stA = [ad[0] for ad in A.vs["out"][q[-1]] if ad[1] == e]
                        if stA:
                            stA = stA[0]

                        nx = NX(unedited_event(e), q[0], G)
                        uo_q2 = frozenset(Euo.intersection(q[1]))
                        next_state_set = G.UR.from_set(nx, uo_q2, freeze_result=True)
                        target = (next_state_set, q[1], None, stA)
                        vertex_counter = add_Q2_state(
                            Q2,
                            target,
                            e,
                            queue,
                            X_crit,
                            X_crit_vert,
                            vertex_counter,
                            source_ind,
                            h2_pairs,
                            h2_labels,
                            state_list,
                        )
    return X_crit_vert


def search(
    G, Q1, Q2, state_list, h1_pairs, h1_labels, h2_pairs, h2_labels, queue, Ea, X_crit,
):
    Euo = G.Euo
    Euc = G.Euc

    X_crit = set([v.index for v in G.vs.select(name_in=X_crit)])

    vertex_counter = 1

    X_crit_vert = set()

    A1 = set()
    find_A1_sets(A1, G, Euc)

    Ea_e = find_Ea_e_events(G, G.events, Ea)
    Eo = {e for e in G.events if e not in Euo}
    # A2: set edited or observable events (sigma_m in paper)
    A2 = Ea_e.union(Eo)

    while queue:
        q, source_ind = queue.pop(0)
        if Q1_state(q):
            # Q1 to Q2 transitions

            for ctr_dec in A1:
                uo_ctr_dec = frozenset(Euo.intersection(ctr_dec.label))
                next_S1 = G.UR.from_set(q, uo_ctr_dec, freeze_result=True)

                target = (next_S1, ctr_dec.label, None)

                vertex_counter = add_Q2_state(
                    Q2,
                    target,
                    ctr_dec,
                    queue,
                    X_crit,
                    X_crit_vert,
                    vertex_counter,
                    source_ind,
                    h1_pairs,
                    h1_labels,
                    state_list,
                )

        # if not Q1 state, q is a Q2 state:
        else:
            # Various types of Q2 transitions
            for e in A2:
                if q[2] == e and e in Ea:
                    # 2nd type, Q2->Q1
                    target = q[0]
                    vertex_counter = add_Q1_state(
                        Q1,
                        target,
                        e,
                        queue,
                        X_crit,
                        X_crit_vert,
                        vertex_counter,
                        source_ind,
                        h2_pairs,
                        h2_labels,
                        state_list,
                    )

                elif q[2] is None:
                    trans_set = {t[1] for v in q[0] for t in G.vs["out"][v]}
                    if e not in Euo and e in trans_set and e in q[1]:
                        # 1st type, Q2->Q1
                        target = NX(e, q[0], G)

                        vertex_counter = add_Q1_state(
                            Q1,
                            target,
                            e,
                            queue,
                            X_crit,
                            X_crit_vert,
                            vertex_counter,
                            source_ind,
                            h2_pairs,
                            h2_labels,
                            state_list,
                        )

                    elif is_inserted(e) and unedited_event(e) in q[1]:
                        # 3rd type, Q2->Q2
                        target = (q[0], q[1], unedited_event(e))
                        vertex_counter = add_Q2_state(
                            Q2,
                            target,
                            e,
                            queue,
                            X_crit,
                            X_crit_vert,
                            vertex_counter,
                            source_ind,
                            h2_pairs,
                            h2_labels,
                            state_list,
                        )

                    elif (
                        is_deleted(e)
                        and unedited_event(e) in trans_set
                        and unedited_event(e) in q[1]
                    ):
                        # 4th type, Q2->Q2
                        # proj is just M(e) since e is in Ead (not in Eai)
                        nx = NX(unedited_event(e), q[0], G)
                        uo_q2 = frozenset(Euo.intersection(q[1]))
                        next_state_set = G.UR.from_set(nx, uo_q2, freeze_result=True)
                        target = (next_state_set, q[1], None)

                        vertex_counter = add_Q2_state(
                            Q2,
                            target,
                            e,
                            queue,
                            X_crit,
                            X_crit_vert,
                            vertex_counter,
                            source_ind,
                            h2_pairs,
                            h2_labels,
                            state_list,
                        )

    return X_crit_vert


def add_Q1_state(
    Q1,
    x,
    e,
    queue,
    X_crit,
    X_crit_vert,
    vertex_counter,
    source_ind,
    h_pairs,
    h_labels,
    state_list,
):
    if x not in Q1:
        Q1[x] = vertex_counter

        # x[0] of using attack strategy, x if using all-out (A not specified)
        state_estimate = x[0] if isinstance(x, tuple) else x

        if not X_crit.intersection(state_estimate):
            queue.append((x, vertex_counter))
        else:
            X_crit_vert.add(vertex_counter)

        state_list.append(x)

        h_pairs.append((source_ind, vertex_counter))
        h_labels.append(e)

        return vertex_counter + 1

    target_ind = Q1[x]
    h_pairs.append((source_ind, target_ind))
    h_labels.append(e)

    return vertex_counter


def add_Q2_state(
    Q2,
    x,
    e,
    queue,
    X_crit,
    X_crit_vert,
    vertex_counter,
    source_ind,
    h_pairs,
    h_labels,
    state_list,
):
    if x not in Q2:
        Q2[x] = vertex_counter

        if not X_crit.intersection(x[0]):
            queue.append((x, vertex_counter))
        else:
            X_crit_vert.add(vertex_counter)

        h_pairs.append((source_ind, vertex_counter))
        h_labels.append(e)

        state_list.append(x)

        return vertex_counter + 1

    target_ind = Q2[x]
    h_pairs.append((source_ind, target_ind))
    h_labels.append(e)
    return vertex_counter


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
        out_dict = {e[1]: e[0] for e in G.vs[u]["out"]}
        if event in out_dict:
            next_states.add(out_dict[event])
    if not next_states:
        # If event is infeasible at all states in S, set NX to X (all states in G)
        return frozenset(i for i in range(G.vcount()))
    return frozenset(next_states)


def Q1_state(c):
    if isinstance(c, frozenset):
        return True
    # o.w. tuple with only 2 entries
    return len(c) == 2


def Q2_state(c):
    return not Q1_state(c)


def state2str(state_list, G, A=None):
    Qname = list()

    unpack_names_G = lambda x: "{" + ",".join(G.vs["name"][i] for i in x) + "}"

    unpack_events = lambda x: "{" + ",".join(str(i) for i in x) + "}"
    pack_names = lambda x: "(" + ",".join(i for i in x) + ")"

    for v in state_list:
        if Q1_state(v):
            if A is not None:
                Qname.append(
                    "Q1" + pack_names((unpack_names_G(v[0]), A.vs["name"][v[-1]]))
                )
            else:
                Qname.append("Q1" + pack_names(unpack_names_G(v)))
        elif Q2_state(v):
            name_s1 = unpack_names_G(v[0])
            name_g = unpack_events(v[1])
            if A is not None:
                Qname.append(
                    "Q2" + pack_names((name_s1, A.vs["name"][v[-1]], name_g, str(v[2])))
                )
            else:
                Qname.append("Q2" + pack_names((name_s1, name_g, str(v[2]))))
    return Qname


def find_A1_sets(A1, G, Euc):
    # A1 is the set of admissable control decisions
    E = set(G.es["label"])
    for l in range(len(E) + 1):
        A1.update(
            Event(frozenset(Euc.union(comb))) for comb in itertools.combinations(E, l)
        )


def singleton_A1_set(A1, G, E, Euc):

    A1.add(Event(frozenset()))
    for l in E.difference(Euc):
        A1.add(Event(frozenset(Euc.union({l}))))


def find_Ea_e_events(G, E, Ea):
    Ea_i = [inserted_event(e) for e in Ea]
    Ea_d = [deleted_event(e) for e in Ea]
    return set(Ea_i) | set(Ea_d)


def select_robust_supervisor(arena):
    # Selects a supervisor from the arena (with safety violations pruned)
    # Use this after solving the meta-supervisory control problem, i.e.
    #   >>> arena = d.SDA.construct_robust_arena(...)
    #   >>> arena_sup = d.supervisor.supremal_sublanguage(arena, mode"controllable-normal")
    #   >>> robust_sup = d.SDA.select_supervisor(arena_sup)

    S = DFA()
    if arena.vcount() == 0:
        return S
    Q = list()
    trans = list()
    trans_labels = list()
    vertex_dict = dict()
    Q.append((0, 0))
    vertex_counter = 0
    vertex_dict[0] = vertex_counter
    while Q:
        source_ind, q = Q.pop(0)

        transitions = [e[1].label for e in arena.vs["out"][q]]
        if not transitions:
            continue

        index_max_ctr_dec = max(range(len(transitions)), key=transitions.__getitem__)

        max_cntr_vert = arena.vs["out"][q][index_max_ctr_dec][0]
        next_q2 = arena.vs["out"][max_cntr_vert]

        for q2 in next_q2:
            e = q2[1]
            if e in arena.Euo:
                # self loop for unobservable:
                trans.append((source_ind, source_ind))
                trans_labels.append(e)
            else:
                # if trans
                transq2 = q2[0]
                vertex_counter = add_vertex(
                    arena, vertex_dict, Q, transq2, vertex_counter
                )
                trans_labels.append(e)
                trans.append((source_ind, vertex_dict[transq2]))

    S.add_vertices(len(vertex_dict))
    S.add_edges(trans, trans_labels)
    S.events.update(
        e for e in arena.events if not isinstance(e.label, frozenset) and is_unedited(e)
    )
    S.generate_out()
    return S


def add_vertex(arena, vertex_dict, Q, v, vertex_counter):
    if v not in vertex_dict:
        vertex_dict[v] = vertex_counter + 1
        Q.append((vertex_counter + 1, v))
        return vertex_counter + 1

    return vertex_counter
