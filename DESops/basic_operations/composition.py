"""
Funcions relevant to the composition operations.
"""
from DESops.automata.automata import _Automata
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError


def product(*automata: _Automata) -> _Automata:
    """
    Computes the product composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = _Automata()
        Euc = G1.Euc | G2.Euc
        Euo = G1.Euo | G2.Euo

        vertices = [
            {
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for x1 in G1.vs
            for x2 in G2.vs
        ]
        G_out.add_vertices(
            len(vertices),
            names=[v["name"] for v in vertices],
            marked=[v["marked"] for v in vertices],
            indexes=[v["indexes"] for v in vertices],
        )

        for x in G_out.vs:
            x1 = G1.vs[x["indexes"][0]]
            x2 = G2.vs[x["indexes"][1]]
            active_events = {out[1] for out in x1["out"]} & {
                out[1] for out in x2["out"]
            }
            if not active_events:
                continue

            for e in active_events:
                if e in Euc:
                    G_out.Euc.add(e)
                if e in Euo:
                    G_out.Euo.add(e)

                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]

    return G_out


def parallel(*automata: _Automata) -> _Automata:
    """
    Computes the parallel composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = _Automata()
        Euc = G1.Euc | G2.Euc
        Euo = G1.Euo | G2.Euo
        E1 = set(G1.es["label"])
        E2 = set(G2.es["label"])

        vertices = [
            {
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for x1 in G1.vs
            for x2 in G2.vs
        ]
        G_out.add_vertices(
            len(vertices),
            names=[v["name"] for v in vertices],
            marked=[v["marked"] for v in vertices],
            indexes=[v["indexes"] for v in vertices],
        )

        for x in G_out.vs:
            x1 = G1.vs[x["indexes"][0]]
            x2 = G2.vs[x["indexes"][1]]
            active_x1 = {out[1] for out in x1["out"]}
            active_x2 = {out[1] for out in x2["out"]}
            active_both = active_x1 & active_x2
            x1_ex = active_x1 - E2
            x2_ex = active_x2 - E1
            if not active_both and not x1_ex and not x2_ex:
                continue

            for e in active_x1 | active_x2:
                if e in Euc:
                    G_out.Euc.add(e)
                if e in Euo:
                    G_out.Euo.add(e)

            for e in active_both:
                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

            for e in x1_ex:
                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

            for e in x2_ex:
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]

    return G_out
