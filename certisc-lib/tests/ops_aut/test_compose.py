"""
Parallel composition and product: the public parallel_2aut and product_2aut (Rust,
rust/verified/src/ops_aut/compose.rs), against a direct construction over pairs and against
the languages (all words up to a length bound).
"""

import itertools
import random
import warnings

import pytest

from core_aut import Automaton, InvalidAutomatonError, validate
from ops_aut import EmptyAutomatonWarning, parallel_2aut, product_2aut

from tests.random_automata import random_aut


def _pair(rng, attrs, n_max=6):
    """Two random automata over overlapping alphabets; each event gets its Euc/Euo flags from
    `attrs` (one choice per event name), so the pair agrees on shared events."""
    out = []
    for prefix in ("s", "t"):
        events = rng.sample(sorted(attrs), rng.randint(1, 4))
        G = random_aut(rng.randint(1, n_max), events, rng)
        for i, s in enumerate(G.states):
            s.name = f"{prefix}{i}"
        G.Euc = {e for e in events if attrs[e][0]}
        G.Euo = {e for e in events if attrs[e][1]}
        out.append(validate(G))
    return out


def _attrs(rng):
    return {e: (rng.random() < 0.3, rng.random() < 0.3) for e in "abcde"}


def _delta(V):
    d = {}
    for x, e, y in V.transitions():
        d.setdefault((x, e), set()).add(y)
    return d


def _expected(V1, V2, par):
    """The composition built directly: the pairs reachable from X01 × X02 (as name pairs),
    init, marked, transitions as name triples."""
    E1, E2 = V1.events, V2.events
    d1, d2 = _delta(V1), _delta(V2)
    init = {(a, b) for a in V1.init for b in V2.init}
    seen, todo, trans = set(init), list(init), set()
    while todo:
        a, b = todo.pop()
        for e in E1 | E2:
            if e in E1 and e in E2:
                nxt = {(c, d) for c in d1.get((a, e), ()) for d in d2.get((b, e), ())}
            elif par and e in E1:
                nxt = {(c, b) for c in d1.get((a, e), ())}
            elif par and e in E2:
                nxt = {(a, d) for d in d2.get((b, e), ())}
            else:
                nxt = set()
            for p in nxt:
                trans.add(((a, b), e, p))
                if p not in seen:
                    seen.add(p)
                    todo.append(p)
    nm = lambda p: (V1.names[p[0]], V2.names[p[1]])           # noqa: E731
    return ({nm(p) for p in seen}, {nm(p) for p in init},
            {nm(p) for p in seen if p[0] in V1.marked and p[1] in V2.marked},
            {(nm(p), e, nm(q)) for p, e, q in trans})


def _summary(H):
    names = list(H.names)
    return (set(names), {names[x] for x in H.init}, {names[x] for x in H.marked},
            {(names[x], e, names[y]) for x, e, y in H.transitions()})


def _ends(V, word):
    """The states reached from the initial states by `word`."""
    d = _delta(V)
    S = set(V.init)
    for e in word:
        S = {y for x in S for y in d.get((x, e), ())}
    return S


def _in_L(V, word, marked=False):
    S = _ends(V, word)
    return bool(S & V.marked) if marked else bool(S)


def _check_languages(V1, V2, H, par, max_len=4):
    """L and Lm of H, word by word, against P1⁻¹ L1 ∩ P2⁻¹ L2 (parallel) or L1 ∩ L2 (product)."""
    E1, E2 = V1.events, V2.events
    alphabet = sorted(E1 | E2)
    for k in range(max_len + 1):
        for w in itertools.product(alphabet, repeat=k):
            if par:
                w1 = [e for e in w if e in E1]
                w2 = [e for e in w if e in E2]
            else:
                w1 = w2 = list(w)
            for marked in (False, True):
                exp = _in_L(V1, w1, marked) and _in_L(V2, w2, marked)
                assert _in_L(H, w, marked) == exp, (w, marked)


@pytest.mark.parametrize("par", [True, False])
def test_matches_direct_construction(par):
    op = parallel_2aut if par else product_2aut
    rng = random.Random(70 if par else 71)
    for trial in range(300):
        attrs = _attrs(rng)
        V1, V2 = _pair(rng, attrs)
        H = op(V1, V2)
        assert _summary(H) == _expected(V1, V2, par), trial
        assert len(set(H.names)) == H.num_states                # each pair once
        assert H.events == V1.events | V2.events
        assert H.Euc == V1.Euc | V2.Euc and H.Euo == V1.Euo | V2.Euo
        # Agreement: every event keeps its attributes (lemma_agree_keeps_flags).
        for e in H.events:
            assert (e in H.Euc) == attrs[e][0] and (e in H.Euo) == attrs[e][1]
        if V1.is_deterministic and V2.is_deterministic:
            assert H.is_deterministic, trial


@pytest.mark.parametrize("par", [True, False])
def test_languages(par):
    op = parallel_2aut if par else product_2aut
    rng = random.Random(72 if par else 73)
    for trial in range(80):
        V1, V2 = _pair(rng, _attrs(rng), n_max=4)
        _check_languages(V1, V2, op(V1, V2), par)


def test_product_private_events_never_enabled():
    rng = random.Random(74)
    for _ in range(100):
        V1, V2 = _pair(rng, _attrs(rng))
        H = product_2aut(V1, V2)
        shared = V1.events & V2.events
        assert all(e in shared for _, e, _ in H.transitions())


def test_composition_of_a_composition():
    """(G1 ‖ G2) ‖ G3: nested name pairs; the language is that of the three together."""
    rng = random.Random(75)
    for trial in range(40):
        attrs = _attrs(rng)
        V1, V2 = _pair(rng, attrs, n_max=3)
        V3, _ = _pair(rng, attrs, n_max=3)
        H = parallel_2aut(parallel_2aut(V1, V2), V3)
        assert all(isinstance(n, tuple) and isinstance(n[0], tuple) for n in H.names)
        Es = [V1.events, V2.events, V3.events]
        for k in range(4):
            for w in itertools.product(sorted(Es[0] | Es[1] | Es[2]), repeat=k):
                for marked in (False, True):
                    exp = all(_in_L(V, [e for e in w if e in E], marked)
                              for V, E in zip((V1, V2, V3), Es))
                    assert _in_L(H, w, marked) == exp, (trial, w, marked)


def _two(euc1=(), euc2=(), euo1=(), euo2=()):
    G1 = Automaton(events=["a", "b"], Euc=euc1, Euo=euo1)
    x = G1.add_state("x", init=True)
    G1.add_transition(x, "a", x)
    G2 = Automaton(events=["a", "c"], Euc=euc2, Euo=euo2)
    y = G2.add_state("y", init=True)
    G2.add_transition(y, "a", y)
    return G1, G2


@pytest.mark.parametrize("op", [parallel_2aut, product_2aut])
def test_disagreement_rejected(op):
    with pytest.raises(ValueError, match="'a' is controllable in one and uncontrollable"):
        op(*_two(euc1=["a"]))
    with pytest.raises(ValueError, match="'a' is controllable in one and uncontrollable"):
        op(*_two(euc2=["a"]))
    with pytest.raises(ValueError, match="'a' is observable in one and unobservable"):
        op(*_two(euo1=["a"]))
    # Private events may have any attributes; shared ones agreeing are fine.
    H = op(*_two(euc1=["a", "b"], euc2=["a", "c"], euo1=["b"]))
    assert H.Euc == {"a", "b", "c"} and H.Euo == {"b"}


@pytest.mark.parametrize("op", [parallel_2aut, product_2aut])
def test_empty_input(op):
    G1, G2 = _two()
    E = Automaton(events=["a"])                      # no states: valid, empty
    for args in ((G1, E), (E, G2), (E, E)):
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            H = op(*args)
        assert H.num_states == 0
        assert any(x.category is EmptyAutomatonWarning for x in w)


def test_plain_and_valid_inputs_and_errors():
    G1, G2 = _two()
    H = parallel_2aut(G1, G2)                         # plain Automaton: validated inside
    assert H.names == (("x", "y"),)
    assert sorted(H.transitions()) == [(0, "a", 0)]
    assert parallel_2aut(validate(G1), validate(G2)).names == H.names
    bad = Automaton(events=["a"])
    bad.add_state("z")                               # states but no initial state (W3)
    with pytest.raises(InvalidAutomatonError):
        parallel_2aut(G1, bad)
    with pytest.raises(ValueError, match="unknown backend"):
        product_2aut(G1, G2, backend="numpy")
