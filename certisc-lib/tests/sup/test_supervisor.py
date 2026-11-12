"""
The supervisor, prefix-closed: method="fast" (verified Rust, rust/verified/src/sup/supcon.rs)
against method="naive" (plain Python iteration), and the defining properties of K↑C checked
word by word: L(S) ⊆ K, L(S) controllable, and the textbook small factory.
"""

import itertools
import random
import warnings

import pytest

from core_aut import Automaton, validate
from ops_aut import EmptyAutomatonWarning
from sup import supervisor

from tests.random_automata import rand_aut


def _plant_spec(rng, n_max=7):
    """A random deterministic plant G and specification H with E_H ⊆ E_G, H agreeing with G
    on Euc and Euo."""
    events = rng.sample(list("abcde"), rng.randint(1, 5))
    G = rand_aut(rng, rng.randint(1, n_max), events, 0.3 + 0.5 * rng.random(), det=True)
    for i, s in enumerate(G.states):
        s.name = f"g{i}"
    eh = rng.sample(events, rng.randint(1, len(events)))
    H = rand_aut(rng, rng.randint(1, n_max), eh, 0.3 + 0.6 * rng.random(), det=True)
    for i, s in enumerate(H.states):
        s.name = f"h{i}"
    H.Euc = {e for e in eh if e in G.Euc}
    H.Euo = {e for e in eh if e in G.Euo}
    return validate(G), validate(H)


def _summary(S):
    names = list(S.names)
    return (set(names), {names[x] for x in S.init}, {names[x] for x in S.marked},
            {(names[x], e, names[y]) for x, e, y in S.transitions()})


def _in_L(V, word):
    d = {(x, e): y for x, e, y in V.transitions()}
    S = set(V.init)
    for e in word:
        S = {d[x, e] for x in S if (x, e) in d}
    return bool(S)


def _in_K(G, H, word):
    """K = L(G) ∩ P_H⁻¹ L(H)."""
    return _in_L(G, word) and _in_L(H, [e for e in word if e in H.events])


def test_fast_equals_naive():
    rng = random.Random(80)
    nonempty = 0
    for trial in range(400):
        G, H = _plant_spec(rng)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            S = supervisor(G, H)
            N = supervisor(G, H, method="naive")
        assert _summary(S) == _summary(N), trial
        assert S.events == G.events and S.Euc == G.Euc and S.Euo == G.Euo
        if S.num_states:
            nonempty += 1
            assert S.is_deterministic
    assert nonempty > 100                       # the comparison is not only on empty results


def _sub_spec(rng, n_max=10):
    """A plant G and a spec H that is G with some transitions removed (same states, renamed):
    a strict subautomaton, which gives many partial supervisors."""
    events = rng.sample(list("abcde"), rng.randint(2, 5))
    G = rand_aut(rng, rng.randint(2, n_max), events, 0.4 + 0.5 * rng.random(), det=True)
    for i, s in enumerate(G.states):
        s.name = f"g{i}"
    H = Automaton(events=events, Euc=G.Euc, Euo=G.Euo)
    for i in range(G.num_states):
        H.add_state(f"h{i}", G.states[i].marked, init=(i in G.init))
    p = 0.05 + 0.25 * rng.random()
    for x, e, y in G.transitions():
        if rng.random() >= p:
            H.add_transition(x, e, y)
    return validate(G), validate(H)


def test_fast_equals_naive_sub_specs():
    """As above, on specs that are subautomata of the plant: here the supervisor often removes
    some states but not all (measured 2026-11-11: about 9% of the cases), so the two methods
    are compared on real partial results."""
    from ops_aut import parallel_2aut
    rng = random.Random(83)
    partial = 0
    for trial in range(1500):
        G, H = _sub_spec(rng)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            S = supervisor(G, H)
            N = supervisor(G, H, method="naive")
        assert _summary(S) == _summary(N), trial
        if 0 < S.num_states < parallel_2aut(G, H).num_states:
            partial += 1
    assert partial > 80


def test_language_properties():
    """Word by word up to length 5: L(S) ⊆ K, and L(S) is controllable w.r.t. L(G)."""
    rng = random.Random(81)
    for trial in range(120):
        G, H = _plant_spec(rng, n_max=5)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            S = supervisor(G, H)
        for k in range(6):
            for w in itertools.product(sorted(G.events), repeat=k):
                w = list(w)
                if not _in_L(S, w):
                    continue
                assert _in_K(G, H, w), (trial, w)
                for e in G.Euc:
                    if _in_L(G, w + [e]):
                        assert _in_L(S, w + [e]), (trial, w, e)


def test_K_controllable_is_kept():
    """If K is already controllable, the supervisor's language is K (words up to length 5)."""
    rng = random.Random(82)
    checked = 0
    for trial in range(300):
        G, H = _plant_spec(rng, n_max=4)
        words = [list(w) for k in range(6) for w in itertools.product(sorted(G.events), repeat=k)]
        K = [w for w in words if _in_K(G, H, w)]
        controllable = all(_in_K(G, H, w + [e]) for w in K if len(w) < 5
                           for e in G.Euc if _in_L(G, w + [e]))
        if not controllable or not K:
            continue
        checked += 1
        S = supervisor(G, H)
        assert all(_in_L(S, w) == _in_K(G, H, w) for w in words), trial
    assert checked > 20


def _small_factory():
    """Two machines and a buffer of one slot (the textbook small factory). a_i (start,
    controllable), b_i (finish, uncontrollable). Spec: no overflow (b1 into a full buffer) and
    no underflow (a2 from an empty buffer)."""
    def machine(i):
        M = Automaton(events=[f"a{i}", f"b{i}"], Euc=[f"b{i}"])
        idle = M.add_state(f"I{i}", marked=True, init=True)
        work = M.add_state(f"W{i}")
        M.add_transition(idle, f"a{i}", work)
        M.add_transition(work, f"b{i}", idle)
        return M
    from ops_aut import parallel_2aut
    G = parallel_2aut(machine(1), machine(2))
    B = Automaton(events=["b1", "a2"], Euc=["b1"])
    empty = B.add_state("E", marked=True, init=True)
    full = B.add_state("F")
    B.add_transition(empty, "b1", full)
    B.add_transition(full, "a2", empty)
    return G, validate(B)


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_small_factory(method):
    G, B = _small_factory()
    S = supervisor(G, B, method=method)
    names = list(S.names)
    # With the buffer full, M1 must not start (b1 would overflow, and b1 cannot be prevented).
    for x, e, _ in S.transitions():
        g, b = names[x]
        if b == "F" and e == "a1":
            pytest.fail("a1 enabled with a full buffer")
    # The good behaviour stays possible: a1 b1 a2 b2 is in L(S); a2 first is not (underflow).
    assert _in_L(S, ["a1", "b1", "a2", "b2"])
    assert not _in_L(S, ["a2"])
    # The supremal one is not empty and the plant stays in it (L(S) ⊆ L(G)).
    assert S.num_states > 0
    assert all(_in_L(G, w) for w in (["a1"], ["a1", "b1"], ["a1", "b1", "a2"]))


def _one(G_unc=("u",), H_moves=(("h0", "u", "h0"),), G_det=True, H_det=True):
    G = Automaton(events=["c", "u"], Euc=list(G_unc))
    g0 = G.add_state("g0", init=True)
    g1 = G.add_state("g1")
    G.add_transition(g0, "c", g1)
    G.add_transition(g1, "u", g0)
    if not G_det:
        G.add_transition(g0, "c", g0)
    H = Automaton(events=["c", "u"], Euc=["u"])
    idx = {"h0": H.add_state("h0", init=True), "h1": H.add_state("h1")}
    for x, e, y in H_moves:
        H.add_transition(idx[x], e, idx[y])
    if not H_det:
        H.add_transition(idx["h0"], "c", idx["h0"])
        H.add_transition(idx["h0"], "c", idx["h1"])
    return G, H


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_empty_when_initial_state_is_bad(method):
    # The plant does c then u (uncontrollable); the spec allows c but never u afterwards: c
    # must be disabled, so S keeps only the initial state.
    G, H = _one(H_moves=(("h0", "c", "h1"),))
    S = supervisor(G, H, method=method)
    assert S.names == (("g0", "h0"),) and not list(S.transitions())
    # A plant whose initial state has an uncontrollable event the spec never allows.
    G2 = Automaton(events=["u"], Euc=["u"])
    x = G2.add_state("x", init=True)
    G2.add_transition(x, "u", x)
    H2 = Automaton(events=["u"], Euc=["u"])
    H2.add_state("y", init=True)
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        E = supervisor(G2, H2, method=method)
    assert E.num_states == 0
    assert any(x.category is EmptyAutomatonWarning for x in w)


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_errors(method):
    G, H = _one(H_moves=(("h0", "c", "h1"), ("h1", "u", "h0")))
    supervisor(G, H, method=method)                          # fine
    with pytest.raises(ValueError, match="plant G must be deterministic"):
        supervisor(*_one(G_det=False), method=method)
    with pytest.raises(ValueError, match="specification H must be deterministic"):
        supervisor(*_one(H_det=False), method=method)
    H3 = Automaton(events=["c", "z"])
    H3.add_state("h", init=True)
    with pytest.raises(ValueError, match="H has events that G does not: 'z'"):
        supervisor(G, H3, method=method)
    H4 = Automaton(events=["u"])                              # u controllable here
    H4.add_state("h", init=True)
    with pytest.raises(ValueError, match="'u' is controllable in one and uncontrollable"):
        supervisor(G, H4, method=method)


def test_options():
    G, H = _one(H_moves=(("h0", "c", "h1"), ("h1", "u", "h0")))
    with pytest.raises(NotImplementedError):
        supervisor(G, H, mode="nonblocking")
    with pytest.raises(ValueError, match="unknown mode"):
        supervisor(G, H, mode="other")
    with pytest.raises(ValueError, match="unknown method"):
        supervisor(G, H, method="other")
    with pytest.raises(ValueError, match="unknown backend"):
        supervisor(G, H, backend="numpy")


# --- constructions: escape, refine, subautomaton -----------------------------------------

_COMBOS = [(c, m) for c in ("escape", "refine") for m in ("fast", "naive")]


def _all(G, H, combos):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", EmptyAutomatonWarning)
        return {cm: _summary(supervisor(G, H, construction=cm[0], method=cm[1]))
                for cm in combos}


def test_refine_equals_escape():
    """Random plants and specs (and sub-specs): the four escape/refine × fast/naive results are
    the same automaton."""
    rng = random.Random(84)
    for trial in range(400):
        G, H = _plant_spec(rng) if trial % 2 else _sub_spec(rng)
        results = list(_all(G, H, _COMBOS).values())
        assert all(r == results[0] for r in results), trial


def _restriction(rng, n_max=10):
    """A plant G (unique names) and H = G with some states deleted (verified delete_states)."""
    from ops_aut import delete_states
    events = rng.sample(list("abcde"), rng.randint(2, 5))
    G = rand_aut(rng, rng.randint(2, n_max), events, 0.4 + 0.5 * rng.random(), det=True)
    for i, s in enumerate(G.states):
        s.name = f"g{i}"
    G = validate(G)
    D = [x for x in range(G.num_states) if rng.random() < 0.3]
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", EmptyAutomatonWarning)
        H = delete_states(G, D)
    return G, H


def test_subautomaton_equals_others():
    """H = G with states deleted: all six construction × method results are the same."""
    rng = random.Random(85)
    combos = _COMBOS + [("subautomaton", "fast"), ("subautomaton", "naive")]
    partial = 0
    for trial in range(400):
        G, H = _restriction(rng)
        results = _all(G, H, combos)
        first = results[("escape", "fast")]
        assert all(r == first for r in results.values()), trial
        S = results[("subautomaton", "fast")]
        if 0 < len(S[0]) < H.num_states:
            partial += 1
    assert partial > 20


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_subautomaton_rejects_non_restrictions(method):
    rng = random.Random(86)
    rejected = 0
    for trial in range(60):
        G, H = _restriction(rng)
        trans = list(H.transitions())
        if not trans:
            continue
        # Drop one transition: no longer G restricted to H's states.
        Hb = H.to_automaton()
        x, e, y = trans[rng.randrange(len(trans))]
        Hb.states[x].out[e] = [z for z in Hb.states[x].out[e] if z != y]
        if not Hb.states[x].out[e]:
            del Hb.states[x].out[e]
        Hb = validate(Hb)
        with pytest.raises(ValueError, match="not a strict subautomaton"):
            supervisor(G, Hb, construction="subautomaton", method=method)
        rejected += 1
    assert rejected > 30
    G, H = _restriction(random.Random(87))
    Hn = H.to_automaton()
    Hn.states[0].name = "nope"
    with pytest.raises(ValueError, match="distinct names of states of G"):
        supervisor(G, Hn, construction="subautomaton", method=method)


def test_unknown_construction():
    G, H = _one(H_moves=(("h0", "c", "h1"), ("h1", "u", "h0")))
    with pytest.raises(ValueError, match="unknown construction"):
        supervisor(G, H, construction="other")


def test_subautomaton_reencoded():
    """H rebuilt independently (states shuffled, events listed in another order): the Rust
    re-encoding path accepts it and gives the same supervisor as the shortcut path."""
    rng = random.Random(88)
    reordered = 0
    for trial in range(200):
        G, H = _restriction(rng)
        if H.num_states == 0:
            continue
        perm = list(range(H.num_states))
        rng.shuffle(perm)
        H2 = Automaton(events=sorted(H.events, reverse=True), Euc=H.Euc, Euo=H.Euo)
        new = {}
        for i in perm:
            new[i] = H2.add_state(H.names[i], i in H.marked, init=(i in H.init))
        for x, e, y in H.transitions():
            H2.add_transition(new[x], e, new[y])
        H2 = validate(H2)
        if H2._event_of != H._event_of or perm != sorted(perm):
            reordered += 1
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            a = _summary(supervisor(G, H, construction="subautomaton"))
            b = _summary(supervisor(G, H2, construction="subautomaton"))
        assert a == b, trial
    assert reordered > 100


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_subautomaton_as_indices(method):
    """H given as the indices of the states of G to keep: same supervisor as H given as the
    automaton G minus the other states."""
    rng = random.Random(89)
    for trial in range(200):
        G, H = _restriction(rng)
        keep = [G.index_of(name) for name in H.names]
        rng.shuffle(keep)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            a = _summary(supervisor(G, H, construction="subautomaton", method=method))
            b = _summary(supervisor(G, keep + keep[:1], construction="subautomaton",
                                    method=method))       # repeats are fine
        assert a == b, trial
    G, _ = _restriction(random.Random(90))
    for bad in ([G.num_states], [-1], ["x"]):
        with pytest.raises(ValueError, match="must be state indices of G"):
            supervisor(G, bad, construction="subautomaton", method=method)


@pytest.mark.parametrize("method", ["fast", "naive"])
def test_forbidden_states(method):
    """forbidden = the states to delete: same supervisor as H = the other states."""
    rng = random.Random(91)
    for trial in range(200):
        G, H = _restriction(rng)
        keep = {G.index_of(name) for name in H.names}
        bad = [x for x in range(G.num_states) if x not in keep]
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            a = _summary(supervisor(G, sorted(keep), construction="subautomaton", method=method))
            b = _summary(supervisor(G, forbidden=bad, method=method))
            c = _summary(supervisor(G, forbidden=bad, construction="subautomaton", method=method))
        assert a == b == c, trial
    G, H = _restriction(random.Random(92))
    with pytest.raises(ValueError, match="not both"):
        supervisor(G, H, forbidden=[0], method=method)
    with pytest.raises(ValueError, match="are needed"):
        supervisor(G, method=method)
    with pytest.raises(ValueError, match="use construction='subautomaton'"):
        supervisor(G, forbidden=[0], construction="refine", method=method)
    with pytest.raises(ValueError, match="forbidden states must be state indices"):
        supervisor(G, forbidden=[G.num_states], method=method)
