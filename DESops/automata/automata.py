# pylint: disable=C0103
# pylint: disable=C0301
"""
Automata class & methods:
Used to represent finite-state automata, by means of a directed
graph object (from the igraph library) with labelled transitions.

Implemented here is the abstract base class _Automata.

Use DFA, NFA or PFA classes instead.

Provides access to many useful methods in discrete event systems,
e.g. parallel & product compositions or observer construction.

In general, these operations can be performed as follows::

    # For automata A , B:
    A_par_B = d.composition.parallel(A, B)
    obs_A = d.composition.observer(A)

Automata can be constructed by 'fsm' filetypes, providing easy
interface with DESUMA.
Alternatively, Automata can be created starting from an underlying
igraph Graph object.

The Automata structure is a directed graph with labelled transitions,
implemented as an igraph Graph object (member var '_graph').
Vertex names and edge labels can be accessed via the igraph Graph
`EdgeSeq` and `VertexSeq` methods, accessed for an Automata G as follows::

    vert_seq = G.vs()
    edge_seq = G.es()

Note that the vs() and es() methods for the Automata class are directly bound to
the vs() and es() methods for the igraph Graph class.
vs() and es() have dict-like behavior for accessing attributes, which are used here
to store edge labels and vertex names, e.g ::

    vert_name_list = G.vs["name"]
    edge_label_list = G.es["label"]

And to access specific entries by value or index::

    vert_index_7 = G.vs["name"][7]
    edge_name_a = G.es(label_eq="a") # if multiple edges labelled 'a', returns first by index

In many cases, information relevant to vertices & edges are stored in attributes. For example,
in PFA, probabilities of a transition occuring are stored in the "prob" attribute, e.g ::

    prob_trans_a = G.es(label_eq="a")["prob"]

Vertices and Edges can be named/labelled after their creation by accessing the
"name"/"label" attribute in the VertexSeq/EdgeSeq dict::

    E.vs["name"] = ['A','B','C','D','E']

Note that the this process cannot be used to update individual entries.
For example, the following code will NOT change the name of vertex 'E'::

    G.vs["name"][4] = 'F' # WILL NOT MODIFY THE VERTEX NAME

Instead, the `update_attributes()` method must be used to modify specific edge or vertex
attributes. These are igraph Graph Edge and Vertex methods. For details on these methods,
see the igraph Edge and Vertex class documentations. ::

    d = {"name" : 'F'}
    G.vs[4].update_attributes(d) # Name of vertex 4 is now 'F'
    G.es[0].update_attributes({"label" : 'b'}) # Change edge 0 label from 'a' to 'b'

More details on using the vs() and es() methods can be found in the igraph documentation.
For simply using the Automata class, further functionality than described here might not be
required. Implementing new functionality might however require the use of certain specific
igraph functions or methods. Having these bindings also means that many times passing an Automata
to a function (implemented here) expecting an igraph Graph will still function normally.
Useful in cases like product and parallel compositions (product_comp() and parallel_comp(),
but might cause some unintended problems?

Further details of how the igraph library is used are included in the implementation files.

"""

from collections import deque, namedtuple
from collections.abc import Iterable
from copy import deepcopy
from typing import Set, Union
from abc import ABC, abstractmethod

from DESops.automata.event import Event
from DESops.basic_operations.generic_functions import find_Euc, find_Euo, find_obs_contr
from DESops.error import (
    ConversionError,
    DependencyNotInstalledError,
    IncongruencyError,
    MissingAttributeError,
)
import warnings

try:
    import igraph as ig
except ImportError:
    raise DependencyNotInstalledError("IGraph library not found")


# TODO: Legacy, to be removed with unobservable_reach method
State_or_StateSet = Union[int, Set[int]]

# TODO: replace mutable default args with E=None and assign E=set() in method body
# TODO: create a standard, obvious method for analyzing adjacent edges and vertices -> replace fill_out?
# TODO: document g.OUT and g.UR
# TODO: Should we put g.events and g.Euc/g.Euo in the same style (i.e. g.E instead of g.events)
# TODO: enforce type constraints on vertex names and edge labels - Should we require these to be strings
# TODO: should **kwargs be used to set vertex and edge attributes? Currently not implemented for vertex attributes
# TODO: should critical states be replaced with a vertex attribute (i.e., g.vs["critical"] = True)
# TODO: Unify convention used to describe vertices or states (IGraph uses vertices, DES uses states)
# TODO: We need to decide if we want to use type hints (i.e., `print(msg: str)`)
# TODO: Should we maintain a list of todo tasks and bugs with GitLab issues (can use confidential mode if we do not want to disclose them to the public)
# TODO: The _Automata class was renamed to Automata to facilitate documentation, can it be changed back
# TODO: should init become a mandatory attribute. I don't think the convention that state 0 is initial is a good one.

class Automata(ABC):
    """Used to represent finite-state automata, by means of a directed
    graph object (from the igraph library) with labelled transitions.


    Attributes
    ----------
    Euc : set
            The uncontrollable events
    Euo : set
        The unobservable events
    events : set
        The set of all events
    _graph: ig.Graph
        underlying igraph Graph instance storing the Automata structure. Contains the
        original EdgeSeq and VertexSeq objects bound by the es() and vs() functions here.
        Usage of DESops should never require directly modifying the igraph Graph member.
        However, implementing new methods might require interfacing with igraph classes
        and functions.
    X_crit: set
        The set of critical states, stored as names of states (not indices)
    type: str
        The 'type' of the Automata (DFA, NFA, PFA, etc.)
    es: ig.EdgeSeq
        binding to igraph Graph 'edgeSeq' object, e.g. ::

            edgeSeqObj = g.es()

        is equivalent to::

            edgeSeqObj = g._graph.es()

    vs: ig.VertexSeq
        binding to igraph Graph 'vertSeq' object, e.g. ::

            vertSeqObj = g.vs()

        is equivalent to::

            vertSeqObj = g._graph.vs()

    """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        """Constructor can create an empty automata, or be created in one of the following ways:
        1.  From an existing igraph-Graph instance, the input graph is stored in self._graph
                If the input graph has distinguished types of states,
                automata is inferred to be type 'IDA'
        2.  From a fsm filetype, an igraph graph can be read from fsm_filename string.
        3.  From another Automata instance, has the same outcome of copying via the copy() method. For example::

                G = a.Automata()
                H1 = a.Automata(G)
                H2 = G.copy()

            G, H1 & H2 in this example would be equivalent.

        Euc and Euo attributes can be inferred from provided graphs.

        Parameters
        ----------
        init :  ig.Graph or Automata
            A graph or automaton to initialize the new automaton with
        Euc : set
            The uncontrollable events
        Euo : set
            The unobservable events
        E : set
            The set of all events
        """

        # Default case; create Automata from scratch.
        self._graph = ig.Graph(directed=True)
        self.events = set()  # IT SHOULD BE A SET OF EVENTS

        if not Euc:
            self.Euc = set()
        else:
            self.Euc = Euc.copy()
        if not Euo:
            self.Euo = set()
        else:
            self.Euo = Euo.copy()

        self.X_crit = set()

        self.type = None

        if isinstance(init, ig.Graph):
            # Create Automata from igraph Graph
            graph = init
            # deepcopy copies attributes
            self._graph = deepcopy(graph)
            self.events = E
            # find_obs_contr(self._graph, self.Euc, self.Euo, self.events)

        elif isinstance(init, Automata):
            # Create Automata from another Automata
            # deepcopy copies attributes
            self._graph = deepcopy(init._graph)
            self.events = init.events.copy()
            self.type = init.type
            self.Euo = init.Euo.copy()
            self.Euc = init.Euc.copy()

        if "label" not in self._graph.es.attributes():
            self._graph.es["label"] = [""]

        if "name" not in self._graph.vs.attributes():
            self._graph.vs["name"] = [""]

        if "out" not in self._graph.vs.attributes():
            self._graph.vs["out"] = [""]

        if "marked" not in self._graph.vs.attributes():
            self._graph.vs["marked"] = []

        # Allow references to graph instance's edge & vertex sequence methods
        # from the Automata (e.g. self.es as opposed to doing self._graph.es)
        self.es = self._graph.es
        self.vs = self._graph.vs

        # More bindings to igraph Graph methods, used in some functions in
        # this file, potentially useful elsewhere?

        self.write_dot = self._graph.write_dot

        self.__bool__ = self._graph.__bool__()

        # Attach UR class object (defined below)
        self.UR = UnobservableReach(self.Euo, self.vs)

        self.Out = namedtuple("Out", ["target", "label"])

    def delete_vertices(self, vs):
        """Deletes vertex seq vs.
        Uses igraph delete_vertices method.

        Updates out attr: since there is no default "in" attribute,
        out is regenerated entirely.

        Faster to use fewer delete_vertices() calls with larger inputs vs
        than multiple calls with smaller inputs.

        Parameters
        ----------
        vs : ig.VertexSeq
            The vertex sequence to delete
        """
        if 0 in vs:
            # TODO - Jack: this is expected behavior, does it need a warning?
            # i.e. deleting vert 0 should always result in deleting everything.
            #
            # import warnings
            # warnings.warn("Initial state deleted.")
            self._graph.delete_vertices([v.index for v in self.vs])

        else:
            if len(vs) == 0:
                return
            self._graph.delete_vertices(vs)
            self.generate_out()


    def delete_edges(self, es):
        """
        Proxy to igraph delete_edges.
        Might invalidate reachability, this function will not compute trim after deleting edges.

        Parameters
        ----------
        es : EdgeSeq
            The edge sequence to delete
        """
        self._graph.delete_edges(es)
        self.generate_out()

    @abstractmethod
    def add_edge(self, source, target, label, prob=None, fill_out=False):
        """
        Adds an edge to the Automata instance. Edge is created across pair, a tuple
        of vertex indices according to the igraph Graph `add_edge` method.
        Additionlly adds label and probability information as edge attributes, if
        they are optionally provided.

        Note: much faster to add multiple edges at once using add_edges

        Parameters
        ----------
        source : int
            The vertex index of the source. See igraph documentation of
            the `add_edge` method for more details on what is acceptable here.
        target : int
            The vertex index of the target
        label : object
            optionally provide label for this transition, to be stored
            in the "label" edge keyword attribute
        prob : float
            optionally provide probability for this transition (indicating
            stochastic transition), to be stored in the "prob" edge keyword attribute.
        fill_out : bool
            If true, then add the outgoing edge to the source in the "out" vertex attribute.

        """
        # Abstract method
        pass


    @abstractmethod
    def add_edges(self, pair_list, labels, probs=None, fill_out=False, **kwargs):
        """
        Add an iterable of edges to the Automata instance.
        Calls the igraph Graph `add_edges` method on the underlying graph
        object. Additionally adds label and probability information as
        edge attributes, if they are optionally provided as parallel iterables.

        Parameters:
        pair_list: an iterable to be passed to the igraph Graph add_edges() method,
            which accepts iterables of pairs or an EdgeSeq (see igraph documentation
            for more details on what is acceptable here).
        labels: optionally provide an iterable of labels to attach as
            keyword attributes. Should be parallel to pair_list (e.g., pair n of
            pair_list corresponding to label n of labels). To be stored in the "label"
            edge keyword attribute.
        probs: (default None) optionally provide an iterable of probabilities to attach
            as keyword attributes (indicating stochastic transitions). Should be
            parallel to pair_list (e.g., pair n of pair_list corresponds to probability
            n of probs). To be stored in the "prob" edge keyword attribute.
        fill_out : bool
            If true, then add the outgoing edges to the source in the "out" vertex attribute.

        Returns nothing.
        """
        # Abstract method
        pass

    # TODO: Should marked=False be the default?
    def add_vertex(self, name=None, marked=None, **kwargs):
        """
        Add a vertex or state to the automaton.
        Calls the igraph Graph `add_vertex` method on the underlying graph.

        Parameters
        ----------
        name : object
            The name of the vertex
        marked : bool or None
            If true, the vertex is marked
        **kwargs : dict
            Names and values assigned to the vertex attributes (not implemented)

        """
        self._graph.add_vertex()
        if name:
            self.vs[self.vcount() - 1].update_attributes({"name": name})
        else:
            self.vs[self.vcount() - 1].update_attributes(
                {"name": str(self.vcount() - 1)}
            )
        if marked is not None:
            self.vs[self.vcount() - 1].update_attributes({"marked": marked})

        self.vs[self.vcount() - 1].update_attributes({"out": []})

        for arg in kwargs.items():
            self._graph.vs[self.vcount() - 1].update_attributes({arg[0]: arg[1]})

        return self.vs[self.vcount() - 1]

    def add_vertices(self, number_vertices, names=None, marked=None, **kwargs):
        """
        Adds a number of vertices or states to the automaton.
        Calls the igraph Graph `add_vertices` method on the underlying graph.

        Parameters
        ----------
        number_vertices : int
            The number of vertices to add
        name : Iterable or None
            The names of the vertices
        marked : Iterable or bool or None
            The markings of the vertices
        **kwargs : dict
            Names and values assigned uniformly to the vertex attributes (not implemented)

        """
        if names:
            if number_vertices != len(names):
                raise IncongruencyError(
                    "Number vertices to be added != number of names provided"
                )
            new_names = self._graph.vs["name"] + names

        else:
            # if no names given, fill in with index names
            new_names = self.vs["name"]
            new_names.extend(
                str(i) for i in range(self.vcount(), self.vcount() + number_vertices)
            )

        if marked is not None:
            if number_vertices != len(marked):
                raise IncongruencyError("Number vertices to be added != number names")
            new_marked = self._graph.vs["marked"] + marked
        else:
            new_marked = self._graph.vs["marked"] + [
                False for _ in range(number_vertices)
            ]

        # list comprehension used instead of [[]] * number_vertices because latter gives list of references to the same object
        new_out = self._graph.vs["out"] + [[] for _ in range(number_vertices)]

        extra_attrs = dict()
        for key, val in kwargs.items():
            if number_vertices != len(val):
                raise IncongruencyError(
                    "Number vertices to be added != number of names provided"
                )
            if key in self._graph.vs.attributes():
                extra_attrs[key] = self._graph.vs[key] + val
            else:
                extra_attrs[key] = [None] * self.vcount() + val

        self._graph.add_vertices(number_vertices)

        self._graph.vs["name"] = new_names
        self._graph.vs["out"] = new_out

        self._graph.vs["marked"] = new_marked

        for key, val in extra_attrs.items():
            self._graph.vs[key] = val

    # TODO - does this need to exist? Can it just be replaced by the assignment in the body
    def update_names(self, names):
        # update vertex names from list of names
        self.vs["name"] = names

    # TODO Should we instead use __copy__ and __deepcopy__?
    # TODO Should we keep this if it is overridden by DFA, NFA
    def copy(self):
        """
        Copy from self to other, as in::

            other = self.copy()

        TODO: This needs to be an abstract method?
        """
        A = Automata(self)
        return A

    def add_critical_state(self, X_crit_state):
        """
        Add the state with the given name to the set of critical states.

        Alternative to adding a critical state::

            A.add_critical_state('critical_state_name')

        is equivalent to::

            A.X_crit.add('critical_state_name')

        Parameters
        ----------
        X_crit_state : object
            The name of the critical state to add
        """
        self.X_crit.add(X_crit_state)

    def generate_out(self):
        """
        Generates the "out" attribute for a graph::

            automata.vs["out"][v] // -> [(target vert, event transition), (...), ...]

        """
        adj_list = self._graph.get_inclist()
        self.vs["out"] = [
            [
                self.Out(self._graph.es[e].target, self._graph.es[e]["label"])
                for e in row
            ]
            for row in adj_list
        ]

    def summary(self, use_state_names=False, lines=None):
        """
        Summarize the automaton in a readable string format.
        Requires the out attribute. See `generate_out`.

        TODO Would there be other useful things to print here?

        Parameters
        ----------
        use_state_names : bool
            If True, then print the "name" attribute of the vertices, otherwise print the index
        lines : int or None
            The maximum number of lines to print. None indicates no limit.

        Returns
        ----------
        str
            The summary of the automaton
        """
        ret_str = "{} : {} V, {} E\n".format(self.type, self.vcount(), self.ecount())
        ret_str += "Events: {}\nEuc: {}\nEuo: {}\n".format(
            self.events, self.Euc, self.Euo
        )
        ret_str += "Source | (Target, Event), ...)\n"

        use_markings = any(self.vs["marked"])

        for v in range(self.vcount()):
            if lines and v == lines:
                break
            if use_state_names:
                vname = self.vs["name"][v]

                out_list = [(self.vs[t[0]]["name"], t[1]) for t in self.vs["out"][v]]
            else:
                vname = v
                out_list = self.vs["out"][v]

            if use_markings:
                markings_str = "*" if self.vs["marked"][v] else " "
                ret_str = ret_str + "{}{}:  {}\n".format(vname, markings_str, out_list)
            else:
                ret_str = ret_str + "{}  :  {}\n".format(vname, out_list)
        return ret_str

    def __str__(self):
        return self.summary(use_state_names=True)

    # TODO should this be here?
    def compute_state_costs(self, starting_states=None, Euc=None):
        """
        Computes the uncontrollable traces preceding states in starting_states.
        Used to find invalid states, e.g. those which transition uncontrollably to critical states.

        TODO: check if this particular automata has an ingoing adjacency list generated already
        and if so, use that.

        Parameters
        ----------
        starting_states : Iterable[int] or None
            Vertex indices to search from, default behavior is to convert
            states in automata attr X_crit to vertex indices and uses these.
        Euc : set or None
            optionally specify uncontrollable event set. If None, uses automata Euc attr.

        Returns
        -------
        set
            Bad vertex indices, which includes states in starting_states.
        """

        if not Euc:
            Euc = self.Euc

        if not starting_states:
            starting_states = [v.index for v in self.vs.select(name_in=self.X_crit)]

        # updates starting_states with infinite cost states
        bad_states = set()
        states_to_check = starting_states
        while states_to_check:
            bad_states.update(states_to_check)
            # Back out the next potentially infinite-cost states as those with uncontrollable transitions
            # to the most recent set of infinite cost states (states_to_check on the RHS).
            states_to_check = {
                self.es[e].source
                for v in states_to_check
                for e in self._graph.incident(v, mode="IN")
                if self.es[e]["label"] in Euc and self.es[e].source not in bad_states
            }
        return bad_states

    # Methods to interface with graph variables & methods

    def vcount(self):
        """
        Return the number of vertices in the Automata.
        Binding to igraph Graph `vcount` method.
        This is the preferred method to find vertex count.

        Returns
        -------
        int
            Vertex count
        """
        return self._graph.vcount()

    def ecount(self):
        """
        Return the number of edges in the Automata.
        Binding to igraph Graph `ecount` method.
        This is the preferred method to find edge count.

        Returns
        -------
        int
            Edge count
        """
        return self._graph.ecount()

    def next_states(self, index):
        """
        Return the set of vertex indices that can be reached from the given vertex index in a single event

        Parameters
        -------
        index : int
            The index of source vertex

        Returns
        -------
        set
            The next states
        """
        return {o.target for o in self.vs[index]["out"]}

    def active_events(self, index):
        """
        Return the set of events that can occur from the given vertex index

        Parameters
        -------
        index : int
            The index of the source vertex

        Returns
        -------
        set
            The active events at the source
        """
        return {o.label for o in self.vs[index]["out"]}

    def events_between(self, X1, X2):
        """
        Return the set of events that transition the system from X1 to X2
        X1 and X2 should each be either a single vertex index, or iterable collections of vertex indices

        Parameters
        ----------
        X1 : int or Iterable[int]
            The indices of the source vertices
        X2 : int or Iterable[int]
            The indices of the target vertices

        Returns
        -------
        set
            The event labels from sources and targets

        """
        # treat single states as singleton list
        if not isinstance(X1, Iterable):
            X1 = [X1]
        if not isinstance(X2, Iterable):
            X2 = [X2]

        events = set()
        for x1 in X1:
            for x2 in X2:
                events.update(o.label for o in self.vs[x1]["out"] if o.target == x2)

        return events

    # TODO - this method only returns one target, instead of all possible next states for NFAs
    def trans(self, source, event):
        """
        Return a target vertex index reached when the given event occurs from the given source vertex index

        Parameters
        -------
        source : int
            The index of the source vertex
        event : object
            The label of the outgoing transitions

        Returns
        -------
        int
            The index of the target vertex
        """
        for out in self.vs[source]["out"]:
            if out.label == event:
                return out.target
        return None

    # TODO: this is legacy, should replace instances of this
    # with the UR class method
    def unobservable_reach(self, from_state: State_or_StateSet) -> Set[int]:
        """
        Finds the set of states in the unobservable reach from the given state.
        """

        warnings.warn(
            "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
        )
        if isinstance(from_state, set):
            states = set()
            for x in from_state:
                states |= self.unobservable_reach(x)

            return states

        visited = {from_state}
        states_stack = deque(visited)
        while len(states_stack) > 0:
            state = states_stack.pop()
            dests_by_unobs = {
                out[0]
                for out in self.vs[state]["out"]
                if out[1] in self.Euo and out[0] not in visited
            }
            visited |= dests_by_unobs
            states_stack.extend(dests_by_unobs)

        return visited


class UnobservableReach:
    """
    Class for saving unobservable reach computations
    """

    def __init__(self, Euo, vs):
        self.USE_CACHE = True
        self.set_of_states_dict = dict()
        self.Euo = Euo
        self.vs = vs

    def empty(self):
        self.set_of_states_dict = dict()

    def from_set(self, set_of_states, events=None, freeze_result=False):
        """
        Compute the unobersvable reach from a set of starting states, considering unobservable events

        set_of_states: collection of state indices to start from
        events: set of events to consider as unobservable.
            Default 'None': uses parent Automata Euo attribute

        If using cache and set_of_states and events are NOT hashable types, this function will construct frozensets
        from each in order to use hashing.


        If a key has already been cached, but a not-frozenset was stored and key is now accessed with freeze_result=True:
            Return a frozenset of the previously stored result, so as to return what's expected.
            Currently overwrites the val (where dict[key]=val) with it's frozenset, although this behavior could be removed.
        """
        if events is None:
            events = self.Euo

        if not self.USE_CACHE:
            if freeze_result:
                return frozenset(self.__ureach_from_set(set_of_states, events))
            return self.__ureach_from_set(set_of_states, events)

        try:
            key = (set_of_states, events)
            if key in self.set_of_states_dict:
                result = self.set_of_states_dict[key]
                if freeze_result and not isinstance(result, frozenset):
                    # What was stored wasn't frozen,
                    # but this call used freeze_result=True
                    # Update the stored result to be frozen now:
                    result = frozenset(result)
                    self.set_of_states_dict[key] = result

                return result
            else:
                ur_set = self.__ureach_from_set(set_of_states, events)
                if freeze_result:
                    ur_set = frozenset(ur_set)
                self.set_of_states_dict[key] = ur_set
                return ur_set

        except TypeError:
            # Trying to hash an 'unhashable type'
            try:
                key = (frozenset(set_of_states), frozenset(events))
                if key in self.set_of_states_dict:
                    result = self.set_of_states_dict[key]
                    if freeze_result and not isinstance(result, frozenset):
                        result = frozenset(result)
                        self.set_of_states_dict[key] = result

                    return result
                else:
                    ur_set = self.__ureach_from_set(set_of_states, events)
                    if freeze_result:
                        ur_set = frozenset(ur_set)
                    self.set_of_states_dict[key] = ur_set
                    return ur_set
            except:
                # Couldn't convert to frozenset?
                print("Entry unhashble, error converting to frozenset().")
                raise

    def __ureach_from_set(self, set_of_states, events):
        """
        Find the collected unobservable reach for all states in S
        set_of_states: set of states to search from (graph indicies)
        events: set of unobservable events to consider
        """
        x_set = set()
        x_set.update(set_of_states)

        if not events:
            return x_set

        uc_neighbors = {
            t[0]
            for s in set_of_states
            for t in self.vs["out"][s]
            if t[1] in events and t[0] not in x_set
        }

        while uc_neighbors:
            x_set.update(uc_neighbors)
            uc_neighbors = {
                t[0]
                for s in uc_neighbors
                for t in self.vs["out"][s]
                if t[1] in events and t[0] not in x_set
            }
        return x_set

    def __str__(self):
        return "UR Class\n   Sets of states: {}\n   Len(keys): {}\n   Len(items): {}".format(
            len(self.set_of_states_dict),
            sum((len(k[0]) + len(k[1])) for k in self.set_of_states_dict.keys()),
            sum(len(i) for i in self.set_of_states_dict.items()),
        )
