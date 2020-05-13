# pylint: disable=C0103
# pylint: disable=C0301
"""
Automata class & methods:
Used to represent finite-state automata, by means of a directed
graph object (from the igraph library) with labelled transitions.

Provides access to many useful methods in discrete event systems,
e.g. parallel & product compositions or observer construction.

In general, these operations can be performed as follows:
>>> # For automata A , B:
>>> C = A.parallel_comp(B)
>>> O = A.observer()

Automata can be constructed by 'fsm' filetypes, providing easy
interface with DESUMA.
Alternatively, Automata can be created starting from an underlying
igraph Graph object.

The Automata structure is a directed graph with labelled transitions.
An igraph Graph object (member var '_graph') is used to represent this
structure. The graph is composed of edges and vertices, annotated respectively
with labels and names. These attributes can be accessed via the igraph Graph
EdgeSeq and VertSeq methods, accessed for an Automata G as follows:
>>> vert_seq = G.vs()
>>> edge_seq = G.es()
Note that the vs() and es() methods for the Automata class are directly bound to
the vs() and es() methods for the igraph Graph class.
vs() and es() have dict-like behavior for accessing attributes, which are used here
to store edge labels and vertex names, e.g:
>>> vert_name_list = G.vs()["name"] # G.vs["name"]
>>> edge_label_list = G.es()["label"] # G.es["label"]
And to access specific entries by value or index:
>>> vert_index_7 = G.vs()["name"][7] # equivalently G.vs()[7]["name"]
>>> edge_name_a = G.es(label_eq="a") # if multiple edges labelled 'a', returns first by index
In many cases, information relevant to vertices & edges are stored in attributes. For example,
in PFA, probabilities of a transition occuring are stored in the "prob" attribute, e.g:
>>> prob_trans_a = G.es(label_eq="a")["prob"]

Vertices and Edges can be named/labelled after their creation by accessing the
"name"/"label" attribute in the VertexSeq/EdgeSeq dict:
>>> E.vs["name"] = ['A','B','C','D','E']
Note that the this process cannot be used to update individual entries.
For example, the following code will NOT change the name of vertex 'E':

>>> G.vs["name"][4] = 'F' # WILL NOT MODIFY THE VERTEX NAME

Instead, the `update_attributes()` method must be used to modify specific edge or vertex
attributes. These are igraph Graph Edge and Vertex methods. For details on these methods,
see the igraph Edge and Vertex class documentations.

>>> d = {"name" : 'F'}
>>> G.vs[4].update_attributes(d) # Name of vertex 4 is now 'F'
>>> G.es[0].update_attributes({"label" : 'b'}) # Change edge 0 label from 'a' to 'b'

More details on using the vs() and es() methods can be found in the igraph documentation.
For simply using the Automata class, further functionality than described here might not be
required. Implementing new functionality might however require the use of certain specific
igraph functions or methods. Having these bindings also means that many times passing an Automata
to a function (implemented here) expecting an igraph Graph will still function normally.
Useful in cases like product and parallel compositions (product_comp() and parallel_comp(),
but might cause some unintended problems?

Class Members:
Euc: set object of uncontrollable events.
Euo: set object of unobservable events.
Ea: set of compromised events (not particularly relevant here? Used in SDA work)
    TODO: Probably shouldn't be here, but some in some functions e.g. copy_event_sets,
    it is a nice convenience. Those functions should instead be overridden in an inherited
    Automata class.
X_crit: set of critical states, stored as names of states.
    e.g., if an Automata is constructed from an igraph Graph with critical vertex named "V1",
    then X_crit will have as a member "V1" and NOT the corresponding indice of the vertex.
dead_state: convenience for operations that create a 'dead' state, usually empty.
type: what 'type' of Automata, default is 'graph'. Used for certain structures that
    need to be differentiated, which are contained exclusively to SDA work.
es: binding to igraph Graph 'edgeSeq' object, e.g.:
    >>> edgeSeqObj = automata_A.es()
    is equivalent to:
    >>> edgeSeqObj = automata_A._graph.es()
vs: binding to igraph Graph 'vertSeq' object, e.g.:
    >>> vertSeqObj = automata_A.vs()
    is equivalent to:
    >>> vertSeqObj = automata_A._graph.vs()

_graph: underlying igraph Graph instance storing the Automata structure. Contains the
    original EdgeSeq and VertSeq objects bound by the es() and vs() functions here.
    Ideally, usage of the the functions here will never require directly modifying
    this member. However, implementing new methods might require interfacing
    with igraph classes and functions.


    Further details of how the igraph library is used are included in the implementation
    files. For example, the observer() method in the Automata class merely does a call to
    the function 'observer_comp' in '..basic.observer_comp'

Methods:?

Additional functions in this file:
parallel_comp
product_comp
supremal_controllable_supervisor
supremal_cn_supervisor
offline_VLPPO
str2
copy_event_sets

"""

from abc import ABC, abstractmethod
from collections.abc import Iterable

from DESops.automata.event.event import Event
from DESops.basic_operations.generic_functions import find_Euc, find_Euo, find_obs_contr
from DESops.error import (
    DependencyNotInstalledError,
    IncongruencyError,
    MissingAttributeError,
    ConversionError,
)

try:
    import igraph as ig
except ImportError:
    raise DependencyNotInstalledError("IGraph library not found")


class _Automata:
    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        """
        Constructor can create an empty automata, or be created in one of the following ways:
        1.  From an existing igraph-Graph instance, the input graph is stored in self._graph
                If the input graph has distinguished types of states,
                automata is inferred to be type 'IDA'
        2.  From a fsm filetype, an igraph graph can be read from fsm_filename string.
        3.  From another Automata instance, has the same outcome of copying via the copy() method
            e.g.    >>> G = a.Automata()
                    >>> H1 = a.Automata(G)
                    >>> H2 = G.copy()
                    G, H1 & H2 in this example would be equivalent.
        Euc and Euo attributes can be inferred from provided graphs.
        """

        # Default case; create Automata from scratch.
        self._graph = ig.Graph(directed=True)
        self.events = set()  # IT SHOULD BE A SET OF EVENTS
        self.states = (
            list()
        )  # A SET OF STATES. I AM GOING BACK TO JUST USE VS OF IGRAPH TO BE THE SET OF STATES

        if not Euc:
            self.Euc = set()
        else:
            self.Euc = Euc.copy()
        if not Euo:
            self.Euo = set()
        else:
            self.Euo = Euo.copy()
        self.type = None

        if isinstance(init, ig.Graph):
            # Create Automata from igraph Graph
            graph = init
            self._graph = graph.copy()
            self.events = E
            # find_obs_contr(self._graph, self.Euc, self.Euo, self.events)

        elif isinstance(init, _Automata):
            # Create Automata from another Automata
            self._graph = init._graph.copy()
            self.events = init.events.copy()
            self.states = init.states.copy()
            self.type = init.type

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

    def add_edge(self, source, target, label, prob=None, fill_out=False):
        """
        Adds an edge to the Automata instance. Edge is created across pair, a tuple
        of vertex indices according to the igraph Graph add_edge() method.
        Additionlly adds label and probability information as edge attributes, if
        they are optionally provided.

        Parameters:
        pair: 2-tuple of vertex indicies as (source, target). See igraph documentation of
            the add_edge() method for more details on what is acceptable here.
        label: (default None) optionally provide label for this transition, to be stored
            in the "label" edge keyword attribute.
        prob: (default None) optionally provide probability for this transition (indicating
            stochastic transition), to be stored in the "prob" edge keyword attribute.
        """

        # SHOULD label be optional?
        # e.g. 'label=None' vs just 'label' in function arguments
        # when would an edge need to be added without a label?
        self._graph.add_edge(source, target)
        if label:
            self.es[self.ecount() - 1].update_attributes({"label": label})
        if prob:
            self.es[self.ecount() - 1].update_attributes({"prob": prob})

        if fill_out:
            self.vs["out"].append((target, label))

    def add_edges(self, pair_list, labels, probs=None, fill_out=False):
        """
        Add an iterable of edges to the Automata instance.
        Calls the igraph Graph add_edges() method on the underlying graph
        object. Additionally adds label and probability information as
        edge attributes, if they are optionally provided as parallel iterables.

        Parameters:
        pair_list: an iterable to be passed to the igraph Graph add_edges() method,
            which accepts iterables of pairs or an EdgeSeq (see igraph documentation
            for more details on what is acceptable here).
        labels: (default None) optionally provide an iterable of labels to attach as
            keyword attributes. Should be parallel to pair_list (e.g., pair n of
            pair_list corresponding to label n of labels). To be stored in the "label"
            edge keyword attribute.
        probs: (default None) optionally provide an iterable of probabilities to attach
            as keyword attributes (indicating stochastic transitions). Should be
            parallel to pair_list (e.g., pair n of pair_list corresponds to probability
            n of probs). To be stored in the "prob" edge keyword attribute.

        Returns nothing.
        """
        # SHOULD label be optional?
        # e.g. 'label=None' vs just 'label' in function arguments
        # when would an edge need to be added without a label?
        if labels:
            if len(pair_list) != len(labels):
                raise IncongruencyError("Length of pairs != length of labels")
            new_labels = list(self._graph.es["label"])
            new_labels.extend(labels)

        if probs:
            if len(pair_list) != len(probs):
                raise IncongruencyError("Length of pairs != length of probs")
            new_probs = list(self._graph.es["prob"])
            new_probs.extend(probs)

        self._graph.add_edges(pair_list)

        if labels:
            self.es["label"] = new_labels

        if probs:
            self.es["prob"] = new_probs

        if fill_out:
            for label, pair in zip(labels, pair_list):
                self.vs["out"][pair[0]].append((pair[1], label))

    def add_vertex(self, name=None, marked=None, **kwargs):
        self._graph.add_vertex()
        if name:
            self.vs[self.vcount() - 1].update_attributes({"name": name})
        if marked:
            self.vs[self.vcount() - 1].update_attributes({"marked" : marked})

        for arg in kwargs.items():
            if arg[0] in self._graph.vs.attributes():
                self._graph.vs[self.vcount() - 1].update_attributes({arg[0] : arg[1]})
            else:
                self._graph.vs[arg[0]] = arg[1]

    def add_vertices(self, number_vertices, names=None, marked=None, **kwargs):
        if names:
            if number_vertices != len(names):
                raise IncongruencyError(
                    "Number vertices to be added != number of names provided"
                )
            new_names = list(self._graph.vs["name"])

            try:
                new_names.extend(n for n in names if isinstance(n, str) or isinstance(n, int) or isinstance(n, Iterable))
            except:
                raise ConversionError("Could not convert state names of type {0}, need str/int/Iterable".format(type(names[0])))
        else:
            # if no names given, fill in with index names
            new_names = list(self.vs["name"])
            new_names.extend(i for i in range(self.vcount(), self.vcount() + number_vertices))

        if marked:
            if number_vertices != len(marked):
                raise IncongruencyError("Number vertices to be added != number names")
            new_marked = list(self._graph.vs["marked"])
            new_marked.extend(marked)

        self._graph.add_vertices(number_vertices)

        self._graph.vs["name"] = new_names

        if marked:
            # if not marked, igraph will fill with whatever the last value in marked vertices was
            # TODO: change this behavior? default false/true?
            self._graph.vs["marked"] = new_marked

        for arg in kwargs.items():
            if number_vertices != len(arg[1]):
                raise IncongruencyError(
                    "Number vertices to be added != number of names provided"
                )
            if arg[0] in self._graph.vs.attributes():
                new_list = list(self._graph.vs[arg[0]])
                new_list.extend(arg[1])
            else:
                self._graph.vs[arg[0]] = arg[1]

    def update_names(self, names):
        # update vertex names from list of names
        self.vs["name"] = names
    def copy(self):
        """
        Copy from self to other, as in:
        >>> other = self.copy()

        TODO: This needs to be an abstract method?
        """
        A = _Automata(self)
        return A

    # Methods to store event info in an Automata instance
    def add_attackable_event(self, event):
        """
        Add event to the Ea attribute.
        Alternative to directly adding to the attribute:
        >>> this_graph.Ea.add(event)
        instead of:
        >>> this_graph.add_attackable_event(event)
        """
        self.Ea.add(event)

    def add_critical_state(self, X_crit_state):
        """
        Alternative to adding a critical state, e.g.
        >>> A.add_critical_state('critical_state_name')
        is equivalent to:
        >>> A.X_crit.add('critical_state_name')
        """
        self.X_crit.add(X_crit_state)

    def set_dead_state(self, dead_state_index):
        """
        Alternative to setting the dead state, e.g.
        >>> A.set_dead_state(7)
        is equivalent to:
        >>> A.dead_state = 7
        """
        self.dead_state = dead_state_index

    def generate_adj_list(self):
        self.vs["out"] = self._graph.get_inclist()

    # Methods to interface w/ functions from automata_operations/basic/generic_functions
    # E.g. find_Euc_Euo finds the sets of uncontr. and unobs. events in the given automata.
    # Results are stored within the the Euc & Euo objects in the current automata.
    def find_Euc_Euo(self):
        """
        Extract uncontrollable & unoberservable events
        from igraph Graph instance.
        """
        find_obs_contr(self._graph, self.Euc, self.Euo, self.E)

    def find_Euc(self):
        """
        Extract uncontrollable events from igraph Graph instance.
        """
        find_Euc_i(self._graph, self.Euc)

    def find_Euo(self):
        """
        Extract unobservable events from igraph Graph instance.
        """
        find_Euo_i(self._graph, self.Euo)

    # Methods to interface with graph variables & methods
    def vcount(self):
        """
        Return the number of vertices in the Automata.
        Binding to igraph Graph vcount() method.
        This is the preferred method to find vertex count.
        """
        return self._graph.vcount()

    def ecount(self):
        """
        Return the number of edges in the Automata.
        Binding to igraph Graph ecount() method.
        This is the preferred method to find edge count.
        """
        return self._graph.ecount()

    def ureach(self, x_set, state_s, e):
        """
        Finds x_set, the set of states in the unobservable reach from
        an intial state/set of states (via unobservable events in e).
        Depends on ureach_from_set and unobservable_reach, both implemented in
        automata_operations/basic/ureach (might want to rename this to something more general).
        The states reached from states in state_s via unobservable event traces (from events in e).
        are added to the set x_set (x_set is modified).
        """
        if isinstance(state_s, Iterable):
            ureach_from_set(x_set, state_s, self._graph, e)
        else:
            unobservable_reach(x_set, state_s, self._graph, e)


def str2(label):
    """
    Helpful function used occasionally in this file.
    Handles smart/alternate casting to strings (str objects).

    e.g:
    If label is an inserted Event object, with label 'a',
    this function will return the string "('a','i')"

    If label is a frozenset, frozenset({1,2,3}), this function
    will return the str casting of the set casting of the frozenset,
    or "{1,2,3}"

    Otherwise, returns the normal str casting of label.
    """
    if isinstance(label, Event):
        return str(label.name())
    if isinstance(label, frozenset):
        return str(set(label))
    return str(label)


def supremal_contr_supervisor(system, specification):
    """
    Computes the supremal controllable supervisor for the given plant
    and specficiation Automata.

    Returns the supremal controllable supervisor as an Automata.

    Parameters:
    system: Automata representing the plant/system.
    specification: Automata representing the desired specification.

    The set of uncontrollable events, Euc, is found as the union
    of the Euc sets in the plant & specification.

    Assumes K is a sublanguage of M, where L(plant) = M & L(spec) = K

    Depends on supremal_controllable_supervisor, implemented in
    automata_operations/supremal/supremal_controllable_supervisor
    """
    Euc_u = system.Euc.union(specification.Euc)
    A = Automata(scs_i(system, specification, Euc_u))
    copy_event_sets([system, specification], A)
    return A


def supremal_cn_supervisor(system, specification):
    """
    Computes the supremal controllable-normal supervisor for the given
    plant and specification Automata.

    Returns the supremal CN supervisor as an Automata.

    Parameters:
    system: Automata representing the plant/system.
    specification: Automata representing the desired specification.

    The sets of uncontrollable and unobservable events, Euc and Euo,
    are found as the unions of their respective sets in the plant & specification.

    Depends on supremal_cn_supervisor, implemented in
    automata_operations/supremal/supremal_cn_supervisor
    """
    Euc_u = system.Euc | specification.Euc
    Euo_u = system.Euo | specification.Euo
    A = Automata(supremal_cn_supervisor_i(specification, system, Euc_u, Euo_u))
    copy_event_sets([system, specification], A)
    return A


def copy_event_sets(this, other):
    """
    Useful function to copy event sets from 'this' to 'other'.
    Event sets being the set of unobservable events Euo, the set
    of uncontrollable events Euc, and the set of compromised
    events Ea.

    Used for example in the parallel_comp function to handle
    copying attributes from an input set of automata to the
    automata resulting from the composition.

    this: either an automata or iteratable collection of automata,
        from which event sets will be copied.
    other: automata, target of the copying.

    If 'this' is an interable, the event sets copied to 'other'
    will be the set union of the automata in 'this'.

    """
    if isinstance(this, _Automata):
        other.Euo = this.Euo
        other.Euc = this.Euc
        other.Ea = this.Ea
    else:
        other.Euo = set.union(*[a.Euo for a in this])
        other.Euc = set.union(*[a.Euc for a in this])
        other.Ea = set.union(*[a.Ea for a in this])
