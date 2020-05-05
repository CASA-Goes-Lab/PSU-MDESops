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

from collections.abc import Iterable

from .AES.SynthSMV_AES import write_AES_SMV_model
from .basic.generic_functions import find_Euc as find_Euc_i
from .basic.generic_functions import find_Euo as find_Euo_i
from .basic.generic_functions import find_obs_contr
from .basic.observer_comp import observer_comp
from .basic.parallel_comp import parallel_comp as parallel_comp_i
from .basic.product_comp import product_comp as product_comp_i
from .basic.ureach import unobservable_reach, ureach_from_set
from .error import DependencyNotInstalledError, IncongruencyError, MissingAttributeError
from .Event import Event
from .file.fsm_to_igraph import fsm_to_igraph
from .file.igraph_to_fsm import igraph_to_fsm
from .supremal.supremal_cn_supervisor import (
    supremal_cn_supervisor as supremal_cn_supervisor_i,
)
from .supremal.supremal_controllable_supervisor import (
    supremal_controllable_supervisor as scs_i,
)
from .VLPPO.VLPPO import offline_VLPPO as offline_VLPPO_i

try:
    import igraph as ig
except ImportError:
    raise DependencyNotInstalledError("IGraph library not found")


# from ..supremal.supremal_controllable_supervisor import supremal_controllable_supervisor_pp
# from ..basic.construct_spa import construct_spa
# from ..basic.construct_subautomata import construct_subautomata
# from ..basic.parallel_comp_old import parallel_comp


class Automata:
    def __init__(self, init=None):
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
        self.Euc = set()
        self.Euo = set()
        self.E = set()
        self.X_crit = set()
        self.Ea = set()
        self.dead_state = None
        self.type = None

        if isinstance(init, str):
            # Create Automata from `*.fsm` filetype.
            fsm_filename = init
            self._graph = ig.Graph(directed=True)
            fsm_to_igraph(fsm_filename, self._graph)
            find_obs_contr(self._graph, self.Euc, self.Euo, self.E)
            if "crit" in self._graph.vs.attributes():
                self.X_crit = {v["name"] for v in self._graph.vs if v["crit"]}

        elif isinstance(init, ig.Graph):
            # Create Automata from igraph Graph
            graph = init
            self._graph = graph.copy()
            find_obs_contr(self._graph, self.Euc, self.Euo, self.E)

        elif isinstance(init, Automata):
            # Create Automata from another Automata
            self._graph = init._graph.copy()
            self.Euc = init.Euc.copy()
            self.Euo = init.Euo.copy()
            self.X_crit = init.X_crit.copy()
            self.dead_state = init.dead_state
            self.type = init.type

        if "label" not in self._graph.es.attributes():
            self._graph.es["label"] = [""]

        if "name" not in self._graph.vs.attributes():
            self._graph.vs["name"] = [""]

        self.type = "graph"
        if "type_state" in self._graph.vs.attributes():
            self.type = "IDA"

        # Allow references to graph instance's edge & vertex sequence methods
        # from the Automata (e.g. self.es as opposed to doing self._graph.es)
        self.es = self._graph.es
        self.vs = self._graph.vs

        # More bindings to igraph Graph methods, used in some functions in
        # this file, potentially useful elsewhere?

        self.write_dot = self._graph.write_dot

        # bool was its own function, but this is easier to understand.
        self.__bool__ = self._graph.__bool__()

    def add_edge(self, source, target, label=None, prob=None):
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
        self._graph.add_edge(source, target)
        if label:
            self._graph.es[self.ecount() - 1].update_attributes({"label": label})
        if prob:
            self._graph.es[self.ecount() - 1].update_attributes({"prob": prob})

    def add_edges(self, pair_list, labels=None, probs=None):
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
            self._graph.es["label"] = new_labels

        if probs:
            self._graph.es["prob"] = new_probs

    def add_vertex(self, name=None):
        self._graph.add_vertex()
        if name:
            self._graph.vs[self.vcount() - 1].update_attributes({"name": name})

    def add_vertices(self, number_vertices, names=None):
        if names:
            if number_vertices != len(names):
                raise IncongruencyError(
                    "Number vertices to be added != number of names provided"
                )
            new_names = list(self._graph.vs["name"])
            new_names.extend(names)
        self._graph.add_vertices(number_vertices)
        if names:
            self._graph.vs["name"] = new_names

    def copy(self):
        """
        Copy from self to other, as in:
        >>> other = self.copy()
        """
        A = Automata(self)
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

    # Read/write Automata (Graph) from/to fsm filetypes
    # Depend on implementation in automata_operations/file/igraph_to_fsm
    # and automata_operations/file/fsm_to_igraph
    # Require the filename to be provided.
    def write_fsm(self, filename):
        """
        Write Automata (Graph) to fsm filetype
        Depends on implementation in automata_operations/file/igraph_to_fsm

        filename: string for file to write to, e.g. 'output.fsm'
        """
        igraph_to_fsm(filename, self._graph)

    def read_fsm(self, filename):
        """
        Read/write Automata (Graph) from/to fsm filetypes
        Depends on implementation in automata_operations/file/fsm_to_igraph

        filename: string to for file to read from, e.g. 'input.fsm'
        """
        P = ig.Graph(directed=True)
        fsm_to_igraph(filename, P)
        self._graph = P
        find_obs_contr(self._graph, self.Euc, self.Euo, self.E)
        if "crit" in self._graph.vs.attributes():
            self.X_crit = {v["name"] for v in self._graph.vs if v["crit"]}

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

    def _extended_ureach():
        # TODO
        return

    def _extended_reach():
        # TODO
        return

    def observer(self, save_state_names=True, save_marked_states=False):
        """
        Constructs an observer of the given automata. Each state in the observer
        represents the best state estimate as a set of possible states the system
        could be in.

        Returns the observer as an Automata

        Requires the unobersvable events in the system be notated in some way.
        If Euo is not empty, those events will be used as the unobservable event set.
        Otherwise, the observer_comp function will check the igraph Graph edges
        for an "Euo" attribute, {G.es()["Euo"]} and from that construct the unobservable
        event set (legacy, shouldn't happen anymore; any initialization method from igraph Graphs
        should find the Euo set already).

        Parameters:
        save_state_names (default True): currently does nothing (!!!!)
            Note: the thinking for this was that currently, state names ("name" vertex attribute)
            are sets of states from the original Automata. This parameter could avoid
            allowing unnecessarily saving this information. Change to be similar to parallel_comp,
            where the names just don't get assigned to the result?

        save_marked_states (default False):

        Usage:
        >>> O = G.observer()

        Depends on observer_comp, implemented in basic/observer_comp
        """
        if save_marked_states:
            if "marked" not in self._graph.vs.attributes():
                raise MissingAttributeError(
                    'Graph does not have "marked" attribute on states'
                )
        PO = ig.Graph(directed=True)
        observer_comp(self._graph, PO, self.Euo, save_state_names, save_marked_states)
        PO_A = Automata(PO)
        PO_A.type = "obs"
        return PO_A

    def plot(self, layout_i="kk", bbox_i=(0, 0, 2000, 2000), margin_i=100):
        """
        Plot the Graph attribute of the Automata.
        If the automata is an IDA or similar, the plot will differentiate the two state types.
        layout_i, bbox_i and margin_i are passed into the igraph plot function,
        and are defined in the igraph plot documentation.
        Roughly:
            layout_i: layout algorithm used, default is Kamada-Kawai force-directed algorithm.
            bbox_i: bounding box of the plot, with dimensions in pixels.
            margin_i: margin width in pixels to surround the plot.
        Plotting is done by the igraph library.
        Requires cairo package to be installed.
        """
        # try:
        #     import cairo
        # except ImportError:
        #     raise DependencyNotInstalledError("cairo required to plot Igraph graphs")

        P = self._graph.copy()
        P.es["label"] = [str2(l) for l in P.es["label"]]

        P.vs["name"] = [str2(v) for v in P.vs["name"]]

        P.vs["label"] = P.vs["name"]
        P.vs["label_size"] = [30]
        P.vs["size"] = [70]
        ig.plot(P, bbox=bbox_i, layout=layout_i, margin=margin_i)

    def write_pickle(self, filename, compress=False):
        """
        Serialize Automata instance with pickle.
        Requires an output filename, e.g. filename = 'ex_out.pickle'
        compress (default False): if true, pickle with compression (use .picklez extension)
            If zipped, have to read_pickle w/ compress=True as well.
        Pickling is done via an igraph Graph method write_pickle.

        Need to package any relevant Automata info into igraph Graph object.
        """
        self._graph["Euc"] = self.Euc
        self._graph["Euo"] = self.Euo
        self._graph["Ea"] = self.Ea
        self._graph["X_crit"] = self.X_crit
        self._graph["type"] = self.type
        if not compress:
            self._graph.write_pickle(filename)
        else:
            self._graph.write_picklez(filename)

    def read_pickle(self, filename, compress=False):
        """
        Unserialize pickle file, obtaining original Automata.
        Requires an input filename, e.g. filename = 'ex_in.pickle'
        compress (default False): set true if converting a zipped pickle file e.g. picklez.
        Uses Read_pickle(z), an igraph Graph class method.

        Unpacks relevant Automata info stored in the igraph Graph object.
        """
        if not compress:
            self._graph = ig.Graph.Read_Pickle(filename)
        else:
            self._graph = ig.Graph.Read_Picklez(filename)
        # Retrieve any other releveant info from graph object e.g. obs/contr sets.
        self.Euc = self._graph["Euc"]
        self.Euo = self._graph["Euo"]
        self.Ea = self._graph["Ea"]
        self.X_crit = self._graph["X_crit"]
        self.type = self._graph["type"]

    def write_svg(  # noqa: C901
        self,
        fname,
        layout="auto",
        width=None,
        height=None,
        vlabels="name",
        elabels="label",
        colors="color",
        shapes="shape",
        vertex_size=10,
        edge_colors="color",
        edge_stroke_widths="width",
        font_size=16,
        *args,
        **kwds
    ):

        try:
            import math
        except ImportError:
            raise DependencyNotInstalledError("Math library not found")

        """Saves the graph as an SVG (Scalable Vector Graphics) file

        *************
        NOTE for Automata class :: this is taken from the igraph library.
        Most of the function is copied directly from the write_svg function
        in the igraph Graph class, but with some modifications to include
        labels in edge attributes.

        Changes to declaration:
        labels="label" --> vlabels = "name" (default name for vertex labels attribute is "name").
        Made elabels = "label" - optionally provide name of edge label attributes,
            or a list of edge names, (default is "label").

        All other changes made here to the original function are indicated.
        *************

        The file will be Inkscape (http://inkscape.org) compatible.
        In Inkscape, as nodes are rearranged, the edges auto-update.

        @param fname: the name of the file or a Python file handle
        @param layout: the layout of the graph. Can be either an
          explicitly specified layout (using a list of coordinate
          pairs) or the name of a layout algorithm (which should
          refer to a method in the L{Graph} object, but without
          the C{layout_} prefix.
        @param width: the preferred width in pixels (default: 400)
        @param height: the preferred height in pixels (default: 400)
        @param labels: the vertex labels. Either it is the name of
          a vertex attribute to use, or a list explicitly specifying
          the labels. It can also be C{None}.
        @param colors: the vertex colors. Either it is the name of
          a vertex attribute to use, or a list explicitly specifying
          the colors. A color can be anything acceptable in an SVG
          file.
        @param shapes: the vertex shapes. Either it is the name of
          a vertex attribute to use, or a list explicitly specifying
          the shapes as integers. Shape 0 means hidden (nothing is drawn),
          shape 1 is a circle, shape 2 is a rectangle and shape 3 is a
          rectangle that automatically sizes to the inner text.
        @param vertex_size: vertex size in pixels
        @param edge_colors: the edge colors. Either it is the name
          of an edge attribute to use, or a list explicitly specifying
          the colors. A color can be anything acceptable in an SVG
          file.
        @param edge_stroke_widths: the stroke widths of the edges. Either
          it is the name of an edge attribute to use, or a list explicitly
          specifying the stroke widths. The stroke width can be anything
          acceptable in an SVG file.
        @param font_size: font size. If it is a string, it is written into
          the SVG file as-is (so you can specify anything which is valid
          as the value of the C{font-size} style). If it is a number, it
          is interpreted as pixel size and converted to the proper attribute
          value accordingly.
        """
        if width is None and height is None:
            width = 400
            height = 400
        elif width is None:
            width = height
        elif height is None:
            height = width

        if width <= 0 or height <= 0:
            raise ValueError("width and height must be positive")

        if isinstance(layout, str):
            # Changed self.layout to ig.layout --> layout is a member of igraph imported as ig (changed)
            layout = self._graph.layout(layout, *args, **kwds)

        if isinstance(vlabels, str):
            # Changed instances of labels here to vlabels (changed)
            try:
                vlabels = self._graph.vs.get_attribute_values(vlabels)
                # Added below to write nothing ("") instead of "None"
                vlabels = ["" if not vl else vl for vl in vlabels]
            except KeyError:
                vlabels = [x + 1 for x in range(self.vcount())]
        elif vlabels is None:
            vlabels = [""] * self.vcount()

        if isinstance(elabels, str):
            # Created as a slightly modified copy of above vlabels logic  (changed)
            try:
                elabels = self._graph.es.get_attribute_values(elabels)
                # Added below to write nothing ("") instead of "None"
                elabels = ["" if not el else el for el in elabels]
            except KeyError:
                elabels = [x + 1 for x in range(self.ecount())]
        elif elabels is None:
            elabels = [""] * self.ecount()

        if isinstance(colors, str):
            try:
                colors = self.vs.get_attribute_values(colors)
            except KeyError:
                colors = ["red"] * self.vcount()

        if isinstance(shapes, str):
            try:
                shapes = self.vs.get_attribute_values(shapes)
            except KeyError:
                shapes = [1] * self.vcount()

        if isinstance(edge_colors, str):
            try:
                edge_colors = self.es.get_attribute_values(edge_colors)
            except KeyError:
                edge_colors = ["black"] * self.ecount()

        if isinstance(edge_stroke_widths, str):
            try:
                edge_stroke_widths = self.es.get_attribute_values(edge_stroke_widths)
            except KeyError:
                edge_stroke_widths = [2] * self.ecount()

        if not isinstance(font_size, str):
            font_size = "%spx" % str(font_size)
        else:
            if ";" in font_size:
                raise ValueError("font size can't contain a semicolon")

        vcount = self.vcount()
        # labels --> vlabels  (changed)
        vlabels.extend(str(i + 1) for i in range(len(vlabels), vcount))
        colors.extend(["red"] * (vcount - len(colors)))

        if isinstance(fname, str):
            f = open(fname, "w")
            our_file = True
        else:
            f = fname
            our_file = False

        # BoundingBox is a graph method  (changed)
        bbox = ig.BoundingBox(layout.bounding_box())

        sizes = [width - 2 * vertex_size, height - 2 * vertex_size]
        w, h = bbox.width, bbox.height

        ratios = []
        if w == 0:
            ratios.append(1.0)
        else:
            ratios.append(sizes[0] / w)
        if h == 0:
            ratios.append(1.0)
        else:
            ratios.append(sizes[1] / h)

        layout = [
            [
                (row[0] - bbox.left) * ratios[0] + vertex_size,
                (row[1] - bbox.top) * ratios[1] + vertex_size,
            ]
            for row in layout
        ]

        # Should all be directed anyways: (changed)
        directed = True  # self._graph.is_directed()

        print('<?xml version="1.0" encoding="UTF-8" standalone="no"?>', file=f)
        print(
            "<!-- Created by igraph (http://igraph.org/) for use in Inkscape (http://www.inkscape.org/) -->",
            file=f,
        )
        print(file=f)
        print(
            '<svg xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:cc="http://creativecommons.org/ns#" xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:svg="http://www.w3.org/2000/svg" xmlns="http://www.w3.org/2000/svg" xmlns:sodipodi="http://sodipodi.sourceforge.net/DTD/sodipodi-0.dtd" xmlns:inkscape="http://www.inkscape.org/namespaces/inkscape"',
            file=f,
        )
        print('width="{0}px" height="{1}px">'.format(width, height), end=" ", file=f)

        edge_color_dict = {}
        print('<defs id="defs3">', file=f)
        for e_col in set(edge_colors):
            if e_col == "#000000":
                marker_index = ""
            else:
                marker_index = str(len(edge_color_dict))
            # Print an arrow marker for each possible line color
            # This is a copy of Inkscape's standard Arrow 2 marker
            print("<marker", file=f)
            print('   inkscape:stockid="Arrow2Lend{0}"'.format(marker_index), file=f)
            print('   orient="auto"', file=f)
            print('   refY="0.0"', file=f)
            print('   refX="0.0"', file=f)
            print('   id="Arrow2Lend{0}"'.format(marker_index), file=f)
            print('   style="overflow:visible;">', file=f)
            print("  <path", file=f)
            print('     id="pathArrow{0}"'.format(marker_index), file=f)
            print(
                '     style="font-size:12.0;fill-rule:evenodd;stroke-width:0.62500000;stroke-linejoin:round;fill:{0}"'.format(
                    e_col
                ),
                file=f,
            )
            print(
                '     d="M 8.7185878,4.0337352 L -2.2072895,0.016013256 L 8.7185884,-4.0017078 C 6.9730900,-1.6296469 6.9831476,1.6157441 8.7185878,4.0337352 z "',
                file=f,
            )
            print('     transform="scale(1.1) rotate(180) translate(1,0)" />', file=f)
            print("</marker>", file=f)

            edge_color_dict[e_col] = "Arrow2Lend{0}".format(marker_index)
        print("</defs>", file=f)
        print(
            '<g inkscape:groupmode="layer" id="layer2" inkscape:label="Lines" sodipodi:insensitive="true">',
            file=f,
        )

        for eidx, edge in enumerate(self.es):
            vidxs = edge.tuple
            x1 = layout[vidxs[0]][0]
            y1 = layout[vidxs[0]][1]
            x2 = layout[vidxs[1]][0]
            y2 = layout[vidxs[1]][1]
            angle = math.atan2(y2 - y1, x2 - x1)
            x2 = x2 - vertex_size * math.cos(angle)
            y2 = y2 - vertex_size * math.sin(angle)

            print("<path", file=f)
            print(
                '    style="fill:none;stroke:{0};stroke-width:{2};stroke-linecap:butt;stroke-linejoin:miter;stroke-miterlimit:4;stroke-opacity:1;stroke-dasharray:none{1}"'.format(
                    edge_colors[eidx],
                    ";marker-end:url(#{0})".format(edge_color_dict[edge_colors[eidx]])
                    if directed
                    else "",
                    edge_stroke_widths[eidx],
                ),
                file=f,
            )
            print('    d="M {0},{1} {2},{3}"'.format(x1, y1, x2, y2), file=f)
            print('    id="path{0}"'.format(eidx), file=f)
            print('    inkscape:connector-type="polyline"', file=f)
            print('    inkscape:connector-curvature="0"', file=f)
            print('    inkscape:connection-start="#g{0}"'.format(edge.source), file=f)
            print('    inkscape:connection-start-point="d4"', file=f)
            print('    inkscape:connection-end="#g{0}"'.format(edge.target), file=f)
            print('    inkscape:connection-end-point="d4" />', file=f)

            # Additions to write label attributes to edges: (changed)
            print('<text dy="-2%">', file=f)  # Move the labels off arrows slightly
            # textPath's for associateed paths made above,
            #  startOffset required to move labels off vertices (should be in the middle of vertices)
            print(
                '    <textPath href="#path{0}" startOffset="50%">'.format(eidx), file=f
            )
            # Text stored in elabels
            print("{0}".format(str2(elabels[eidx])), file=f)
            print("    </textPath>", file=f)
            print("</text>", file=f)

        print("  </g>", file=f)
        print(file=f)

        print(
            '  <g inkscape:label="Nodes" \
                    inkscape:groupmode="layer" id="layer1">',
            file=f,
        )
        print("  <!-- Vertices -->", file=f)

        if any(x == 3 for x in shapes):
            # Only import tkFont if we really need it. Unfortunately, this will
            # flash up an unneccesary Tk window in some cases
            import tkinter.font
            import tkinter as tk

            # This allows us to dynamically size the width of the nodes
            font = tkinter.font.Font(
                root=tk.Tk(), font=("Sans", font_size, tkinter.font.NORMAL)
            )

        for vidx in range(self.vcount()):
            print(
                '    <g id="g{0}" transform="translate({1},{2})">'.format(
                    vidx, layout[vidx][0], layout[vidx][1]
                ),
                file=f,
            )
            if shapes[vidx] == 1:
                # Undocumented feature: can handle two colors but only for circles
                c = str(colors[vidx])
                if " " in c:
                    c = c.split(" ")
                    vs = str(vertex_size)
                    print(
                        '     <path d="M -{0},0 A{0},{0} 0 0,0 {0},0 L \
                                -{0},0" fill="{1}"/>'.format(
                            vs, c[0]
                        ),
                        file=f,
                    )
                    print(
                        '     <path d="M -{0},0 A{0},{0} 0 0,1 {0},0 L \
                                -{0},0" fill="{1}"/>'.format(
                            vs, c[1]
                        ),
                        file=f,
                    )
                    print(
                        '     <circle cx="0" cy="0" r="{0}" fill="none"/>'.format(vs),
                        file=f,
                    )
                else:
                    print(
                        '     <circle cx="0" cy="0" r="{0}" fill="{1}"/>'.format(
                            str(vertex_size), str(colors[vidx])
                        ),
                        file=f,
                    )
            elif shapes[vidx] == 2:
                print(
                    '      <rect x="-{0}" y="-{0}" width="{1}" height="{1}" id="rect{2}" style="fill:{3};fill-opacity:1" />'.format(
                        vertex_size, vertex_size * 2, vidx, colors[vidx]
                    ),
                    file=f,
                )
            elif shapes[vidx] == 3:
                (vertex_width, vertex_height) = (
                    font.measure(str(vlabels[vidx])) + 2,
                    font.metrics("linespace") + 2,
                )
                print(
                    '      <rect ry="5" rx="5" x="-{0}" y="-{1}" width="{2}" height="{3}" id="rect{4}" style="fill:{5};fill-opacity:1" />'.format(
                        vertex_width / 2.0,
                        vertex_height / 2.0,
                        vertex_width,
                        vertex_height,
                        vidx,
                        colors[vidx],
                    ),
                    file=f,
                )

            print(
                '      <text sodipodi:linespacing="125%" y="{0}" x="0" id="text{1}" style="font-size:{2}px;font-style:normal;font-weight:normal;text-align:center;line-height:125%;letter-spacing:0px;word-spacing:0px;text-anchor:middle;fill:#000000;fill-opacity:1;stroke:none;font-family:Sans">'.format(
                    vertex_size / 2.0, vidx, font_size
                ),
                file=f,
            )
            print(
                '<tspan y="{0}" x="0" id="tspan{1}" sodipodi:role="line">{2}</tspan></text>'.format(
                    vertex_size / 2.0, vidx, str2(vlabels[vidx])
                ),
                file=f,
            )
            print("    </g>", file=f)

        print("</g>", file=f)
        print(file=f)
        print("</svg>", file=f)

        if our_file:
            f.close()


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


def parallel_comp(
    inputs, save_state_names=True, save_marked_states=False, common_events=None
):
    """
    Computes the parallel composition of 2 (or more) Automata, and returns
    the resulting composition as an automata.

    Parameters

    inputs: an iterable collection of Automata (class object) for which
        the parallel composition will be computed. If saving state names (when
        save_state_names=True), this should be ordered, as it determines the
        order that vertex indices are stored in the composition's vertex names.

    save_state_names (default True): whether vertex names should be saved
        in the igraph Graph "name" attribute. If set to false, the attribute
        will not be set (less memory usage). Vertex names are a list of indicies
        from each input, in the order used by 'inputs'. For example, in the operation
        A || B || C, a vertex name '(0,3,1)' in the output O means that state is
        composed of vertex 0 in A, 3 in B, and 1 in C (by index, NOT vertex name).

    save_marked_states (default False): whether states in the composition
        should be 'marked' or not (marked if the composed states are both marked).
        An error will be raised if this parameter is True, but not all Automata
        in the composition have the "marked" parameter on their vertices.

    common_events (default None): if there are events in the event set that are not
        on any transitions of the input graphs, they can be provided through this
        parameter. For example, if in the operation A || B, A has 'c' in its event set,
        but no active transitions, including 'c' in common_events forces 'c' not
        to be a private event.

    Returns an Automata object.

    Usage: for composing Automata A, B and C with common event 'a'.
    >>> O = Automata([A, B, C], common_events='a')

    Depends on parallel_comp_i, implemented in basic/parallel_comp
    """

    # Change every state name to str or list of str
    for graph in inputs:
        graph.vs["name"] = [
            [str(n) for n in name]
            if isinstance(name, Iterable) and not isinstance(name, str)
            else str(name)
            for name in graph.vs["name"]
        ]

    if save_marked_states:
        if not all(["marked" in a.vs.attributes() for a in inputs]):
            raise MissingAttributeError(
                'Graph does not have "marked" attribute on states'
            )

    P = ig.Graph(directed=True)
    # Appears to work fine even though inputs are provided as automata, meaning
    # the parallel_comp_i function works on Automata objects & igraph Graphs?
    parallel_comp_i(P, inputs, save_state_names, save_marked_states, common_events)
    A = Automata(P)
    copy_event_sets(inputs, A)
    return A


def product_comp(inputs, save_state_names=True, save_marked_states=False):
    """
    Computes the product composition of 2 (or more) Automata, and returns
    the resulting composition as an automata.

    Parameters

    inputs: an iterable collection of Automata (class object) for which
        the parallel composition will be computed. If saving state names,
        this should be ordered, as it determines the order that vertex indices
        are stored in the composition's vertex names. MUST have at least two
        automata (length > 1). MUST have at least two graphs (length > 1).

    save_state_names (default True): whether vertex names should be saved
        in the igraph Graph "name" attribute. If set to false, the attribute
        will not be set (less memory usage). Vertex names are a list of indicies
        from each input, in the order used by 'inputs'. For example, in the operation
        A || B || C, a vertex name '(0,3,1)' in the output O means that state is
        composed of vertex 0 in A, 3 in B, and 1 in C (by index, NOT vertex name).

    save_marked_states (default False): whether states in the composition
        should be 'marked' or not (marked if the composed states are both marked).
        An error will be raised if this parameter is True, but not all Automata
        in the composition have the "marked" parameter on their vertices.

    Returns an Automata object.

    Depends on product_comp_i, implemented in basic/product_comp
    """
    if save_marked_states:
        if not all(["marked" in a.vs.attributes() for a in inputs]):
            raise MissingAttributeError(
                'Graph does not have "marked" attribute on states'
            )

    P = ig.Graph(directed=True)
    # Appears to work fine even though inputs are provided as automata, meaning
    # the parallel_comp_i function works on Automata objects & igraph Graphs?
    product_comp_i(P, inputs, save_state_names, save_marked_states)
    A = Automata(P)
    copy_event_sets(inputs, A)
    return A


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


def offline_VLPPO(
    system, specification, event_ordering=None, G_bad_states=None, construct_SA=True
):
    """
    Returns an Automata object which is a maximal controllable & observable supervisor of
        the given system and specification Automata.

    Parameters:
    system: Automata representing the plant/system.
    specification: Automata representing the desired specification.
    event_ordering: optionally provide a priority list of controllable events;
        if not provided, an arbitrary ordering will be used (the set of controllable
        events will be found as a python set(), and then casting the set into a list()).
    G_bad_states (default None): if the specification only intends to disable states in the plant,
        those vertices can be provided directly (slightly more efficient, as the specification
        associated with a list of bad states would already be a subautomaton of the system,
        skipping the step in offline_VLPPO_i where the system & spec are constructed again as
        subautomata). Can be provided as a list or iterable of vertices (as indices, NOT names)
        in the system.
    construct_SA (default True): flag to construct an equivalent G', H' from the system G and
        specification H such that H' is a subautomata of G'. Set to False if the input spec is
        already a subautomata of the input system or G_bad_states was provided (the specification
        is just a disabling of certain states in the system).

    The sets of uncontrollable and unobservable events, Euc and Euo respectively,
    are found as the unions of the Euc & Euo sets in the plant & specification.

    Depends on offline_VLPPO_i, implemented in automata_operations/VLPPO/VLPPO as
    offline_VLPPO().
    """
    Euc_u = system.Euc | specification.Euc
    Euo_u = system.Euo | specification.Euo
    P = offline_VLPPO_i(
        system, specification, Euc_u, Euo_u, event_ordering, G_bad_states, construct_SA
    )
    A = Automata(P)
    A.Euc = Euc_u
    A.Euo = Euo_u
    if system.Ea or specification.Ea:
        A.Ea = system.Ea | specification.Ea
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
    if isinstance(this, Automata):
        other.Euo = this.Euo
        other.Euc = this.Euc
        other.Ea = this.Ea
    else:
        other.Euo = set.union(*[a.Euo for a in this])
        other.Euc = set.union(*[a.Euc for a in this])
        other.Ea = set.union(*[a.Ea for a in this])
