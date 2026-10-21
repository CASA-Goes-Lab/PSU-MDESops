"""Convert Supremica .wmod format to internal IGraph Automaton representation"""

import DESops as d

import xml.etree.ElementTree as ET


def read_wmod(file_name, g=None, type_aut=d.NFA):
    """
    Read a Supremica wmod file (XML) into an Automaton.
    These files are used to store modules in Supremica, representing a collection of interconnected automata.
    They are produced using the save functionality in Supremica.

    Parameters
    ----------
    file_name : str
        The wmod file
    g : Automaton or None
        The optional location to store the read automaton
    type_aut : class
        The type of automaton to create (DFA, NFA, or PFA)

    Returns
    -------
    Automaton
        The automaton that was read
    """
    if g is None:
        g = type_aut()

    wmod = ET.parse(file_name)
    root = wmod.getroot()
    ns = {'d': "http://waters.sourceforge.net/xsd/module"}

    auto_name = root.get('Name')

    props = set()
    event_list = root.find('d:EventDeclList', ns)
    for event_dec in event_list.findall('d:EventDecl', ns):
        event_kind = event_dec.get('Kind')
        event_name = event_dec.get('Name')
        if event_kind == "PROPOSITION":
            props.add(event_name)
        elif event_kind == "CONTROLLABLE":
            g.events.add(event_name)
        elif event_kind == "UNCONTROLLABLE":
            g.events.add(event_name)
            g.Euc.add(event_name)


    comp_list = root.find('d:ComponentList', ns)
    if len(comp_list) > 1:
        raise NotImplementedError("Currently only files with a single component are supported.")
    simple_comp = comp_list.find('d:SimpleComponent', ns)
    graph = simple_comp.find('d:Graph', ns)
    node_list = graph.find('d:NodeList', ns)
    node_dict = dict()
    for node in node_list.findall('d:SimpleNode', ns):
        name = node.get("Name")
        init = node.get("Initial") == "true"

        node_event_list = node.find('d:EventList', ns)
        attr_dict = dict()
        if not (node_event_list is None):
            attr_dict = {ident.get("Name"): True
                    for ident in node_event_list.findall('d:SimpleIdentifier', ns)}
        if ":accepting" in attr_dict:
            attr_dict["marked"] = attr_dict.pop(":accepting")
        node_dict[name] = g.add_vertex(name=name, init=init, **attr_dict).index

    print(node_dict)
    edge_list = graph.find('d:EdgeList', ns)
    for edge in edge_list.findall('d:Edge', ns):
        source = node_dict[edge.get('Source')]
        target = node_dict[edge.get('Target')]
        event_ident = edge.find('d:LabelBlock', ns).find('d:SimpleIdentifier', ns)
        event_name = event_ident.get('Name')
        g.add_edge(source, target, event_name)
    return g


def read_xml_automaton(file_name, g=None, type_aut=d.NFA):
    """
    Read an XML file exported by Supremica into an Automaton.
    Such an XML file is produced by exporting an automaton from Supremica in the analyze tab

    Parameters
    ----------
    file_name : str
        The wmod file
    g : Automaton or None
        The optional location to store the read automaton
    type_aut : class
        The type of automaton to create (DFA, NFA, or PFA)

    Returns
    -------
    Automaton
        The automaton that was read
    """
    xml_file = ET.parse(file_name)
    root = xml_file.getroot()

    if g is None:
        g = type_aut()

    graph_name = root.get('Name')

    automaton = root.find('Automaton')
    auto_name = automaton.get("name")

    event_dict = {}
    state_dict = {}

    events = automaton.find('Events')
    for event in events.findall('Event'):
        eid = event.get('id')
        label = event.get('label')
        event_dict[eid] = label
        if event.get('controllable') == 'false':
            g.Euc.add(label)
        g.events.add(label)

    states = automaton.find('States')
    g.vs["init"] = False
    g.vs["marked"] = False
    g.vs["forbidden"] = False
    for state in states.findall('State'):
        sid = state.get('id')
        name = state.get('name')
        state_dict[sid] = name
        attr_dict = {"name":name,
                     "init":state.get('initial') == "true"}
        if state.get('accepting') == 'true':
            attr_dict['marked'] = True
        if state.get('forbidden') == 'true':
            attr_dict['forbidden'] = True
        g.add_vertex(**attr_dict)

    transitions = automaton.find('Transitions')
    for trans in transitions.findall('Transition'):
        source = state_dict[trans.get('source')]
        dest = state_dict[trans.get('dest')]
        event = trans.get('event')
        g.add_edge(source, dest, event=event_dict[event])

    return g



def write_wmod(file_name, g):
    """
    Write an Automaton object into Supremica wmod file (XML).

    Parameters
    ----------
    file_name : str
        The wmod file
    g : Automaton
        The automaton
    """
    ET.register_namespace('d', "http://waters.sourceforge.net/xsd/module")
    root = ET.Element("Module")
    root.set("xmlns", "http://waters.sourceforge.net/xsd/module")
    root.set("xmlns:ns2", "http://waters.sourceforge.net/xsd/module")
    root.set("xmlns:ns3", "http://waters.sourceforge.net/xsd/module")

    auto_name = root.get('Name')

    event_list = ET.SubElement(root, 'EventDeclList')
    ET.SubElement(event_list, "EventDecl", Kind="PROPOSITION", Name=":accepting")
    ET.SubElement(event_list, "EventDecl", Kind="PROPOSITION", Name=":accepting")
    for event in g.events:
        kind = "UNCONTROLLABLE" if event in g.Euc else "CONTROLLABLE"
        ET.SubElement(event_list, "EventDecl", Kind=kind, Name=event)

    comp_list = ET.SubElement(root, 'ComponentList')
    simple_comp = ET.SubElement(comp_list, 'SimpleComponent')
    graph = ET.SubElement(simple_comp, 'Graph')
    node_list = ET.SubElement(graph, 'NodeList')
    for node in g.vs:
        simple_node = ET.SubElement(node_list, "SimpleNode", Name=node["name"])
        if node["init"]:
            simple_node.set("Initial", "true")
        if node["marked"]:
            el = ET.SubElement(simple_node, "EventList")
            ET.SubElement(el, "SimpleIdentifier", Name=":accepting")

    edge_list = ET.SubElement(graph, "EdgeList")
    for edge in g.es:
        edge_elem = ET.SubElement(edge_list, 'Edge',
                                  Source=edge.source_vertex["name"], Target=edge.target_vertex["name"])
        event_ident = ET.SubElement(edge_elem, 'LabelBlock')
        ET.SubElement(event_ident, 'SimpleIdentifier', Name=edge["label"])

    tree = ET.ElementTree(root)
    ET.indent(tree, '  ')
    tree.write(file_name, xml_declaration=True, encoding="utf-8", method="xml")


def write_wmod_multi(file_name, plants=None, specs=None):
    if plants is None:
        plants = []
    if specs is None:
        specs = []

    ET.register_namespace('d', "http://waters.sourceforge.net/xsd/module")
    root = ET.Element("Module")
    root.set("xmlns", "http://waters.sourceforge.net/xsd/module")
    root.set("xmlns:ns2", "http://waters.sourceforge.net/xsd/module")
    root.set("xmlns:ns3", "http://waters.sourceforge.net/xsd/module")
    root.set("Name", 'DESops_sys')

    E = set()
    Euc = set()
    for plant in plants:
        E |= plant.events
        Euc |= plant.Euc
    for spec in specs:
        E |= spec.events
        Euc |= spec.Euc

    event_list = ET.SubElement(root, 'EventDeclList')
    ET.SubElement(event_list, "EventDecl", Kind="PROPOSITION", Name=":accepting")
    for event in E:
        kind = "UNCONTROLLABLE" if event in Euc else "CONTROLLABLE"
        ET.SubElement(event_list, "EventDecl", Kind=kind, Name=event)

    comp_list = ET.SubElement(root, 'ComponentList')

    for i, g in enumerate(plants):
        _write_wmod_component(comp_list, g, kind="PLANT", name=f"plant_{i}")
    for i, g in enumerate(specs):
        _write_wmod_component(comp_list, g, kind="SPEC", name=f"spec_{i}")

    tree = ET.ElementTree(root)
    ET.indent(tree, '  ')
    tree.write(file_name, xml_declaration=True, encoding="utf-8", method="xml")


def _write_wmod_component(comp_list, g, kind, name):

    simple_comp = ET.SubElement(comp_list, 'SimpleComponent')
    simple_comp.set("Kind", kind)
    simple_comp.set("Name", name)
    graph = ET.SubElement(simple_comp, 'Graph')
    node_list = ET.SubElement(graph, 'NodeList')
    for node in g.vs:
        simple_node = ET.SubElement(node_list, "SimpleNode", Name=node["name"])
        if node["init"]:
            simple_node.set("Initial", "true")
        if node["marked"]:
            el = ET.SubElement(simple_node, "EventList")
            ET.SubElement(el, "SimpleIdentifier", Name=":accepting")

    edge_list = ET.SubElement(graph, "EdgeList")
    for edge in g.es:
        edge_elem = ET.SubElement(edge_list, 'Edge',
                                  Source=edge.source_vertex["name"], Target=edge.target_vertex["name"])
        event_ident = ET.SubElement(edge_elem, 'LabelBlock')
        ET.SubElement(event_ident, 'SimpleIdentifier', Name=edge["label"])
