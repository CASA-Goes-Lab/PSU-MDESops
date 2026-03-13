import json
from dash import Dash, html, dcc, Input, Output, State
import dash_cytoscape as cyto

app = Dash(__name__)

# ============================================================
# Helpers: Combined-state node ids + labels
# ============================================================
def combo_id(state_tuple):
    return "|".join(map(str, state_tuple))

def combo_label(state_tuple):
    return "(" + ",".join(map(str, state_tuple)) + ")"

def make_combo_node(state_tuple, x, y, classes=""):
    return {
        "data": {"id": combo_id(state_tuple), "label": combo_label(state_tuple)},
        "position": {"x": x, "y": y},
        "classes": classes,
    }

def make_edge(src_tuple, dst_tuple, event_label, edge_id=None, classes=""):
    """
    Creates an edge. If it's a self-loop (source == target), automatically
    adds the 'selfLoop' class so we can style it.
    """
    src = combo_id(src_tuple)
    dst = combo_id(dst_tuple)

    data = {"source": src, "target": dst, "label": event_label}
    if edge_id is not None:
        data["id"] = edge_id

    el = {"data": data}

    cls = (classes or "").strip()
    if src == dst:
        cls = (cls + " selfLoop").strip()

    if cls:
        el["classes"] = cls

    return el


# ============================================================
# Self-loop policy: allow at most ONE self-loop in the whole graph
# ============================================================
def is_self_loop(edge_el):
    d = edge_el.get("data", {})
    return d.get("source") == d.get("target")

def count_self_loops(elements):
    return sum(
        1
        for el in elements
        if el.get("data", {}).get("source") is not None and is_self_loop(el)
    )

def add_edge_with_single_self_loop_policy(edges_list, new_edge):
    if is_self_loop(new_edge):
        existing = sum(1 for e in edges_list if is_self_loop(e))
        if existing >= 1:
            raise ValueError(
                "Self-loop rejected: only ONE node in the entire graph may have a self-loop."
            )
    edges_list.append(new_edge)


# ============================================================
# Component metadata (G1/G2/G3 info)
# ============================================================
COMPONENT_INFO = [
    {
        "key": "G1",
        "name": "G1 (Valve mode)",
        "tuple_index": 0,
        "states": {"A": "Valve state A", "B": "Valve state B", "C": "Valve state C"},
        "note": "First entry in the tuple.",
    },
    {
        "key": "G2",
        "name": "G2 (Controller step)",
        "tuple_index": 1,
        "states": {1: "Controller state 1", 2: "Controller state 2", 3: "Controller state 3"},
        "note": "Second entry in the tuple.",
    },
    {
        "key": "G3",
        "name": "G3 (Heater)",
        "tuple_index": 2,
        "states": {"off": "Heater OFF", "on": "Heater ON"},
        "note": "Third entry in the tuple.",
    },
]


# ============================================================
# Per-component automata diagrams (placeholders - edit later)
# ============================================================
def node_el(node_id, label, x, y, classes=""):
    el = {"data": {"id": node_id, "label": label}, "position": {"x": x, "y": y}}
    if classes:
        el["classes"] = classes
    return el

def edge_el(src, dst, label, edge_id=None, classes=""):
    d = {"source": src, "target": dst, "label": label}
    if edge_id:
        d["id"] = edge_id
    el = {"data": d}
    if classes:
        el["classes"] = classes
    return el

def start_marker(start_id, start_edge_id, target_id, x, y):
    start_node = {"data": {"id": start_id}, "position": {"x": x, "y": y}, "classes": "start"}
    start_edge = {
        "data": {"id": start_edge_id, "source": start_id, "target": target_id, "label": ""},
        "classes": "startEdge",
    }
    return start_node, start_edge

G_AUTOMATA = {}

# G1
g1_nodes = [node_el("A", "A", 200, 200), node_el("B", "B", 450, 200), node_el("C", "C", 325, 380)]
g1_edges = [edge_el("A", "B", "to_B"), edge_el("B", "C", "to_C"), edge_el("C", "A", "to_A")]
g1_start, g1_start_edge = start_marker("__g1_start__", "__g1_start_edge__", "A", 110, 200)
G_AUTOMATA["G1"] = [g1_start, *g1_nodes, g1_start_edge, *g1_edges]

# G2
g2_nodes = [node_el("1", "1", 200, 220), node_el("2", "2", 420, 220), node_el("3", "3", 310, 380)]
g2_edges = [edge_el("1", "2", "step"), edge_el("2", "3", "step"), edge_el("3", "1", "reset")]
g2_start, g2_start_edge = start_marker("__g2_start__", "__g2_start_edge__", "1", 110, 220)
G_AUTOMATA["G2"] = [g2_start, *g2_nodes, g2_start_edge, *g2_edges]

# G3
g3_nodes = [node_el("off", "off", 220, 260), node_el("on", "on", 460, 260)]
g3_edges = [
    edge_el("off", "on", "turn_on"),
    edge_el("on", "off", "turn_off"),
    edge_el("on", "on", "hold", classes="selfLoop"),
]
g3_start, g3_start_edge = start_marker("__g3_start__", "__g3_start_edge__", "off", 130, 260)
G_AUTOMATA["G3"] = [g3_start, *g3_nodes, g3_start_edge, *g3_edges]


# ============================================================
# Combined graph initial/marked
# ============================================================
INITIAL_STATE = ("A", 1, "off")
MARKED_STATES = {("A", 1, "on")}

START_NODE_ID = "__start__"
START_EDGE_ID = "__start_edge__"

q0 = ("A", 1, "off")
q1 = ("A", 1, "on")
q2 = ("B", 2, "on")
q3 = ("C", 3, "on")

nodes = [
    make_combo_node(q0, x=250, y=250, classes="marked" if q0 in MARKED_STATES else ""),
    make_combo_node(q1, x=650, y=250, classes="marked" if q1 in MARKED_STATES else ""),
    make_combo_node(q2, x=650, y=500, classes="marked" if q2 in MARKED_STATES else ""),
    make_combo_node(q3, x=250, y=500, classes="marked" if q3 in MARKED_STATES else ""),
]

start_node = {"data": {"id": START_NODE_ID}, "position": {"x": 150, "y": 250}, "classes": "start"}
start_edge = {
    "data": {"id": START_EDGE_ID, "source": START_NODE_ID, "target": combo_id(INITIAL_STATE), "label": ""},
    "classes": "startEdge",
}

edges = []
add_edge_with_single_self_loop_policy(edges, make_edge(q0, q1, "turn_on"))
add_edge_with_single_self_loop_policy(edges, make_edge(q1, q2, "next"))
add_edge_with_single_self_loop_policy(edges, make_edge(q2, q3, "advance"))
add_edge_with_single_self_loop_policy(edges, make_edge(q3, q0, "reset"))

# ✅ self-loop label is "hold"
add_edge_with_single_self_loop_policy(edges, make_edge(q1, q1, "hold"))

elements = [start_node, *nodes, start_edge, *edges]


# ============================================================
# Stylesheet builders
# ============================================================
def build_stylesheet(node_color, node_font_px, edge_font_px):
    return [
        {
            "selector": "node",
            "style": {
                "label": "data(label)",
                "background-color": node_color,
                "width": 92,
                "height": 92,
                "text-valign": "center",
                "text-halign": "center",
                "font-size": f"{node_font_px}px",
                "color": "black",
                "text-wrap": "wrap",
                "text-max-width": 130,
            },
        },
        {"selector": ".marked", "style": {"border-width": 7, "border-style": "double", "border-color": "black"}},
        {"selector": ".start", "style": {"width": 1, "height": 1, "opacity": 0, "label": ""}},
        {
            "selector": ".startEdge",
            "style": {
                "curve-style": "straight",
                "target-arrow-shape": "triangle",
                "arrow-scale": 1.2,
                "width": 2.5,
                "line-color": "#444",
                "target-arrow-color": "#444",
                "label": "",
            },
        },

        # ✅ EDGE LABELS: always horizontal + pushed UP (above the line)
        {
            "selector": "edge",
            "style": {
                "label": "data(label)",
                "font-size": f"{edge_font_px}px",
                "color": "black",

                # KEY FIX:
                "text-rotation": "none",     # keep horizontal so "above the line" is always up on the screen
                "text-margin-y": -26,        # push label upward (above edge line)
                "text-margin-x": 0,

                # readability
                "text-background-color": "white",
                "text-background-opacity": 1,
                "text-background-padding": "3px",

                "curve-style": "straight",
                "target-arrow-shape": "triangle",
                "arrow-scale": 1.2,
                "width": 2,
                "line-color": "#9a9a9a",
                "target-arrow-color": "#9a9a9a",
            },
        },

        # ✅ SELF LOOP LABEL also horizontal and above the loop
        {
            "selector": "edge.selfLoop",
            "style": {
                "curve-style": "bezier",
                "loop-direction": "0deg",
                "loop-sweep": "40deg",
                "control-point-step-size": 75,
                "width": 2,

                "text-rotation": "none",
                "text-margin-y": -30,
                "text-margin-x": 0,

                "text-background-color": "white",
                "text-background-opacity": 1,
                "text-background-padding": "3px",
            },
        },
    ]

def build_g_stylesheet():
    return [
        {
            "selector": "node",
            "style": {
                "label": "data(label)",
                "width": 70,
                "height": 70,
                "text-valign": "center",
                "text-halign": "center",
                "font-size": "18px",
                "color": "black",
                "background-color": "#dfefff",
            },
        },
        {"selector": ".start", "style": {"width": 1, "height": 1, "opacity": 0, "label": ""}},
        {
            "selector": ".startEdge",
            "style": {
                "curve-style": "straight",
                "target-arrow-shape": "triangle",
                "width": 2,
                "line-color": "#444",
                "target-arrow-color": "#444",
                "label": "",
            },
        },

        # ✅ same fix for tab automata
        {
            "selector": "edge",
            "style": {
                "label": "data(label)",
                "font-size": "16px",
                "color": "black",

                "text-rotation": "none",
                "text-margin-y": -22,
                "text-margin-x": 0,

                "text-background-color": "white",
                "text-background-opacity": 1,
                "text-background-padding": "3px",

                "curve-style": "straight",
                "target-arrow-shape": "triangle",
                "width": 2,
                "line-color": "#888",
                "target-arrow-color": "#888",
            },
        },
        {
            "selector": "edge.selfLoop",
            "style": {
                "curve-style": "bezier",
                "loop-direction": "0deg",
                "loop-sweep": "40deg",
                "control-point-step-size": 65,
                "width": 2,

                "text-rotation": "none",
                "text-margin-y": -26,
                "text-margin-x": 0,

                "text-background-color": "white",
                "text-background-opacity": 1,
                "text-background-padding": "3px",
            },
        },
    ]


# ============================================================
# Tabs UI for G1/G2/G3
# ============================================================
def component_tab_content(info):
    key = info["key"]
    states = info["states"]

    return html.Div(
        [
            html.Div(
                [
                    html.Div(
                        [
                            html.H4(info["name"], style={"marginTop": 0}),
                            html.Div(f"Tuple position: {info['tuple_index'] + 1}"),
                            html.Div(info.get("note", "")),
                            html.H5("States", style={"marginTop": "12px"}),
                            html.Ul([html.Li([html.Code(str(k)), " = ", v]) for k, v in states.items()]),
                        ],
                        style={"flex": "1", "minWidth": "280px"},
                    ),
                    html.Div(
                        [
                            html.H5("Automation diagram", style={"marginTop": 0}),
                            cyto.Cytoscape(
                                id=f"cy_{key}",
                                elements=G_AUTOMATA[key],
                                layout={"name": "preset"},
                                stylesheet=build_g_stylesheet(),
                                style={"width": "520px", "height": "340px", "border": "1px solid #ddd"},
                            ),
                        ],
                        style={"flex": "1", "minWidth": "560px"},
                    ),
                ],
                style={"display": "flex", "gap": "16px", "flexWrap": "wrap"},
            )
        ],
        style={"padding": "12px"},
    )

def component_tabs_panel():
    info_by_key = {c["key"]: c for c in COMPONENT_INFO}

    return html.Div(
        [
            html.H4("Components (Gi)"),
            dcc.Tabs(
                id="g-tabs",
                value="G1",
                children=[
                    dcc.Tab(label="G1", value="G1", children=component_tab_content(info_by_key["G1"])),
                    dcc.Tab(label="G2", value="G2", children=component_tab_content(info_by_key["G2"])),
                    dcc.Tab(label="G3", value="G3", children=component_tab_content(info_by_key["G3"])),
                ],
            ),
        ],
        style={
            "border": "1px solid #ddd",
            "borderRadius": "12px",
            "padding": "12px",
            "marginBottom": "12px",
            "background": "white",
        },
    )


# ============================================================
# Layout
# ============================================================
DEFAULT_NODE_COLOR = "#5dade2"
DEFAULT_NODE_FONT = 18
DEFAULT_EDGE_FONT = 18

app.layout = html.Div(
    [
        html.H3("DES Combined-State (Product) Graph Editor"),
        component_tabs_panel(),

        dcc.Store(id="font-store", data={"node": DEFAULT_NODE_FONT, "edge": DEFAULT_EDGE_FONT}),

        html.Div(
            [
                dcc.Dropdown(
                    id="color",
                    options=[{"label": c, "value": c} for c in ["#5dade2", "#58d68d", "#f5b041", "#e74c3c"]],
                    value=DEFAULT_NODE_COLOR,
                    style={"width": "240px"},
                ),
                html.Button("A-", id="btn-node-font-dec", n_clicks=0, title="Decrease node font"),
                html.Button("A+", id="btn-node-font-inc", n_clicks=0, title="Increase node font"),
                html.Button("e-", id="btn-edge-font-dec", n_clicks=0, title="Decrease edge font"),
                html.Button("e+", id="btn-edge-font-inc", n_clicks=0, title="Increase edge font"),
                html.Span(id="font-readout", style={"marginLeft": "10px"}),
                html.Button("Save JSON", id="btn-save-json", n_clicks=0),
            ],
            style={"display": "flex", "gap": "10px", "alignItems": "center", "flexWrap": "wrap"},
        ),

        dcc.Download(id="download-json"),

        cyto.Cytoscape(
            id="cy",
            elements=elements,
            layout={"name": "preset"},
            stylesheet=build_stylesheet(DEFAULT_NODE_COLOR, DEFAULT_NODE_FONT, DEFAULT_EDGE_FONT),
            style={"width": "100%", "height": "75vh", "border": "1px solid #ddd", "marginTop": "8px"},
        ),
    ],
    style={"padding": "12px"},
)


# ============================================================
# Update font store when +/- buttons are clicked
# ============================================================
@app.callback(
    Output("font-store", "data"),
    Input("btn-node-font-dec", "n_clicks"),
    Input("btn-node-font-inc", "n_clicks"),
    Input("btn-edge-font-dec", "n_clicks"),
    Input("btn-edge-font-inc", "n_clicks"),
    State("font-store", "data"),
)
def update_font_sizes(n_nd, n_ni, n_ed, n_ei, data):
    from dash import callback_context

    if not callback_context.triggered:
        return data

    trig = callback_context.triggered[0]["prop_id"].split(".")[0]
    node_font = int(data.get("node", DEFAULT_NODE_FONT))
    edge_font = int(data.get("edge", DEFAULT_EDGE_FONT))

    def clamp(v, lo=8, hi=48):
        return max(lo, min(hi, v))

    if trig == "btn-node-font-dec":
        node_font = clamp(node_font - 1)
    elif trig == "btn-node-font-inc":
        node_font = clamp(node_font + 1)
    elif trig == "btn-edge-font-dec":
        edge_font = clamp(edge_font - 1)
    elif trig == "btn-edge-font-inc":
        edge_font = clamp(edge_font + 1)

    return {"node": node_font, "edge": edge_font}


# ============================================================
# Update Cytoscape stylesheet when color or fonts change
# ============================================================
@app.callback(
    Output("cy", "stylesheet"),
    Output("font-readout", "children"),
    Input("color", "value"),
    Input("font-store", "data"),
)
def apply_styles(color, font_data):
    node_font = int(font_data.get("node", DEFAULT_NODE_FONT))
    edge_font = int(font_data.get("edge", DEFAULT_EDGE_FONT))
    ss = build_stylesheet(color, node_font, edge_font)
    return ss, f"Node font: {node_font}px | Edge font: {edge_font}px"


# ============================================================
# Save JSON + validate self-loop policy
# ============================================================
@app.callback(
    Output("download-json", "data"),
    Input("btn-save-json", "n_clicks"),
    State("cy", "elements"),
    State("cy", "stylesheet"),
    prevent_initial_call=True,
)
def save_graph_json(n_clicks, current_elements, current_stylesheet):
    n_loops = count_self_loops(current_elements)
    if n_loops > 1:
        raise ValueError(f"Invalid graph: found {n_loops} self-loops. Only 1 is allowed.")

    payload = {
        "elements": current_elements,
        "layout": {"name": "preset"},
        "stylesheet": current_stylesheet,
        "meta": {
            "tuple_format": "(G1_state, G2_state, G3_state)",
            "initial_state": combo_label(INITIAL_STATE),
            "marked_states": [combo_label(s) for s in MARKED_STATES],
            "components": COMPONENT_INFO,
        },
    }
    return dcc.send_string(json.dumps(payload, indent=2), "combined_graph.json")


if __name__ == "__main__":
    app.run(debug=True)