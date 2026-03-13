import json
from dash import Dash, html, dcc, Input, Output, State
import dash_cytoscape as cyto

app = Dash(__name__)

# ============================================================
# Small helpers
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


# ============================================================
# Dining Philosophers (Example 2.20 / Fig 2.19 and 2.20)
# Event meaning:
#   i f j  = philosopher i picks up fork j
#   i f    = philosopher i puts both forks down (returns to thinking)
# ============================================================
META = {
    "event_meaning": {
        "ifj": "Philosopher i picks up fork j (j ∈ {1,2})",
        "if": "Philosopher i puts both forks down (returns to thinking)",
    },
    "components": {
        "P1": {
            "name": "P1 (Philosopher 1)",
            "states": {
                "1T": "thinking",
                "1I1": "holding fork 1",
                "1I2": "holding fork 2",
                "1E": "eating",
            },
            "events": ["1f1", "1f2", "1f"],
            "initial": "1T",
            "marked": ["1T"],  # matches the double-circle in Fig 2.19
        },
        "P2": {
            "name": "P2 (Philosopher 2)",
            "states": {
                "2T": "thinking",
                "2I1": "holding fork 1",
                "2I2": "holding fork 2",
                "2E": "eating",
            },
            "events": ["2f1", "2f2", "2f"],
            "initial": "2T",
            "marked": ["2T"],
        },
        "F1": {
            "name": "F1 (Fork 1 resource)",
            "states": {"1A": "available", "1U": "in use"},
            "events": ["1f1", "2f1", "1f", "2f"],
            "initial": "1A",
            "marked": ["1A"],
        },
        "F2": {
            "name": "F2 (Fork 2 resource)",
            "states": {"2A": "available", "2U": "in use"},
            "events": ["1f2", "2f2", "1f", "2f"],
            "initial": "2A",
            "marked": ["2A"],
        },
        "PF": {
            "name": "PF = P1 || P2 || F1 || F2 (parallel composition)",
            "notes": [
                "Only a subset of product states are reachable due to synchronization on shared events.",
                "PF contains deadlock states (each philosopher holds one fork and waits for the other).",
            ],
        },
    },
}

# ============================================================
# Automata definitions (with preset positions)
# ============================================================

# ---- P1 (Fig 2.19) ----
P1_nodes = [
    node_el("1T", "1T", 180, 220, classes="marked"),
    node_el("1I1", "1I1", 360, 140),
    node_el("1I2", "1I2", 360, 320),
    node_el("1E", "1E", 540, 220),
]
P1_edges = [
    edge_el("1T", "1I1", "1f1"),
    edge_el("1I1", "1E", "1f2"),
    edge_el("1T", "1I2", "1f2"),
    edge_el("1I2", "1E", "1f1"),
    edge_el("1E", "1T", "1f"),
]
P1_start, P1_start_edge = start_marker("__p1_start__", "__p1_start_edge__", "1T", 90, 220)
P1_elements = [P1_start, *P1_nodes, P1_start_edge, *P1_edges]

# ---- P2 (Fig 2.19) ----
P2_nodes = [
    node_el("2T", "2T", 180, 220, classes="marked"),
    node_el("2I1", "2I1", 360, 140),
    node_el("2I2", "2I2", 360, 320),
    node_el("2E", "2E", 540, 220),
]
P2_edges = [
    edge_el("2T", "2I1", "2f1"),
    edge_el("2I1", "2E", "2f2"),
    edge_el("2T", "2I2", "2f2"),
    edge_el("2I2", "2E", "2f1"),
    edge_el("2E", "2T", "2f"),
]
P2_start, P2_start_edge = start_marker("__p2_start__", "__p2_start_edge__", "2T", 90, 220)
P2_elements = [P2_start, *P2_nodes, P2_start_edge, *P2_edges]

# ---- F1 (Fig 2.19) ----
F1_nodes = [
    node_el("1A", "1A", 220, 220, classes="marked"),
    node_el("1U", "1U", 480, 220),
]
F1_edges = [
    edge_el("1A", "1U", "1f1, 2f1"),
    edge_el("1U", "1A", "1f, 2f"),
]
F1_start, F1_start_edge = start_marker("__f1_start__", "__f1_start_edge__", "1A", 130, 220)
F1_elements = [F1_start, *F1_nodes, F1_start_edge, *F1_edges]

# ---- F2 (Fig 2.19) ----
F2_nodes = [
    node_el("2A", "2A", 220, 220, classes="marked"),
    node_el("2U", "2U", 480, 220),
]
F2_edges = [
    edge_el("2A", "2U", "1f2, 2f2"),
    edge_el("2U", "2A", "1f, 2f"),
]
F2_start, F2_start_edge = start_marker("__f2_start__", "__f2_start_edge__", "2A", 130, 220)
F2_elements = [F2_start, *F2_nodes, F2_start_edge, *F2_edges]

# ---- PF (Fig 2.20) ----
# We encode the 9-state reachable graph shown, using readable tuple labels.
# State labels shown in your figure:
#   s0 = (1T,2T,1A,2A) initial
#   sE = (1E,2T,1U,2U)
#   sD1 = (1I2,2I1,1U,2U)
#   sD2 = (1I1,2I2,1U,2U)
# plus intermediate ones consistent with the drawing.

PF_nodes = [
    node_el("s0", "(1T,2T,1A,2A)", 180, 140, classes="marked"),
    node_el("s1", "(1I1,2T,1U,2A)", 360, 140),
    node_el("s2", "(1I2,2T,1A,2U)", 360, 20),

    node_el("s3", "(1E,2T,1U,2U)", 560, 80),
    node_el("s4", "(1I1,2I2,1U,2U)", 560, 200),

    node_el("s5", "(1T,2I1,1U,2A)", 180, 260),
    node_el("s6", "(1T,2I2,1A,2U)", 180, 380),

    node_el("s7", "(1I2,2I1,1U,2U)", 560, 320),
    node_el("s8", "(1T,2E,1U,2U)", 360, 470),
]

PF_edges = [
    # From initial
    edge_el("s0", "s1", "1f1"),
    edge_el("s0", "s2", "1f2"),
    edge_el("s0", "s5", "2f1"),
    edge_el("s0", "s6", "2f2"),

    # Top path: P1 gets both forks => eating
    edge_el("s1", "s3", "1f2"),
    edge_el("s2", "s3", "1f1"),

    # Release from eating back to initial
    edge_el("s3", "s0", "1f"),

    # Deadlock states (each holds one fork)
    edge_el("s1", "s4", "2f2"),
    edge_el("s6", "s4", "1f1"),

    edge_el("s2", "s7", "2f1"),
    edge_el("s5", "s7", "1f2"),

    # P2 gets both forks => eating (bottom)
    edge_el("s5", "s8", "2f2"),
    edge_el("s6", "s8", "2f1"),

    # Release from P2 eating back to initial
    edge_el("s8", "s0", "2f"),
]

PF_start, PF_start_edge = start_marker("__pf_start__", "__pf_start_edge__", "s0", 90, 140)
PF_elements = [PF_start, *PF_nodes, PF_start_edge, *PF_edges]

AUTOMATA = {
    "P1": P1_elements,
    "P2": P2_elements,
    "F1": F1_elements,
    "F2": F2_elements,
    "PF": PF_elements,
}


# ============================================================
# Stylesheet builder (keeps your “labels above line” rule)
# ============================================================
def build_stylesheet(node_color, node_font_px, edge_font_px):
    return [
        {
            "selector": "node",
            "style": {
                "label": "data(label)",
                "background-color": node_color,
                "width": 84,
                "height": 84,
                "text-valign": "center",
                "text-halign": "center",
                "font-size": f"{node_font_px}px",
                "color": "black",
                "text-wrap": "wrap",
                "text-max-width": 170,
            },
        },
        # Marked states (double circle)
        {
            "selector": ".marked",
            "style": {
                "border-width": 7,
                "border-style": "double",
                "border-color": "black",
            },
        },
        # Hide start node
        {"selector": ".start", "style": {"width": 1, "height": 1, "opacity": 0, "label": ""}},
        # Start arrow
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
        # Edges: labels ALWAYS above the line
        {
            "selector": "edge",
            "style": {
                "label": "data(label)",
                "font-size": f"{edge_font_px}px",
                "color": "black",
                "text-rotation": "none",   # <--- keep horizontal
                "text-margin-y": -28,      # <--- push above the line
                "text-margin-x": 0,
                "text-background-color": "white",
                "text-background-opacity": 1,
                "text-background-padding": "3px",
                "curve-style": "straight",
                "target-arrow-shape": "triangle",
                "arrow-scale": 1.2,
                "width": 2,
                "line-color": "#888",
                "target-arrow-color": "#888",
            },
        },
    ]


# ============================================================
# Component info panel (changes with tab)
# ============================================================
def info_panel(component_key):
    c = META["components"][component_key]
    items = []

    if component_key in ["P1", "P2", "F1", "F2"]:
        items.append(html.H4(c["name"], style={"marginTop": 0}))
        items.append(html.Div([html.B("Initial state: "), html.Code(c["initial"])]))
        items.append(html.Div([html.B("Marked state(s): "), ", ".join(c.get("marked", []))]))
        items.append(html.Div([html.B("Events: "), ", ".join(c.get("events", []))]))
        items.append(html.H5("States", style={"marginTop": "10px"}))
        items.append(
            html.Ul([html.Li([html.Code(k), " = ", v]) for k, v in c["states"].items()])
        )
        items.append(
            html.Div(
                [
                    html.B("Event meaning: "),
                    html.Code("ifj"),
                    " = philosopher i picks up fork j; ",
                    html.Code("if"),
                    " = philosopher i puts both forks down.",
                ],
                style={"marginTop": "8px"},
            )
        )
    else:
        items.append(html.H4(c["name"], style={"marginTop": 0}))
        if "notes" in c:
            items.append(html.Ul([html.Li(n) for n in c["notes"]]))
        items.append(
            html.Div(
                [
                    html.B("Event meaning: "),
                    html.Code("ifj"),
                    " = philosopher i picks up fork j; ",
                    html.Code("if"),
                    " = philosopher i puts both forks down.",
                ],
                style={"marginTop": "8px"},
            )
        )

    return html.Div(items, style={"minWidth": "320px"})


# ============================================================
# Layout
# ============================================================
DEFAULT_NODE_COLOR = "#5dade2"
DEFAULT_NODE_FONT = 18
DEFAULT_EDGE_FONT = 16

app.layout = html.Div(
    [
        html.H3("Dining Philosophers (2 philosophers, 2 forks) — Automata Viewer"),

        dcc.Store(id="font-store", data={"node": DEFAULT_NODE_FONT, "edge": DEFAULT_EDGE_FONT}),

        html.Div(
            [
                html.H4("Automata Tabs", style={"marginBottom": "6px"}),
                dcc.Tabs(
                    id="auto-tabs",
                    value="P1",
                    children=[
                        dcc.Tab(label="P1", value="P1"),
                        dcc.Tab(label="P2", value="P2"),
                        dcc.Tab(label="F1", value="F1"),
                        dcc.Tab(label="F2", value="F2"),
                        dcc.Tab(label="PF (composition)", value="PF"),
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
        ),

        html.Div(
            [
                # Left: info
                html.Div(id="component-info", style={"flex": "1"}),

                # Right: graph
                html.Div(
                    [
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
                            elements=AUTOMATA["P1"],
                            layout={"name": "preset"},
                            stylesheet=build_stylesheet(DEFAULT_NODE_COLOR, DEFAULT_NODE_FONT, DEFAULT_EDGE_FONT),
                            style={"width": "980px", "height": "560px", "border": "1px solid #ddd", "marginTop": "10px"},
                        ),
                    ],
                    style={"flex": "2"},
                ),
            ],
            style={"display": "flex", "gap": "16px", "flexWrap": "wrap"},
        ),
    ],
    style={"padding": "12px"},
)


# ============================================================
# Update info panel + graph when tab changes
# ============================================================
@app.callback(
    Output("component-info", "children"),
    Output("cy", "elements"),
    Input("auto-tabs", "value"),
)
def update_tab(tab_key):
    return info_panel(tab_key), AUTOMATA[tab_key]


# ============================================================
# Font store update
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
# Apply stylesheet (color + fonts)
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
# Save JSON for current tab (includes positions + meta)
# ============================================================
@app.callback(
    Output("download-json", "data"),
    Input("btn-save-json", "n_clicks"),
    State("auto-tabs", "value"),
    State("cy", "elements"),
    State("cy", "stylesheet"),
    prevent_initial_call=True,
)
def save_graph_json(n_clicks, tab_key, current_elements, current_stylesheet):
    payload = {
        "automaton": tab_key,
        "elements": current_elements,
        "layout": {"name": "preset"},
        "stylesheet": current_stylesheet,
        "meta": META["components"].get(tab_key, {}),
        "global_meta": {"event_meaning": META["event_meaning"]},
    }
    filename = f"dining_philosophers_{tab_key}.json"
    return dcc.send_string(json.dumps(payload, indent=2), filename)


if __name__ == "__main__":
    app.run(debug=True)