import json
from dash import Dash, html, dcc, Input, Output, State
import dash_cytoscape as cyto

app = Dash(__name__)

# ============================================================
# Helpers: "combined state" node ids + labels
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
    data = {"source": combo_id(src_tuple), "target": combo_id(dst_tuple), "label": event_label}
    if edge_id is not None:
        data["id"] = edge_id
    el = {"data": data}
    if classes:
        el["classes"] = classes
    return el


# ============================================================
# Define what each tuple entry means (for readers)
# ============================================================
# This is only documentation shown in the UI (not used by Cytoscape).
COMPONENT_INFO = [
    {
        "name": "G1 (Valve mode)",
        "tuple_index": 0,
        "states": {
            "A": "Valve state A",
            "B": "Valve state B",
            "C": "Valve state C",
        },
        "note": "First entry in the tuple."
    },
    {
        "name": "G2 (Controller step)",
        "tuple_index": 1,
        "states": {
            1: "Controller state 1",
            2: "Controller state 2",
            3: "Controller state 3",
        },
        "note": "Second entry in the tuple."
    },
    {
        "name": "G3 (Heater)",
        "tuple_index": 2,
        "states": {
            "off": "Heater OFF",
            "on": "Heater ON",
        },
        "note": "Third entry in the tuple."
    },
]

# ============================================================
# Choose initial + marked combined states
# ============================================================
INITIAL_STATE = ("A", 1, "off")          # initial combined state
MARKED_STATES = {("A", 1, "on")}         # example marked combined states

# Start-arrow (visual marker only)
START_NODE_ID = "__start__"
START_EDGE_ID = "__start_edge__"


# ============================================================
# Example combined-state graph (edit as needed)
# ============================================================
q0 = ("A", 1, "off")   # initial
q1 = ("A", 1, "on")    # marked
q2 = ("B", 2, "on")
q3 = ("C", 3, "on")

nodes = [
    make_combo_node(q0, x=250, y=250, classes="marked" if q0 in MARKED_STATES else ""),
    make_combo_node(q1, x=600, y=250, classes="marked" if q1 in MARKED_STATES else ""),
    make_combo_node(q2, x=600, y=450, classes="marked" if q2 in MARKED_STATES else ""),
    make_combo_node(q3, x=250, y=450, classes="marked" if q3 in MARKED_STATES else ""),
]

# Start marker (hidden node + arrow to initial)
start_node = {"data": {"id": START_NODE_ID}, "position": {"x": 150, "y": 250}, "classes": "start"}
start_edge = {
    "data": {"id": START_EDGE_ID, "source": START_NODE_ID, "target": combo_id(INITIAL_STATE), "label": ""},
    "classes": "startEdge",
}

edges = [
    make_edge(q0, q1, "turn_on"),
    make_edge(q1, q2, "next"),
    make_edge(q2, q3, "advance"),
    make_edge(q3, q0, "reset"),
]

elements = [start_node, *nodes, start_edge, *edges]


# ============================================================
# Styles
# ============================================================
stylesheet = [
    {
        "selector": "node",
        "style": {
            "label": "data(label)",
            "width": 92,
            "height": 92,
            "text-valign": "center",
            "text-halign": "center",
            "font-size": "18px",
            "color": "black",
            "text-wrap": "wrap",
            "text-max-width": 130,
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
    {
        "selector": ".start",
        "style": {"width": 1, "height": 1, "opacity": 0, "label": ""},
    },
    # Start arrow style
    {
        "selector": ".startEdge",
        "style": {
            "curve-style": "bezier",
            "target-arrow-shape": "triangle",
            "arrow-scale": 1.2,
            "width": 2.5,
            "line-color": "#444",
            "target-arrow-color": "#444",
            "label": "",
        },
    },
    # Normal edges
    {
        "selector": "edge",
        "style": {
            "label": "data(label)",
            "font-size": "18px",
            "color": "black",
            "text-rotation": "autorotate",
            "text-margin-y": -12,
            "text-margin-x": 10,
            "text-background-opacity": 0,
            "curve-style": "bezier",
            "target-arrow-shape": "triangle",
            "arrow-scale": 1.2,
            "width": 2,
        },
    },
]


# ============================================================
# UI: legend panel explaining tuple meaning
# ============================================================
def legend_panel():
    return html.Div(
        [
            html.H4("Legend: How to read each combined-state node"),
            html.Div(
                [
                    html.Div(
                        [
                            html.Div(
                                [
                                    html.B("Combined state format: "),
                                    html.Span("(G1_state, G2_state, G3_state)"),
                                ]
                            ),
                            html.Div(
                                [
                                    html.B("Initial state: "),
                                    html.Span(f"{combo_label(INITIAL_STATE)} (start arrow points to it)"),
                                ]
                            ),
                            html.Div(
                                [
                                    html.B("Marked state(s): "),
                                    html.Span(", ".join(combo_label(s) for s in MARKED_STATES) or "None"),
                                    html.Span(" (double circle)"),
                                ]
                            ),
                        ],
                        style={"marginBottom": "10px"},
                    ),
                    html.Div(
                        [
                            html.Div(
                                [
                                    html.B(info["name"]),
                                    html.Span(f" — tuple position {info['tuple_index'] + 1}. "),
                                    html.Span(info.get("note", "")),
                                    html.Ul(
                                        [
                                            html.Li([html.Code(str(k)), " = ", v])
                                            for k, v in info["states"].items()
                                        ],
                                        style={"marginTop": "6px"},
                                    ),
                                ],
                                style={
                                    "flex": "1",
                                    "minWidth": "240px",
                                    "border": "1px solid #e5e5e5",
                                    "borderRadius": "10px",
                                    "padding": "12px",
                                    "background": "#fafafa",
                                },
                            )
                            for info in COMPONENT_INFO
                        ],
                        style={"display": "flex", "gap": "10px", "flexWrap": "wrap"},
                    ),
                ]
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
app.layout = html.Div(
    [
        html.H3("DES Combined-State (Product) Graph Editor"),
        legend_panel(),
        html.Div(
            [
                dcc.Dropdown(
                    id="color",
                    options=[{"label": c, "value": c} for c in ["#5dade2", "#58d68d", "#f5b041", "#e74c3c"]],
                    value="#5dade2",
                    style={"width": "240px"},
                ),
                html.Button("Save JSON", id="btn-save-json", n_clicks=0),
            ],
            style={"display": "flex", "gap": "12px", "alignItems": "center"},
        ),
        dcc.Download(id="download-json"),
        cyto.Cytoscape(
            id="cy",
            elements=elements,
            layout={"name": "preset"},
            stylesheet=stylesheet,
            style={"width": "100%", "height": "75vh", "border": "1px solid #ddd"},
        ),
    ],
    style={"padding": "12px"},
)


# ============================================================
# Recolor nodes
# ============================================================
@app.callback(
    Output("cy", "stylesheet"),
    Input("color", "value"),
    State("cy", "stylesheet"),
)
def recolor_nodes(color, current_stylesheet):
    ss = [s for s in current_stylesheet if s.get("selector") != "node"]
    ss.insert(
        0,
        {
            "selector": "node",
            "style": {
                "label": "data(label)",
                "background-color": color,
                "width": 92,
                "height": 92,
                "text-valign": "center",
                "text-halign": "center",
                "font-size": "18px",
                "color": "black",
                "text-wrap": "wrap",
                "text-max-width": 130,
            },
        },
    )
    return ss


# ============================================================
# Save JSON (includes positions)
# ============================================================
@app.callback(
    Output("download-json", "data"),
    Input("btn-save-json", "n_clicks"),
    State("cy", "elements"),
    prevent_initial_call=True,
)
def save_graph_json(n_clicks, current_elements):
    payload = {
        "elements": current_elements,
        "layout": {"name": "preset"},
        "stylesheet": stylesheet,
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