#MDESops Research
#Souvik Kar
#FSM Interactive Visualization Tool
#This script reads a .fsm automaton file and builds an interactive graph
#The graph is exported to an HTML file and opened automatically

from __future__ import annotations
import argparse
import sys
from pathlib import Path
import webbrowser

#we need the repository root so python can find DESops correctly
REPO_ROOT = Path(__file__).resolve().parents[2]

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import plotly.graph_objects as go

#DESops is the library used for discrete event system automata
try:
    import DESops as d
except ImportError:
    print("DESops could not be imported.")
    print("Run this script from the PSU-MDESops root directory.")
    print("Alternatively install locally with: pip install -e .")
    sys.exit(1)


#helper function because DESops events sometimes have name() methods
#so we try that first before converting directly to string
def convertEventLabel(e):
    if hasattr(e, "name"):
        return str(e.name())
    return str(e)


#load the FSM automaton from disk
def loadFSM(filePath):

    filePath = Path(filePath)

    #quick check so we don't crash later
    if not filePath.exists():
        raise FileNotFoundError("FSM file not found: " + str(filePath))

    #DESops provides the parser for .fsm format
    automaton = d.read_fsm(str(filePath))

    return automaton


#compute a layout for the graph
#DESops internally wraps igraph so we reuse igraph layouts
def computeGraphLayout(g, layoutChoice="kk"):

    #grab igraph object if wrapped
    ig = g._graph if hasattr(g, "_graph") else g

    try:

        #tree layout is useful for hierarchical FSMs
        if layoutChoice == "tree":
            layout = ig.layout_reingold_tilford(mode="in", root=[0])

        #circular layout sometimes looks nice for small automata
        elif layoutChoice == "circle":
            layout = ig.layout_circle()

        #grid layout for debugging
        elif layoutChoice == "grid":
            layout = ig.layout_grid()

        else:
            #kamada-kawai tends to give good results
            layout = ig.layout_kk()

    except Exception:
        #fallback if something fails
        layout = ig.layout_auto()

    coords = []

    #convert igraph layout into simple (x,y)
    for p in layout:
        coords.append((float(p[0]), float(p[1])))

    return coords


#this builds the interactive plotly graph
#nodes are states, edges are events
def buildFSMPlot(g, layoutCoords, titleText, initialStateIndex=0):

    #state names stored inside the vertex attributes
    stateNames = g.vs["name"]

    #marked states (if attribute exists)
    if "marked" in g.vs.attributes():
        markedStates = g.vs["marked"]
    else:
        markedStates = [False] * g.vcount()

    #check if edge attributes exist
    hasObs = "obs" in g.es.attributes()
    hasContr = "contr" in g.es.attributes()

    #event labels for edges
    eventLabels = [convertEventLabel(l) for l in g.es["label"]]

    #separate coordinates
    xs = [p[0] for p in layoutCoords]
    ys = [p[1] for p in layoutCoords]

    #--------------------------------------------------
    #Step 1: assign node colors and borders
    #--------------------------------------------------

    nodeColors = []
    nodeBorderWidths = []
    nodeBorderColors = []

    for i in range(g.vcount()):

        #initial state
        if i == initialStateIndex:
            nodeColors.append("rgba(100,149,237,0.85)")
            nodeBorderWidths.append(3)
            nodeBorderColors.append("rgb(65,105,225)")

        #marked states
        elif markedStates[i]:
            nodeColors.append("rgba(144,238,144,0.9)")
            nodeBorderWidths.append(2)
            nodeBorderColors.append("rgb(34,139,34)")

        #normal reachable state
        else:
            nodeColors.append("rgba(255,250,250,0.95)")
            nodeBorderWidths.append(1)
            nodeBorderColors.append("rgb(128,128,128)")


    nodeLabels = [str(n) for n in stateNames]

    #hover text so when user moves mouse over node
    hoverInfo = []

    for i in range(g.vcount()):

        role = []

        if i == initialStateIndex:
            role.append("initial")

        if markedStates[i]:
            role.append("marked")

        if role:
            roleText = "<br>".join(role)
        else:
            roleText = "reachable"

        hoverInfo.append("State: " + str(stateNames[i]) + "<br>" + roleText)


    #--------------------------------------------------
    #Step 2: group edges by event type
    #--------------------------------------------------

    edgeTraces = []

    #mapping system for observability / controllability
    edgeTypeMap = {

        (True, True): ("Controllable, Observable", "black", "solid"),

        (True, False): ("Uncontrollable, Observable", "rgb(200,80,80)", "solid"),

        (False, True): ("Controllable, Unobservable", "rgb(80,80,200)", "dash"),

        (False, False): ("Uncontrollable, Unobservable", "rgb(180,100,180)", "dash"),
    }

    for (obs, contr), (labelText, color, dashStyle) in edgeTypeMap.items():

        ex = []
        ey = []
        hover = []

        for e in g.es:

            o = e["obs"] if hasObs else True
            c = e["contr"] if hasContr else True

            if (o, c) != (obs, contr):
                continue

            s = e.source
            t = e.target

            ex.extend([xs[s], xs[t], None])
            ey.extend([ys[s], ys[t], None])

            eventLabel = eventLabels[e.index]

            hover.append(stateNames[s] + " → " + stateNames[t] + " : " + eventLabel)

        if not ex:
            continue

        edgeTraces.append(

            go.Scatter(
                x=ex,
                y=ey,
                mode="lines",
                line=dict(color=color, width=2, dash=dashStyle),
                hoverinfo="text",
                hovertext=hover,
                name=labelText,
            )
        )


    #--------------------------------------------------
    #Step 3: create node trace
    #--------------------------------------------------

    nodeTrace = go.Scatter(

        x=xs,
        y=ys,

        mode="markers+text",

        text=nodeLabels,
        textposition="middle center",

        marker=dict(
            size=32,
            color=nodeColors,
            line=dict(width=nodeBorderWidths, color=nodeBorderColors)
        ),

        hoverinfo="text",
        hovertext=hoverInfo,
        name="States"
    )

    #--------------------------------------------------
    #Step 4: build final figure
    #--------------------------------------------------

    fig = go.Figure()

    for tr in edgeTraces:
        fig.add_trace(tr)

    fig.add_trace(nodeTrace)

    fig.update_layout(

        title=titleText,

        showlegend=True,

        xaxis=dict(visible=False),
        yaxis=dict(visible=False),

        plot_bgcolor="rgba(248,248,255,0.5)",
        paper_bgcolor="white",

        hovermode="closest",
    )

    fig.update_yaxes(scaleanchor="x", scaleratio=1)

    return fig


#--------------------------------------------------
#Main driver code
#--------------------------------------------------

def main():

    parser = argparse.ArgumentParser(
        description="Visualize DES automata (.fsm) as interactive graphs"
    )

    parser.add_argument("fsm", help="Path to FSM file")

    parser.add_argument(
        "--layout",
        choices=["kk", "tree", "circle", "grid"],
        default="kk",
        help="Layout algorithm"
    )

    args = parser.parse_args()

    fsmFile = Path(args.fsm)

    if not fsmFile.exists():
        print("FSM file not found.")
        return

    #load automaton
    automaton = loadFSM(fsmFile)

    #compute layout
    layout = computeGraphLayout(automaton, args.layout)

    title = fsmFile.stem + " (DES automaton)"

    #build visualization
    fig = buildFSMPlot(automaton, layout, title)

    #output html
    outputFile = Path.cwd() / (fsmFile.stem + "_viz.html")

    fig.write_html(str(outputFile))

    print("Visualization saved to:")
    print(outputFile)

    #automatically open in browser
    webbrowser.open(outputFile.resolve().as_uri())


if __name__ == "__main__":
    main()