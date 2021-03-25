from pydash import flatten_deep

def write_tikz(
    fname,
    automata,
    vlabels="name",
    elabels="label",
    vstyles="style",
    default_vstyle="state",
    style_dict=None,
    square_secret=True,
    path_style="->",
    picture_style="initial text=, transform shape, every text node part/.style={align=center}",
    node_dist="2cm",
    scale=1,
    flatten_state_name=False,
    make_figure=True,
    caption="Caption Here",
    label="fig:automata_label"
):
    g = automata.copy()  # to avoid side effects

    if "name" not in g.vs.attributes():
        g.vs["name"] = [i for i in range(0, g.vcount())]
    elif flatten_state_name is True:
        g.vs["name"] = [",".join(flatten_deep(v["name"])) for v in g.vs]

    if isinstance(vlabels, str):
        # Changed instances of labels here to vlabels (changed)
        try:
            vlabels = g._graph.vs.get_attribute_values(vlabels)
            # Added below to write nothing ("") instead of "None"
            vlabels = ["" if vl is None else str2(vl) for vl in vlabels]
        except KeyError:
            vlabels = [x + 1 for x in range(g.vcount())]
    elif vlabels is None:
        vlabels = [""] * g.vcount()

    if isinstance(elabels, str):
        # Created as a slightly modified copy of above vlabels logic  (changed)
        try:
            elabels = g._graph.es.get_attribute_values(elabels)
            # Added below to write nothing ("") instead of "None"
            elabels = ["" if not el else el for el in elabels]
        except KeyError:
            elabels = [x + 1 for x in range(g.ecount())]
    elif elabels is None:
        elabels = [""] * g.ecount()

    if square_secret:
        try:
            vstyles = ['sec state' if secret else 'state' for secret in g.vs.get_attribute_values("secret")]
        except KeyError:
            pass
    if isinstance(vstyles, str):
        try:
            vstyles = g.vs.get_attribute_values(vstyles)
        except KeyError:
            vstyles = [default_vstyle] * g.vcount()

    d_style_dict = default_style_dict()
    if style_dict is None:
        style_dict = {}
    d_style_dict.update(style_dict)
    style_dict = d_style_dict

    with open(fname, 'w') as f:
        if make_figure:
            f.write("\\begin{figure}[]\n")
            f.write("\\centering\n")
            f.write("\n")

        f.write("% Created with DESops: https://gitlab.eecs.umich.edu/M-DES-tools/desops\n")
        begin_tikz = "\\begin{tikzpicture}[" + f"node distance={node_dist}, scale={scale}"
        if picture_style:
            begin_tikz += ", " + picture_style
        begin_tikz += "]\n\n"
        f.write(begin_tikz)

        vstyles_set = set(vstyles)
        for key, value in style_dict.items():
            if key == "state":
                continue
            if key in vstyles_set:
                f.write(f"\\tikzset{{{key}/.style={value}}}\n")
        f.write("\n")

        mod_vstyles = [vstyle + (", initial" if init else "") + (", accepting" if marked else "")
                       for (vstyle, init, marked) in zip(vstyles, g.vs['init'], g.vs['marked'])]
        v_widths = [35, 10, 20]
        for ind, (vlabel, vstyle) in enumerate(zip(vlabels, mod_vstyles)):
            v_cols = [f"\\node[{vstyle}]",
                      f"({ind})",
                      f"[right=of {ind-1}]" if ind > 0 else "[]",
                      f"{{${vlabel}$}};\n"]
            f.writelines([f"{v_col:<{v_width}}" for v_col, v_width in zip(v_cols, v_widths)])
            f.write(v_cols[-1])

        f.write(f"\n\\path[{path_style}]\n")
        e_widths = [10, 25, 25, 25]
        for ind in range(g.vcount()):
            for e_ind, edge in enumerate(g.es.select(_source=ind)):
                self_loop = edge.target == edge.source
                e_cols = [f"({ind})" if e_ind == 0 else "",
                          f"edge []" if not self_loop else f"edge [loop above]",
                          f"node [above]",
                          f"{{${elabels[edge.index]}$}}",
                          f"({edge.target})\n" if not self_loop else f"()\n"]
                f.writelines([f"{e_col:<{e_width}}" for e_col, e_width in zip(e_cols, e_widths)])
                f.write(e_cols[-1])
        f.write(";\n\n")

        f.write("\\end{tikzpicture}\n")

        if make_figure:
            if caption:
                f.write(f"\\caption{{{caption}}}\n")
            if label:
                f.write(f"\\label{{{label}}}\n")
            f.write("\\end{figure}\n")


def str2(label):
    """
    Converts frozenset to set, easier to read
    """
    if isinstance(label, frozenset):
        return str(set(label))
    return str(label)

def default_style_dict():
    """
    The defualt styles
    """
    styles = {"sec state": "draw,rectangle,minimum size=1cm",
              "rect state": "draw,rectangle"}
    return styles
