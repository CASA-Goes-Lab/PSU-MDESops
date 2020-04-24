# pylint: disable=C0103
"""
Function to construct a subautomata with the specified vertices and edges
"""


def subautomaton(
        g,
        h,
        vertices,
        edges
):
    vertex_lookup = {}
    h.add_vertices(len(vertices))
    for index,vert in enumerate(vertices):
        h.vs[index].update_attributes(g.vs[vert].attributes())
        h.vs[index].update_attributes({"orig_vert":vert})
        vertex_lookup[vert] = index

    for edge in enumerate(edges):
        source = g.es[edge].source
        target = g.es[edge].target
        if source in vertices and target in vertices:
            h.add_edge(source, target)
            h.es[-1].update_attributes(g.es[edge].attributes())
            h.es[-1].update_attributes({"orig_edge":edge})



