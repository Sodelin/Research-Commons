"""Source-admitted sunlet builder reused from independent necessity control."""
from math import atan2,cos,sin,pi
from inputs.exact_networks import Net,adjacency,edge

def sunlet(n):
    assert n >= 4
    vertices = [f"v{i:03d}" for i in range(n)]
    leaves = [f"x{i:03d}" for i in range(n)]
    coords = {}
    for i in range(n):
        theta = 2*pi*i/n
        coords[vertices[i]] = (cos(theta), sin(theta))
        coords[leaves[i]] = (1.3*cos(theta), 1.3*sin(theta))
    root = "root"
    coords[root] = tuple((x+y)/2 for x, y in zip(coords[vertices[1]], coords[vertices[2]]))
    edges = {edge(vertices[i], vertices[(i+1) % n]) for i in range(n)}
    edges.remove(edge(vertices[1], vertices[2]))
    edges.update((edge(vertices[1], root), edge(root, vertices[2])))
    edges.update(edge(v, x) for v, x in zip(vertices, leaves))
    adj = adjacency(edges)
    rotation = {v: sorted(ns, key=lambda w: atan2(coords[w][1]-coords[v][1], coords[w][0]-coords[v][0])) for v, ns in adj.items()}
    return Net(edges, leaves, {vertices[0]: (vertices[1], vertices[-1])}, root, rotation, f"sunlet-{n}"), leaves

