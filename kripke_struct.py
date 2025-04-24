import json
from pyvis.network import Network
import webbrowser
import os

def visualize_kripke_fixed(json_path, html_out="kripke_graph.html"):
    with open(json_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    nodes = data["nodes"]

    src_ids = set()
    dst_ids = set()
    edges = []

    for node in nodes:
        nid = node["id"]
        for target in node.get("outgoing_edges", []):
            edges.append((nid, target))
            src_ids.add(nid)
            dst_ids.add(target)

    net = Network(height="1000px", width="100%", directed=True, notebook=False, cdn_resources="remote")
    net.force_atlas_2based(gravity=-50, central_gravity=0.005, spring_length=120, spring_strength=0.02)

    for node in nodes:
        nid = node["id"]
        name = node["label"]
        props = node.get("properties", [])
        tooltip_text = f"{name}\n" + "\n".join(props)

        if nid not in dst_ids:
            color = "lightgreen"
        elif nid not in src_ids:
            color = "salmon"
        else:
            color = "lightgrey"

        net.add_node(
            nid,
            label=f"S{nid}",
            title=tooltip_text,
            color=color,
            shape="circle",
            size=30,
            font={"size": 22, "color": "#000000"}
        )

    for src, dst in edges:
        net.add_edge(src, dst)

    net.set_options("""
    var options = {
      "nodes": {
        "scaling": {"min": 30, "max": 30},
        "font": {"size": 22, "face": "arial"}
      },
      "edges": {
        "arrows": {"to": {"enabled": true}},
        "smooth": false
      },
      "physics": {
        "forceAtlas2Based": {
          "gravitationalConstant": -50,
          "centralGravity": 0.005,
          "springLength": 120,
          "springConstant": 0.02
        },
        "minVelocity": 0.75,
        "solver": "forceAtlas2Based"
      }
    }
    """)

    net.save_graph(html_out)
    webbrowser.open("file://" + os.path.abspath(html_out))