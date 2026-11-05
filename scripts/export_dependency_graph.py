#!/usr/bin/env python3
"""Export Blueprint's Full Graph as a static SVG for the README (requires dot)."""
from pathlib import Path
import json
import shutil
import subprocess
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'blueprint'
OUTPUT = ROOT / 'docs/assets/dependency-graph.svg'
SVG = 'http://www.w3.org/2000/svg'
XLINK = 'http://www.w3.org/1999/xlink'


def main():
    dot = shutil.which('dot')
    if dot is None:
        raise SystemExit('Install Graphviz to provide the dot executable, then rerun this script.')
    manifest_path = SITE / '-verso-data/blueprint-manifest.json'
    if not manifest_path.is_file():
        raise SystemExit('Generate the local site first: run lake exe vbp build, then '
                         'python3 scripts/export_blueprint.py.')
    manifest = json.loads(manifest_path.read_text())
    full_graphs = [(graph, variant) for graph in manifest['graphs']
                   for variant in graph['variants'] if variant['key'] == 'full']
    if len(full_graphs) != 1:
        raise SystemExit('Expected exactly one Full Graph in the Blueprint manifest.')
    graph, variant = full_graphs[0]

    # Global ranking keeps the four groups compact without changing nodes,
    # dependencies, labels, shapes, or status colors from Blueprint's Full Graph.
    result = subprocess.run([dot, '-Tsvg', '-Gnewrank=true'], input=variant['dot'],
                            text=True, capture_output=True, check=True)
    ET.register_namespace('', SVG)
    ET.register_namespace('xlink', XLINK)
    svg = ET.fromstring(result.stdout)

    # Keep the committed image independent of the untracked HTML site.
    # Preserve status tooltips, but omit links to locally generated pages.
    for link in svg.iter(f'{{{SVG}}}a'):
        tooltip = link.get(f'{{{XLINK}}}title')
        link.tag = f'{{{SVG}}}g'
        link.attrib.clear()
        if tooltip:
            title = ET.Element(f'{{{SVG}}}title')
            title.text = tooltip
            link.insert(0, title)

    svg.set('role', 'img')
    svg.set('aria-labelledby', 'graph-title graph-description')
    title = ET.Element(f'{{{SVG}}}title', id='graph-title')
    title.text = 'Full Blueprint dependency graph'
    description = ET.Element(f'{{{SVG}}}desc', id='graph-description')
    description.text = (
        f"All {len(graph['nodes'])} nodes and {len(graph['edges'])} recorded dependencies "
        'from the Blueprint Full Graph. Arrows point from dependencies to their users. '
        'Shapes, borders, and fills retain Blueprint declaration kinds and proof status. '
        'Explicit classical premises require separate review.'
    )
    svg.insert(0, title)
    svg.insert(1, description)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    ET.ElementTree(svg).write(OUTPUT, encoding='utf-8', xml_declaration=True)
    print(f"Exported {len(graph['nodes'])} nodes and {len(graph['edges'])} dependencies "
          f'to {OUTPUT.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
