import json

notebook = {
    'cells': [],
    'metadata': {
        'language_info': {'name': 'python'},
        'kernel_spec': {'display_name': 'Python 3', 'language': 'python', 'name': 'python3'}
    },
    'nbformat': 4,
    'nbformat_minor': 4
}

def add_md(text):
    notebook['cells'].append({
        'cell_type': 'markdown',
        'metadata': {},
        'source': [line + '\n' for line in text.split('\n')]
    })

def add_code(code):
    notebook['cells'].append({
        'cell_type': 'code',
        'execution_count': None,
        'metadata': {},
        'outputs': [],
        'source': [line + '\n' for line in code.split('\n')]
    })

# Title
add_md('''# Riemann Hypothesis Formalization Knowledge Graph Explorer
### Digital Humanities Perspective & Historical $H_1 \\to H_{15}$ Lineage (1859–2026)

This notebook provides an interactive exploration of `unified-complete-knowledge-graph.jsonld` (21,942 nodes, 15,338 semantic relations, 460 DOI papers, 384 mathematicians, 303 DH themes, 8,529 Lean build jobs).

In particular, it analyzes:
1. **Digital Humanities Themes & Proof Routes**
2. **Historical Lineage of $H_1 \\to H_{15}$ Mathematics**
3. **Intellectual & Spatial Networks of Mathematicians & AI Parliament**
4. **BBLS Frontier Literature Landscape & Data Visualizations**
''')

# Cell 1: Environment Setup & Data Loading
add_code('''import json
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from collections import Counter, defaultdict
import networkx as nx
from pathlib import Path
from IPython.display import Image, display
import warnings
warnings.filterwarnings('ignore')

GRAPH_FILE = Path('unified-complete-knowledge-graph.jsonld')
if not GRAPH_FILE.exists():
    GRAPH_FILE = Path('data/unified-complete-knowledge-graph.jsonld')

CSV_FILE = Path('lean_files_theorems_map.csv')
if not CSV_FILE.exists():
    CSV_FILE = Path('data/lean_files_theorems_map.csv')

DATAVIZ_DIR = Path('dataviz')
if not DATAVIZ_DIR.exists():
    DATAVIZ_DIR = Path('data/dataviz')
DATAVIZ_DIR.mkdir(parents=True, exist_ok=True)

sns.set_style('whitegrid')
plt.rcParams['figure.figsize'] = (14, 8)
plt.rcParams['font.size'] = 11

print("Loading unified knowledge graph...")
with open(GRAPH_FILE) as f:
    graph = json.load(f)

lean_files = pd.read_csv(CSV_FILE) if CSV_FILE.exists() else pd.DataFrame()
print(f"✓ Loaded Knowledge Graph: {len(graph['nodes']):,} nodes, {len(graph.get('relations', [])):,} relations")
print(f"✓ Loaded Lean Formalization Map: {len(lean_files)} files")
''')

# Cell 2: Graph Summary Statistics
add_md('## 1. Knowledge Graph Summary Statistics')
add_code('''stats = graph.get('statistics', {})
metadata = graph.get('metadata', {})

print("=" * 60)
print(f"Title: {metadata.get('title')}")
print(f"Version: {metadata.get('version')} | Last Updated: {metadata.get('last_updated')}")
print("=" * 60)
print(f"Total Nodes: {len(graph['nodes']):,}")
print(f"Total Relations: {len(graph.get('relations', [])):,}")
print(f"Total Papers: {stats.get('total_papers', 460):,}")
print(f"Total Persons: {stats.get('total_persons', 384):,}")
print(f"Total DH Themes: {stats.get('total_themes', 303):,}")
print(f"Lean Build Jobs: {metadata.get('lean_build_jobs', 8529):,}")
print(f"Custom Axioms in Umbrella: {metadata.get('lean_custom_axioms', 0)}")
print("=" * 60)

# Display summary plot
display(Image(filename=str(DATAVIZ_DIR / '05_integration_summary.png')))
''')

# Cell 3: Proof Route Categories
add_md('## 2. Proof Route Categories & Mathematical Areas')
add_code('''if len(lean_files) > 0 and 'Route_Category' in lean_files.columns:
    display(Image(filename=str(DATAVIZ_DIR / '01_lean_route_categories.png')))
    display(Image(filename=str(DATAVIZ_DIR / '02_lean_mathematical_areas.png')))
''')

# Cell 4: AI Parliament vs Literature Base
add_md('## 3. AI Parliament vs Literature-Grounded Formal Modules')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '03_llm_vs_literature.png')))
''')

# Cell 5: Network Graph of Lean Routes
add_md('## 4. Bipartite Network Graph: Proof Routes → Mathematical Domains')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '04_lean_network_graph.png')))
''')

# Cell 6: Session Contributions
add_md('## 5. Formalization Progress Across Sessions 1–9c')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '06_session_contributions.png')))
''')

# Cell 7: Historical Timeline H1-H15
add_md('## 6. Historical & Conceptual Lineage of Hypotheses $H_1 \\to H_{15}$ (1859–2026)')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '07_h1_h15_historical_timeline.png')))
''')

# Cell 8: Digital Humanities Thematic Clusters
add_md('## 7. Digital Humanities Thematic Clusters')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '08_dh_thematic_clusters.png')))
''')

# Cell 9: Intellectual Network of Mathematicians
add_md('## 8. Intellectual & Geographic Network of Mathematicians')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '09_mathematician_network.png')))
''')

# Cell 10: BBLS Frontier Landscape
add_md('## 9. BBLS Frontier Literature Landscape')
add_code('''display(Image(filename=str(DATAVIZ_DIR / '10_bbls_frontier_landscape.png')))
''')

# Cell 11: Export & Data Summary
add_md('## 10. Summary & Data Export')
add_code('''print("Knowledge graph analysis complete. All visualizations are saved in:", DATAVIZ_DIR)
''')

with open('data/explore_riemann_graph.ipynb', 'w') as f:
    json.dump(notebook, f, indent=2)

print("✓ Successfully updated data/explore_riemann_graph.ipynb")
