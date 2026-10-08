"""Small accessible Raubeson/Tsuga report reader (stdlib, no model/API calls)."""
from pathlib import Path
import argparse, html, json
BASE=Path(__file__).resolve().parent

def build():
 c=json.loads((BASE/'CWU-RUNS/COMPARISON.json').read_text())
 f=json.loads((BASE/'DRYAD-FILE-INVENTORY.json').read_text())
 c['public_artifacts']=[{'name':x['path'],'bytes':x['size'],'deposit_md5':x['digest'],'description':x['description']} for x in f['_embedded']['stash:files']]
 c['data_retrieval']={'metadata_and_inventory':'HTTP200, exact saved bytes','api_file_downloads':'HTTP401 Unauthorized','public_landing_file_downloads':'HTTP403 Forbidden','full_alignments_verified':False}
 real=BASE/'REAL-BASELINE/COMPARISON.json'
 if real.exists():c['real_sequence_baseline']=json.loads(real.read_text())
 c['next_empirical_step']='Verify the original complete Dryad CC0 alignments; map specimen/accession, orthology, partitions and genuinely independent ancestry blocks; justify compartment inheritance and calibrated sequence/tree uncertainty before source fitting.'
 return c

def text(c):
 return '\n'.join([
  'Linda Raubeson / eastern Asian hemlocks',
  'Question: what can the nuclear/chloroplast disagreement establish?',
  '',
  'Paper-reported nuclear relationship: T. chinensis + T. caroliniana.',
  'Paper-reported chloroplast relationship: T. chinensis + Japanese T. sieboldii.',
  'Baseline: these two sister clades cross; one rooted tree cannot contain both.',
  '',
  'Actual public GenBank marker pilot (same published four specimens):',
  *['  '+r['marker']+': '+str(r['sites'])+' sites; '+str(r['estimated_split'])+'; '+str(round(r['bootstrap_support']*100))+'/'+str(r['bootstrap_replicates'])+' descriptive column-bootstrap resamples.' for r in c.get('real_sequence_baseline',{}).get('rows',[])],
  '  The original sequence adapter and receipt replay pass; biological target ABSTAIN.',
  '  T.chinensis rbcL is explicitly homology-inferred, not deposited annotation.',
  '',
  'Our exact-law software comparison (synthetic, not paper frequencies):',
  *['  '+x['name']+': '+x['status']+'; checker '+x['checker']['status']+'; target '+str(x.get('decoded_original_taxon_target')) for x in c['original_solver_controls']],
  '',
  'Empirical chloroplast-capture answer: UNKNOWN.',
  'No numerical confidence interval: no sequence/gene-tree sampling law was admitted.',
  'Real GenBank records are available; full original Dryad alignment retrieval remains blocked.',
  'The authors suggest chloroplast capture. This demonstration does not test that cause.',
  '',
  'Next: '+c['next_empirical_step'],
  'Source: Holman et al. 2017, DOI 10.1600/036364417X696474.',
  'Dataset: https://datadryad.org/dataset/doi:10.5061/dryad.2r12j',
 ])

def page(c):
 rows=''.join('<tr><td>'+html.escape(x['name'])+'</td><td>'+html.escape(x['description'])+'</td><td>'+str(x['bytes'])+'</td></tr>' for x in c['public_artifacts'])
 realrows=''.join('<tr><td>'+html.escape(r['marker'])+'</td><td>'+str(r['sites'])+'</td><td>'+html.escape(str(r['estimated_split']))+'</td><td>'+str(round(r['bootstrap_support']*100))+'/'+str(r['bootstrap_replicates'])+'</td></tr>' for r in c.get('real_sequence_baseline',{}).get('rows',[]))
 realtable='<h2>Actual public sequence pilot</h2><p>Eight versioned GenBank records match the same four specimens listed in the paper. One nuclear4CL1 marker (1048 sites) and one chloroplast rbcL marker (1428 sites) give the following exploratory quartet estimates. The original sequence adapter and receipt reexecution pass. Bootstrap here resamples alignment columns; it is not a probability of capture, a calibrated historical confidence region, or100 independent loci.</p><table><thead><tr><th>Marker</th><th>Sites</th><th>Estimated split</th><th>100 column resamples</th></tr></thead><tbody>'+realrows+'</tbody></table><p>T.chinensis rbcL is explicitly a homology-inferred region at zero-based74466:75894, using33 unique40-base anchors to a deposited reference CDS; the other three have deposited annotations. This is a small marker comparison, not the original whole-plastome/two-nuclear-gene reanalysis. Both biological target outputs abstain.</p>'
 controls=''.join('<tr><td>'+html.escape(x['name'])+'</td><td>'+html.escape(x['status'])+'</td><td>'+html.escape(x['checker']['status'])+'<br>'+html.escape(str(x.get('decoded_original_taxon_target')))+ '</td></tr>' for x in c['original_solver_controls'])
 return '''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Hemlock relationship comparison</title><style>body{font:18px/1.5 system-ui,sans-serif;max-width:900px;margin:2rem auto;padding:0 1rem;color:#183025;background:#f8faf8}h1{font-size:2rem}h2{font-size:1.3rem}.cards{display:flex;gap:1rem;flex-wrap:wrap}.card{background:white;border:1px solid #c7d9cb;border-radius:12px;padding:1.2rem;flex:1;min-width:250px}.state{background:#fff4d6;padding:1rem;border-radius:12px}table{width:100%;font-size:14px;border-collapse:collapse}td,th{padding:.6rem;text-align:left;border-bottom:1px solid #d8e1db;overflow-wrap:anywhere}code{overflow-wrap:anywhere}a{color:#156543}</style><h1>Two hemlock histories disagree. What follows?</h1><p>Linda Raubeson's coauthored study asks about eastern Asian hemlock relationships. This small reproducible comparison reads the paper's reported sister groups and keeps the biological question separate from software controls.</p><div class="cards"><div class="card"><b>Nuclear 4CL summary</b><p><i>T. chinensis</i> + <i>T. caroliniana</i></p></div><div class="card"><b>Chloroplast summary</b><p><i>T. chinensis</i> + Japanese <i>T. sieboldii</i></p></div></div><p>The groups share <i>T. chinensis</i> but neither contains the other. Descendant groups in one rooted tree are nested or disjoint, so these reported groups conflict. This reproduces a concrete part of the published disagreement.</p><div class="state"><b>Chloroplast capture: UNKNOWN in this system.</b><p>The authors suggest capture. The comparison does not select capture over other causes or identify a donor/recipient. Genealogy-law probabilities, compartment inheritance and calibrated sequence/tree uncertainty have not been admitted.</p></div>'''+realtable+'''<h2>What our software adds</h2><p>The original source solver and its certificate checker run two separately declared synthetic quartet laws (4/5, 1/10, 1/10), giving different tree targets under a complete zero-hybrid registry. The empirical intake refuses the unadmitted Tsuga case. These controls demonstrate exact source consistency and honest abstention; the numbers are invented software fixtures, not paper estimates.</p><table><thead><tr><th>Control</th><th>Producer</th><th>Checker</th></tr></thead><tbody>'''+controls+'''</tbody></table><h2>Public data and the next real comparison</h2><p>Fresh Dryad metadata identify the following CC0 artifacts. Original Dryad alignment bytes could not be retrieved (API401, standard public route403). The separate GenBank-derived marker alignments above use actual public sequence bytes. No numerical confidence interval is displayed because a sampling/calibration contract is absent.</p><table><thead><tr><th>Artifact</th><th>Description</th><th>Bytes</th></tr></thead><tbody>'''+rows+'''</tbody></table><p>Next: verify original bytes and specimen/orthology/partition joins; establish independent ancestry blocks and a compartment-specific model; then compare a sequence/tree baseline with supported source candidates and uncertainty on the same admitted data.</p><p>AlphaGenome's human/mouse molecular predictions are a separate application. They are not a plant/hemlock observation channel.</p><p><a href="https://doi.org/10.1600/036364417X696474">Holman et al. (2017)</a> · <a href="https://datadryad.org/dataset/doi:10.5061/dryad.2r12j">CC0 dataset</a> · <a href="CWU-RUNS/COMPARISON.json">Exact comparison and command receipts</a></p><p>Reproduce: <code>python3 cwu_baseline.py</code>. Recompute source controls with the pinned environment: <code>python run_cwu_demo.py</code>.</p></html>'''

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--json',action='store_true');p.add_argument('--report',type=Path);a=p.parse_args();c=build()
 if a.report:a.report.write_text(page(c))
 print(json.dumps(c,indent=2) if a.json else text(c))

if __name__=='__main__':main()
