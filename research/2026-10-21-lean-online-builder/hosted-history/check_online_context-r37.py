#!/usr/bin/env python3
"""Check a complete retained context using the same hosted/capture protocol.

Separate authored-source1MiB input limit. No native/Lake/controller admission,
new key, arbitrary backend, automatic retry or plaintext runtime fallback.
"""
import argparse
from pathlib import Path
from online_capture import run_case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=['population-certificate',
        'scoped-population-certificate', 'population-exporter-source-boundary', 'probe'], required=True)
    parser.add_argument('--record-codec', type=Path, required=True)
    parser.add_argument('--codec-sha256', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    cases = {
        'probe': ('lean/OnlineTransportProbe.lean', ['online_transport_probe']),
        'population-certificate': ('lean/full-context/PopulationTableCertificate.lean',
            ['Astra.NativePopulationTableCertificate.check_sound',
             'Astra.NativePopulationTableCertificate.checked_actual_population']),
        'population-exporter-source-boundary': ('lean/scoped-context/PopulationExporterSourceBoundary.lean',
            ['GProgram.G7.FiniteReachability.decideReach',
             'GProgram.G7.EffectiveSourceEnumeration.sourceValidDecidable',
             'Astra.PopulationExporterSourceBoundary.root_exact',
             'Astra.PopulationExporterSourceBoundary.edge_sources_exact',
             'Astra.PopulationExporterSourceBoundary.edge_targets_exact',
             'Astra.PopulationExporterSourceBoundary.taxa_exact',
             'Astra.PopulationExporterSourceBoundary.retained_input_source_valid',
             'Astra.PopulationExporterSourceBoundary.retained_input_decider']),
        'scoped-population-certificate': ('lean/scoped-context/PopulationTableCertificate.lean',
            ['GProgram.G7.EffectivePopulationCoefficients.actual_population_coefficients',
             'GProgram.G7.EffectiveCoefficientSupport.coefficients_polynomial_zero_of_not_mem',
             'Astra.NativePopulationTableCertificate.check_sound',
             'Astra.NativePopulationTableCertificate.checked_actual_population']),
    }
    source, audits = cases[args.case]
    return run_case(root, args.case, source, audits,
        'online_lean_full_context_drain.mjs', 'online_lean_full_context.mjs',
        args.record_codec, args.codec_sha256, Path(__file__).name,
        process_timeout=370)


if __name__ == '__main__':
    raise SystemExit(main())
