"""
Summary Generator for BSD Experimental Validation
===================================================

Generates summary documentation and CSV files for all experimental results.

Author: BSD Spectral Framework
Date: November 2025
"""

import csv
import json
import os
from datetime import datetime


# Maximum length for j-invariant display in CSV (for readability)
J_INVARIANT_MAX_LENGTH = 30


def generate_summary_csv(results_list, output_path):
    """
    Generate summary CSV file from experimental results.

    Args:
        results_list: List of experiment result dictionaries
        output_path: Path for output CSV file

    Returns:
        str: Path to generated file
    """
    os.makedirs(os.path.dirname(output_path), exist_ok=True)

    # Define CSV columns
    fieldnames = [
        'label',
        'conductor',
        'rank',
        'j_invariant',
        'torsion_order',
        'omega',
        'regulator',
        'tamagawa_product',
        'lhs',
        'rhs_sha_1',
        'sha_estimate',
        'relative_error_percent',
        'status',
        'timestamp',
    ]

    with open(output_path, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        for result in results_list:
            comparison = result.get('comparison', {})
            terms = comparison.get('terms', {})

            row = {
                'label': result.get('label', 'N/A'),
                'conductor': terms.get('conductor', ''),
                'rank': terms.get('rank', ''),
                'j_invariant': (terms.get('j_invariant', '')[:J_INVARIANT_MAX_LENGTH]
                                if terms.get('j_invariant') else ''),
                'torsion_order': terms.get('torsion', {}).get('order', ''),
                'omega': f"{terms.get('omega', {}).get('omega_plus', 0):.10f}",
                'regulator': f"{terms.get('regulator', {}).get('value', 0):.10f}",
                'tamagawa_product': terms.get('tamagawa', {}).get('product', ''),
                'lhs': f"{comparison.get('lhs', 0):.10e}" if comparison.get('lhs') else '',
                'rhs_sha_1': f"{comparison.get('rhs_sha_1', 0):.10e}" if comparison.get('rhs_sha_1') else '',
                'sha_estimate': f"{comparison.get('sha_estimate', 0):.6f}" if comparison.get('sha_estimate') else '',
                'relative_error_percent': (f"{comparison.get('relative_error', 0) * 100:.4f}"
                                           if comparison.get('relative_error') else ''),
                'status': '✓' if comparison.get('sha_is_1') else '×' if comparison.get('sha_estimate') else '?',
                'timestamp': datetime.now().isoformat(),
            }
            writer.writerow(row)

    return output_path


def generate_readme_genesis(results_list, output_path, title="BSD Genesis Experimental Validation"):
    """
    Generate README_BSD_GENESIS.md documentation file.

    Args:
        results_list: List of experiment result dictionaries
        output_path: Path for output markdown file
        title: Title for the document

    Returns:
        str: Path to generated file
    """
    os.makedirs(os.path.dirname(output_path), exist_ok=True)

    # Build markdown content
    lines = [
        f"# {title}",
        "",
        "## Overview",
        "",
        "This document summarizes experimental validation of the Birch and Swinnerton-Dyer",
        "conjecture on elliptic curves not covered by classical proofs (BHK, Gross-Zagier, Kolyvagin).",
        "",
        "### Key Features:",
        "- Curves with conductor > 1000",
        "- Curves with rank ≥ 2 (not covered by Gross-Zagier/Kolyvagin)",
        "- Non-trivial torsion structures",
        "- QCAL seal validation with cryptographic hashes",
        "",
        "## Validation Framework",
        "",
        "The BSD formula states that for an elliptic curve E/ℚ:",
        "",
        "**For rank 0:**",
        "```",
        "L(E,1) / Ω = |Sha(E)| × ∏cₚ / |E(ℚ)_tors|²",
        "```",
        "",
        "**For rank r > 0:**",
        "```",
        "L⁽ʳ⁾(E,1) / (r! × Ω × Reg) = |Sha(E)| × ∏cₚ / |E(ℚ)_tors|²",
        "```",
        "",
        "We compute both sides and estimate |Sha(E)|.",
        "",
        "## Experimental Results",
        "",
        f"**Date:** {datetime.now().strftime('%Y-%m-%d')}",
        f"**Number of curves tested:** {len(results_list)}",
        "",
    ]

    # Add results table
    lines.extend([
        "### Results Summary",
        "",
        "| Label | Conductor | Rank | LHS | RHS | Sha Est. | Error | Status |",
        "|-------|-----------|------|-----|-----|----------|-------|--------|",
    ])

    for result in results_list:
        comparison = result.get('comparison', {})
        terms = comparison.get('terms', {})

        label = result.get('label', 'N/A')
        conductor = terms.get('conductor', 'N/A')
        rank = terms.get('rank', 'N/A')

        lhs = comparison.get('lhs')
        rhs = comparison.get('rhs_sha_1')
        sha_est = comparison.get('sha_estimate')
        error = comparison.get('relative_error')

        lhs_str = f"{lhs:.4e}" if lhs is not None else "N/A"
        rhs_str = f"{rhs:.4e}" if rhs is not None else "N/A"
        sha_str = f"{sha_est:.4f}" if sha_est is not None else "N/A"
        error_str = f"{error * 100:.2f}%" if error is not None else "N/A"

        status = "✓" if comparison.get('sha_is_1') else "×" if sha_est is not None else "?"

        lines.append(f"| {label} | {conductor} | {rank} | {lhs_str} | {rhs_str} | {sha_str} | {error_str} | {status} |")

    # Add detailed sections
    lines.extend([
        "",
        "## Detailed Results",
        "",
    ])

    for result in results_list:
        comparison = result.get('comparison', {})
        terms = comparison.get('terms', {})
        label = result.get('label', 'N/A')

        lines.extend([
            f"### Curve: {label}",
            "",
            f"- **Conductor:** {terms.get('conductor', 'N/A')}",
            f"- **Rank:** {terms.get('rank', 'N/A')}",
            f"- **j-invariant:** `{terms.get('j_invariant', 'N/A')}`",
            f"- **Torsion:** {terms.get('torsion', {}).get('structure', [])}",
            "",
            "**BSD Terms:**",
            f"- Ω (real period): {terms.get('omega', {}).get('omega_plus', 'N/A')}",
            f"- Regulator: {terms.get('regulator', {}).get('value', 'N/A')}",
            f"- Tamagawa product: {terms.get('tamagawa', {}).get('product', 'N/A')}",
            "",
            "**Comparison:**",
        ])

        lhs = comparison.get('lhs')
        rhs = comparison.get('rhs_sha_1')
        sha_est = comparison.get('sha_estimate')
        error = comparison.get('relative_error')

        if lhs is not None:
            lines.append(f"- LHS: {lhs:.10e}")
            lines.append(f"- RHS (Sha=1): {rhs:.10e}")
            if sha_est is not None:
                lines.append(f"- |Sha(E)| estimate: {sha_est:.6f}")
                lines.append(f"- Relative error: {error * 100:.4f}%")

                if comparison.get('sha_is_1'):
                    lines.append("- **Status:** ✓ Experimental match (Sha ≈ 1)")
                else:
                    lines.append("- **Status:** × Mismatch or requires further analysis")
        else:
            lines.append("- Could not compute full BSD comparison")

        lines.append("")

    # Add methodology section
    lines.extend([
        "## Methodology",
        "",
        "### Curve Selection Criteria",
        "",
        "Curves were selected based on:",
        "1. **Conductor > 1000**: Beyond small conductor databases",
        "2. **Rank ≥ 2**: Not covered by Gross-Zagier and Kolyvagin (rank 0,1)",
        "3. **Non-trivial torsion**: Additional arithmetic complexity",
        "4. **Not in BHK database**: Not covered by Bhargava-Harrell-Kane methods",
        "",
        "### Computation",
        "",
        "All computations performed using SageMath with high precision arithmetic.",
        "The following terms are computed:",
        "",
        "1. **L-function value** at s=1 (or derivatives for rank > 0)",
        "2. **Real period Ω** from period lattice",
        "3. **Regulator** from Mordell-Weil basis",
        "4. **Tamagawa numbers** at all bad primes",
        "5. **Torsion order** of E(ℚ)_tors",
        "",
        "### Error Tolerance",
        "",
        "An experimental match is declared if:",
        "- Relative error < 1%",
        "- |Sha(E)| estimate ≈ 1.00",
        "",
        "## QCAL Certification",
        "",
        "Each curve is certified with a QCAL seal containing:",
        "- SHA-256 hash of j-invariant",
        "- Timestamp",
        "- Relative error",
        "- Validation status",
        "",
        "**QCAL Frequency:** f₀ = 141.7001 Hz",
        "",
        "## References",
        "",
        "1. Birch, B. J., & Swinnerton-Dyer, H. P. F. (1965). Notes on elliptic curves II.",
        "2. Gross, B. H., & Zagier, D. B. (1986). Heegner points and derivatives of L-series.",
        "3. Kolyvagin, V. A. (1988). Finiteness of E(ℚ) and Sha for a class of Weil curves.",
        "4. Spectral BSD Framework: Adelic-BSD Repository",
        "",
        "---",
        f"*Generated: {datetime.now().isoformat()}*",
    ])

    content = "\n".join(lines)

    with open(output_path, 'w') as f:
        f.write(content)

    return output_path


def generate_all_summaries(results_list, output_dir):
    """
    Generate all summary files in the output directory.

    Args:
        results_list: List of experiment result dictionaries
        output_dir: Directory for output files

    Returns:
        dict: Paths to generated files
    """
    os.makedirs(output_dir, exist_ok=True)

    csv_path = os.path.join(output_dir, 'summary_results.csv')
    readme_path = os.path.join(output_dir, 'README_BSD_GENESIS.md')

    generate_summary_csv(results_list, csv_path)
    generate_readme_genesis(results_list, readme_path)

    # Also save raw results as JSON
    json_path = os.path.join(output_dir, 'all_results.json')
    with open(json_path, 'w') as f:
        json.dump(results_list, f, indent=2, default=str)

    return {
        'csv': csv_path,
        'readme': readme_path,
        'json': json_path,
    }
