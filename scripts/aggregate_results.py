#!/usr/bin/env python3
"""
Results Aggregation Script

This script aggregates validation results from the spectral BSD framework
and prepares them for deployment and archival.

Usage:
    python3 scripts/aggregate_results.py
    python3 scripts/aggregate_results.py --output results/
"""

import argparse
import json
import sys
from datetime import datetime
from pathlib import Path


def create_results_structure():
    """Create results directory structure."""
    results_dir = Path("results")
    results_dir.mkdir(exist_ok=True)
    
    subdirs = ["datasets", "certificates", "reports", "logs"]
    for subdir in subdirs:
        (results_dir / subdir).mkdir(exist_ok=True)
    
    print(f"✓ Created results directory structure")
    return results_dir


def collect_certificates():
    """Collect generated certificates."""
    cert_sources = [
        Path("certificados"),
        Path("certificates")
    ]
    
    certificates = []
    for cert_dir in cert_sources:
        if cert_dir.exists():
            for cert_file in cert_dir.glob("*.tex"):
                certificates.append({
                    "file": cert_file.name,
                    "path": str(cert_file),
                    "size": cert_file.stat().st_size,
                    "modified": datetime.fromtimestamp(
                        cert_file.stat().st_mtime
                    ).isoformat()
                })
    
    print(f"✓ Collected {len(certificates)} certificates")
    return certificates


def collect_validation_results():
    """Collect validation test results."""
    tests_dir = Path("tests")
    
    results = {
        "timestamp": datetime.now().isoformat(),
        "tests_found": 0,
        "structure_valid": False
    }
    
    if tests_dir.exists():
        test_files = list(tests_dir.glob("test_*.py"))
        results["tests_found"] = len(test_files)
        results["structure_valid"] = True
        print(f"✓ Found {len(test_files)} test files")
    else:
        print("⚠️  Tests directory not found")
    
    return results


def aggregate_module_info():
    """Aggregate information about implemented modules."""
    src_dir = Path("src")
    
    modules = []
    if src_dir.exists():
        for py_file in src_dir.rglob("*.py"):
            if py_file.name != "__init__.py":
                modules.append({
                    "name": py_file.stem,
                    "path": str(py_file.relative_to(src_dir.parent)),
                    "size": py_file.stat().st_size,
                    "lines": len(py_file.read_text().splitlines())
                })
    
    print(f"✓ Cataloged {len(modules)} modules")
    return modules


def generate_summary_report(aggregated_data):
    """Generate comprehensive summary report."""
    report = {
        "generation_time": datetime.now().isoformat(),
        "framework": "Adelic-BSD Spectral Framework",
        "version": "v0.2.1",
        "summary": {
            "total_certificates": len(aggregated_data["certificates"]),
            "total_modules": len(aggregated_data["modules"]),
            "validation_tests": aggregated_data["validation"]["tests_found"],
            "structure_valid": aggregated_data["validation"]["structure_valid"]
        },
        "details": aggregated_data
    }
    
    return report


def save_aggregated_results(results_dir, report):
    """Save aggregated results to JSON file."""
    output_file = results_dir / "aggregated_results.json"
    
    with open(output_file, "w") as f:
        json.dump(report, f, indent=2)
    
    print(f"✓ Saved aggregated results to {output_file}")
    
    # Also save a timestamped version
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    timestamped_file = results_dir / f"results_{timestamp}.json"
    
    with open(timestamped_file, "w") as f:
        json.dump(report, f, indent=2)
    
    print(f"✓ Saved timestamped copy to {timestamped_file}")


def generate_markdown_summary(report, results_dir):
    """Generate human-readable markdown summary."""
    summary_file = results_dir / "SUMMARY.md"
    
    summary = f"""# Results Summary

Generated: {report['generation_time']}

## Framework Information

- **Name**: {report['framework']}
- **Version**: {report['version']}

## Summary Statistics

- **Total Certificates**: {report['summary']['total_certificates']}
- **Total Modules**: {report['summary']['total_modules']}
- **Validation Tests**: {report['summary']['validation_tests']}
- **Structure Valid**: {'✓' if report['summary']['structure_valid'] else '✗'}

## Modules

"""
    
    for module in report['details']['modules'][:10]:  # First 10 modules
        summary += f"- `{module['name']}` ({module['lines']} lines)\n"
    
    if len(report['details']['modules']) > 10:
        summary += f"\n... and {len(report['details']['modules']) - 10} more modules\n"
    
    summary += f"""
## Certificates

Generated {report['summary']['total_certificates']} certificates.

## Validation Status

- Tests found: {report['summary']['validation_tests']}
- Structure validated: {report['summary']['structure_valid']}

---

*This report was automatically generated by the QCAL aggregation pipeline.*
"""
    
    with open(summary_file, "w") as f:
        f.write(summary)
    
    print(f"✓ Generated markdown summary at {summary_file}")


def main():
    """Main aggregation routine."""
    parser = argparse.ArgumentParser(
        description="Aggregate QCAL validation results"
    )
    
    parser.add_argument(
        "--output",
        type=str,
        default="results",
        help="Output directory for aggregated results (default: results/)"
    )
    
    args = parser.parse_args()
    
    print("=" * 60)
    print("QCAL RESULTS AGGREGATION")
    print("=" * 60)
    print()
    
    # Create results structure
    results_dir = Path(args.output)
    results_dir = create_results_structure()
    
    # Collect data from various sources
    print("\nCollecting data...")
    aggregated_data = {
        "certificates": collect_certificates(),
        "validation": collect_validation_results(),
        "modules": aggregate_module_info()
    }
    
    # Generate comprehensive report
    print("\nGenerating report...")
    report = generate_summary_report(aggregated_data)
    
    # Save results
    print("\nSaving results...")
    save_aggregated_results(results_dir, report)
    generate_markdown_summary(report, results_dir)
    
    print("\n" + "=" * 60)
    print("✅ AGGREGATION COMPLETE")
    print("=" * 60)
    print(f"\nResults saved to: {results_dir.absolute()}")
    print(f"Summary available at: {results_dir / 'SUMMARY.md'}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
