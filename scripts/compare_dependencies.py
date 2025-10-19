#!/usr/bin/env python3
"""
Script to compare local dependencies with CI frozen packages.
Usage: python scripts/compare_dependencies.py [frozen.txt]
"""

import sys
import subprocess
from pathlib import Path


def get_local_packages():
    """Get locally installed packages."""
    result = subprocess.run(
        ['pip', 'freeze'],
        capture_output=True,
        text=True,
        check=True
    )
    packages = {}
    for line in result.stdout.strip().split('\n'):
        if '==' in line:
            name, version = line.split('==', 1)
            packages[name.lower()] = version
    return packages


def parse_frozen_file(filepath):
    """Parse frozen packages file."""
    packages = {}
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if line and '==' in line:
                name, version = line.split('==', 1)
                packages[name.lower()] = version
    return packages


def compare_packages(local_packages, ci_packages):
    """Compare local and CI packages."""
    all_packages = set(local_packages.keys()) | set(ci_packages.keys())
    
    differences = {
        'only_local': [],
        'only_ci': [],
        'version_mismatch': []
    }
    
    for pkg in sorted(all_packages):
        if pkg in local_packages and pkg in ci_packages:
            if local_packages[pkg] != ci_packages[pkg]:
                differences['version_mismatch'].append({
                    'package': pkg,
                    'local': local_packages[pkg],
                    'ci': ci_packages[pkg]
                })
        elif pkg in local_packages:
            differences['only_local'].append({
                'package': pkg,
                'version': local_packages[pkg]
            })
        else:
            differences['only_ci'].append({
                'package': pkg,
                'version': ci_packages[pkg]
            })
    
    return differences


def print_report(differences):
    """Print comparison report."""
    print("\n" + "="*70)
    print("🔍 DEPENDENCY COMPARISON REPORT")
    print("="*70)
    
    if differences['version_mismatch']:
        print(f"\n⚠️  VERSION MISMATCHES ({len(differences['version_mismatch'])} packages):")
        print("-" * 70)
        for item in differences['version_mismatch']:
            print(f"  {item['package']}")
            print(f"    Local: {item['local']}")
            print(f"    CI:    {item['ci']}")
            print()
    
    if differences['only_local']:
        print(f"\n📦 ONLY IN LOCAL ({len(differences['only_local'])} packages):")
        print("-" * 70)
        for item in differences['only_local']:
            print(f"  {item['package']}=={item['version']}")
    
    if differences['only_ci']:
        print(f"\n🔧 ONLY IN CI ({len(differences['only_ci'])} packages):")
        print("-" * 70)
        for item in differences['only_ci']:
            print(f"  {item['package']}=={item['version']}")
    
    if not any(differences.values()):
        print("\n✅ No differences found! Local and CI environments match.")
    else:
        print("\n" + "="*70)
        total_issues = (
            len(differences['version_mismatch']) + 
            len(differences['only_local']) + 
            len(differences['only_ci'])
        )
        print(f"📊 SUMMARY: {total_issues} difference(s) found")
        print("="*70)
        print("\n💡 RECOMMENDATIONS:")
        if differences['version_mismatch']:
            print("  - Update local packages to match CI versions")
            print("  - Run: pip install -r requirements_ci.txt --force-reinstall")
        if differences['only_local']:
            print("  - Consider if these packages should be in requirements files")
            print("  - Or use a clean virtual environment for testing")
        if differences['only_ci']:
            print("  - These packages may be CI-specific dependencies")
            print("  - Verify requirements_ci.txt is up to date")
    print()


def main():
    """Main function."""
    if len(sys.argv) > 1:
        frozen_file = Path(sys.argv[1])
    else:
        # Try to find frozen.txt in common locations
        possible_locations = [
            Path('frozen.txt'),
            Path('ci-frozen.txt'),
            Path('frozen-packages.txt'),
        ]
        frozen_file = None
        for loc in possible_locations:
            if loc.exists():
                frozen_file = loc
                break
        
        if frozen_file is None:
            print("❌ Error: No frozen.txt file found")
            print("\nUsage:")
            print("  python scripts/compare_dependencies.py [path/to/frozen.txt]")
            print("\nTo get CI frozen packages:")
            print("  1. Go to GitHub Actions workflow run")
            print("  2. Download 'frozen-packages-py*.txt' artifact")
            print("  3. Extract and rename to frozen.txt")
            print("\nOr generate local frozen packages:")
            print("  pip freeze > frozen.txt")
            sys.exit(1)
    
    if not frozen_file.exists():
        print(f"❌ Error: File not found: {frozen_file}")
        sys.exit(1)
    
    print(f"📋 Comparing with: {frozen_file}")
    print("🔄 Getting local packages...")
    
    try:
        local_packages = get_local_packages()
        ci_packages = parse_frozen_file(frozen_file)
        
        print(f"✅ Local packages: {len(local_packages)}")
        print(f"✅ CI packages: {len(ci_packages)}")
        
        differences = compare_packages(local_packages, ci_packages)
        print_report(differences)
        
        # Exit with error code if there are differences
        if any(differences.values()):
            sys.exit(1)
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Error running pip freeze: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
