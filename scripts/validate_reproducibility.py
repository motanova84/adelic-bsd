#!/usr/bin/env python3
"""
Validation script to check CI/CD reproducibility setup.

This script validates:
1. All dependencies use exact version pinning (==)
2. GitHub Actions are pinned to commit SHAs
3. OS versions are explicitly specified
4. No floating version constraints
"""

import re
import sys
import yaml
from pathlib import Path


def validate_requirements_file(filepath):
    """Validate that a requirements file uses exact version pinning."""
    errors = []
    with open(filepath) as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            
            # Skip comments, empty lines, and -r includes
            if not line or line.startswith('#') or line.startswith('-r'):
                continue
            
            # Check for exact version pinning
            if '==' not in line:
                errors.append(f"Line {line_num}: No exact version pin: {line}")
            elif '>=' in line or '<=' in line or '~=' in line:
                errors.append(f"Line {line_num}: Uses floating version: {line}")
    
    return errors


def validate_workflow_file(filepath):
    """Validate that a workflow file uses pinned actions and OS."""
    errors = []
    
    with open(filepath) as f:
        try:
            data = yaml.safe_load(f)
        except yaml.YAMLError as e:
            errors.append(f"YAML parse error: {e}")
            return errors
    
    jobs = data.get('jobs', {})
    
    for job_name, job_data in jobs.items():
        # Check for OS pinning
        runs_on = job_data.get('runs-on', '')
        if runs_on == 'ubuntu-latest' or runs_on == 'windows-latest' or runs_on == 'macos-latest':
            errors.append(f"Job '{job_name}': Uses floating OS version '{runs_on}'")
        
        # Check container image pinning
        container = job_data.get('container', {})
        if isinstance(container, dict):
            image = container.get('image', '')
            if image and ':latest' in image:
                errors.append(f"Job '{job_name}': Container uses ':latest' tag")
        elif isinstance(container, str) and ':latest' in container:
            errors.append(f"Job '{job_name}': Container uses ':latest' tag")
        
        # Check action pinning
        steps = job_data.get('steps', [])
        for step_idx, step in enumerate(steps):
            if 'uses' in step:
                action = step['uses']
                if '@' not in action:
                    errors.append(
                        f"Job '{job_name}', step {step_idx + 1}: "
                        f"Action missing version: {action}"
                    )
                    continue
                
                # Split action and ref, handle malformed strings
                parts = action.split('@', 1)
                if len(parts) != 2 or not parts[1]:
                    errors.append(
                        f"Job '{job_name}', step {step_idx + 1}: "
                        f"Malformed action reference: {action}"
                    )
                    continue
                
                ref = parts[1].split('#')[0].strip()
                # Check if it's a SHA (40 hex chars) or a tag
                if not re.match(r'^[0-9a-f]{40}$', ref):
                    errors.append(
                        f"Job '{job_name}', step {step_idx + 1}: "
                        f"Action not pinned to SHA: {action}"
                    )
    
    return errors


def main():
    """Main validation function."""
    repo_root = Path(__file__).parent.parent
    
    print("=" * 70)
    print("CI/CD Reproducibility Validation")
    print("=" * 70)
    print()
    
    all_errors = []
    
    # Validate requirements files
    requirements_files = [
        'requirements.txt',
        'requirements_ci.txt',
        'requirements-dev.txt',
    ]
    
    print("Checking requirements files...")
    for req_file in requirements_files:
        filepath = repo_root / req_file
        if not filepath.exists():
            print(f"  ⚠️  {req_file}: Not found (optional)")
            continue
        
        errors = validate_requirements_file(filepath)
        if errors:
            print(f"  ❌ {req_file}: {len(errors)} error(s)")
            all_errors.extend([f"{req_file}: {e}" for e in errors])
        else:
            print(f"  ✅ {req_file}: OK")
    
    print()
    
    # Validate workflow files
    workflow_files = [
        '.github/workflows/python-tests.yml',
        '.github/workflows/python-package-conda.yml',
    ]
    
    print("Checking workflow files...")
    for workflow_file in workflow_files:
        filepath = repo_root / workflow_file
        if not filepath.exists():
            print(f"  ⚠️  {workflow_file}: Not found")
            continue
        
        errors = validate_workflow_file(filepath)
        if errors:
            print(f"  ❌ {workflow_file}: {len(errors)} error(s)")
            all_errors.extend([f"{workflow_file}: {e}" for e in errors])
        else:
            print(f"  ✅ {workflow_file}: OK")
    
    print()
    print("=" * 70)
    
    if all_errors:
        print(f"❌ Validation failed with {len(all_errors)} error(s):")
        print()
        for error in all_errors:
            print(f"  - {error}")
        print()
        return 1
    else:
        print("✅ All validation checks passed!")
        print()
        print("CI/CD setup follows reproducibility best practices:")
        print("  - All dependencies use exact version pinning")
        print("  - All GitHub Actions are pinned to commit SHAs")
        print("  - OS versions are explicitly specified")
        print()
        return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as e:
        print(f"❌ Validation script error occurred: {e}", file=sys.stderr)
        import traceback
        if sys.stderr.isatty():
            # Only print full traceback in interactive mode
            traceback.print_exc()
        sys.exit(2)
