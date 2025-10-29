#!/usr/bin/env python3
"""
Update README.md with Lean validation results from validation_report.json
"""

import json
import re
from datetime import datetime
from pathlib import Path


def load_validation_report():
    """Load validation report from JSON file."""
    report_path = Path("validation_report.json")
    if not report_path.exists():
        print("⚠️  validation_report.json not found")
        return None
    
    with open(report_path, 'r') as f:
        return json.load(f)


def format_status_badge(status):
    """Format status as a colored badge."""
    if status == "success":
        return "✅ Success"
    elif status == "failed":
        return "❌ Failed"
    elif status == "warning":
        return "⚠️ Warning"
    else:
        return f"❓ {status}"


def create_validation_table(validation_data):
    """Create a markdown table with validation results."""
    status = validation_data.get('status', 'unknown')
    build_time = validation_data.get('build_time_seconds', 0)
    warnings = validation_data.get('warnings', 0)
    errors = validation_data.get('errors', 0)
    lean_version = validation_data.get('lean_version', 'unknown')
    timestamp = validation_data.get('timestamp_utc', 'unknown')
    
    table = f"""
## 🔍 Lean Validation Status

| Metric | Value |
|--------|-------|
| **Status** | {format_status_badge(status)} |
| **Build Time** | {build_time}s |
| **Warnings** | {warnings} |
| **Errors** | {errors} |
| **Lean Version** | {lean_version} |
| **Last Updated** | {timestamp} |

"""
    return table


def update_readme(validation_table):
    """Update README.md with validation table."""
    readme_path = Path("README.md")
    if not readme_path.exists():
        print("⚠️  README.md not found")
        return False
    
    with open(readme_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Pattern to match existing validation table
    pattern = r'## 🔍 Lean Validation Status\n\n.*?\n\n'
    
    # Check if validation table already exists
    if re.search(pattern, content, re.DOTALL):
        # Replace existing table
        new_content = re.sub(pattern, validation_table, content, flags=re.DOTALL)
        print("📝 Updated existing validation table")
    else:
        # Insert after badges section (after first set of badges)
        # Find the first occurrence of "---" after badges
        badges_end = content.find('---')
        if badges_end != -1:
            # Insert before the first "---"
            new_content = content[:badges_end] + validation_table + content[badges_end:]
            print("📝 Inserted new validation table")
        else:
            # Fallback: insert after first paragraph
            lines = content.split('\n')
            insert_pos = 0
            for i, line in enumerate(lines):
                if line.strip() == '' and i > 10:  # After header section
                    insert_pos = i
                    break
            
            if insert_pos > 0:
                lines.insert(insert_pos, validation_table)
                new_content = '\n'.join(lines)
                print("📝 Inserted validation table after header")
            else:
                print("⚠️  Could not find suitable location for validation table")
                return False
    
    # Write updated content
    with open(readme_path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print("✅ README.md updated successfully")
    return True


def main():
    """Main function to update README with validation results."""
    print("🔄 Starting README update with Lean validation results...")
    
    # Load validation report
    report = load_validation_report()
    if not report:
        return 1
    
    validation_data = report.get('validation', {})
    if not validation_data:
        print("⚠️  No validation data found in report")
        return 1
    
    # Create validation table
    validation_table = create_validation_table(validation_data)
    print("📊 Generated validation table:")
    print(validation_table)
    
    # Update README
    if update_readme(validation_table):
        return 0
    else:
        return 1


if __name__ == "__main__":
    exit(main())
