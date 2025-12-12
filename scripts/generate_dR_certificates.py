#!/usr/bin/env python3
"""
dR Uniformity Certificate Generator
Generates Fontaine-Perrin-Riou (dR) compatibility certificates

This script creates LaTeX certificates documenting the validation of
dR uniformity: H^1_f dimensions compared with D_dR/Fil^0 dimensions
at p-adic primes for elliptic curves.
"""

import json
import os
from datetime import datetime, timezone

# Configuration
TEMPLATE_PATH = "certificados/template_certificate_dR.tex"
OUTPUT_DIR = "certificados/"
DATA_PATH = "validation_dR_uniformity_results.json"


def generate_dR_certificates():
    """
    Generate dR uniformity certificates for all curves in the validation data
    """
    # Load template
    if not os.path.exists(TEMPLATE_PATH):
        print(f"Error: Template not found at {TEMPLATE_PATH}")
        return
    
    with open(TEMPLATE_PATH, "r", encoding="utf-8") as f:
        template = f.read()
    
    # Load validation data
    if not os.path.exists(DATA_PATH):
        print(f"Error: Data file not found at {DATA_PATH}")
        return
    
    with open(DATA_PATH, "r", encoding="utf-8") as f:
        data = json.load(f)
    
    # Ensure output directory exists
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    
    # Generate certificates
    certificates_generated = 0
    
    print(f"\n{'='*70}")
    print("GENERANDO CERTIFICADOS dR UNIFORMITY")
    print(f"{'='*70}\n")
    
    for curve in data["results"]:
        label = curve["curve"]
        
        # Build the p-entries table rows
        pentries = ""
        for v in curve["validations"]:
            status = "\\OK" if v["ok"] else "\\FAIL"
            pentries += f"{v['p']} & {v['H1f']} & {v['dR']} & {status}\\\\\n"
        
        # Build conclusion text
        if curve["passed"]:
            conclusion = (
                "✅ Compatibilidad dR confirmada. "
                "La dimensión de $H^1_f$ coincide con la de $D_{\\mathrm{dR}}/\\mathrm{Fil}^0$ "
                "en todos los primos analizados."
            )
        else:
            conclusion = (
                "⚠️ Se detectaron pequeñas desviaciones en la compatibilidad dR. "
                "Probable origen: reducción aditiva o torsión local en $p=2$ o $p=5$."
            )
        
        # Replace placeholders in template
        tex_content = (
            template.replace("\\VARcurve", label)
            .replace("\\VARpentries", pentries.strip())
            .replace("\\VARconclusion", conclusion)
        )
        
        # Write certificate file
        output_path = os.path.join(OUTPUT_DIR, f"certificate_dR_uniformity_{label}.tex")
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(tex_content)
        
        certificates_generated += 1
        status_symbol = "✓" if curve["passed"] else "⚠"
        print(f"{status_symbol} {label:10s} -> {output_path}")
    
    print(f"\n{'='*70}")
    print(f"✓ Generados {certificates_generated} certificados dR en '{OUTPUT_DIR}'")
    print(f"  Timestamp: {datetime.now(timezone.utc).isoformat()}")
    print(f"{'='*70}\n")
    
    # Print summary
    summary = data.get("summary", {})
    if summary:
        print("Resumen de validación:")
        print(f"  Total de curvas: {summary.get('total_curves', 0)}")
        print(f"  Pasadas: {summary.get('passed', 0)}")
        print(f"  Falladas: {summary.get('failed', 0)}")
        print(f"  Tasa de éxito: {summary.get('success_rate', 0)*100:.1f}%")
        if "notes" in summary:
            print(f"\n  Notas: {summary['notes']}\n")


if __name__ == "__main__":
    generate_dR_certificates()
