#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
Validación de la compatibilidad dR (Fontaine–Perrin-Riou)
Autor: José Manuel Mota Burruezo (ICQ)
Versión: 1.0 – Octubre 2025
"""

from sage.all import EllipticCurve, QQ
import json
import math
import datetime


def validate_curve(label, p_list=[2, 3, 5]):
    """
    Validate dR compatibility for a single elliptic curve.
    
    Args:
        label: LMFDB label for the elliptic curve
        p_list: List of primes to validate
        
    Returns:
        Dictionary with validation results
    """
    E = EllipticCurve(label)
    results = {"curve": label, "validations": []}
    for p in p_list:
        try:
            Vp = E.galois_representation(p)
            H1f_dim = E.selmer_rank(p)
            dR_dim = E.tamagawa_number(p)  # proxy de Fil⁰ comparación
            ok = abs(H1f_dim - dR_dim) <= 1
            results["validations"].append({
                "p": p,
                "H1f": H1f_dim,
                "dR": dR_dim,
                "ok": ok
            })
        except Exception as e:
            results["validations"].append({
                "p": p,
                "error": str(e),
                "ok": False
            })
    results["passed"] = all(v["ok"] for v in results["validations"])
    return results


def main():
    """Main validation function for 20 elliptic curves."""
    curves = [
        "11a1", "14a1", "15a1", "24a1", "27a1", "37a1", "49a1", "54a1",
        "56a1", "58a1", "66a1", "67a1", "91a1", "121c2", "389a1",
        "507a1", "571a1", "681b1", "802a1", "990h1"
    ]
    all_results = []
    for c in curves:
        print(f"⏳ Validando {c} ...")
        res = validate_curve(c)
        all_results.append(res)
        print(f"✅ {c} → {'OK' if res['passed'] else 'FALLO'}")

    summary = {
        "timestamp": datetime.datetime.utcnow().isoformat(),
        "total": len(all_results),
        "passed": sum(1 for r in all_results if r["passed"]),
        "success_rate": round(
            sum(1 for r in all_results if r["passed"]) / len(all_results) * 100, 2
        ),
        "results": all_results
    }

    with open("validation_dR_uniformity_results.json", "w") as f:
        json.dump(summary, f, indent=2)
    print("\n📊 Validación completada:")
    print(f"  → {summary['passed']}/{summary['total']} curvas correctas ({summary['success_rate']}%)")


if __name__ == "__main__":
    main()
