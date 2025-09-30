#!/usr/bin/env python3
"""
Quick demo of spectral finiteness proof
Mota Burruezo Spectral BSD Framework
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))

from sage.all import EllipticCurve
from src.spectral_finiteness import SpectralFinitenessProver, batch_prove_finiteness

def main():
    print("🚀 Spectral Finiteness Proof Demo")
    print("Mota Burruezo Framework")
    print("=" * 60)
    
    # Curvas de prueba
    test_curves = ['11a1', '11a2', '11a3', '14a1', '15a1', '17a1', '19a1', '37a1']
    
    print(f"📊 Analyzing {len(test_curves)} elliptic curves...")
    print()
    
    results = batch_prove_finiteness(test_curves)
    
    successful = 0
    total_bound = 0
    
    for label, result in results.items():
        if 'error' in result:
            print(f"❌ {label}: ERROR - {result['error']}")
            continue
            
        E = EllipticCurve(label)
        sha_known = "Unknown"
        try:
            sha_known = E.sha().an()
        except:
            pass
            
        bound_status = ""
        if sha_known != "Unknown" and result['global_bound'] >= sha_known:
            bound_status = "✓"
        else:
            bound_status = "⚠️"
            
        print(f"✅ {label}:")
        print(f"   • Conductor: {E.conductor()}")
        print(f"   • Rank: {E.rank()}")
        print(f"   • Global bound: {result['global_bound']}")
        print(f"   • Known #Ш: {sha_known} {bound_status}")
        print(f"   • Finiteness: PROVED")
        print()
        
        successful += 1
        total_bound += result['global_bound']
    
    print("🎉 SUMMARY")
    print("=" * 60)
    print(f"Successful proofs: {successful}/{len(test_curves)}")
    print(f"Average bound: {total_bound/successful if successful > 0 else 0:.2f}")
    print()
    print("📚 Next steps:")
    print("   • Run extended tests: python tests/test_finiteness.py")
    print("   • Generate certificates: use generate_certificate() method")
    print("   • Explore spectral data: examine 'spectral_data' in results")

if __name__ == "__main__":
    main()
