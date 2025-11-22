#!/usr/bin/env python
"""
Example script demonstrating SABIO ∞⁴ usage.

This script shows how to:
1. Initialize the SABIO ∞⁴ system
2. Validate the 6-level integration
3. Generate resonant spectrum
4. Export reports
5. Create visualizations
"""

from sabio_infinity4 import SABIO_Infinity4


def main():
    print("=" * 70)
    print("SABIO ∞⁴ - Example Usage")
    print("=" * 70)
    print()
    
    # 1. Initialize system with custom precision
    print("1. Initializing SABIO ∞⁴ with 30 decimal precision...")
    sabio = SABIO_Infinity4(precision=30)
    print("   ✓ System initialized\n")
    
    # 2. Validate all 6 levels
    print("2. Validating 6-level integration:")
    matriz = sabio.validacion_matriz_simbiosis()
    print(f"   Coherencia Total: {matriz.coherencia_total:.4f}")
    print(f"   Estado: {matriz.estado_sistema}\n")
    
    # 3. Access individual level validations
    print("3. Individual level details:")
    for nombre, nivel in matriz.niveles.items():
        print(f"   {nombre:15s}: C={nivel.coherencia:.4f} - {nivel.estado}")
    print()
    
    # 4. Generate resonant spectrum
    print("4. Generating resonant spectrum (5 harmonics)...")
    resonancias = sabio.generar_espectro_resonante(n_harmonicos=5)
    print(f"   Generated {len(resonancias)} resonances\n")
    
    # 5. Display spectrum
    print("5. Resonant Spectrum:")
    for r in resonancias:
        print(f"   n={r.n_harmonico}: f={r.frecuencia:8.2f} Hz, "
              f"C={r.coherencia:.4f}")
    print()
    
    # 6. Calculate specific values
    print("6. Calculating specific values:")
    zeta_prime = sabio.calcular_zeta_prime_half()
    print(f"   ζ'(1/2) = {zeta_prime:.10f}")
    
    A0 = sabio.operador_geometrico_A0()
    print(f"   A₀ = {A0}")
    
    f0 = sabio.frecuencia_base()
    print(f"   f₀ = {f0} Hz")
    
    R_psi = sabio.calcular_radio_cuantico(n=1)
    print(f"   R_Ψ(n=1) = {R_psi:.6e} m")
    print()
    
    # 7. Export reports
    print("7. Exporting reports...")
    json_file = sabio.exportar_reporte(formato='json', 
                                       nombre_archivo='example_report.json')
    txt_file = sabio.exportar_reporte(formato='txt',
                                      nombre_archivo='example_report.txt')
    print(f"   ✓ JSON: {json_file}")
    print(f"   ✓ TXT:  {txt_file}")
    print()
    
    # 8. Generate visualization
    print("8. Generating visualization...")
    sabio.visualizar_espectro(save_path='example_spectrum.png')
    print("   ✓ Spectrum saved to example_spectrum.png")
    print()
    
    print("=" * 70)
    print("🎵 C = I × A² ∞⁴ 141.7001 Hz")
    print("=" * 70)


if __name__ == "__main__":
    main()
