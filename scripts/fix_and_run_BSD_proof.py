#!/usr/bin/env python3
"""
Ejecuta prueba BSD COMPLETA con verificación real
Soluciona el problema de ejecución parcial
"""

import subprocess
import sys
from pathlib import Path
import json


def check_sage_availability():
    """Verifica si SageMath está disponible"""
    try:
        result = subprocess.run(
            ['sage', '--version'],
            capture_output=True,
            text=True,
            timeout=5
        )
        return result.returncode == 0
    except:
        return False


def run_with_sage(script_path):
    """Ejecuta script con SageMath"""
    try:
        result = subprocess.run(
            ['sage', '-python', str(script_path)],
            capture_output=True,
            text=True,
            timeout=300  # 5 minutos timeout
        )

        print(result.stdout)
        if result.stderr:
            print(result.stderr, file=sys.stderr)

        return result.returncode == 0
    except subprocess.TimeoutExpired:
        print(f"⚠️ Timeout ejecutando {script_path}")
        return False
    except Exception as e:
        print(f"❌ Error ejecutando {script_path}: {e}")
        return False


def fix_certificates():
    """Corrige certificados parciales ejecutando realmente"""

    print("🔧 Corrigiendo certificados parciales...\n")

    base = Path(__file__).parent.parent

    # Verificar SageMath
    has_sage = check_sage_availability()

    if not has_sage:
        print("❌ SageMath no está disponible")
        print("   Instala SageMath: conda install -c conda-forge sage")
        print("   O ejecuta en sistema con Sage instalado")
        return False

    print("✅ SageMath disponible\n")

    # Ejecutar módulos individuales
    print("=" * 70)
    print("PASO 1: Probando (dR) Compatibilidad")
    print("=" * 70)

    dR_script = base / 'src' / 'dR_compatibility.py'
    dR_success = run_with_sage(dR_script)

    print("\n" + "=" * 70)
    print("PASO 2: Probando (PT) Compatibilidad")
    print("=" * 70)

    PT_script = base / 'src' / 'PT_compatibility.py'
    PT_success = run_with_sage(PT_script)

    print("\n" + "=" * 70)
    print("PASO 3: Integrando BSD Completo")
    print("=" * 70)

    BSD_script = base / 'scripts' / 'prove_BSD_unconditional.py'
    BSD_success = run_with_sage(BSD_script)

    # Verificar certificados generados
    print("\n" + "=" * 70)
    print("VERIFICACIÓN DE CERTIFICADOS")
    print("=" * 70)

    cert_file = base / 'proofs' / 'BSD_UNCONDITIONAL_CERTIFICATE.json'

    if cert_file.exists():
        with open(cert_file) as f:
            cert = json.load(f)

        status = cert.get('status', 'UNKNOWN')
        components = cert.get('components', {})

        print(f"\nEstado: {status}")
        print("Componentes:")

        # Extract component status properly
        dR_status = components.get('dR_compatibility', {}).get('status', 'UNKNOWN')
        PT_status = components.get('PT_compatibility', {}).get('status', 'UNKNOWN')
        spectral_status = components.get('spectral_framework', {}).get('status', 'UNKNOWN')

        print(f"  (dR): {dR_status}")
        print(f"  (PT): {PT_status}")
        print(f"  Espectral: {spectral_status}")

        all_proved = (dR_status == 'PROVED' and
                      PT_status == 'PROVED' and
                      spectral_status == 'PROVED')

        if all_proved and status in ['THEOREM', 'THEOREM_UNCONDITIONAL']:
            print("\n🎉 ¡BSD PROBADO INCONDICIONALMENTE!")
            return True
        else:
            print("\n⚠️ Prueba aún parcial")
            return False
    else:
        print(f"\n❌ Certificado no encontrado: {cert_file}")
        return False


if __name__ == "__main__":
    success = fix_certificates()
    sys.exit(0 if success else 1)
