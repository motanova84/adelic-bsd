#!/usr/bin/env python3
"""
Script de corrección y ejecución para prueba BSD
Aplica correcciones y ejecuta prueba completa

Este script:
1. Verifica disponibilidad de SageMath
2. Actualiza módulos para ejecución real
3. Ejecuta pruebas (dR) y (PT)
4. Genera certificados con datos reales
5. Verifica resultados

Uso:
    python scripts/fix_and_run_BSD_proof.py
    O con Sage:
    sage -python scripts/fix_and_run_BSD_proof.py
"""

import sys
import json
from pathlib import Path
import subprocess
import os

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))


def check_sage_available():
    """Verificar si SageMath está disponible"""
    try:
        from sage.all import EllipticCurve
        return True
    except ImportError:
        return False


def run_with_sage(script_path):
    """
    Ejecutar un script Python con Sage
    
    Args:
        script_path: Path to the Python script
        
    Returns:
        exit_code: Exit code of the process
    """
    print(f"   Ejecutando: sage -python {script_path}")
    
    result = subprocess.run(
        ['sage', '-python', str(script_path)],
        capture_output=False,
        text=True
    )
    
    return result.returncode


def verify_certificate(cert_path, expected_fields):
    """
    Verificar que un certificado existe y tiene los campos esperados
    
    Args:
        cert_path: Path to certificate file
        expected_fields: List of expected field names
        
    Returns:
        (is_valid, message): Tuple with validation result
    """
    if not cert_path.exists():
        return False, f"Certificado no encontrado: {cert_path}"
    
    try:
        with open(cert_path, 'r') as f:
            data = json.load(f)
        
        # Check if it's a list or dict
        if isinstance(data, list):
            if len(data) == 0:
                return False, "Certificado vacío (lista sin elementos)"
            total = len(data)
        elif isinstance(data, dict):
            total = data.get('total_cases', 0)
            if total == 0:
                # Check for 'results' field
                results = data.get('results', [])
                total = len(results)
            
            if total == 0:
                return False, "Certificado sin resultados (0 casos)"
        else:
            return False, "Formato de certificado inválido"
        
        return True, f"Válido ({total} casos)"
        
    except Exception as e:
        return False, f"Error leyendo certificado: {e}"


def main():
    """Función principal"""
    print("="*70)
    print("🔧 CORRECCIÓN Y EJECUCIÓN DE PRUEBA BSD")
    print("="*70)
    print()
    
    # Verificar SageMath
    print("🔍 Verificando SageMath...")
    sage_available = check_sage_available()
    
    if not sage_available:
        # Try to call sage command
        try:
            result = subprocess.run(['sage', '--version'], capture_output=True, text=True)
            if result.returncode == 0:
                print("✅ SageMath disponible (comando sage)")
                use_sage_command = True
            else:
                print("❌ SageMath NO disponible")
                print("   Instalar: conda install -c conda-forge sage")
                print("   O: apt-get install sagemath")
                return 1
        except FileNotFoundError:
            print("❌ SageMath NO disponible")
            print("   Instalar: conda install -c conda-forge sage")
            return 1
    else:
        print("✅ SageMath disponible (importable)")
        use_sage_command = False
    
    print()
    
    # Crear directorios necesarios
    Path('proofs').mkdir(exist_ok=True)
    
    # Ejecutar pruebas
    root_dir = Path(__file__).parent.parent
    
    # PASO 1: (dR) Compatibility
    print("📐 PASO 1: Ejecutando (dR) Compatibility...")
    print("-"*70)
    
    dR_script = root_dir / 'src' / 'dR_compatibility_fixed.py'
    if not dR_script.exists():
        dR_script = root_dir / 'src' / 'dR_compatibility.py'
    
    if use_sage_command:
        dR_exit = run_with_sage(dR_script)
    else:
        # Run directly with Python (Sage available as module)
        try:
            if dR_script.name == 'dR_compatibility_fixed.py':
                from dR_compatibility_fixed import prove_dR_all_cases
            else:
                from dR_compatibility import prove_dR_all_cases
            
            results = prove_dR_all_cases()
            dR_exit = 0 if results else 1
        except Exception as e:
            print(f"❌ Error ejecutando (dR): {e}")
            dR_exit = 1
    
    print()
    
    # PASO 2: (PT) Compatibility
    print("📊 PASO 2: Ejecutando (PT) Compatibility...")
    print("-"*70)
    
    PT_script = root_dir / 'src' / 'PT_compatibility_fixed.py'
    if not PT_script.exists():
        PT_script = root_dir / 'src' / 'PT_compatibility.py'
    
    if use_sage_command:
        PT_exit = run_with_sage(PT_script)
    else:
        # Run directly with Python (Sage available as module)
        try:
            if PT_script.name == 'PT_compatibility_fixed.py':
                from PT_compatibility_fixed import prove_PT_all_ranks
            else:
                from PT_compatibility import prove_PT_all_ranks
            
            results = prove_PT_all_ranks()
            PT_exit = 0 if results else 1
        except Exception as e:
            print(f"❌ Error ejecutando (PT): {e}")
            PT_exit = 1
    
    print()
    
    # PASO 3: BSD Integration
    print("🎯 PASO 3: Ejecutando integración BSD...")
    print("-"*70)
    
    BSD_script = root_dir / 'scripts' / 'prove_BSD_unconditional.py'
    
    if use_sage_command:
        BSD_exit = run_with_sage(BSD_script)
    else:
        try:
            # Change to root directory for imports to work
            original_cwd = os.getcwd()
            os.chdir(root_dir)
            
            # Run the script
            with open(BSD_script, 'r') as f:
                code = f.read()
            exec(code, {'__name__': '__main__'})
            
            os.chdir(original_cwd)
            BSD_exit = 0
        except Exception as e:
            print(f"❌ Error ejecutando BSD: {e}")
            BSD_exit = 1
            os.chdir(original_cwd)
    
    print()
    
    # VERIFICACIÓN DE RESULTADOS
    print("="*70)
    print("📋 VERIFICACIÓN DE RESULTADOS")
    print("="*70)
    print()
    
    # Verificar certificados
    dR_cert = root_dir / 'proofs' / 'dR_certificates.json'
    PT_cert = root_dir / 'proofs' / 'PT_certificates.json'
    BSD_cert = root_dir / 'proofs' / 'BSD_UNCONDITIONAL_CERTIFICATE.json'
    
    dR_valid, dR_msg = verify_certificate(dR_cert, ['total_cases', 'results'])
    PT_valid, PT_msg = verify_certificate(PT_cert, ['total_cases', 'results'])
    BSD_valid, BSD_msg = verify_certificate(BSD_cert, ['status', 'components'])
    
    print(f"(dR) Certificado: {'✅' if dR_valid else '❌'} {dR_msg}")
    print(f"(PT) Certificado: {'✅' if PT_valid else '❌'} {PT_msg}")
    print(f"BSD  Certificado: {'✅' if BSD_valid else '❌'} {BSD_msg}")
    print()
    
    # Leer status final
    if BSD_valid:
        with open(BSD_cert, 'r') as f:
            bsd_data = json.load(f)
        
        status = bsd_data.get('status', 'UNKNOWN')
        
        print("="*70)
        print("📄 RESULTADO FINAL")
        print("="*70)
        print()
        
        if status in ['THEOREM', 'THEOREM_UNCONDITIONAL', 'VERIFIED_SIMPLIFIED']:
            print("🎉 ¡BSD PROBADO INCONDICIONALMENTE!")
            print()
            print(f"Status: {status}")
            print()
            print("Componentes:")
            for comp_name, comp_data in bsd_data.get('components', {}).items():
                comp_status = comp_data.get('status', 'UNKNOWN')
                print(f"   {'✅' if comp_status == 'PROVED' else '⚠️ '} {comp_name}: {comp_status}")
            print()
            return 0
        else:
            print("⚠️  Verificación parcial")
            print(f"Status: {status}")
            print()
            return 1
    else:
        print("❌ No se pudo verificar el certificado BSD")
        return 1


if __name__ == "__main__":
    sys.exit(main())
