#!/usr/bin/env python3
"""
Script de configuración del entorno de desarrollo
"""

import os
import sys
import subprocess
import platform


def check_sage_installation():
    """Verificar si SageMath está instalado"""
    try:
        result = subprocess.run(['sage', '--version'], 
                              capture_output=True, text=True)
        if result.returncode == 0:
            print(f"✅ SageMath encontrado: {result.stdout.strip()}")
            return True
        else:
            print("❌ SageMath no encontrado o no funciona")
            return False
    except FileNotFoundError:
        print("❌ SageMath no está instalado")
        return False


def install_basic_dependencies():
    """Instalar dependencias básicas de Python"""
    dependencies = ['numpy', 'scipy', 'matplotlib', 'sympy', 'pytest']
    
    print("📦 Instalando dependencias básicas...")
    for dep in dependencies:
        try:
            subprocess.run([sys.executable, '-m', 'pip', 'install', dep], 
                         check=True, capture_output=True)
            print(f"✅ {dep} instalado")
        except subprocess.CalledProcessError:
            print(f"❌ Error instalando {dep}")


def setup_test_environment():
    """Configurar entorno de pruebas"""
    print("🔧 Configurando entorno de pruebas...")
    
    # Crear directorios necesarios
    os.makedirs('tests', exist_ok=True)
    os.makedirs('certificates', exist_ok=True)
    
    # Verificar estructura
    required_files = [
        'src/spectral_finiteness.py',
        'README.md'
    ]
    
    for file_path in required_files:
        if os.path.exists(file_path):
            print(f"✅ {file_path} encontrado")
        else:
            print(f"❌ {file_path} NO encontrado")


def main():
    """Función principal"""
    print("🎯 CONFIGURACIÓN DEL ENTORNO ADELIC-BSD")
    print("=" * 50)
    
    # Verificar Python
    print(f"🐍 Python: {sys.version}")
    
    # Verificar SageMath
    has_sage = check_sage_installation()
    
    if not has_sage:
        print("\n⚠️  ADVERTENCIA: SageMath no está disponible")
        print("   Los tests matemáticos avanzados fallarán")
        print("   Pero los tests básicos deberían funcionar")
    
    # Instalar dependencias
    install_basic_dependencies()
    
    # Configurar entorno
    setup_test_environment()
    
    print("\n🎉 CONFIGURACIÓN COMPLETADA")
    if has_sage:
        print("✅ Entorno completo listo para desarrollo")
    else:
        print("⚠️  Entorno básico listo (sin SageMath)")


if __name__ == "__main__":
    main()
