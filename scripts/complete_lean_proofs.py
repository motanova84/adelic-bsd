#!/usr/bin/env python3
"""
Script para Identificar y Completar Pruebas Incompletas en Lean 4

Este script mapea todas las pruebas pendientes (marcadas con 'sorry') en el
proyecto de formalización Lean 4 y genera un reporte de prioridades.

Author: José Manuel Mota Burruezo (JMMB Ψ · ∴)
Date: November 2025
"""

import os
import re
from typing import List, Dict, Tuple
from pathlib import Path
import sys


def find_lean_files(base_dir: str = "formalization/lean") -> List[Path]:
    """
    Encuentra todos los archivos .lean en el directorio de formalización.
    
    Args:
        base_dir: Directorio base para la búsqueda
        
    Returns:
        Lista de rutas a archivos .lean
    """
    lean_dir = Path(base_dir)
    if not lean_dir.exists():
        print(f"⚠️  Directorio {base_dir} no existe")
        return []
    
    return list(lean_dir.rglob("*.lean"))


def extract_sorries(file_path: Path) -> List[Dict[str, any]]:
    """
    Extrae todas las instancias de 'sorry' de un archivo Lean.
    
    Args:
        file_path: Ruta al archivo Lean
        
    Returns:
        Lista de diccionarios con información sobre cada 'sorry'
    """
    sorries = []
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
            
        current_theorem = None
        for i, line in enumerate(lines, 1):
            # Detectar definición de teorema/lema
            theorem_match = re.search(r'(theorem|lemma|def)\s+(\w+)', line)
            if theorem_match:
                current_theorem = theorem_match.group(2)
            
            # Detectar 'sorry'
            if 'sorry' in line.lower():
                sorries.append({
                    'file': file_path.name,
                    'line': i,
                    'theorem': current_theorem,
                    'context': line.strip()
                })
    
    except Exception as e:
        print(f"⚠️  Error leyendo {file_path}: {e}")
    
    return sorries


def analyze_dependencies(lean_files: List[Path]) -> Dict[str, List[str]]:
    """
    Analiza las dependencias entre archivos Lean.
    
    Args:
        lean_files: Lista de archivos Lean
        
    Returns:
        Diccionario de dependencias {archivo: [dependencias]}
    """
    dependencies = {}
    
    for file_path in lean_files:
        deps = []
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # Buscar imports
            imports = re.findall(r'import\s+(\S+)', content)
            deps.extend(imports)
            
        except Exception as e:
            print(f"⚠️  Error analizando dependencias de {file_path}: {e}")
        
        dependencies[file_path.name] = deps
    
    return dependencies


def prioritize_proofs(sorries: List[Dict], dependencies: Dict[str, List[str]]) -> List[Dict]:
    """
    Prioriza las pruebas pendientes según las dependencias.
    
    Archivos fundamentales (sin dependencias internas) tienen mayor prioridad.
    
    Args:
        sorries: Lista de 'sorry' encontrados
        dependencies: Diccionario de dependencias
        
    Returns:
        Lista de 'sorry' ordenada por prioridad
    """
    # Archivos fundamentales (típicamente constantes y definiciones básicas)
    fundamental_files = ['Constants.lean', 'Zeta.lean', 'GoldenRatio.lean']
    
    # Ordenar por prioridad
    prioritized = []
    
    # Prioridad 1: Archivos fundamentales
    for file in fundamental_files:
        prioritized.extend([s for s in sorries if s['file'] == file])
    
    # Prioridad 2: Resto de archivos
    for sorry in sorries:
        if sorry not in prioritized:
            prioritized.append(sorry)
    
    return prioritized


def generate_report(sorries: List[Dict], dependencies: Dict[str, List[str]]) -> str:
    """
    Genera un reporte detallado de las pruebas pendientes.
    
    Args:
        sorries: Lista de 'sorry' encontrados
        dependencies: Diccionario de dependencias
        
    Returns:
        Reporte en formato de texto
    """
    report = []
    report.append("="*70)
    report.append("REPORTE DE PRUEBAS INCOMPLETAS - LEAN 4")
    report.append("="*70)
    report.append(f"\nTotal de 'sorry' encontrados: {len(sorries)}\n")
    
    if not sorries:
        report.append("✅ No se encontraron pruebas incompletas!")
        return "\n".join(report)
    
    # Agrupar por archivo
    by_file = {}
    for sorry in sorries:
        file = sorry['file']
        if file not in by_file:
            by_file[file] = []
        by_file[file].append(sorry)
    
    # Generar reporte por archivo
    report.append("RESUMEN POR ARCHIVO:")
    report.append("-"*70)
    for file, items in sorted(by_file.items()):
        report.append(f"\n{file}: {len(items)} prueba(s) pendiente(s)")
        for item in items:
            theorem = item['theorem'] or 'unknown'
            report.append(f"  Línea {item['line']}: {theorem}")
    
    # Orden de prioridad
    report.append("\n" + "="*70)
    report.append("ORDEN DE COMPLETACIÓN RECOMENDADO:")
    report.append("="*70)
    
    prioritized = prioritize_proofs(sorries, dependencies)
    
    for i, sorry in enumerate(prioritized, 1):
        report.append(f"\n{i}. {sorry['file']} (línea {sorry['line']})")
        report.append(f"   Teorema: {sorry['theorem'] or 'unknown'}")
        report.append(f"   Contexto: {sorry['context'][:60]}...")
    
    return "\n".join(report)


def create_completion_templates(sorries: List[Dict], output_dir: str = "formalization/lean/templates"):
    """
    Crea templates para completar las pruebas pendientes.
    
    Args:
        sorries: Lista de 'sorry' encontrados
        output_dir: Directorio de salida para templates
    """
    templates_path = Path(output_dir)
    templates_path.mkdir(parents=True, exist_ok=True)
    
    for sorry in sorries:
        if not sorry['theorem']:
            continue
            
        template_file = templates_path / f"{sorry['theorem']}_template.lean"
        
        template_content = f"""-- Template para completar: {sorry['theorem']}
-- Archivo original: {sorry['file']} (línea {sorry['line']})
-- 
-- TODO: Implementar la prueba

theorem {sorry['theorem']} : ... := by
  -- Estrategia sugerida:
  -- 1. Identificar hipótesis necesarias
  -- 2. Aplicar lemas relevantes
  -- 3. Construir la prueba paso a paso
  sorry
"""
        
        try:
            with open(template_file, 'w', encoding='utf-8') as f:
                f.write(template_content)
        except Exception as e:
            print(f"⚠️  Error creando template para {sorry['theorem']}: {e}")


def main():
    """Función principal"""
    print("╔" + "="*68 + "╗")
    print("║  MAPEO DE PRUEBAS INCOMPLETAS - LEAN 4                          ║")
    print("║  Framework Espectral Adelico                                    ║")
    print("╚" + "="*68 + "╝\n")
    
    # Buscar archivos Lean
    print("🔍 Buscando archivos .lean...")
    lean_files = find_lean_files()
    
    if not lean_files:
        print("⚠️  No se encontraron archivos .lean")
        print("    Asegúrate de que el directorio formalization/lean existe")
        print("    y contiene archivos .lean")
        return 1
    
    print(f"✅ Encontrados {len(lean_files)} archivo(s) .lean\n")
    
    # Extraer 'sorry'
    print("📋 Extrayendo pruebas incompletas...")
    all_sorries = []
    for file_path in lean_files:
        sorries = extract_sorries(file_path)
        all_sorries.extend(sorries)
        if sorries:
            print(f"   {file_path.name}: {len(sorries)} sorry")
    
    print()
    
    # Analizar dependencias
    print("🔗 Analizando dependencias...")
    dependencies = analyze_dependencies(lean_files)
    print()
    
    # Generar reporte
    report = generate_report(all_sorries, dependencies)
    print(report)
    
    # Guardar reporte
    report_file = Path("formalization") / "incomplete_proofs_report.txt"
    try:
        report_file.parent.mkdir(parents=True, exist_ok=True)
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"\n💾 Reporte guardado en: {report_file}")
    except Exception as e:
        print(f"\n⚠️  Error guardando reporte: {e}")
    
    # Crear templates
    if all_sorries:
        print("\n📝 Creando templates de completación...")
        create_completion_templates(all_sorries)
        print("✅ Templates creados en: formalization/lean/templates/")
    
    return 0 if not all_sorries else 1


if __name__ == "__main__":
    sys.exit(main())
