#!/usr/bin/env python3
"""
Script para Identificar y Completar Pruebas Incompletas en Lean 4

Este script mapea todas las pruebas pendientes (marcadas con 'sorry') en el
proyecto de formalización Lean 4 y genera un reporte de prioridades.
Script para guiar la completación de pruebas Lean 4

Este script:
1. Encuentra todas las ubicaciones de 'sorry' en el código Lean
2. Genera templates de prueba para completar
3. Prioriza qué pruebas completar primero
4. Genera un reporte detallado

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
import json
import re
from pathlib import Path
from typing import List, Dict, Optional


def find_sorry_locations(lean_dir: str = "formalization/lean") -> List[Dict]:
    """
    Encuentra todas las ubicaciones de 'sorry' en el código Lean
    
    Args:
        lean_dir: Directorio raíz de formalizaciones Lean
    
    Returns:
        List[Dict]: Lista de ubicaciones con contexto
    """
    lean_path = Path(lean_dir)
    
    if not lean_path.exists():
        print(f"⚠️  Directorio {lean_dir} no encontrado")
        return []
    
    sorry_locations = []
    
    for lean_file in lean_path.rglob("*.lean"):
        with open(lean_file, 'r', encoding='utf-8') as f:
            for i, line in enumerate(f, 1):
                if "sorry" in line:
                    sorry_locations.append({
                        "file": str(lean_file),
                        "line": i,
                        "context": line.strip()
                    })
    
    return sorry_locations


def extract_theorem_name(file_path: str, line_num: int) -> Optional[str]:
    """
    Extrae el nombre del teorema que contiene un 'sorry'
    
    Args:
        file_path: Ruta al archivo Lean
        line_num: Número de línea del sorry
    
    Returns:
        Optional[str]: Nombre del teorema o None
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    # Buscar hacia atrás desde el sorry
    for i in range(line_num - 1, max(0, line_num - 30), -1):
        line = lines[i]
        
        # Buscar declaraciones de teorema/lemma
        match = re.search(r'(theorem|lemma|axiom)\s+(\w+)', line)
        if match:
            return match.group(2)
    
    return None


def generate_proof_template(sorry_location: Dict) -> str:
    """
    Genera un template de prueba para completar un 'sorry'
    
    Args:
        sorry_location: Diccionario con información del sorry
    
    Returns:
        str: Template de prueba
    """
    file_path = sorry_location['file']
    line_num = sorry_location['line']
    
    theorem_name = extract_theorem_name(file_path, line_num)
    
    if not theorem_name:
        theorem_name = "unknown_theorem"
    
    template = f"""
-- TODO: Complete proof for {Path(file_path).name}:{line_num}
-- Theorem: {theorem_name}

/-
Estrategia sugerida para completar '{theorem_name}':

1. Identificar hipótesis disponibles en el contexto
2. Buscar lemas existentes en Mathlib que puedan aplicarse
3. Si el resultado es conocido matemáticamente pero difícil de probar:
   - Considerar axiomatizarlo temporalmente con referencia bibliográfica
   - Marcar para completación futura
4. Validar con 'lake build' (si Lean está configurado)

Pasos típicos:
  intro        -- Introducir variables
  apply        -- Aplicar lema existente
  exact        -- Dar prueba exacta
  rw [...]     -- Reescribir usando ecuaciones
  simp         -- Simplificar
  norm_num     -- Normalizar números
  ring         -- Para álgebra de anillos
  linarith     -- Para aritmética lineal

Referencias útiles:
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Lean manual: https://leanprover.github.io/theorem_proving_in_lean4/
-/

-- Reemplazar el 'sorry' original con:
-- by
--   <tácticas aquí>
--   sorry  -- Temporalmente, hasta completar cada paso
"""
    
    return template


def prioritize_proofs(sorry_locations: List[Dict]) -> List[Dict]:
    """
    Prioriza qué pruebas completar primero
    
    Orden de prioridad:
    1. Constants.lean (fundamentos)
    2. Zeta.lean (teoría de números)
    3. Emergence.lean (resultados principales)
    4. Otros archivos
    
    Args:
        sorry_locations: Lista de ubicaciones de sorry
    
    Returns:
        List[Dict]: Lista ordenada por prioridad
    """
    priorities = {
        "Constants.lean": 1,
        "Zeta.lean": 2,
        "Emergence.lean": 3,
    }
    
    def get_priority(loc):
        filename = Path(loc['file']).name
        return priorities.get(filename, 99)
    
    return sorted(sorry_locations, key=get_priority)


def generate_completion_report(sorry_locations: List[Dict], output_path: str = None) -> Dict:
    """
    Genera un reporte detallado de completación de pruebas
    
    Args:
        sorry_locations: Lista de ubicaciones de sorry
        output_path: Ruta opcional para guardar el reporte
    
    Returns:
        Dict: Reporte de completación
    """
    prioritized = prioritize_proofs(sorry_locations)
    
    # Agrupar por archivo
    by_file = {}
    for loc in prioritized:
        filename = Path(loc['file']).name
        if filename not in by_file:
            by_file[filename] = []
        by_file[filename].append(loc)
    
    report = {
        "total_sorry": len(sorry_locations),
        "files_affected": len(by_file),
        "by_file": {},
        "prioritized_locations": []
    }
    
    # Información por archivo
    for filename, locs in by_file.items():
        report["by_file"][filename] = {
            "count": len(locs),
            "lines": [loc['line'] for loc in locs]
        }
    
    # Lista priorizada
    for i, loc in enumerate(prioritized, 1):
        theorem = extract_theorem_name(loc['file'], loc['line'])
        report["prioritized_locations"].append({
            "priority": i,
            "file": loc['file'],
            "line": loc['line'],
            "theorem": theorem,
            "context": loc['context']
        })
    
    # Calcular porcentaje de completación
    # (Asumimos que 0 sorry = 100%)
    if len(sorry_locations) == 0:
        report["completion_percentage"] = 100
    else:
        # Placeholder: se actualizará conforme se completen pruebas
        report["completion_percentage"] = 0
    
    # Guardar reporte si se especifica ruta
    if output_path:
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        print(f"\n📄 Reporte guardado en: {output_path}")
    
    return report


def main():
    """
    Función principal
    """
    print("=" * 70)
    print("🔍 ANÁLISIS DE FORMALIZACIONES LEAN 4")
    print("   Búsqueda de pruebas incompletas (sorry)")
    print("=" * 70)
    print()
    
    # Encontrar sorry
    sorry_locs = find_sorry_locations()
    
    if not sorry_locs:
        print("✅ ¡No se encontraron 'sorry'!")
        print("   Todas las formalizaciones están completas.")
        return {
            "status": "complete",
            "total_sorry": 0
        }
    
    print(f"⚠️  Encontrados {len(sorry_locs)} 'sorry' pendientes:\n")
    
    # Priorizar
    prioritized = prioritize_proofs(sorry_locs)
    
    # Mostrar lista priorizada
    for i, loc in enumerate(prioritized, 1):
        theorem = extract_theorem_name(loc['file'], loc['line'])
        filename = Path(loc['file']).name
        
        print(f"{i}. {filename}:{loc['line']}")
        if theorem:
            print(f"   Teorema: {theorem}")
        print(f"   Contexto: {loc['context']}")
        print()
    
    # Generar templates
    templates_dir = Path("formalization/lean/templates")
    templates_dir.mkdir(parents=True, exist_ok=True)
    
    print("📝 Generando templates de prueba...")
    for i, loc in enumerate(prioritized[:5], 1):  # Primeros 5
        template = generate_proof_template(loc)
        template_path = templates_dir / f"proof_template_{i}.lean"
        
        with open(template_path, 'w', encoding='utf-8') as f:
            f.write(template)
        
        print(f"   ✓ {template_path}")
    
    # Generar reporte
    report_path = Path("formalization/lean/PROOF_COMPLETION_REPORT.json")
    report = generate_completion_report(sorry_locs, str(report_path))
    
    # Resumen final
    print("\n" + "=" * 70)
    print("📊 RESUMEN")
    print("=" * 70)
    print(f"\n   Total de 'sorry': {report['total_sorry']}")
    print(f"   Archivos afectados: {report['files_affected']}")
    print(f"   Completación: {report['completion_percentage']}%")
    
    print(f"\n📋 Distribución por archivo:")
    for filename, info in report['by_file'].items():
        print(f"   • {filename}: {info['count']} sorry")
    
    print(f"\n💡 Próximos pasos:")
    print(f"   1. Revisar templates en: formalization/lean/templates/")
    print(f"   2. Completar pruebas en orden de prioridad")
    print(f"   3. Ejecutar 'lake build' para validar (si Lean está configurado)")
    print(f"   4. Actualizar reporte de progreso")
    
    print("\n" + "=" * 70)
    
    return report


if __name__ == "__main__":
    report = main()
