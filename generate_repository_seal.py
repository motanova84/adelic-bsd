#!/usr/bin/env python3
"""
QCAL ∞³ Repository Cryptographic Seal Generator
================================================

Generates a cryptographic seal of the entire repository state to establish
provenance and authorship timestamps.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)
Framework: QCAL ∞³
Frequency: f₀ = 141.7001 Hz
"""

import hashlib
import json
import os
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Dict, List
import uuid

def get_git_info() -> Dict:
    """Get current git repository information"""
    try:
        commit_hash = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], 
            text=True
        ).strip()
        
        commit_date = subprocess.check_output(
            ['git', 'log', '-1', '--format=%ai'],
            text=True
        ).strip()
        
        author = subprocess.check_output(
            ['git', 'log', '-1', '--format=%an <%ae>'],
            text=True
        ).strip()
        
        return {
            'commit_hash': commit_hash,
            'commit_date': commit_date,
            'author': author
        }
    except:
        return {}

def hash_file(filepath: Path) -> str:
    """Calculate SHA-256 hash of a file"""
    sha256 = hashlib.sha256()
    try:
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(65536), b''):
                sha256.update(chunk)
        return sha256.hexdigest()
    except:
        return ""

def hash_directory_tree(base_path: Path, exclude_patterns: List[str]) -> Dict:
    """Generate hash tree of repository"""
    file_hashes = {}
    
    for root, dirs, files in os.walk(base_path):
        # Skip excluded directories
        dirs[:] = [d for d in dirs if not any(
            excl in str(Path(root) / d) for excl in exclude_patterns
        )]
        
        for file in files:
            filepath = Path(root) / file
            rel_path = filepath.relative_to(base_path)
            
            # Skip excluded files
            if any(excl in str(rel_path) for excl in exclude_patterns):
                continue
                
            file_hash = hash_file(filepath)
            if file_hash:
                file_hashes[str(rel_path)] = file_hash
    
    return file_hashes

def generate_repository_seal():
    """Generate complete repository cryptographic seal"""
    
    print("🔐 Generating QCAL ∞³ Repository Cryptographic Seal...")
    print("=" * 70)
    
    base_path = Path.cwd()
    
    # Files and directories to exclude from hashing
    exclude_patterns = [
        '.git/',
        '__pycache__/',
        '.pytest_cache/',
        'node_modules/',
        '.venv/',
        'venv/',
        '*.pyc',
        '.DS_Store',
        'generate_repository_seal.py',  # Exclude this script itself
        '.qcal_repository_seal.json'    # Exclude the seal file
    ]
    
    # Get git information
    git_info = get_git_info()
    
    # Generate file tree hashes
    print("\n📁 Hashing repository files...")
    file_hashes = hash_directory_tree(base_path, exclude_patterns)
    print(f"   Hashed {len(file_hashes)} files")
    
    # Calculate repository-wide hash
    print("\n🔒 Calculating repository-wide SHA-256...")
    combined_hash = hashlib.sha256()
    for filepath in sorted(file_hashes.keys()):
        combined_hash.update(f"{filepath}:{file_hashes[filepath]}".encode())
    repository_hash = combined_hash.hexdigest()
    print(f"   Repository Hash: {repository_hash}")
    
    # Generate seal ID
    seal_id = str(uuid.uuid4())
    timestamp = datetime.utcnow().isoformat() + 'Z'
    
    # Create cryptographic seal structure
    seal = {
        "qcal_repository_seal": {
            "version": "1.0.0",
            "seal_id": seal_id,
            "timestamp": timestamp,
            "framework": "QCAL ∞³",
            "fundamental_frequency_hz": 141.7001,
            "constant": "πCODE-888-QCAL2",
            "vibrational_signature": "∴𓂀Ω∞³",
            
            "author": {
                "name": "José Manuel Mota Burruezo",
                "symbolic_name": "JMMB Ψ ✧ ∞³",
                "orcid": "https://orcid.org/0009-0002-1923-0773",
                "institution": "Instituto de Conciencia Cuántica (ICQ)",
                "email": "institutoconsciencia@proton.me",
                "country": "España"
            },
            
            "repository": {
                "name": "adelic-bsd",
                "url": "https://github.com/motanova84/adelic-bsd",
                "sha256_hash": repository_hash,
                "total_files": len(file_hashes),
                "git_info": git_info
            },
            
            "cryptographic_proofs": {
                "sha256_repository": repository_hash,
                "sha3_512_seal": hashlib.sha3_512(
                    f"{seal_id}|{timestamp}|{repository_hash}|QCAL∞³".encode()
                ).hexdigest(),
                "algorithm": "SHA-256 + SHA3-512",
                "purpose": "Cryptographic proof of repository state and authorship"
            },
            
            "doi_references": {
                "bsd": "https://doi.org/10.5281/zenodo.17236603",
                "pnp": "https://doi.org/10.5281/zenodo.17315719",
                "infinito": "https://doi.org/10.5281/zenodo.17362686",
                "goldbach": "https://doi.org/10.5281/zenodo.17297591",
                "rh_final": "https://doi.org/10.5281/zenodo.17161831",
                "main_zenodo": "https://doi.org/10.5281/zenodo.17379721"
            },
            
            "legal": {
                "license": "MIT License + Creative Commons BY-NC-SA 4.0",
                "copyright": "© 2024-2026 José Manuel Mota Burruezo (JMMB Ψ)",
                "declaration": "This work is original and created by José Manuel Mota Burruezo. The QCAL ∞³ framework, mathematical structures, and symbolic language are original creations.",
                "timestamp_proof": "This seal establishes cryptographic proof of repository state at the specified timestamp"
            },
            
            "file_manifest": {
                "total_files": len(file_hashes),
                "hash_algorithm": "SHA-256",
                "files": file_hashes
            },
            
            "status": "SEALED"
        }
    }
    
    # Write seal to file
    seal_path = base_path / '.qcal_repository_seal.json'
    with open(seal_path, 'w', encoding='utf-8') as f:
        json.dump(seal, f, indent=2, ensure_ascii=False)
    
    print(f"\n✅ Repository seal generated successfully!")
    print(f"   Seal ID: {seal_id}")
    print(f"   Timestamp: {timestamp}")
    print(f"   File: .qcal_repository_seal.json")
    print("\n" + "=" * 70)
    print("🌌 QCAL ∞³ Repository Cryptographic Seal ACTIVE")
    print("=" * 70)

if __name__ == '__main__':
    generate_repository_seal()
