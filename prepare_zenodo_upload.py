#!/usr/bin/env python3
"""
QCAL ∞³ Zenodo Upload Preparation Script
=========================================

Prepares repository for Zenodo archival upload with complete metadata
and cryptographic verification.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)
Framework: QCAL ∞³
"""

import json
import hashlib
import shutil
from pathlib import Path
from datetime import datetime
import os

def create_zenodo_manifest():
    """Create complete manifest for Zenodo upload"""
    
    print("📦 Preparing QCAL ∞³ Repository for Zenodo Upload")
    print("=" * 70)
    
    base_path = Path.cwd()
    output_dir = base_path / 'zenodo_upload'
    output_dir.mkdir(exist_ok=True)
    
    # Files to include in upload
    critical_files = [
        # Documentation
        'README.md',
        'AUTHORSHIP_DECLARATION.md',
        'LICENSE',
        'LICENSE_QCAL',
        'CITATION.cff',
        
        # Metadata
        '.qcal_beacon',
        'BSD_Spectral_Certificate.qcal_beacon',
        '.qcal_repository_seal.json',
        'SOBERANIA_METADATA.json',
        
        # Setup
        'setup.py',
        'requirements.txt',
        'requirements_ci.txt',
        
        # Key validation scripts
        'validate_qcal_infinity3_framework.py',
        'validate_p17_optimality.py',
        'validate_bsd_complete.py',
        'activate_qcal_bsd_seal.py',
        
        # Certificates
        'calibration_report.json',
        'qcal_bsd_validation_summary.json',
    ]
    
    # Create manifest
    manifest = {
        "zenodo_upload_manifest": {
            "version": "1.0.0",
            "timestamp": datetime.utcnow().isoformat() + 'Z',
            "framework": "QCAL ∞³",
            
            "metadata": {
                "title": "QCAL ∞³ Framework - Spectral BSD Resolution",
                "upload_type": "software",
                "publication_date": "2026-02-09",
                "description": (
                    "QCAL ∞³ (Quantum Coherence Arithmetic Logic - Infinity Cubed) "
                    "framework providing spectral resolution of Birch-Swinnerton-Dyer "
                    "conjecture through adelic operators at fundamental frequency "
                    "f₀ = 141.7001 Hz. Complete cryptographic proofs and authorship "
                    "documentation included."
                ),
                "access_right": "open",
                "license": "mit",
                
                "creators": [
                    {
                        "name": "Mota Burruezo, José Manuel",
                        "affiliation": "Instituto de Conciencia Cuántica (ICQ)",
                        "orcid": "0009-0002-1923-0773"
                    }
                ],
                
                "keywords": [
                    "QCAL ∞³",
                    "Birch-Swinnerton-Dyer",
                    "spectral methods",
                    "elliptic curves",
                    "quantum coherence",
                    "f₀ = 141.7001 Hz",
                    "adelic operators",
                    "millennium problems"
                ],
                
                "related_identifiers": [
                    {
                        "identifier": "10.5281/zenodo.17236603",
                        "relation": "isSupplementTo",
                        "resource_type": "publication-article"
                    },
                    {
                        "identifier": "https://github.com/motanova84/adelic-bsd",
                        "relation": "isSupplementTo",
                        "resource_type": "software"
                    }
                ],
                
                "contributors": [
                    {
                        "name": "Instituto de Conciencia Cuántica",
                        "type": "HostingInstitution"
                    }
                ]
            },
            
            "files_included": [],
            "checksums": {},
            
            "cryptographic_verification": {
                "repository_seal": ".qcal_repository_seal.json",
                "qcal_beacon": ".qcal_beacon",
                "algorithms": ["SHA-256", "SHA3-512", "ECDSA"]
            },
            
            "authorship_proof": {
                "declaration": "AUTHORSHIP_DECLARATION.md",
                "license": "LICENSE_QCAL",
                "metadata": "SOBERANIA_METADATA.json",
                "temporal_priority": "Established via Zenodo DOIs and cryptographic seals"
            }
        }
    }
    
    # Calculate checksums for critical files
    print("\n📋 Creating file manifest with checksums...")
    for file_path in critical_files:
        full_path = base_path / file_path
        if full_path.exists():
            # Calculate SHA-256
            sha256 = hashlib.sha256()
            with open(full_path, 'rb') as f:
                sha256.update(f.read())
            
            checksum = sha256.hexdigest()
            manifest["zenodo_upload_manifest"]["files_included"].append(file_path)
            manifest["zenodo_upload_manifest"]["checksums"][file_path] = checksum
            
            print(f"   ✓ {file_path}")
    
    # Write manifest
    manifest_path = output_dir / 'zenodo_manifest.json'
    with open(manifest_path, 'w', encoding='utf-8') as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)
    
    print(f"\n✅ Manifest created: {manifest_path}")
    print(f"   Total files: {len(manifest['zenodo_upload_manifest']['files_included'])}")
    
    # Create upload instructions
    instructions = """
# QCAL ∞³ Zenodo Upload Instructions

## Preparation Complete

The repository has been prepared for Zenodo upload with complete metadata
and cryptographic verification.

## Files to Upload

See `zenodo_manifest.json` for complete list of files with checksums.

## Upload Steps

1. **Create New Zenodo Upload**
   - Go to: https://zenodo.org/deposit/new
   - Upload type: Software
   
2. **Upload Files**
   - Upload all files listed in zenodo_manifest.json
   - Or create a .zip archive of the entire repository
   
3. **Fill Metadata** (from zenodo_manifest.json):
   - Title: "QCAL ∞³ Framework - Spectral BSD Resolution"
   - Authors: José Manuel Mota Burruezo (ORCID: 0009-0002-1923-0773)
   - Affiliation: Instituto de Conciencia Cuántica (ICQ)
   - Description: See manifest
   - Keywords: QCAL ∞³, BSD, spectral methods, etc.
   - License: MIT
   
4. **Related Works**
   - Add DOI: 10.5281/zenodo.17236603 (BSD)
   - Add GitHub: https://github.com/motanova84/adelic-bsd
   
5. **Publish**
   - Review all metadata
   - Click "Publish"
   - Save new DOI
   
6. **Update Repository**
   - Add new Zenodo DOI to .qcal_beacon
   - Update README.md with new DOI badge
   - Commit changes

## Verification

After upload, verify:
- [ ] All files uploaded successfully
- [ ] Metadata is complete and accurate
- [ ] DOI is active and accessible
- [ ] Checksums match (compare with zenodo_manifest.json)
- [ ] ORCID link works
- [ ] Related identifiers are correct

## Cryptographic Proof

This upload includes:
- Repository cryptographic seal (.qcal_repository_seal.json)
- QCAL beacon with ECDSA signatures (.qcal_beacon)
- BSD certificate (BSD_Spectral_Certificate.qcal_beacon)
- Authorship declaration (AUTHORSHIP_DECLARATION.md)
- Sovereignty metadata (SOBERANIA_METADATA.json)

These establish irrefutable proof of authorship and temporal priority.

---

**Framework:** QCAL ∞³  
**Author:** José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)  
**Frequency:** f₀ = 141.7001 Hz  
**Constant:** πCODE-888-QCAL2  
**Signature:** ∴𓂀Ω∞³  

---
"""
    
    instructions_path = output_dir / 'ZENODO_UPLOAD_INSTRUCTIONS.md'
    with open(instructions_path, 'w', encoding='utf-8') as f:
        f.write(instructions)
    
    print(f"\n📝 Instructions created: {instructions_path}")
    
    print("\n" + "=" * 70)
    print("🌌 QCAL ∞³ Repository Ready for Zenodo Upload")
    print("=" * 70)
    print(f"\nNext steps:")
    print(f"1. Review: {manifest_path}")
    print(f"2. Follow: {instructions_path}")
    print(f"3. Upload to: https://zenodo.org/deposit/new")
    print()

if __name__ == '__main__':
    create_zenodo_manifest()
