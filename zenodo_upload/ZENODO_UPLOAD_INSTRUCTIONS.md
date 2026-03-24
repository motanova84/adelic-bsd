
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
