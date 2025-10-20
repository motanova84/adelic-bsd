"""
Certificate Generator
Generates formal verification certificates for BSD proofs

This module creates, saves, and validates certificates for
BSD conjecture verification results.
"""

from sage.all import EllipticCurve
import json
import os
from datetime import datetime
import hashlib


class CertificateGenerator:
    """
    Certificate Generator for BSD Verification
    
    Creates formal certificates documenting:
    - Curve properties
    - Verification steps
    - Proof results
    - Computational evidence
    """
    
    def __init__(self, output_dir='certificates'):
        """
        Initialize certificate generator
        
        Args:
            output_dir: Directory to save certificates (default: 'certificates')
        """
        self.output_dir = output_dir
        
        # Create directory if it doesn't exist
        os.makedirs(output_dir, exist_ok=True)
    
    def generate_certificate(self, E, verification_data, format='json'):
        """
        Generate verification certificate for curve E
        
        Args:
            E: EllipticCurve object
            verification_data: Dict with verification results
            format: Output format ('json', 'text', 'latex') (default: 'json')
            
        Returns:
            dict: Certificate data
        """
        # Build certificate structure
        certificate = {
            'metadata': self._generate_metadata(E),
            'curve_data': self._extract_curve_data(E),
            'verification': verification_data,
            'timestamp': datetime.now().isoformat(),
            'format_version': '1.0'
        }
        
        # Add hash for integrity
        certificate['certificate_hash'] = self._compute_hash(certificate)
        
        return certificate
    
    def _generate_metadata(self, E):
        """Generate certificate metadata"""
        return {
            'generator': 'adelic-bsd-framework',
            'version': '0.2.0',
            'curve_label': E.cremona_label() if hasattr(E, 'cremona_label') else str(E),
            'generated_at': datetime.now().isoformat()
        }
    
    def _extract_curve_data(self, E):
        """Extract relevant curve data"""
        return {
            'label': E.cremona_label() if hasattr(E, 'cremona_label') else str(E),
            'conductor': int(E.conductor()),
            'discriminant': int(E.discriminant()),
            'j_invariant': str(E.j_invariant()),
            'rank': E.rank(),
            'torsion_order': E.torsion_order(),
            'ainvariants': [int(a) for a in E.ainvariants()]
        }
    
    def _compute_hash(self, certificate):
        """Compute SHA256 hash of certificate for integrity"""
        # Remove hash field if present
        cert_copy = {k: v for k, v in certificate.items() if k != 'certificate_hash'}
        
        # Convert to JSON and hash
        cert_json = json.dumps(cert_copy, sort_keys=True)
        hash_obj = hashlib.sha256(cert_json.encode('utf-8'))
        
        return hash_obj.hexdigest()
    
    def save_certificate(self, certificate, filename=None, format='json'):
        """
        Save certificate to file
        
        Args:
            certificate: Certificate dict
            filename: Output filename (auto-generated if None)
            format: Output format ('json', 'text')
            
        Returns:
            str: Path to saved certificate
        """
        # Auto-generate filename if not provided
        if filename is None:
            curve_label = certificate['curve_data']['label']
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f"certificate_{curve_label}_{timestamp}.{format}"
        
        filepath = os.path.join(self.output_dir, filename)
        
        # Save based on format
        if format == 'json':
            with open(filepath, 'w') as f:
                json.dump(certificate, f, indent=2)
        elif format == 'text':
            with open(filepath, 'w') as f:
                f.write(self._format_as_text(certificate))
        else:
            raise ValueError(f"Unsupported format: {format}")
        
        return filepath
    
    def _format_as_text(self, certificate):
        """Format certificate as human-readable text"""
        lines = []
        lines.append("=" * 70)
        lines.append("BSD VERIFICATION CERTIFICATE")
        lines.append("=" * 70)
        lines.append("")
        
        # Metadata
        lines.append("METADATA:")
        for key, value in certificate['metadata'].items():
            lines.append(f"  {key}: {value}")
        lines.append("")
        
        # Curve data
        lines.append("CURVE DATA:")
        for key, value in certificate['curve_data'].items():
            lines.append(f"  {key}: {value}")
        lines.append("")
        
        # Verification results
        lines.append("VERIFICATION RESULTS:")
        verification = certificate['verification']
        lines.append(f"  BSD Proven: {verification.get('bsd_proven', False)}")
        
        if 'verification_status' in verification:
            lines.append(f"  Status: {verification['verification_status']}")
        
        lines.append("")
        lines.append(f"Certificate Hash: {certificate.get('certificate_hash', 'N/A')}")
        lines.append("=" * 70)
        
        return "\n".join(lines)
    
    def load_certificate(self, filename):
        """
        Load certificate from file
        
        Args:
            filename: Certificate filename
            
        Returns:
            dict: Certificate data
        """
        filepath = os.path.join(self.output_dir, filename)
        
        with open(filepath, 'r') as f:
            certificate = json.load(f)
        
        return certificate
    
    def verify_certificate_integrity(self, certificate):
        """
        Verify certificate hash for integrity
        
        Args:
            certificate: Certificate dict
            
        Returns:
            bool: True if hash is valid
        """
        stored_hash = certificate.get('certificate_hash')
        
        if not stored_hash:
            return False
        
        # Recompute hash
        computed_hash = self._compute_hash(certificate)
        
        return stored_hash == computed_hash
    
    def save_text_certificate(self, certificate, filename=None):
        """
        Save certificate in text format (convenience method)
        
        Args:
            certificate: Certificate dict
            filename: Output filename (auto-generated if None)
            
        Returns:
            str: Path to saved certificate
        """
        return self.save_certificate(certificate, filename=filename, format='text')
    
    def generate_batch_summary(self, certificates):
        """
        Generate summary certificate for batch verification
        
        Args:
            certificates: List of individual certificates
            
        Returns:
            dict: Summary certificate
        """
        total = len(certificates)
        successful = sum(1 for c in certificates 
                        if c.get('verification', {}).get('bsd_proven', False))
        
        summary = {
            'type': 'batch_summary',
            'total_curves': total,
            'successful_verifications': successful,
            'success_rate': f"{(successful/total*100):.1f}%" if total > 0 else "0%",
            'timestamp': datetime.now().isoformat(),
            'individual_certificates': [
                {
                    'curve': c['curve_data']['label'],
                    'bsd_proven': c.get('verification', {}).get('bsd_proven', False),
                    'hash': c.get('certificate_hash')
                }
                for c in certificates
            ]
        }
        
        # Add hash
        summary['summary_hash'] = self._compute_hash(summary)
        
        return summary


def generate_certificate(E, verification_data, save=False, output_dir='certificates'):
    """
    Convenience function to generate certificate
    
    Args:
        E: EllipticCurve
        verification_data: Verification results
        save: Whether to save to file
        output_dir: Output directory
        
    Returns:
        dict: Certificate
    """
    generator = CertificateGenerator(output_dir=output_dir)
    certificate = generator.generate_certificate(E, verification_data)
    
    if save:
        generator.save_certificate(certificate)
    
    return certificate


def save_certificate(certificate, filename=None, output_dir='certificates', format='json'):
    """
    Convenience function to save certificate
    
    Args:
        certificate: Certificate dict
        filename: Output filename
        output_dir: Output directory
        format: Output format
        
    Returns:
        str: Path to saved file
    """
    generator = CertificateGenerator(output_dir=output_dir)
    return generator.save_certificate(certificate, filename=filename, format=format)


__all__ = [
    'CertificateGenerator',
    'generate_certificate',
    'save_certificate'
]
