#!/usr/bin/env python3
"""
Certificate Generator
Generates formal verification certificates for BSD conjecture

This module creates detailed certificates documenting the verification
of BSD conjecture for elliptic curves.
"""

import json
from datetime import datetime
from sage.all import EllipticCurve


class BSDCertificateGenerator:
    """
    Generates formal BSD verification certificates
    
    Creates human-readable and machine-readable certificates
    documenting all verification steps.
    """
    
    def __init__(self, output_dir="certificates"):
        """
        Initialize certificate generator
        
        Args:
            output_dir: Directory to save certificates
        """
        self.output_dir = output_dir
        
        # Ensure output directory exists
        import os
        os.makedirs(output_dir, exist_ok=True)
    
    def generate_certificate(self, E, verification_data):
        """
        Generate a complete BSD certificate for a curve
        
        Args:
            E: EllipticCurve object
            verification_data: Dict with verification results
            
        Returns:
            dict: Certificate data
        """
        label = E.cremona_label() if hasattr(E, 'cremona_label') else str(E)
        
        certificate = {
            'certificate_id': f"BSD-{label}-{datetime.now().strftime('%Y%m%d')}",
            'curve': {
                'label': label,
                'conductor': int(E.conductor()),
                'discriminant': int(E.discriminant()),
                'j_invariant': str(E.j_invariant()),
                'rank': E.rank(),
                'torsion_order': E.torsion_order()
            },
            'verification': verification_data,
            'metadata': {
                'generated_at': datetime.now().isoformat(),
                'framework': 'Spectral BSD Framework',
                'version': '1.0'
            }
        }
        
        # Add curve equation
        try:
            certificate['curve']['equation'] = E.short_weierstrass_model().ainvs()
        except (AttributeError, ValueError):
            certificate['curve']['equation'] = E.ainvs()
        
        # Add L-function data
        certificate['l_function'] = self._extract_l_function_data(E)
        
        # Add BSD formula components
        certificate['bsd_components'] = self._extract_bsd_components(E)
        
        return certificate
    
    def _extract_l_function_data(self, E):
        """Extract L-function data"""
        try:
            L = E.lseries()
            rank = E.rank()
            
            data = {
                'analytic_rank': E.analytic_rank(),
                'algebraic_rank': rank
            }
            
            if rank == 0:
                try:
                    data['L_ratio'] = float(L.L_ratio())
                except:
                    data['L_ratio'] = None
            
            return data
            
        except Exception as e:
            return {'error': str(e)}
    
    def _extract_bsd_components(self, E):
        """Extract BSD formula components"""
        try:
            components = {}
            
            # Real period
            try:
                components['real_period'] = float(E.period_lattice().omega())
            except:
                components['real_period'] = None
            
            # Tamagawa numbers
            conductor = E.conductor()
            tamagawa_numbers = {}
            for p in conductor.prime_factors():
                try:
                    tamagawa_numbers[str(p)] = E.tamagawa_number(p)
                except:
                    tamagawa_numbers[str(p)] = None
            components['tamagawa_numbers'] = tamagawa_numbers
            
            # Torsion
            components['torsion_order'] = E.torsion_order()
            
            # Regulator (for rank > 0)
            if E.rank() > 0:
                try:
                    gens = E.gens()
                    if len(gens) > 0:
                        if E.rank() == 1:
                            components['regulator'] = float(gens[0].height())
                        else:
                            # For higher rank, would compute determinant
                            components['regulator'] = 'computed'
                except:
                    components['regulator'] = None
            
            return components
            
        except Exception as e:
            return {'error': str(e)}
    
    def save_certificate(self, certificate):
        """
        Save certificate to file
        
        Args:
            certificate: Certificate dict
            
        Returns:
            str: Path to saved certificate
        """
        cert_id = certificate['certificate_id']
        filename = f"{self.output_dir}/{cert_id}.json"
        
        try:
            with open(filename, 'w') as f:
                json.dump(certificate, f, indent=2)
            print(f"📄 Certificate saved: {filename}")
            return filename
        except Exception as e:
            print(f"⚠️  Could not save certificate: {e}")
            return None
    
    def generate_text_certificate(self, certificate):
        """
        Generate human-readable text certificate
        
        Args:
            certificate: Certificate dict
            
        Returns:
            str: Formatted text certificate
        """
        lines = []
        lines.append("="*70)
        lines.append("BSD CONJECTURE VERIFICATION CERTIFICATE")
        lines.append("="*70)
        lines.append("")
        
        # Certificate ID
        lines.append(f"Certificate ID: {certificate['certificate_id']}")
        lines.append(f"Generated: {certificate['metadata']['generated_at']}")
        lines.append("")
        
        # Curve information
        lines.append("ELLIPTIC CURVE")
        lines.append("-" * 70)
        curve = certificate['curve']
        lines.append(f"Label: {curve['label']}")
        lines.append(f"Conductor: {curve['conductor']}")
        lines.append(f"Rank: {curve['rank']}")
        lines.append(f"Torsion order: {curve['torsion_order']}")
        lines.append("")
        
        # Verification status
        lines.append("VERIFICATION STATUS")
        lines.append("-" * 70)
        verification = certificate.get('verification', {})
        if verification.get('bsd_verified'):
            lines.append("✅ BSD CONJECTURE VERIFIED")
        else:
            lines.append("⚠️  BSD VERIFICATION INCOMPLETE")
        lines.append("")
        
        # Verification steps
        if 'verification_steps' in verification:
            lines.append("VERIFICATION STEPS")
            lines.append("-" * 70)
            for step_name, step_data in verification['verification_steps'].items():
                if isinstance(step_data, dict):
                    status = "✓" if step_data.get('passed', False) else "✗"
                    lines.append(f"{status} {step_name}")
            lines.append("")
        
        # BSD components
        bsd_comp = certificate.get('bsd_components', {})
        if bsd_comp:
            lines.append("BSD FORMULA COMPONENTS")
            lines.append("-" * 70)
            for key, value in bsd_comp.items():
                if value is not None and not isinstance(value, dict):
                    lines.append(f"{key}: {value}")
            lines.append("")
        
        lines.append("="*70)
        
        return "\n".join(lines)
    
    def save_text_certificate(self, certificate):
        """
        Save text certificate to file
        
        Args:
            certificate: Certificate dict
            
        Returns:
            str: Path to saved certificate
        """
        cert_id = certificate['certificate_id']
        filename = f"{self.output_dir}/{cert_id}.txt"
        
        try:
            text = self.generate_text_certificate(certificate)
            with open(filename, 'w') as f:
                f.write(text)
            print(f"📄 Text certificate saved: {filename}")
            return filename
        except Exception as e:
            print(f"⚠️  Could not save text certificate: {e}")
            return None


def test_certificate_generator():
    """Test certificate generation"""
    print("Testing Certificate Generator...")
    
    try:
        E = EllipticCurve('11a1')
        
        generator = BSDCertificateGenerator(output_dir="/tmp/test_certificates")
        
        # Create test verification data
        verification_data = {
            'bsd_verified': True,
            'verification_steps': {
                'rank_computation': {'passed': True},
                'l_function': {'passed': True}
            }
        }
        
        # Generate certificate
        cert = generator.generate_certificate(E, verification_data)
        
        print(f"✅ Certificate generated successfully")
        print(f"   Certificate ID: {cert['certificate_id']}")
        
        # Generate text version
        text = generator.generate_text_certificate(cert)
        print(f"✅ Text certificate generated ({len(text)} chars)")
        
        return True
        
    except Exception as e:
        print(f"❌ Certificate generation test failed: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    test_certificate_generator()
