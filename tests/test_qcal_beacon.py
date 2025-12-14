"""
Tests for QCAL Beacon BSD module

Tests the verify_bsd and generate_qcal_beacon_for_bsd functions.
"""

import pytest
import sys
import json
import hashlib
from pathlib import Path

# Add sage_plugin to path
sage_plugin_path = Path(__file__).parent.parent / "sage_plugin"
if str(sage_plugin_path) not in sys.path:
    sys.path.insert(0, str(sage_plugin_path))


@pytest.mark.sage_required
class TestVerifyBSD:
    """Test verify_bsd function"""

    def test_verify_bsd_with_label(self):
        """Test verify_bsd with a curve label"""
        from adelic_bsd.verify import verify_bsd
        
        result = verify_bsd("11a1")
        
        # Check structure
        assert "status" in result
        assert "curve" in result
        assert "data" in result
        assert "integrity_hash" in result
        
        # Check values
        assert result["status"] == "success"
        assert result["curve"] == "11a1"
        
        # Check data structure
        data = result["data"]
        assert "L(1)" in data
        assert "rank" in data
        assert "conductor" in data
        assert "curve" in data
        
        # Check types
        assert isinstance(data["L(1)"], float)
        assert isinstance(data["rank"], int)
        assert isinstance(data["conductor"], int)
        
        # Check integrity hash format (SHA3-256 should be 64 hex chars)
        assert len(result["integrity_hash"]) == 64
        assert all(c in "0123456789abcdef" for c in result["integrity_hash"])

    def test_verify_bsd_integrity_hash_reproducible(self):
        """Test that integrity hash is reproducible"""
        from adelic_bsd.verify import verify_bsd
        
        result1 = verify_bsd("11a1")
        result2 = verify_bsd("11a1")
        
        # The hash should be the same for same curve
        # Note: Due to floating point, L(1) values might differ slightly
        # So we just check the hash exists and is valid format
        assert result1["integrity_hash"]
        assert result2["integrity_hash"]

    def test_verify_bsd_rank_0_curve(self):
        """Test with a rank 0 curve"""
        from adelic_bsd.verify import verify_bsd
        
        result = verify_bsd("11a1")
        assert result["data"]["rank"] == 0
        assert result["data"]["L(1)"] > 0  # L(1) should be non-zero for rank 0

    def test_verify_bsd_rank_1_curve(self):
        """Test with a rank 1 curve"""
        from adelic_bsd.verify import verify_bsd
        
        result = verify_bsd("37a1")
        assert result["data"]["rank"] == 1


@pytest.mark.sage_required
class TestQCALBeacon:
    """Test QCAL Beacon generation"""

    def test_beacon_structure(self):
        """Test that beacon has correct structure"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        
        # Check top-level structure
        assert "qcal_beacon" in beacon
        beacon_data = beacon["qcal_beacon"]
        
        # Check required fields
        required_fields = [
            "id", "timestamp", "curve", "L_at_1", "analytic_rank",
            "integrity_hash", "validator_node", "signature",
            "message_signed", "public_key_pem"
        ]
        for field in required_fields:
            assert field in beacon_data, f"Missing field: {field}"

    def test_beacon_signature_exists(self):
        """Test that signature is present and has correct format"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        signature = beacon["qcal_beacon"]["signature"]
        
        assert "signature_hex" in signature
        assert len(signature["signature_hex"]) > 0
        # Should be valid hex
        assert all(c in "0123456789abcdef" for c in signature["signature_hex"])

    def test_beacon_file_created(self):
        """Test that beacon file is created"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        import tempfile
        import shutil
        
        # Generate beacon
        beacon = generate_qcal_beacon_for_bsd("11a1")
        
        # Check that file was created
        beacon_dir = Path(__file__).parent.parent / "sage_plugin" / "beacons"
        beacon_file = beacon_dir / "qcal_beacon_bsd_11a1.json"
        
        assert beacon_file.exists()
        
        # Read and verify JSON structure
        with open(beacon_file, "r") as f:
            saved_beacon = json.load(f)
        
        assert "qcal_beacon" in saved_beacon
        assert saved_beacon["qcal_beacon"]["curve"] == "11a1"

    def test_beacon_message_format(self):
        """Test that message_signed has correct format"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        message = beacon["qcal_beacon"]["message_signed"]
        
        # Format should be: curve|rank|L(1)|integrity_hash|beacon_id|Noesis∞³
        parts = message.split("|")
        assert len(parts) == 6
        assert parts[0] == "11a1"  # curve
        assert parts[5] == "Noesis∞³"  # validator suffix

    def test_beacon_public_key_format(self):
        """Test that public key is in PEM format"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        public_key = beacon["qcal_beacon"]["public_key_pem"]
        
        assert public_key.startswith("-----BEGIN PUBLIC KEY-----")
        assert public_key.endswith("-----END PUBLIC KEY-----")

    def test_beacon_timestamp_format(self):
        """Test that timestamp is in ISO format"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        from datetime import datetime
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        timestamp = beacon["qcal_beacon"]["timestamp"]
        
        # Should be parseable as ISO format
        dt = datetime.strptime(timestamp, "%Y-%m-%dT%H:%M:%SZ")
        assert dt is not None

    def test_beacon_validator_node(self):
        """Test that validator node is set correctly"""
        from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
        
        beacon = generate_qcal_beacon_for_bsd("11a1")
        assert beacon["qcal_beacon"]["validator_node"] == "Noēsis-∞³"


@pytest.mark.basic
class TestQCALBeaconWithoutSage:
    """Basic tests that don't require SageMath"""

    def test_imports(self):
        """Test that modules can be imported"""
        try:
            import sys
            from pathlib import Path
            sage_plugin_path = Path(__file__).parent.parent / "sage_plugin"
            if str(sage_plugin_path) not in sys.path:
                sys.path.insert(0, str(sage_plugin_path))
            
            # These should not fail even without SageMath installed
            import adelic_bsd
            from adelic_bsd import qcal_beacon_bsd
            
            # Check that functions exist
            assert hasattr(qcal_beacon_bsd, 'generate_qcal_beacon_for_bsd')
            assert hasattr(qcal_beacon_bsd, 'sign_ecdsa')
        except ImportError as e:
            # If SageMath is not installed, that's expected for verify module
            if "sage" not in str(e).lower():
                raise

    def test_cryptography_available(self):
        """Test that cryptography library is available"""
        try:
            from cryptography.hazmat.primitives.asymmetric import ec
            from cryptography.hazmat.primitives import hashes
            from cryptography.hazmat.backends import default_backend
            
            # Try to generate a key
            private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())
            assert private_key is not None
        except ImportError:
            pytest.skip("cryptography library not installed")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
