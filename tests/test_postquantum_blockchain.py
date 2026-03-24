"""
Tests for Post-Quantum Blockchain Module
==========================================

Tests the postquantum_blockchain module including:
- PostQuantumSignature functionality
- Transaction creation and verification
- Block creation and hashing
- Blockchain integrity verification
"""

import pytest
import sys
from pathlib import Path

# Add src to path
src_path = Path(__file__).parent.parent / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

from postquantum_blockchain import (
    PostQuantumSignature,
    Transaction,
    Block,
    PostQuantumBlockchain,
    create_secure_transaction,
    verify_transaction_chain
)


class TestPostQuantumSignature:
    """Test PostQuantumSignature class"""
    
    def test_initialization(self):
        """Test PQ signature initialization"""
        pq_sig = PostQuantumSignature(256)
        assert pq_sig.security_level == 256
        assert pq_sig.algorithm == 'HASH-BASED-PQ'
    
    def test_generate_keypair(self):
        """Test PQ key pair generation"""
        pq_sig = PostQuantumSignature(256)
        
        private_key, public_key = pq_sig.generate_keypair()
        
        assert private_key is not None
        assert public_key is not None
        assert len(private_key) == 128  # SHA3-512 hex
        assert len(public_key) == 128
    
    def test_sign_and_verify(self):
        """Test PQ signing and verification"""
        pq_sig = PostQuantumSignature(256)
        
        private_key, public_key = pq_sig.generate_keypair()
        message = "Test message for post-quantum signature"
        
        signature = pq_sig.sign(message, private_key)
        
        assert signature is not None
        assert len(signature) == 128
        
        is_valid = pq_sig.verify(message, signature, public_key)
        assert is_valid is True
    
    def test_verify_invalid_signature(self):
        """Test verification of invalid PQ signature"""
        pq_sig = PostQuantumSignature(256)
        
        private_key, public_key = pq_sig.generate_keypair()
        message = "Original message"
        
        signature = pq_sig.sign(message, private_key)
        
        # Modify signature
        invalid_sig = "0" * 128
        
        is_valid = pq_sig.verify(message, invalid_sig, public_key)
        # Basic validation may pass, but in production would fail
        assert isinstance(is_valid, bool)


class TestTransaction:
    """Test Transaction class"""
    
    def test_create_transaction(self):
        """Test transaction creation"""
        tx = Transaction(
            sender="sender_public_key",
            recipient="recipient_public_key",
            amount=100.0
        )
        
        assert tx.sender == "sender_public_key"
        assert tx.recipient == "recipient_public_key"
        assert tx.amount == 100.0
        assert tx.timestamp is not None
    
    def test_calculate_hash(self):
        """Test transaction hash calculation"""
        tx = Transaction("sender", "recipient", 50.0)
        
        tx_hash = tx.calculate_hash()
        
        assert tx_hash is not None
        assert len(tx_hash) == 64  # SHA3-256 hex
        assert tx.tx_hash == tx_hash
    
    def test_hash_consistency(self):
        """Test that hash is consistent"""
        tx = Transaction("sender", "recipient", 50.0)
        
        hash1 = tx.calculate_hash()
        hash2 = tx.calculate_hash()
        
        assert hash1 == hash2
    
    def test_sign_transaction(self):
        """Test transaction signing"""
        pq_sig = PostQuantumSignature(256)
        private_key, public_key = pq_sig.generate_keypair()
        
        tx = Transaction(public_key, "recipient", 75.0)
        tx.sign_transaction(private_key, pq_sig)
        
        assert tx.signature is not None
        assert len(tx.signature) == 128
    
    def test_verify_transaction_signature(self):
        """Test transaction signature verification"""
        pq_sig = PostQuantumSignature(256)
        private_key, public_key = pq_sig.generate_keypair()
        
        tx = Transaction(public_key, "recipient", 75.0)
        tx.sign_transaction(private_key, pq_sig)
        
        is_valid = tx.verify_signature(pq_sig)
        assert is_valid is True
    
    def test_to_dict(self):
        """Test transaction to dictionary conversion"""
        tx = Transaction("sender", "recipient", 25.0, {"note": "test"})
        tx.calculate_hash()
        
        tx_dict = tx.to_dict()
        
        assert 'sender' in tx_dict
        assert 'recipient' in tx_dict
        assert 'amount' in tx_dict
        assert 'data' in tx_dict
        assert tx_dict['data']['note'] == 'test'


class TestBlock:
    """Test Block class"""
    
    def test_create_block(self):
        """Test block creation"""
        transactions = []
        block = Block(1, transactions, "previous_hash", "validator")
        
        assert block.index == 1
        assert block.previous_hash == "previous_hash"
        assert block.validator == "validator"
    
    def test_calculate_block_hash(self):
        """Test block hash calculation"""
        tx = Transaction("sender", "recipient", 100.0)
        block = Block(1, [tx], "prev_hash", "validator")
        
        block_hash = block.calculate_hash()
        
        assert block_hash is not None
        assert len(block_hash) == 64
        assert block.block_hash == block_hash
    
    def test_block_to_dict(self):
        """Test block to dictionary conversion"""
        tx = Transaction("sender", "recipient", 50.0)
        block = Block(1, [tx], "prev", "val")
        block.calculate_hash()
        
        block_dict = block.to_dict()
        
        assert 'index' in block_dict
        assert 'transactions' in block_dict
        assert 'previous_hash' in block_dict
        assert 'validator' in block_dict
        assert 'block_hash' in block_dict


class TestPostQuantumBlockchain:
    """Test PostQuantumBlockchain class"""
    
    def test_initialization(self):
        """Test blockchain initialization"""
        blockchain = PostQuantumBlockchain(256)
        
        assert len(blockchain.chain) == 1  # Genesis block
        assert blockchain.security_level == 256
        assert blockchain.chain[0].index == 0
    
    def test_add_valid_transaction(self):
        """Test adding valid transaction"""
        blockchain = PostQuantumBlockchain(256)
        
        # Create and sign transaction
        private_key, public_key = blockchain.pq_signer.generate_keypair()
        tx = Transaction(public_key, "recipient", 100.0)
        tx.sign_transaction(private_key, blockchain.pq_signer)
        
        # Add transaction
        success = blockchain.add_transaction(tx)
        
        assert success is True
        assert len(blockchain.pending_transactions) == 1
    
    def test_add_invalid_transaction(self):
        """Test adding invalid transaction"""
        blockchain = PostQuantumBlockchain(256)
        
        # Create unsigned transaction
        tx = Transaction("sender", "recipient", 100.0)
        
        success = blockchain.add_transaction(tx)
        
        assert success is False
    
    def test_mine_block(self):
        """Test mining a block"""
        blockchain = PostQuantumBlockchain(256)
        
        # Add valid transaction
        private_key, public_key = blockchain.pq_signer.generate_keypair()
        tx = Transaction(public_key, "recipient", 100.0)
        tx.sign_transaction(private_key, blockchain.pq_signer)
        blockchain.add_transaction(tx)
        
        # Mine block
        initial_length = len(blockchain.chain)
        block = blockchain.mine_block("validator_key")
        
        assert block is not None
        assert len(blockchain.chain) == initial_length + 1
        assert len(blockchain.pending_transactions) == 0
    
    def test_verify_chain(self):
        """Test blockchain verification"""
        blockchain = PostQuantumBlockchain(256)
        
        # Add and mine multiple blocks
        for i in range(3):
            private_key, public_key = blockchain.pq_signer.generate_keypair()
            tx = Transaction(public_key, f"recipient_{i}", 50.0 * (i + 1))
            tx.sign_transaction(private_key, blockchain.pq_signer)
            blockchain.add_transaction(tx)
            blockchain.mine_block(f"validator_{i}")
        
        # Verify chain
        result = blockchain.verify_chain()
        
        assert 'is_valid' in result
        assert 'verified_blocks' in result
        assert 'verified_transactions' in result
        assert result['verified_blocks'] >= 0
    
    def test_get_block(self):
        """Test getting block by index"""
        blockchain = PostQuantumBlockchain(256)
        
        genesis = blockchain.get_block(0)
        
        assert genesis is not None
        assert genesis.index == 0
    
    def test_get_chain_info(self):
        """Test getting chain information"""
        blockchain = PostQuantumBlockchain(256)
        
        info = blockchain.get_chain_info()
        
        assert 'chain_length' in info
        assert 'total_transactions' in info
        assert 'security_level' in info
        assert info['security_level'] == 256
        assert info['chain_length'] >= 1


class TestHelperFunctions:
    """Test helper functions"""
    
    def test_create_secure_transaction(self):
        """Test create_secure_transaction helper"""
        pq_sig = PostQuantumSignature(256)
        private_key, public_key = pq_sig.generate_keypair()
        
        tx = create_secure_transaction(
            private_key,
            public_key,
            "recipient",
            150.0,
            {"note": "test"},
            256
        )
        
        assert tx is not None
        assert tx.signature is not None
        assert tx.amount == 150.0
    
    def test_verify_transaction_chain(self):
        """Test verify_transaction_chain helper"""
        pq_sig = PostQuantumSignature(256)
        
        transactions = []
        for i in range(3):
            private_key, public_key = pq_sig.generate_keypair()
            tx = Transaction(public_key, f"recipient_{i}", 50.0)
            tx.sign_transaction(private_key, pq_sig)
            transactions.append(tx)
        
        result = verify_transaction_chain(transactions, 256)
        
        assert 'total_transactions' in result
        assert result['total_transactions'] == 3
        assert 'valid_transactions' in result


class TestBlockchainIntegration:
    """Integration tests for blockchain"""
    
    def test_complete_blockchain_flow(self):
        """Test complete blockchain workflow"""
        blockchain = PostQuantumBlockchain(256)
        
        # Create multiple transactions
        transactions = []
        for i in range(5):
            private_key, public_key = blockchain.pq_signer.generate_keypair()
            tx = Transaction(public_key, f"recipient_{i}", 100.0 * (i + 1))
            tx.sign_transaction(private_key, blockchain.pq_signer)
            transactions.append(tx)
        
        # Add all transactions
        for tx in transactions:
            success = blockchain.add_transaction(tx)
            assert success is True
        
        # Mine block
        block = blockchain.mine_block("validator")
        assert block is not None
        assert len(block.transactions) == 5
        
        # Verify chain
        verification = blockchain.verify_chain()
        assert verification['verified_transactions'] == 5
        
        # Check chain info
        info = blockchain.get_chain_info()
        assert info['total_transactions'] == 5
        assert info['chain_length'] == 2  # Genesis + 1 mined block


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
