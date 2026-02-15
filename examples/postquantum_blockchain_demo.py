#!/usr/bin/env python3
"""
Post-Quantum Blockchain Demo
=============================

Demonstrates the post-quantum blockchain capabilities of the Adelic-BSD framework.

This script shows:
1. Post-quantum signature generation and verification
2. Transaction creation and signing
3. Block mining
4. Blockchain verification
5. Complete blockchain workflow

Usage:
    python examples/postquantum_blockchain_demo.py
"""

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


def demo_pq_signatures():
    """Demonstrate post-quantum signature generation"""
    print("\n" + "=" * 70)
    print("DEMO 1: Post-Quantum Signature Generation")
    print("=" * 70)
    
    pq_sig = PostQuantumSignature(security_level=256)
    
    print(f"\nSecurity Level: {pq_sig.security_level} bits")
    print(f"Algorithm: {pq_sig.algorithm}")
    
    # Generate key pair
    print("\nGenerating post-quantum key pair...")
    private_key, public_key = pq_sig.generate_keypair()
    print(f"Private Key: {private_key[:32]}...")
    print(f"Public Key:  {public_key[:32]}...")
    
    # Sign messages
    messages = [
        "Blockchain transaction #1",
        "Blockchain transaction #2",
        "Blockchain transaction #3"
    ]
    
    print(f"\nSigning {len(messages)} messages with post-quantum signature...")
    
    for i, message in enumerate(messages):
        signature = pq_sig.sign(message, private_key)
        is_valid = pq_sig.verify(message, signature, public_key)
        status = "✓ VALID" if is_valid else "✗ INVALID"
        print(f"  Message {i+1}: {message[:30]}... - {status}")


def demo_transactions():
    """Demonstrate transaction creation and signing"""
    print("\n" + "=" * 70)
    print("DEMO 2: Transaction Creation and Signing")
    print("=" * 70)
    
    pq_sig = PostQuantumSignature(256)
    
    # Generate key pairs for sender and recipient
    sender_private, sender_public = pq_sig.generate_keypair()
    _, recipient_public = pq_sig.generate_keypair()
    
    print("\nCreating transaction...")
    tx = Transaction(
        sender=sender_public,
        recipient=recipient_public,
        amount=150.0,
        data={"note": "Payment for services", "invoice": "INV-2026-001"}
    )
    
    print(f"Transaction Details:")
    print(f"  Sender: {tx.sender[:32]}...")
    print(f"  Recipient: {tx.recipient[:32]}...")
    print(f"  Amount: {tx.amount}")
    print(f"  Data: {tx.data}")
    print(f"  Timestamp: {tx.timestamp}")
    
    # Calculate hash
    tx_hash = tx.calculate_hash()
    print(f"\nTransaction Hash: {tx_hash}")
    
    # Sign transaction
    print("\nSigning transaction with post-quantum signature...")
    tx.sign_transaction(sender_private, pq_sig)
    print(f"Signature: {tx.signature[:32]}...")
    
    # Verify signature
    is_valid = tx.verify_signature(pq_sig)
    status = "✓ VALID" if is_valid else "✗ INVALID"
    print(f"Signature Verification: {status}")


def demo_blockchain_creation():
    """Demonstrate blockchain creation and operations"""
    print("\n" + "=" * 70)
    print("DEMO 3: Blockchain Creation and Operations")
    print("=" * 70)
    
    # Initialize blockchain
    print("\nInitializing post-quantum blockchain...")
    blockchain = PostQuantumBlockchain(security_level=256)
    
    info = blockchain.get_chain_info()
    print(f"Chain Length: {info['chain_length']}")
    print(f"Security Level: {info['security_level']} bits")
    print(f"Algorithm: {info['algorithm']}")
    print(f"Genesis Block Hash: {info['latest_block_hash']}")
    
    # Create users
    print("\n\nCreating user accounts...")
    users = []
    for i in range(3):
        private_key, public_key = blockchain.pq_signer.generate_keypair()
        users.append({
            'id': f'User{i+1}',
            'private': private_key,
            'public': public_key
        })
        print(f"  {users[i]['id']}: {users[i]['public'][:32]}...")
    
    # Create transactions
    print("\n\nCreating transactions...")
    transactions = []
    
    tx_details = [
        (users[0], users[1], 100.0, "Payment for consulting"),
        (users[1], users[2], 50.0, "Software license"),
        (users[2], users[0], 25.0, "Refund")
    ]
    
    for sender, recipient, amount, note in tx_details:
        tx = Transaction(sender['public'], recipient['public'], amount, {'note': note})
        tx.sign_transaction(sender['private'], blockchain.pq_signer)
        transactions.append(tx)
        
        success = blockchain.add_transaction(tx)
        status = "✓ Added" if success else "✗ Failed"
        print(f"  {sender['id']} → {recipient['id']}: {amount} - {status}")
    
    # Mine block
    print("\n\nMining new block...")
    validator_key = users[0]['public']
    new_block = blockchain.mine_block(validator_key)
    
    if new_block:
        print(f"Block Mined Successfully!")
        print(f"  Block Index: #{new_block.index}")
        print(f"  Block Hash: {new_block.block_hash}")
        print(f"  Transactions: {len(new_block.transactions)}")
        print(f"  Validator: {new_block.validator[:32]}...")
    
    # Display updated chain info
    info = blockchain.get_chain_info()
    print(f"\nUpdated Chain Info:")
    print(f"  Chain Length: {info['chain_length']}")
    print(f"  Total Transactions: {info['total_transactions']}")
    print(f"  Pending Transactions: {info['pending_transactions']}")


def demo_blockchain_verification():
    """Demonstrate blockchain verification"""
    print("\n" + "=" * 70)
    print("DEMO 4: Blockchain Verification")
    print("=" * 70)
    
    # Create blockchain with multiple blocks
    blockchain = PostQuantumBlockchain(256)
    
    print("\nCreating blockchain with multiple blocks...")
    
    # Add 3 blocks with transactions
    for block_num in range(3):
        print(f"\nBlock {block_num + 1}:")
        
        # Create transactions for this block
        for tx_num in range(2):
            private_key, public_key = blockchain.pq_signer.generate_keypair()
            _, recipient = blockchain.pq_signer.generate_keypair()
            
            tx = Transaction(public_key, recipient, 100.0 * (tx_num + 1))
            tx.sign_transaction(private_key, blockchain.pq_signer)
            blockchain.add_transaction(tx)
            print(f"  Transaction {tx_num + 1}: {tx.amount} units")
        
        # Mine block
        block = blockchain.mine_block("validator")
        print(f"  Mined: {block.block_hash[:32]}...")
    
    # Verify blockchain
    print("\n\nVerifying blockchain integrity...")
    verification = blockchain.verify_chain()
    
    print(f"\nVerification Results:")
    print(f"  Chain Valid: {verification['is_valid']} {'✓' if verification['is_valid'] else '✗'}")
    print(f"  Verified Blocks: {verification['verified_blocks']}")
    print(f"  Verified Transactions: {verification['verified_transactions']}")
    
    if verification['errors']:
        print(f"  Errors Found: {len(verification['errors'])}")
        for error in verification['errors']:
            print(f"    - {error}")
    else:
        print(f"  Errors Found: 0 ✓")


def demo_complete_workflow():
    """Demonstrate complete blockchain workflow"""
    print("\n" + "=" * 70)
    print("DEMO 5: Complete Blockchain Workflow")
    print("=" * 70)
    
    # Initialize
    blockchain = PostQuantumBlockchain(256)
    
    print("\n📊 SCENARIO: Multi-party transaction system")
    print("\nParticipants:")
    
    # Create participants
    alice_priv, alice_pub = blockchain.pq_signer.generate_keypair()
    bob_priv, bob_pub = blockchain.pq_signer.generate_keypair()
    charlie_priv, charlie_pub = blockchain.pq_signer.generate_keypair()
    
    print(f"  👤 Alice:   {alice_pub[:24]}...")
    print(f"  👤 Bob:     {bob_pub[:24]}...")
    print(f"  👤 Charlie: {charlie_pub[:24]}...")
    
    # Transaction sequence
    print("\n\n💰 Transaction Sequence:")
    
    transactions = [
        ("Alice", alice_priv, alice_pub, "Bob", bob_pub, 500.0, "Initial funding"),
        ("Bob", bob_priv, bob_pub, "Charlie", charlie_pub, 300.0, "Product purchase"),
        ("Charlie", charlie_priv, charlie_pub, "Alice", alice_pub, 100.0, "Service payment"),
        ("Bob", bob_priv, bob_pub, "Alice", alice_pub, 150.0, "Refund"),
    ]
    
    for sender_name, s_priv, s_pub, recv_name, r_pub, amt, desc in transactions:
        tx = create_secure_transaction(s_priv, s_pub, r_pub, amt, {'description': desc}, 256)
        success = blockchain.add_transaction(tx)
        status = "✓" if success else "✗"
        print(f"  {status} {sender_name} → {recv_name}: {amt} ({desc})")
    
    # Mine block
    print("\n\n⛏️  Mining block...")
    block = blockchain.mine_block(alice_pub)
    print(f"  Block #{block.index} mined by Alice")
    print(f"  Hash: {block.block_hash}")
    
    # Verify
    print("\n\n🔍 Verification:")
    verification = blockchain.verify_chain()
    print(f"  Blockchain valid: {'✓ Yes' if verification['is_valid'] else '✗ No'}")
    print(f"  Verified transactions: {verification['verified_transactions']}")
    
    # Final state
    info = blockchain.get_chain_info()
    print(f"\n\n📈 Final State:")
    print(f"  Total blocks: {info['chain_length']}")
    print(f"  Total transactions: {info['total_transactions']}")
    print(f"  Security level: {info['security_level']} bits")
    print(f"  Latest hash: {info['latest_block_hash'][:32]}...")


def main():
    """Run all demonstrations"""
    print("\n" + "=" * 70)
    print("POST-QUANTUM BLOCKCHAIN DEMONSTRATION")
    print("Adelic-BSD Framework")
    print("=" * 70)
    
    try:
        demo_pq_signatures()
        demo_transactions()
        demo_blockchain_creation()
        demo_blockchain_verification()
        demo_complete_workflow()
        
        print("\n" + "=" * 70)
        print("DEMONSTRATION COMPLETE")
        print("=" * 70)
        print("\n✓ All post-quantum blockchain features demonstrated successfully!")
        print("📖 See docs/CRYPTO_BLOCKCHAIN_DOCUMENTATION.md for detailed usage.\n")
        
    except Exception as e:
        print(f"\n✗ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
