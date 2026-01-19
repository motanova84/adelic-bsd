# Cryptographic Validation and Post-Quantum Blockchain

## Overview

This documentation covers the new cryptographic validation and post-quantum blockchain features added to the Adelic-BSD framework.

## Modules

### 1. Cryptographic Validation (`src/crypto_validation.py`)

Provides advanced cryptographic validation for elliptic curves used in cryptographic applications.

#### Features

- **Elliptic Curve Security Validation**: Validates curve parameters for cryptographic security
- **ECDSA Signatures**: Generates and verifies ECDSA signatures
- **EdDSA Signatures**: Supports Ed25519 signature scheme
- **Key Management**: Secure key generation and export
- **Curve Fingerprinting**: Unique cryptographic fingerprints for curves

#### Usage Examples

##### Basic Curve Validation

```python
from src.crypto_validation import CryptoValidator

# Initialize validator
validator = CryptoValidator()

# Validate curve security
curve_params = {
    'field_size': 256,
    'order': 2**256 - 2**32 - 977,
    'cofactor': 1,
    'discriminant': 123456
}

result = validator.validate_curve_security(curve_params)
print(f"Is Secure: {result['is_secure']}")
print(f"Security Level: {result['security_level']} bits")
print(f"Security Rating: {result['security_rating']}")
```

##### ECDSA Signature Generation and Verification

```python
from src.crypto_validation import CryptoValidator

validator = CryptoValidator()

# Generate key pair
private_key, public_key = validator.generate_key_pair('secp256r1')

# Sign a message
message = "Secure transaction data"
signature_data = validator.sign_message(message, private_key)

print(f"Signature: {signature_data['signature'][:32]}...")
print(f"Algorithm: {signature_data['algorithm']}")

# Verify signature
is_valid = validator.verify_signature(
    message,
    signature_data['signature'],
    public_key
)

print(f"Signature Valid: {is_valid}")
```

##### EdDSA (Ed25519) Signatures

```python
from src.crypto_validation import EdDSAValidator

validator = EdDSAValidator()

# Generate Ed25519 key pair
private_key, public_key = validator.generate_key_pair()

# Sign message
message = "Post-quantum secure message"
signature_data = validator.sign_message(message, private_key)

print(f"Algorithm: {signature_data['algorithm']}")

# Verify signature
is_valid = validator.verify_signature(
    message,
    signature_data['signature'],
    public_key
)

print(f"Ed25519 Signature Valid: {is_valid}")
```

##### Elliptic Curve Validation for Cryptography

```python
from src.crypto_validation import validate_elliptic_curve_for_crypto

# Validate a specific curve from LMFDB
result = validate_elliptic_curve_for_crypto('11a1')

if result['status'] == 'success':
    print(f"Curve: {result['curve_label']}")
    validation = result['validation']
    print(f"Security Level: {validation['security_level']} bits")
    print(f"Is Secure: {validation['is_secure']}")
else:
    print(f"Error: {result['message']}")
```

### 2. Post-Quantum Blockchain (`src/postquantum_blockchain.py`)

Implements a quantum-resistant blockchain for secure transaction verification.

#### Features

- **Post-Quantum Signatures**: Hash-based signatures resistant to quantum attacks
- **Secure Transactions**: Cryptographically signed and verified transactions
- **Blockchain Structure**: Complete blockchain with blocks and mining
- **Chain Verification**: Integrity verification of the entire blockchain
- **Configurable Security**: Adjustable security levels (128, 192, 256 bits)

#### Usage Examples

##### Creating a Post-Quantum Blockchain

```python
from src.postquantum_blockchain import PostQuantumBlockchain

# Initialize blockchain with 256-bit security
blockchain = PostQuantumBlockchain(security_level=256)

print(f"Blockchain initialized with {len(blockchain.chain)} blocks")
print(f"Security Level: {blockchain.security_level} bits")
```

##### Creating and Signing Transactions

```python
from src.postquantum_blockchain import (
    PostQuantumBlockchain,
    Transaction
)

blockchain = PostQuantumBlockchain(256)

# Generate key pair
private_key, public_key = blockchain.pq_signer.generate_keypair()

# Create transaction
tx = Transaction(
    sender=public_key,
    recipient="recipient_public_key",
    amount=100.0,
    data={"note": "Payment for services"}
)

# Sign transaction
tx.sign_transaction(private_key, blockchain.pq_signer)

print(f"Transaction Hash: {tx.calculate_hash()}")
print(f"Transaction Signed: {tx.signature is not None}")

# Add to blockchain
success = blockchain.add_transaction(tx)
print(f"Transaction Added: {success}")
```

##### Mining Blocks

```python
from src.postquantum_blockchain import PostQuantumBlockchain

blockchain = PostQuantumBlockchain(256)

# Add multiple transactions (code from previous example)
# ... add transactions ...

# Mine a new block
validator_key = "validator_public_key"
new_block = blockchain.mine_block(validator_key)

if new_block:
    print(f"Block Mined: #{new_block.index}")
    print(f"Block Hash: {new_block.block_hash}")
    print(f"Transactions in Block: {len(new_block.transactions)}")
```

##### Verifying Blockchain Integrity

```python
from src.postquantum_blockchain import PostQuantumBlockchain

blockchain = PostQuantumBlockchain(256)

# ... add transactions and mine blocks ...

# Verify entire blockchain
verification = blockchain.verify_chain()

print(f"Blockchain Valid: {verification['is_valid']}")
print(f"Verified Blocks: {verification['verified_blocks']}")
print(f"Verified Transactions: {verification['verified_transactions']}")

if verification['errors']:
    print("Errors found:")
    for error in verification['errors']:
        print(f"  - {error}")
```

##### Complete Workflow Example

```python
from src.postquantum_blockchain import (
    PostQuantumBlockchain,
    create_secure_transaction
)

# Initialize blockchain
blockchain = PostQuantumBlockchain(security_level=256)

# Create multiple users
users = []
for i in range(3):
    private_key, public_key = blockchain.pq_signer.generate_keypair()
    users.append({'private': private_key, 'public': public_key})

# Create transactions between users
for i in range(len(users) - 1):
    tx = create_secure_transaction(
        sender_private_key=users[i]['private'],
        sender_public_key=users[i]['public'],
        recipient_public_key=users[i + 1]['public'],
        amount=50.0 * (i + 1),
        data={"transfer": f"payment_{i}"},
        security_level=256
    )
    blockchain.add_transaction(tx)

# Mine block
block = blockchain.mine_block(users[0]['public'])

# Get chain info
info = blockchain.get_chain_info()
print(f"Chain Length: {info['chain_length']}")
print(f"Total Transactions: {info['total_transactions']}")
print(f"Security Algorithm: {info['algorithm']}")

# Verify chain
verification = blockchain.verify_chain()
print(f"Blockchain Valid: {verification['is_valid']}")
```

## Integration with Adelic-BSD Framework

Both modules integrate seamlessly with the existing Adelic-BSD framework:

```python
# Import all modules together
from src import (
    # Cryptographic validation
    CryptoValidator,
    EdDSAValidator,
    validate_elliptic_curve_for_crypto,
    # Post-quantum blockchain
    PostQuantumBlockchain,
    Transaction,
    create_secure_transaction,
    verify_transaction_chain,
    # Existing BSD modules
    SABIO_Infinity4,
    compute_vacuum_energy
)

# Use together for comprehensive validation
validator = CryptoValidator()
blockchain = PostQuantumBlockchain(256)

# Validate curve and create secure transactions
curve_result = validate_elliptic_curve_for_crypto('11a1')
if curve_result['status'] == 'success':
    # Create cryptographic fingerprint
    fingerprint = validator.generate_curve_fingerprint(
        curve_result['curve_params']
    )
    
    # Use in blockchain transaction
    tx = Transaction(
        sender="sender_key",
        recipient="recipient_key",
        amount=100.0,
        data={'curve_fingerprint': fingerprint}
    )
```

## Security Considerations

### Cryptographic Validation

1. **Key Storage**: Private keys should be stored securely using hardware security modules (HSM) or secure enclaves
2. **Signature Verification**: Always verify signatures before trusting transaction data
3. **Curve Selection**: Use standard, well-tested curves (secp256r1, secp384r1) for production
4. **Security Levels**: Minimum 256-bit security recommended for high-value applications

### Post-Quantum Blockchain

1. **Quantum Resistance**: The hash-based signatures provide quantum resistance
2. **Production Use**: For production systems, integrate with libraries like liboqs-python for NIST-approved PQ algorithms
3. **Chain Integrity**: Regularly verify blockchain integrity
4. **Transaction Validation**: Validate all transactions before adding to blocks
5. **Security Level**: Use 256-bit security for maximum protection

## Testing

Run the test suites:

```bash
# Test cryptographic validation
pytest tests/test_crypto_validation.py -v

# Test post-quantum blockchain
pytest tests/test_postquantum_blockchain.py -v

# Run all tests
pytest tests/test_crypto_validation.py tests/test_postquantum_blockchain.py -v
```

## Future Enhancements

1. **NIST PQ Algorithms**: Integration with CRYSTALS-Dilithium and FALCON
2. **Hardware Wallet Support**: HSM integration for key management
3. **Multi-signature Support**: M-of-N signature schemes
4. **Zero-Knowledge Proofs**: Privacy-preserving transaction validation
5. **Smart Contract Support**: Programmable transaction logic
6. **Consensus Mechanisms**: Proof-of-Stake and other consensus algorithms

## References

- NIST Post-Quantum Cryptography: https://csrc.nist.gov/projects/post-quantum-cryptography
- ECDSA: FIPS 186-4 Digital Signature Standard
- EdDSA: RFC 8032
- Elliptic Curve Cryptography: Guide to Elliptic Curve Cryptography (Hankerson, Menezes, Vanstone)
