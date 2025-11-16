# ============================================================
# ARCHIVO: qcal_beacon_bsd.py
# FUNCION: Genera un QCAL Beacon firmado para resultados BSD
# AUTOR: JMMB Ψ✧ — Noēsis ∞³
# ============================================================

import json
import uuid
from datetime import datetime
from pathlib import Path

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.backends import default_backend

from adelic_bsd.verify import verify_bsd  # Módulo generado anteriormente


# ============================================================
# 1. CLAVES (en producción: guardar en ficheros PEM)
# ============================================================

private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())
public_key = private_key.public_key()

public_pem = public_key.public_bytes(
    encoding=serialization.Encoding.PEM,
    format=serialization.PublicFormat.SubjectPublicKeyInfo
).decode()


def sign_ecdsa(message: str):
    """Firma ECDSA sobre SHA3-256"""
    signature = private_key.sign(message.encode(), ec.ECDSA(hashes.SHA3_256()))
    return {"signature_hex": signature.hex()}


# ============================================================
# 2. GENERADOR DEL BEACON
# ============================================================

def generate_qcal_beacon_for_bsd(E_str: str):
    """Genera .qcal_beacon para la curva elíptica dada."""

    # 1 — Ejecutar validación BSD
    result = verify_bsd(E_str)

    data = result["data"]
    lvalue = data["L(1)"]
    rank = data["rank"]
    integrity_hash = result["integrity_hash"]

    # 2 — Preparar mensaje firmado
    beacon_id = str(uuid.uuid4())
    timestamp = datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")

    message_to_sign = f"{E_str}|{rank}|{lvalue}|{integrity_hash}|{beacon_id}|Noesis∞³"

    signature = sign_ecdsa(message_to_sign)

    print("   Firma ECDSA generada.")

    # 3 — Construir beacon
    beacon = {
        "qcal_beacon": {
            "id": beacon_id,
            "timestamp": timestamp,
            "curve": E_str,
            "L_at_1": lvalue,
            "analytic_rank": rank,
            "integrity_hash": integrity_hash,
            "validator_node": "Noēsis-∞³",
            "signature": signature,
            "message_signed": message_to_sign,
            "public_key_pem": public_pem.strip(),
        }
    }

    # 4 — Guardar archivo JSON
    out_dir = Path(__file__).resolve().parent.parent / "beacons"
    out_dir.mkdir(exist_ok=True)

    filename = out_dir / f"qcal_beacon_bsd_{E_str.replace('/', '_')}.json"

    with open(filename, "w", encoding="utf-8") as f:
        json.dump(beacon, f, ensure_ascii=False, indent=2)

    print(f"✅ Beacon generado: {filename}")
    return beacon
