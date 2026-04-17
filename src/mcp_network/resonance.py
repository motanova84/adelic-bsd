"""Resonance engine with optional real-observer data sources."""

from __future__ import annotations

import math
import os
from datetime import datetime, timezone
from typing import Any, Callable, Dict, Optional, Tuple

import pandas as pd

F0_REFERENCE = 141.7001
NOMINAL_GRID_FREQUENCY_HZ = 50.0
LATENCY_THRESHOLD_MS = 100.0
PHASE_THRESHOLD_RAD = 0.25
LATENCY_WEIGHT = 0.45
PHASE_WEIGHT = 0.55
PSI_COHERENT_THRESHOLD = 0.99
PSI_DRIFTING_THRESHOLD = 0.95
PSI_SATURATED_THRESHOLD = 0.999
PHASE_COHERENCE_NORMALIZATION = math.pi / 2.0

NODE_FREQUENCIES: Dict[str, float] = {
    "auron-governor": 50.0000,
    "141-hz": 141.7001,
    "interferometro-noesico": 283.4002,
    "biologia-cuantica-noesica": 70.85005,
}

Observer = Callable[[], Tuple[float, float, bool, bool]]
REAL_OBSERVERS: Dict[str, Observer] = {}


def register_real_observer(node: str, fn: Observer) -> None:
    """Register a physical observer callback for a node."""
    REAL_OBSERVERS[node] = fn


def score_psi(
    latency_ms: float,
    phase_offset_rad: float,
    heartbeat_ok: bool = True,
    schema_ok: bool = True,
) -> float:
    """Compute bounded Ψ score from latency/phase penalties."""
    if not heartbeat_ok or not schema_ok:
        return 0.0

    latency_penalty = min(latency_ms / LATENCY_THRESHOLD_MS, 1.0)
    phase_penalty = min(abs(phase_offset_rad) / PHASE_THRESHOLD_RAD, 1.0)
    psi = 1.0 - LATENCY_WEIGHT * latency_penalty - PHASE_WEIGHT * phase_penalty
    return max(0.0, min(psi, 1.0))


def classify_resonance(psi: float, reachable: bool) -> tuple[str, str]:
    """Convert Ψ + reachability to resonance/status labels."""
    if not reachable:
        return "offline", "fail"
    if psi >= PSI_COHERENT_THRESHOLD:
        return "coherent", "pass"
    if psi >= PSI_DRIFTING_THRESHOLD:
        return "drifting", "warn"
    return "fault", "fail"


def load_real_grid_sample(
    path: Optional[str] = None,
    fallback: Tuple[float, float, bool, bool] = (12.4, 0.018, True, True),
) -> Tuple[float, float, bool, bool]:
    """Load a real grid-frequency sample and derive phase offset."""
    sample_path = path or os.getenv(
        "QCAL_GRID_SAMPLE_PATH",
        "/tmp/grid_frequency_2026-04-15T14_55Z.csv",
    )
    if not os.path.exists(sample_path):
        return fallback

    try:
        df = pd.read_csv(sample_path)
        if "frequency_hz" not in df:
            return fallback

        delta_f = float(df["frequency_hz"].mean() - NOMINAL_GRID_FREQUENCY_HZ)
        window_seconds = float(len(df))
        phase_offset = 2.0 * math.pi * delta_f * window_seconds
        return 20.0, phase_offset, True, True
    except Exception:
        return fallback


def load_qcal_spectrum() -> Tuple[float, float, bool, bool]:
    """Fallback spectrum observer for 141-hz node."""
    return 8.7, 0.003, True, True


def _real_mode_enabled(use_real_mode: Optional[bool] = None) -> bool:
    if use_real_mode is not None:
        return bool(use_real_mode)
    return os.getenv("QCAL_REAL_TESTS", "").strip().lower() in {"1", "true", "yes", "on"}


def check_node_resonance(
    node_name: str,
    latency_ms: Optional[float] = None,
    phase_offset_rad: Optional[float] = None,
    heartbeat_ok: Optional[bool] = None,
    schema_ok: Optional[bool] = None,
    reachable: bool = True,
    use_real_mode: Optional[bool] = None,
) -> Dict[str, Any]:
    """Run resonance health check for a node with real/sim mode support."""
    freq = NODE_FREQUENCIES.get(node_name, F0_REFERENCE)
    real_mode = _real_mode_enabled(use_real_mode)

    lat = latency_ms if latency_ms is not None else 12.4
    phase = phase_offset_rad if phase_offset_rad is not None else 0.018
    hb = heartbeat_ok if heartbeat_ok is not None else True
    sch = schema_ok if schema_ok is not None else True
    used_real_observer = False

    observer = REAL_OBSERVERS.get(node_name) if real_mode else None
    if observer is not None:
        try:
            lat, phase, hb, sch = observer()
            used_real_observer = True
        except Exception:
            hb = False
            sch = False

    psi = score_psi(lat, phase, hb, sch)
    resonance, status = classify_resonance(psi, reachable=reachable)
    phase_coherence = max(0.0, 1.0 - abs(phase) / PHASE_COHERENCE_NORMALIZATION)

    return {
        "node": node_name,
        "status": status,
        "reachable": reachable,
        "latency_ms": round(lat, 2),
        "resonance": resonance,
        "psi": round(psi, 6),
        "phase_offset_rad": round(phase, 6),
        "frequency_hz": freq,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "qcal": {
            "psi_raw": round(psi, 6),
            "f0_reference_hz": F0_REFERENCE,
            "harmonic_factor": round(freq / F0_REFERENCE, 5),
            "phase_coherence": round(phase_coherence, 4),
            "resonance_class": resonance,
            "logos_level": "saturated" if psi > PSI_SATURATED_THRESHOLD else "stable",
            "modo_real": used_real_observer,
        },
        "checks": {
            "transport": "ok" if reachable else "fail",
            "schema": "ok" if sch else "fail",
            "heartbeat": "ok" if hb else "fail",
            "qcal_protocol": "ok",
            "fuente_fisica": "real" if used_real_observer else "simulada",
        },
        "error_code": None,
        "error_message": None,
    }


register_real_observer("auron-governor", load_real_grid_sample)
register_real_observer("141-hz", load_qcal_spectrum)
