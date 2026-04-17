"""Tests for MCP resonance real/sim observer behavior."""

import math

import pandas as pd
import pytest

from src.mcp_network.resonance import (
    REAL_OBSERVERS,
    check_node_resonance,
    classify_resonance,
    load_real_grid_sample,
    register_real_observer,
    score_psi,
)

NUM_SAMPLES = 4


@pytest.fixture
def restore_observers():
    previous = REAL_OBSERVERS.copy()
    try:
        yield
    finally:
        REAL_OBSERVERS.clear()
        REAL_OBSERVERS.update(previous)


def test_score_psi_and_classification_basics():
    psi = score_psi(latency_ms=20.0, phase_offset_rad=0.005, heartbeat_ok=True, schema_ok=True)
    resonance, status = classify_resonance(psi, reachable=True)

    assert 0.0 <= psi <= 1.0
    assert resonance in {"coherent", "drifting", "fault"}
    assert status in {"pass", "warn", "fail"}


def test_check_node_resonance_simulated_mode_by_default(monkeypatch):
    monkeypatch.delenv("QCAL_REAL_TESTS", raising=False)
    health = check_node_resonance("auron-governor")

    assert health["qcal"]["modo_real"] is False
    assert health["checks"]["fuente_fisica"] == "simulada"
    assert health["frequency_hz"] == pytest.approx(50.0, rel=1e-12)


def test_check_node_resonance_real_mode_with_registered_observer(monkeypatch, restore_observers):
    monkeypatch.setenv("QCAL_REAL_TESTS", "1")

    register_real_observer(
        "interferometro-noesico",
        lambda: (2.0, 0.001, True, True),
    )
    health = check_node_resonance("interferometro-noesico")

    assert health["qcal"]["modo_real"] is True
    assert health["checks"]["fuente_fisica"] == "real"
    assert health["status"] in {"pass", "warn"}
    assert health["frequency_hz"] == pytest.approx(283.4002, rel=1e-9)


def test_load_real_grid_sample_from_csv(tmp_path):
    csv_path = tmp_path / "grid_frequency_sample.csv"
    pd.DataFrame({"frequency_hz": [50.001, 49.999, 50.002, 50.0]}).to_csv(csv_path, index=False)

    latency_ms, phase_offset, heartbeat_ok, schema_ok = load_real_grid_sample(path=str(csv_path))
    expected_delta_f = (50.001 + 49.999 + 50.002 + 50.0) / NUM_SAMPLES - 50.0
    expected_phase = 2.0 * math.pi * expected_delta_f * NUM_SAMPLES

    assert latency_ms == pytest.approx(20.0, rel=0.0, abs=1e-12)
    assert phase_offset == pytest.approx(expected_phase, rel=1e-12)
    assert heartbeat_ok is True
    assert schema_ok is True


def test_real_mode_fallback_when_observer_not_registered(monkeypatch):
    monkeypatch.setenv("QCAL_REAL_TESTS", "1")
    health = check_node_resonance("nodo-no-registrado")

    assert health["qcal"]["modo_real"] is False
    assert health["checks"]["fuente_fisica"] == "simulada"
