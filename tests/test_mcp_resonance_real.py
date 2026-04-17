"""Tests for MCP real-observer resonance checks."""

import math
import os
from pathlib import Path

import pandas as pd
import pytest

from mcp_network.resonance import (
    F0_REFERENCE,
    check_node_resonance,
    load_hrv_eeg_biologia,
    load_magnetometer_interferometer,
)

pytestmark = pytest.mark.skipif(
    os.getenv("QCAL_REAL_TESTS") != "1",
    reason="Set QCAL_REAL_TESTS=1 to run real observer resonance tests",
)


class TestCheckNodeResonanceRealObservers:
    """Validation suite for real physical observer nodes."""

    def test_biologia_cuantica_psi_above_gate(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["psi"] >= health["gate"]["psi_min"]

    def test_biologia_cuantica_phase_calculation(self):
        fixture = Path("tests/data/hrv_eeg_biologia_cuantica.csv")
        df = pd.read_csv(fixture)
        rr_mean = float(df["rr_interval_ms"].mean())
        expected_rr = 1000.0 / (F0_REFERENCE / 2.0)
        delta_rr = rr_mean - expected_rr
        expected_phase = 2.0 * math.pi * (delta_rr / 1000.0) * 60.0

        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_biologia_cuantica_harmonic_factor(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["qcal"]["harmonic_factor"] == 0.5

    def test_biologia_cuantica_source_is_real(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["checks"]["fuente_fisica"] == "real"
        assert health["qcal"]["modo_real"] is True

    def test_biologia_cuantica_phase_within_gate(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert abs(health["phase_offset_rad"]) < health["gate"]["phase_max_rad"]

    def test_biologia_cuantica_resonance_coherent(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["resonance"] == "coherent"

    def test_biologia_cuantica_observer_contract(self):
        latency_ms, phase_offset, signal_ok, online = load_hrv_eeg_biologia()
        assert latency_ms > 0
        assert isinstance(phase_offset, float)
        assert signal_ok is True
        assert online is True

    def test_interferometro_psi_above_gate(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["psi"] >= health["gate"]["psi_min"]

    def test_interferometro_phase_from_magnetometer(self):
        fixture = Path("tests/data/magnetometer_interferometer.csv")
        df = pd.read_csv(fixture)
        peak_freq = float(df["frequency_hz"].mean())
        target = F0_REFERENCE * 2.0
        expected_phase = 2.0 * math.pi * (peak_freq - target) / target

        health = check_node_resonance("interferometro-noesico")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_interferometro_harmonic_factor(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["qcal"]["harmonic_factor"] == 2.0

    def test_interferometro_source_is_real(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["checks"]["fuente_fisica"] == "real"
        assert health["qcal"]["modo_real"] is True

    def test_interferometro_phase_within_gate(self):
        health = check_node_resonance("interferometro-noesico")
        assert abs(health["phase_offset_rad"]) < health["gate"]["phase_max_rad"]

    def test_interferometro_resonance_coherent(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["resonance"] == "coherent"

    def test_interferometro_observer_contract(self):
        latency_ms, phase_offset, signal_ok, online = load_magnetometer_interferometer()
        assert latency_ms > 0
        assert isinstance(phase_offset, float)
        assert signal_ok is True
        assert online is True
