import numpy as np
import pytest
from operador_H import build_R_matrix, spectrum_from_R, fourier_eigs_H

def test_symmetry_R():
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=80)
    assert np.allclose(R, R.T, atol=1e-12), "R should be symmetric"

def test_positive_H():
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=120)
    lam_H, gammas = spectrum_from_R(R, h)
    assert np.all(lam_H > 0.25), "Eigenvalues of H should exceed 1/4"
    assert np.all(gammas >= 0), "Gammas should be real nonnegative"

def test_cosine_vs_fourier_convergence():
    h = 1e-3
    L = 1.0
    # Fourier (exact reference)
    lam_H_F, _ = fourier_eigs_H(n_modes=5, h=h, L=L)

    # Cosenos con cuadratura, creciente Nq
    R1 = build_R_matrix(n_basis=5, h=h, L=L, Nq=60)
    lam_H1, _ = spectrum_from_R(R1, h)

    R2 = build_R_matrix(n_basis=5, h=h, L=L, Nq=160)
    lam_H2, _ = spectrum_from_R(R2, h)

    # Se espera que lam_H2 esté más cerca de lam_H_F que lam_H1
    err1 = np.linalg.norm(lam_H1 - lam_H_F)
    err2 = np.linalg.norm(lam_H2 - lam_H_F)
    assert err2 <= err1, "Higher quadrature should improve convergence to Fourier spectrum"
