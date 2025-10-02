import numpy as np
from operador_H import build_R_matrix, spectrum_from_R, fourier_eigs_H

def test_print_convergence_table():
    h = 1e-3
    L = 3.0
    n_basis = 5

    # Fourier (exact reference)
    lam_H_F, gammas_F = fourier_eigs_H(n_modes=n_basis, h=h, L=L)

    print("\n=== Convergencia cosenos → Fourier ===")
    print(f"Referencia Fourier (exacta): eig(H) = {lam_H_F}")
    print(f"Gammas Fourier: {gammas_F}")

    print("\nTabla de convergencia cosenos → Fourier:")
    print("Nq | Norma diferencia | Eig(H) cosenos | Diferencia (cos-Fourier)")
    for Nq in [40, 80, 160, 200, 500, 1000]:
        R = build_R_matrix(n_basis=n_basis, h=h, L=L, Nq=Nq)
        lam_H, gammas = spectrum_from_R(R, h)

        diff = lam_H - lam_H_F
        norm_diff = np.linalg.norm(diff)

        print(f"{Nq:4d} | {norm_diff:12.3e} | {np.array2string(lam_H, precision=4, separator=', ')} | {np.array2string(diff, precision=4, separator=', ')}")
