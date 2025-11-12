import numpy as np
from numpy.polynomial.legendre import leggauss
from numpy.linalg import eigh

# --- Núcleo analítico (forma cerrada) ---
def K_gauss(t, s, h):
    """
    Núcleo gaussiano en variables logarítmicas:
    K_h(t,s) = exp(-h/4) * sqrt(pi/h) * exp(-(t-s)^2/(4h))
    """
    return np.exp(-h/4.0) * np.sqrt(np.pi / h) * np.exp(- (t - s)**2 / (4.0*h))

# --- Base de cosenos ortonormal en [-L,L] ---
def cos_basis(t, L, k):
    if k == 0:
        return np.ones_like(t) / np.sqrt(2.0*L)
    return np.cos(k * np.pi * t / L) / np.sqrt(L)

# --- Construcción de R_h en base de cosenos ---
def build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160):
    """
    Construye la matriz del operador de calor R_h en la base de cosenos.
    """
    x, w = leggauss(Nq)        # nodos/pesos en [-1,1]
    t = L * x                  # nodos en [-L,L]
    w = L * w                  # pesos reescalados

    # Matriz del núcleo
    K = np.empty((Nq, Nq))
    for a in range(Nq):
        K[a, :] = K_gauss(t[a], t, h)

    # Matriz de proyección de base
    Phi = np.vstack([cos_basis(t, L, k) for k in range(n_basis)])

    # Integral doble: R = Phi * (W*K*W) * Phi^T
    W = np.diag(w)
    M = W @ K @ W
    R = Phi @ M @ Phi.T
    R = 0.5 * (R + R.T)  # simetriza

    return R

def spectrum_from_R(R, h):
    """
    Diagonaliza R y obtiene el espectro de H por el mapa:
    H = -(1/h) log(R/(2π))
    """
    vals, _ = eigh(R)
    vals = np.clip(vals, 1e-300, None)  # evita log de 0
    lam_H = -(1.0/h) * np.log(vals / (2.0*np.pi))
    lam_H = np.sort(lam_H)
    gammas = np.sqrt(np.clip(lam_H - 0.25, 0.0, None))
    return lam_H, gammas

# --- Versión exacta en base de Fourier (diagonal) ---
def fourier_eigs_H(n_modes=5, h=1e-3, L=1.0):
    """
    En base de Fourier, R_h es diagonal:
    eig(H) = ω^2 + 1/4 con ω = πk/L
    """
    k = np.arange(n_modes, dtype=float)
    omega = (np.pi / L) * k
    eig_R = 2.0*np.pi * np.exp(-h*(omega**2 + 0.25))
    eig_H = -(1.0/h)*np.log(eig_R/(2.0*np.pi))  # = ω^2+1/4
    gammas = np.sqrt(np.maximum(eig_H - 0.25, 0.0))
    return eig_H, gammas

if __name__ == "__main__":
    h = 1e-3
    L = 1.0
    R = build_R_matrix(n_basis=5, h=h, L=L, Nq=160)
    lam_H, gammas = spectrum_from_R(R, h)
    print("Eigs(H) via cos basis:", lam_H)
    print("Gammas (approx):", gammas)

    lam_H_F, gammas_F = fourier_eigs_H(n_modes=5, h=h, L=L)
    print("Eigs(H) via Fourier:", lam_H_F)
    print("Gammas (exact):", gammas_F)
