import numpy as np
from scipy.special import logit, expit, logsumexp

def loglik_event(snr, pi, mu=6.0, sigma=1.0):
    """
    Log-likelihood for a single event under hierarchical mixture model.
    
    Parameters
    ----------
    snr : float
        Signal-to-noise ratio for the event
    pi : float
        Fraction of events with coherent tone (0 to 1)
    mu : float
        Mean SNR under signal hypothesis
    sigma : float
        Standard deviation under signal hypothesis
    
    Returns
    -------
    float
        Log-likelihood value
    """
    # mezcla: H0 (ruido) ~ N(0,1), H1 (tono) ~ N(mu, sigma)
    ll0 = -0.5 * snr**2
    ll1 = -0.5 * ((snr - mu) / sigma)**2 - np.log(sigma)
    return logsumexp([np.log1p(-pi) + ll0, np.log(pi) + ll1])


def logpost(snr_list, pi):
    """
    Log-posterior for hierarchical model (flat prior on pi).
    
    Parameters
    ----------
    snr_list : list of float
        SNR values for all events
    pi : float
        Global fraction parameter
    
    Returns
    -------
    float
        Log-posterior value
    """
    return sum(loglik_event(x, pi) for x in snr_list) + np.log(1.0)  # prior llano


def bayes_factor(snr_list):
    """
    Compute hierarchical Bayes factor for signal vs. noise.
    
    Parameters
    ----------
    snr_list : list of float
        SNR values for all events
    
    Returns
    -------
    float
        Bayes factor (evidence ratio)
    """
    grid = np.linspace(0, 1, 1001)
    lps = np.array([logpost(snr_list, p) for p in grid])
    logZ = logsumexp(lps) - np.log(len(grid))
    logZ0 = sum(-0.5 * np.array(snr_list)**2)
    return np.exp(logZ - logZ0)


if __name__ == "__main__":
    # Example usage
    test_snr = [5.2, 6.1, 4.8, 7.3, 5.9]
    bf = bayes_factor(test_snr)
    print(f"Bayes Factor for test data: {bf:.2e}")
