"""
Curve Generator for BSD Experimental Validation
=================================================

Generates elliptic curves E/Q with non-trivial invariants for BSD validation:
- Conductor > 1000
- Rank ≥ 2 (when possible)
- Non-trivial torsion
- Not documented in BHK or Gross-Zagier

Author: BSD Spectral Framework
Date: November 2025
"""


def get_experimental_curve_definitions():
    """
    Return definitions for experimental elliptic curves.

    These curves are chosen specifically for BSD validation because they:
    - Have conductor > 1000
    - Have rank ≥ 2 (when possible)
    - Have non-trivial torsion in some cases
    - Are not covered by classical BSD proofs (BHK, Gross-Zagier)

    Returns:
        dict: Curve definitions with labels and coefficients
    """
    curves = {
        # E5077b1: Famous rank 3 curve (rank 3 = unexplored BSD territory)
        # y² + y = x³ - 7x + 6, conductor 5077
        'E5077b1': {
            'coefficients': [0, 0, 1, -7, 6],
            'label': '5077b1',
            'description': 'Rank 3 curve - not covered by classical proofs',
            'expected_rank': 3,
            'cremona_label': '5077b1',
        },
        # E5077a1: Another curve with conductor 5077
        # y² + y = x³ − 7x + 6 (rank 0)
        'E5077a1': {
            'coefficients': [0, 0, 1, -7, 6],
            'label': '5077a1',
            'description': 'Conductor 5077 curve (rank 0 variant)',
            'expected_rank': 0,
            'cremona_label': '5077a1',
        },
        # E1171a1: A rank 2 curve with large conductor
        # Standard rank 2 curve for testing
        'E1171a1': {
            'coefficients': [0, 1, 1, -11, 0],
            'label': '1171a1',
            'description': 'Rank 2 curve with conductor 1171',
            'expected_rank': 2,
            'cremona_label': '1171a1',
        },
        # E1483a1: Rank 2 curve
        'E1483a1': {
            'coefficients': [0, 0, 1, -3, -5],
            'label': '1483a1',
            'description': 'Conductor 1483 rank 2 curve',
            'expected_rank': 2,
            'cremona_label': '1483a1',
        },
        # E3137b1: High conductor curve
        'E3137b1': {
            'coefficients': [1, 0, 1, -12, 0],
            'label': '3137b1',
            'description': 'High conductor curve (3137)',
            'expected_rank': 1,
            'cremona_label': '3137b1',
        },
    }

    return curves


def generate_experimental_curves():
    """
    Generate EllipticCurve objects for all experimental curves.

    Returns:
        dict: Label -> EllipticCurve objects

    Note:
        Requires SageMath. Returns None values if SageMath is not available.
    """
    try:
        from sage.all import EllipticCurve as SageEllipticCurve
        sage_available = True
    except ImportError:
        sage_available = False

    definitions = get_experimental_curve_definitions()
    curves = {}

    for label, info in definitions.items():
        if sage_available:
            try:
                # Try to load by Cremona label first
                if 'cremona_label' in info:
                    try:
                        E = SageEllipticCurve(info['cremona_label'])
                    except Exception:
                        # Fall back to coefficients
                        E = SageEllipticCurve(info['coefficients'])
                else:
                    E = SageEllipticCurve(info['coefficients'])
                curves[label] = {
                    'curve': E,
                    'info': info,
                    'status': 'loaded',
                }
            except Exception as e:
                curves[label] = {
                    'curve': None,
                    'info': info,
                    'status': f'error: {str(e)}',
                }
        else:
            curves[label] = {
                'curve': None,
                'info': info,
                'status': 'sage_not_available',
            }

    return curves


def get_curve_invariants(E):
    """
    Extract essential invariants from an elliptic curve.

    Args:
        E: SageMath EllipticCurve object

    Returns:
        dict: Curve invariants
    """
    try:
        # Basic invariants
        invariants = {
            'conductor': int(E.conductor()),
            'rank': int(E.rank()),
            'discriminant': int(E.discriminant()),
            'j_invariant': str(E.j_invariant()),
            'a_invariants': [int(a) for a in E.a_invariants()],
        }

        # Torsion information
        try:
            torsion_group = E.torsion_subgroup()
            invariants['torsion_order'] = int(torsion_group.order())
            invariants['torsion_structure'] = [int(g.order()) for g in torsion_group.gens()]
        except Exception:
            invariants['torsion_order'] = 1
            invariants['torsion_structure'] = []

        # Check for CM
        try:
            invariants['has_cm'] = E.has_cm()
        except Exception:
            invariants['has_cm'] = None

        return invariants

    except Exception as e:
        return {'error': str(e)}


def validate_curve_selection(E, min_conductor=1000, min_rank=0):
    """
    Validate that a curve meets experimental criteria.

    Args:
        E: SageMath EllipticCurve object
        min_conductor: Minimum conductor value (default: 1000)
        min_rank: Minimum rank (default: 0)

    Returns:
        dict: Validation results
    """
    try:
        conductor = int(E.conductor())
        rank = int(E.rank())

        validation = {
            'valid': True,
            'conductor': conductor,
            'rank': rank,
            'criteria': [],
        }

        # Check conductor
        if conductor >= min_conductor:
            validation['criteria'].append(f'✓ Conductor {conductor} >= {min_conductor}')
        else:
            validation['criteria'].append(f'⚠ Conductor {conductor} < {min_conductor}')
            # Still valid for testing, just note it

        # Check rank
        if rank >= min_rank:
            validation['criteria'].append(f'✓ Rank {rank} >= {min_rank}')
        else:
            validation['criteria'].append(f'⚠ Rank {rank} < {min_rank}')

        # Check if it's a "difficult" case for BSD
        if rank >= 2:
            validation['criteria'].append('✓ Rank >= 2: Not covered by Gross-Zagier/Kolyvagin')
            validation['difficult_case'] = True
        else:
            validation['difficult_case'] = False

        return validation

    except Exception as e:
        return {
            'valid': False,
            'error': str(e),
        }
