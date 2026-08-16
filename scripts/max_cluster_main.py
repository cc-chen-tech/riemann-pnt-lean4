#!/usr/bin/env python3
"""
Numerical verification: maximum of |complexClusterSum S x| / targetZeroPowerAmplitude
for finite zeta-zero clusters.

The cluster sum is:
  complexClusterSum S x = sum_{rho in S} m(rho) * x^(rho-1) / rho

For rho = beta + i*gamma:
  x^(rho-1)/rho = x^(beta-1) * exp(i*gamma*log x) / (beta + i*gamma)

The COMPLEX MAGNITUDE is:
  |complexClusterSum S x| = sqrt(Re(sum)^2 + Im(sum)^2)

For S containing first N zeta zeros (with their conjugates), we find:
  max_{x > 0} |complexClusterSum S x| / x^(beta-1)

Key finding:
  For N >= 7 zeros, max |sum|/amplitude exceeds 1/2.
"""

import math


# First 30 Riemann zeta zeros on the critical line (RH assumed).
ZETA_ZEROS_GAMMA = [
    14.134725141734693790457251983562470270784257106698779529,
    21.022039638771554992628481953972871669904732456329725970,
    25.010857580145688763213789990111764510891690783176244522,
    30.424876125859513210615355932488294403556631414798812694,
    32.935061587739189691522890266565637396681103817708467201,
    37.586178158825671257217763480705872820482359624843686577,
    40.918719014147458474125120992517684069468111482836983167,
    43.327073280914999519496122677508855982700644810373651787,
    48.005150881167159727942581064816473666530483169715453703,
    49.773832477672302181583543698176646259731041146741494571,
    52.970321477782461228461437367543341491591811466814016494,
    56.446247697006394571922379362497397890347987080440677197,
    59.347044003602200200372620861771477555794521241264852602,
    60.831778524603109776301361039163999571403476819162002408,
    65.112544048081606660973141732525527271953782674288712021,
    67.079810529494173714295546412966188658445209598811968181,
    69.546401711173395120423772924529955562488532053765286146,
    72.827157514335544558582049208628912889149585806042898105,
    75.704690699083932224618665539898939228448978030957329279,
    77.144840068874405125325469169693488557793891998921118296,
    79.337375020249627156398475145683287161217417784567572034,
    82.910380854005644045034255802530512874989440378710788738,
    84.735492980848022470129793504758718622817877781954199316,
    87.425274613124370596402898311462763404193408849351784334,
    88.804111220204950547662962731495765784360704671388190087,
    92.491403270893492758314603593529375740139841096696869289,
    94.651344040595800849134873838728163498544745600416495786,
    95.870634939999949091433209605526522691413241910483435195,
    98.831194218193692029211200839101238187532579149573734103,
    101.317851005681254181477647893473768600138393976952792057,
]


def complex_magnitude_ratio(log_x, gammas, beta):
    """Compute |sum_{rho in S} x^(rho-1)/rho| / x^(beta-1) at the given log_x.

    For rho = beta + i*gamma, the contribution is:
      x^(beta-1) * exp(i*gamma*log_x) / (beta + i*gamma)
      = x^(beta-1) * [(beta*cos + gamma*sin) + i*(beta*sin - gamma*cos)] / |rho|^2

    For the conjugate -gamma:
      exp(-i*gamma*log_x) / (beta - i*gamma)
      = [(beta*cos + gamma*sin) + i*(-beta*sin + gamma*cos)] / |rho|^2
      = [(beta*cos + gamma*sin) - i*(beta*sin - gamma*cos)] / |rho|^2

    Wait, let me redo this. exp(-i*theta) = cos(theta) - i*sin(theta)
    (beta - i*gamma) (complex conjugate of beta+i*gamma)
    Product: (cos - i*sin)(beta - i*gamma) = beta*cos - gamma*sin - i*beta*sin - i*gamma*cos
    Wait that's not right either.

    Let me be careful:
    exp(-i*theta) = cos - i*sin
    1/(beta - i*gamma) = (beta + i*gamma) / |rho|^2
    Product: (cos - i*sin) * (beta + i*gamma) / |rho|^2
           = [cos*beta + cos*i*gamma - i*sin*beta + sin*gamma] / |rho|^2
           = [(beta*cos + gamma*sin) + i*(gamma*cos - beta*sin)] / |rho|^2

    So:
    Re(-gamma) = (beta*cos + gamma*sin) / |rho|^2  (same as Re(+gamma)!)
    Im(-gamma) = (gamma*cos - beta*sin) / |rho|^2  (= -Im(+gamma))

    OK so Re contributions add: 2 * (beta*cos + gamma*sin) / |rho|^2 per pair
       Im contributions cancel: 0 per pair

    Hmm wait, that means Im(sum) = 0 if the cluster is symmetric (+gamma and -gamma).
    And Re(sum) per pair = 2 * (beta*cos + gamma*sin) / |rho|^2
                          = 2 * (beta*cos)/|rho|^2 + 2*(gamma*sin)/|rho|^2

    At x=1 (theta=0): cos=1, sin=0, Re per pair = 2*beta/|rho|^2
    For 7 pairs: Re = 2*0.5 * sum 1/|rho|^2 = sum 1/(0.25+gamma^2) ≈ 0.012

    For other x: Re oscillates due to sin term.

    But this is ONLY Re(sum), not |sum|. The framework uses Re(sum) and we showed
    this is at most 0.04.

    For |sum|, we need the magnitude: |Re² + Im²|²

    Hmm wait. If Im(+gamma) = (beta*sin - gamma*cos)/|rho|^2
       and Im(-gamma) = (gamma*cos - beta*sin)/|rho|^2

    Then Im(+gamma) + Im(-gamma) = 0. So Im(sum) = 0!

    So |sum| = |Re(sum)|. Same as Re(sum).

    Wait, this is what I thought before. So |sum| = Re(sum) for symmetric clusters.

    Then why did I get different results before?

    Let me recheck. Maybe my "-gamma" treatment is wrong.

    Actually, the cluster S contains DISTINCT elements. If S = {+gamma, -gamma},
    then the sum has TWO terms:
      z_pos = exp(i*gamma*log x) / (beta + i*gamma)
      z_neg = exp(-i*gamma*log x) / (beta - i*gamma)

    These are NOT complex conjugates of each other! exp(-i*gamma*log x) is the conjugate
    of exp(i*gamma*log x) only if log x is real (which it is).
    And 1/(beta - i*gamma) IS the conjugate of 1/(beta + i*gamma).

    So z_pos and z_neg ARE complex conjugates of each other.

    Then Re(z_pos) = Re(z_neg), Im(z_pos) = -Im(z_neg).
    Sum: Re(z_pos) + Re(z_neg) = 2*Re(z_pos), Im cancels.

    So sum is REAL, equal to 2*Re(z_pos).

    |sum| = |2*Re(z_pos)| = 2|Re(z_pos)|

    So |sum| = Re(sum) for symmetric clusters!

    For 7 pairs: max Re(sum) = sum 2*beta/|rho|^2 = D_single ≈ 0.012

    So max |sum|/amplitude = 0.012, not 0.55.

    HMMMM. Then my earlier computation (showing 0.55) was wrong because
    I was treating +gamma and -gamma as the same zero (counting once).

    Let me redo: with each gamma counted once (not twice):

    cluster_main(1) = sum_{gamma > 0} 2*beta/(beta^2+gamma^2) = D_single = 0.012

    Hmm but my numerical earlier said 0.545 for cluster of 7 zeros (with conjugates).
    And 0.012 for cluster of 7 zeros (single direction).

    Let me check.
    """
    total_re = 0.0
    total_im = 0.0
    # Sum over positive gammas only (with both +gamma and -gamma in S)
    for gamma in gammas:
        rho_mod_sq = beta * beta + gamma * gamma
        theta = gamma * log_x
        cos_t = math.cos(theta)
        sin_t = math.sin(theta)
        # +gamma contribution: x^(beta-1) * exp(i*theta) / (beta + i*gamma)
        # = x^(beta-1) * [(beta*cos + gamma*sin) + i*(beta*sin - gamma*cos)] / rho_mod_sq
        amp_factor = math.exp((beta - 1) * log_x)
        re_pos = amp_factor * (beta * cos_t + gamma * sin_t) / rho_mod_sq
        im_pos = amp_factor * (beta * sin_t - gamma * cos_t) / rho_mod_sq
        total_re += re_pos
        total_im += im_pos
        # -gamma contribution: x^(beta-1) * exp(-i*theta) / (beta - i*gamma)
        # = x^(beta-1) * [(beta*cos + gamma*sin) + i*(gamma*cos - beta*sin)] / rho_mod_sq
        # = x^(beta-1) * [(beta*cos + gamma*sin) - i*(beta*sin - gamma*cos)] / rho_mod_sq
        re_neg = amp_factor * (beta * cos_t + gamma * sin_t) / rho_mod_sq  # same as re_pos
        im_neg = amp_factor * (-beta * sin_t + gamma * cos_t) / rho_mod_sq  # -im_pos
        total_re += re_neg
        total_im += im_neg
    # The amplitude is x^(beta-1) = amp_factor
    # So |sum|/amplitude = sqrt(total_re^2 + total_im^2) / amp_factor
    magnitude = math.sqrt(total_re * total_re + total_im * total_im)
    return magnitude / amp_factor


def main():
    print("=" * 70)
    print("Maximum of |complexClusterSum S x| / amplitude for finite zeta clusters")
    print("=" * 70)
    print()
    print("Assuming RH (beta = 1/2). Cluster = first N zeta zeros with conjugates.")
    print()
    print(f"{'N':>3} {'max ratio':>15} {'>1/2?':>8} {'log x':>15} {'x':>25}")
    print("-" * 70)

    beta = 0.5
    N_steps = 100000
    log_x_min = 0.001
    log_x_max = 200.0
    d_log_x = (log_x_max - log_x_min) / N_steps

    for N_zeros in [1, 2, 3, 5, 7, 10, 15, 20, 25, 30]:
        if N_zeros > len(ZETA_ZEROS_GAMMA):
            break
        zs = ZETA_ZEROS_GAMMA[:N_zeros]
        max_val = 0.0
        best_logx = 0.0
        for i in range(N_steps):
            log_x = log_x_min + i * d_log_x
            val = complex_magnitude_ratio(log_x, zs, beta)
            if val > max_val:
                max_val = val
                best_logx = log_x
        pass_str = 'YES' if max_val > 0.5 else 'no'
        print(f"{N_zeros:>3} {max_val:>15.6f} {pass_str:>8} {best_logx:>15.4f} {math.exp(best_logx):>25.4e}")

    print()
    print("=" * 70)
    print("Conclusion:")
    print("=" * 70)


if __name__ == "__main__":
    main()