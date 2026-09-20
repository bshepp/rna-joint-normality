"""Exact joint distribution of (hairpins, basepairs) at finite n versus the Gaussian limit.

Illustration and sanity check only: no step of the proof depends on it.

Method. The weight enumerators f_n(x,z) satisfy (Lemma 3 of the note)
    S = 1 + X S + z X^2 S (S - 1 + (x-1) X/(1-X)),        S = sum_n f_n X^n .
We run this recurrence simultaneously at all points (x,z) of a grid of roots of unity and recover the
coefficients of f_n by an inverse DFT. Everything is rescaled by rho0^n so the numbers stay O(1).
Floating point (relative error about 1e-13 on the bulk of the distribution, which is all that is plotted).

Usage:  python joint_distribution.py            -> joint_distribution.pdf/.png + printed table
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

RHO0 = (3 - 5 ** 0.5) / 2
MU = np.array([1 - 2 / 5 ** 0.5, (5 - 5 ** 0.5) / 10])
H = np.array([[2 - 22 / (5 * 5 ** 0.5), (25 - 11 * 5 ** 0.5) / 50],
              [(25 - 11 * 5 ** 0.5) / 50, 1 / (10 * 5 ** 0.5)]])


def pmfs(ns):
    """Exact joint pmf P(hairpins=i, basepairs=j) for each n in ns. Returns {n: array[i,j]}."""
    nmax = max(ns)
    A, B = nmax // 3 + 2, nmax // 2 + 2          # hairpins <= (n-1)/3... , basepairs <= (n-1)/2
    x = np.exp(2j * np.pi * np.arange(A) / A)[:, None] * np.ones((1, B))
    z = np.ones((A, 1)) * np.exp(2j * np.pi * np.arange(B) / B)[None, :]
    x, z = x.ravel(), z.ravel()
    G = x.size
    s = np.zeros((nmax + 1, G), dtype=complex)   # s[n] = f_n * rho0^n on the grid
    t = np.zeros((nmax + 1, G), dtype=complex)   # t[k] = coefficient of X^k in S - 1 + (x-1)X/(1-X), rescaled
    s[0] = 1
    for n in range(1, nmax + 1):
        s[n] = RHO0 * s[n - 1]
        if n >= 3:
            ks = np.arange(1, n - 1)
            s[n] += z * RHO0 ** 2 * np.einsum("kg,kg->g", t[ks], s[n - 2 - ks])
        t[n] = s[n] + (x - 1) * RHO0 ** n
    out = {}
    for n in ns:
        c = np.fft.fft2(s[n].reshape(A, B)).real / (A * B)   # coefficient extraction: sum_a f(w^a) w^(-ak) / A
        c[c < 0] = 0
        out[n] = c / c.sum()
    return out


def moments(p):
    i = np.arange(p.shape[0])[:, None]
    j = np.arange(p.shape[1])[None, :]
    m = np.array([(p * i).sum(), (p * j).sum()])
    cov = np.array([[(p * (i - m[0]) ** 2).sum(), (p * (i - m[0]) * (j - m[1])).sum()],
                    [0, (p * (j - m[1]) ** 2).sum()]])
    cov[1, 0] = cov[0, 1]
    return m, cov


def gaussian_on_lattice(shape, m, cov):
    i = np.arange(shape[0])[:, None] - m[0]
    j = np.arange(shape[1])[None, :] - m[1]
    P = np.linalg.inv(cov)
    g = np.exp(-0.5 * (P[0, 0] * i * i + 2 * P[0, 1] * i * j + P[1, 1] * j * j))
    return g / g.sum()


def main():
    ns = [50, 100, 200, 400, 800]   # n = 800 dominates the run time (about 10 minutes)
    import os
    if os.path.exists("pmfs_cache.npz"):          # delete this file to recompute from scratch
        z = np.load("pmfs_cache.npz"); P = {n: z[str(n)] for n in ns}
    else:
        P = pmfs(ns); np.savez_compressed("pmfs_cache.npz", **{str(n): P[n] for n in ns})

    # external validation against the exact moments computed in verify.wls (n = 200)
    m, cov = moments(P[200])
    ref = np.array([0.10715348527, 0.27452661711, 0.03236548856, 0.04499314274, 0.21383381619])
    got = np.array([m[0] / 200, m[1] / 200, cov[0, 0] / 200, cov[1, 1] / 200,
                    cov[0, 1] / np.sqrt(cov[0, 0] * cov[1, 1])])
    assert np.allclose(got, ref, rtol=1e-9, atol=0), (got, ref)

    print(" n    E[X]/n    E[Z]/n   Var X/n   Var Z/n     corr     TV(exact, Gaussian)")
    rows = []
    for n in ns:
        m, cov = moments(P[n])
        tv = 0.5 * np.abs(P[n] - gaussian_on_lattice(P[n].shape, m, cov)).sum()
        rows.append((n, tv))
        print(f"{n:4d}  {m[0]/n:.6f}  {m[1]/n:.6f}  {cov[0,0]/n:.6f}  {cov[1,1]/n:.6f}  "
              f"{cov[0,1]/np.sqrt(cov[0,0]*cov[1,1]):.6f}   {tv:.4f}")
    print(f"limit {MU[0]:.6f}  {MU[1]:.6f}  {H[0,0]:.6f}  {H[1,1]:.6f}  "
          f"{H[0,1]/np.sqrt(H[0,0]*H[1,1]):.6f}   0")

    # ---------------- figure (n = 400) ----------------
    n = 400
    p = P[n]
    m, cov = moments(p)
    sd = np.sqrt(np.diag(cov))
    ink, muted, blue = "#1a1a1a", "#6b6b6b", "#2a6fb0"
    plt.rcParams.update({"font.size": 8, "axes.edgecolor": muted, "axes.linewidth": 0.6,
                         "xtick.color": muted, "ytick.color": muted, "axes.labelcolor": ink,
                         "font.family": "DejaVu Sans"})
    fig, ax = plt.subplots(1, 3, figsize=(7.2, 2.5), gridspec_kw={"width_ratios": [1.25, 1, 1]})

    # joint: exact pmf as a one-hue heatmap, limit law as 1,2,3-sigma ellipses
    i0, i1 = int(m[0] - 4.2 * sd[0]), int(m[0] + 4.2 * sd[0]) + 1
    j0, j1 = int(m[1] - 4.2 * sd[1]), int(m[1] + 4.2 * sd[1]) + 1
    a = ax[0]
    a.imshow(p[i0:i1 + 1, j0:j1 + 1], origin="lower", cmap="Blues", aspect="auto",
             extent=(j0 - .5, j1 + .5, i0 - .5, i1 + .5), interpolation="nearest")
    Hn = n * H
    w, v = np.linalg.eigh(Hn[::-1, ::-1])        # (basepairs, hairpins) order for plotting
    th = np.linspace(0, 2 * np.pi, 400)
    mean_lim = (n * MU + np.array([(13 - 3 * 5 ** .5) / 20, -(3 + 2 * 5 ** .5) / 20]))[::-1]
    for r in (1, 2, 3):
        e = mean_lim[:, None] + r * (v @ (np.sqrt(w)[:, None] * np.array([np.cos(th), np.sin(th)])))
        a.plot(e[0], e[1], color=ink, lw=0.8)
    a.text(mean_lim[0], mean_lim[1] + 3.15 * np.sqrt(Hn[0, 0]), "1, 2, 3 σ of the limit law",
           ha="center", va="bottom", color=ink, fontsize=7)
    a.set_xlim(j0 - .5, j1 + .5); a.set_ylim(i0 - .5, i1 + .5)
    a.set_xlabel("basepairs"); a.set_ylabel("hairpins")
    a.set_title(f"exact joint distribution, n = {n}", fontsize=8, color=ink, loc="left")

    # marginals: exact pmf (dots) against the normal density with the limit parameters (line)
    for a, axis, k, name in ((ax[1], 1, 0, "hairpins"), (ax[2], 0, 1, "basepairs")):
        q = p.sum(axis=axis)
        lo, hi = int(m[k] - 4.2 * sd[k]), int(m[k] + 4.2 * sd[k]) + 1
        kk = np.arange(lo, hi + 1)
        mu_k, var_k = mean_lim[::-1][k], n * H[k, k]
        xs = np.linspace(lo, hi, 400)
        a.plot(xs, np.exp(-(xs - mu_k) ** 2 / (2 * var_k)) / np.sqrt(2 * np.pi * var_k), color=ink, lw=1.0,
               label="normal limit")
        a.plot(kk, q[kk], "o", ms=2.6, color=blue, mec="white", mew=0.3, label="exact")
        a.set_xlabel(name); a.set_yticks([])
        for sp in ("top", "right", "left"):
            a.spines[sp].set_visible(False)
        a.set_title(f"{name}: exact vs. normal", fontsize=8, color=ink, loc="left")
    ax[1].legend(frameon=False, fontsize=6.5, loc="upper left", bbox_to_anchor=(-0.04, 1.0), handlelength=1.2,
                 borderpad=0, labelspacing=0.3)
    fig.tight_layout(w_pad=1.2)
    fig.savefig("joint_distribution.pdf")
    fig.savefig("joint_distribution.png", dpi=220)
    with open("joint_distribution_table.txt", "w") as f:
        for n_, tv in rows:
            f.write(f"{n_} {tv:.4f}\n")


if __name__ == "__main__":
    main()
