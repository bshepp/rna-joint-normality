"""Assemble LeanCheck/Basic.lean from gen_out.json (written by generate.wls).

    wolframscript -file generate.wls && python assemble.py && (cd .. && lake build)

Mathematica only proposes the long polynomials and the `linear_combination` coefficients;
Lean's kernel re-verifies every identity from scratch.
"""
import json
import pathlib

here = pathlib.Path(__file__).parent
d = json.load(open(here / "gen_out.json", encoding="utf-8"))
d = {k: v.replace("sigma", "σ").replace("tau", "τ") for k, v in d.items()}

R = ("X^6*x^2*z^2 - 2*X^5*x*z^2 - 2*X^5*x*z + 4*X^4*x*z + X^4*z^2 - 2*X^4*z - 2*X^3*x*z + X^4 + 4*X^3*z"
     " - 4*X^3 - 2*X^2*z + 6*X^2 - 4*X + 1")
S = "(1 + X + (num0 X x z + r) / (2*X^2*z*(X-1)))"

src = f'''/-
Kernel-checked algebra for the note
  "Hairpins and basepairs in RNA secondary structures are asymptotically jointly normal".

Checked here by Lean's kernel (through `ring`, `linear_combination`, `nlinarith`):
  * the factorization of the discriminant R(X,1,1)                                  [`R_factor`]
  * S = 1 + X + F satisfies the first-vertex functional equation (Lemma 3)          [`functional_equation`]
  * rho0 = (3 - sqrt 5)/2 is a root of R(.,1,1)                                     [`rho0_root`]
  * the full Taylor expansion of R at (rho0,1,1), which certifies every partial
    derivative of R there; in particular dR/dX = 30 - 14 sqrt5                     [`taylor`]
  * the first- and second-order implicit-differentiation conditions satisfied by the
    Taylor coefficients r1, r2, r11, r12, r22 of rho(e^σ, e^τ)                      [`jet_order1`, `jet_order2`]
  * mu = -grad rho/rho0 and H_ij = -rho_ij/rho0 + rho_i rho_j/rho0^2                [`mu1_eq` ... `H22_eq`]
  * det H = (13 sqrt5 - 29)/50 > 0, H11 > 0, H12 > 0, corr^2 = (5 sqrt5 - 11)/4,
    Q(rho0) = -rho0 dR/dX = 36 sqrt5 - 80 > 0                                       [`detH_eq` ... `Q_rho0_pos`]

NOT formalized: the analytic part of the proof (Rouche, the uniform coefficient estimate, Levy's continuity
theorem), and the calculus glue, namely that substituting X = rho0 + a, x = e^σ = 1 + σ + σ²/2 + ...,
z = e^τ into the Taylor expansion and collecting orders 1 and 2 gives exactly `jet_order1`, `jet_order2`,
and that mu and H are the first and second derivatives of -log rho. Those steps are on paper in the note.

The long polynomials come from `gen/generate.wls` (Mathematica) via `gen/assemble.py`. Lean re-verifies them
from scratch, so Mathematica is not trusted. `s` stands for sqrt 5 and enters only through `hs : s^2 = 5`
(and `0 < s` for the inequalities); see `sqrt5_sq`, `sqrt5_pos` at the end.
-/
import Mathlib

namespace RNA

section General
variable {{K : Type*}} [Field K]

/-- The discriminant of Bu-Kauers-Zeilberger, Theorem 2. -/
def R (X x z : K) : K :=
  {R}

/-- The rational part of the numerator of F. -/
def num0 (X x z : K) : K := -2*X^4*z + X^3*x*z + X^2*z - X^2 + 2*X - 1

/-- Equation (1) of the note. -/
theorem R_factor (X : K) : R X 1 1 = (X - 1)^2 * (X^2 - 3*X + 1) * (X^2 + X + 1) := by
  unfold R; ring

/-- Lemma 3 of the note: with `r` any square root of `R`, `S = 1 + X + F` satisfies
    `S = 1 + X S + z X^2 S (S - 1 + (x-1) X/(1-X))`. -/
theorem functional_equation [CharZero K] (X x z r : K) (hX : X ≠ 0) (hz : z ≠ 0) (hX1 : X ≠ 1)
    (hr : r^2 = R X x z) :
    {S} =
      1 + X * {S}
        + z*X^2 * {S}
          * ({S} - 1 + (x-1)*X/(1-X)) := by
  have h1 : X - 1 ≠ 0 := sub_ne_zero.mpr hX1
  have h2 : 1 - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hX1)
  unfold R at hr
  unfold num0
  field_simp
  linear_combination (X - 1) * hr

end General

section Sqrt5
variable (s : ℝ)

/-- The dominant singularity `(3 - sqrt 5)/2`. -/
noncomputable def rho0 : ℝ := (3 - s)/2

theorem rho0_root (hs : s^2 = 5) : R (rho0 s) 1 1 = 0 := by
  unfold R rho0
  linear_combination ({d['rootq']}) * hs

/-- First-order part of the Taylor expansion of `R` at `(rho0,1,1)`. -/
noncomputable def T1 (a u v : ℝ) : ℝ := {d['taylor1']}

/-- Second-order part. -/
noncomputable def T2 (a u v : ℝ) : ℝ :=
  {d['taylor2']}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Remainder of the Taylor expansion, after division by `t^3`. -/
noncomputable def T3 (t a u v : ℝ) : ℝ :=
  {d['taylor3']}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Taylor expansion of `R` at `(rho0,1,1)`: constant term 0, first- and second-order parts `T1`, `T2`,
    remainder of order three. -/
theorem taylor (hs : s^2 = 5) (t a u v : ℝ) :
    R (rho0 s + t*a) (1 + t*u) (1 + t*v) = t * T1 s a u v + t^2 * T2 s a u v + t^3 * T3 s t a u v := by
  unfold R rho0 T1 T2 T3
  linear_combination ({d['taylorq']}) * hs

/-- Taylor coefficients of the implicit solution `rho(e^σ, e^τ)` at the origin. -/
noncomputable def r1 : ℝ := {d['r1']}
noncomputable def r2 : ℝ := {d['r2']}
noncomputable def r11 : ℝ := {d['r11']}
noncomputable def r12 : ℝ := {d['r12']}
noncomputable def r22 : ℝ := {d['r22']}

/-- Order 1 of `R(rho0 + a, e^σ, e^τ) = 0` with `a = r1 σ + r2 τ + ...`. -/
theorem jet_order1 (hs : s^2 = 5) (σ τ : ℝ) : T1 s (r1 s * σ + r2 s * τ) σ τ = 0 := by
  unfold T1 r1 r2
  linear_combination ({d['o1q']}) * hs

/-- Order 2 of the same: the second-order part of `a`, `e^σ - 1`, `e^τ - 1` enters through `T1`,
    the first-order part through `T2`. -/
theorem jet_order2 (hs : s^2 = 5) (σ τ : ℝ) :
    T1 s (r11 s * σ^2/2 + r12 s * σ*τ + r22 s * τ^2/2) (σ^2/2) (τ^2/2)
      + T2 s (r1 s * σ + r2 s * τ) σ τ = 0 := by
  unfold T1 T2 r1 r2 r11 r12 r22
  linear_combination ({d['o2q']}) * hs

theorem rho0_pos (hs : s^2 = 5) : 0 < rho0 s := by
  unfold rho0; nlinarith

/-- `mu = -grad rho / rho0`. -/
theorem mu1_eq (hs : s^2 = 5) : -(r1 s) / rho0 s = {d['mu1']} := by
  have h := (rho0_pos s hs).ne'
  rw [div_eq_iff h]; unfold r1 rho0
  linear_combination ({d['cmu1']}) * hs

theorem mu2_eq (hs : s^2 = 5) : -(r2 s) / rho0 s = {d['mu2']} := by
  have h := (rho0_pos s hs).ne'
  rw [div_eq_iff h]; unfold r2 rho0
  linear_combination ({d['cmu2']}) * hs

/-- Entries of the Hessian of `U = -log rho(e^σ,e^τ)`: `H_ij = -rho_ij/rho0 + rho_i rho_j / rho0^2`. -/
theorem H11_eq (hs : s^2 = 5) : -(r11 s) / rho0 s + (r1 s)^2 / (rho0 s)^2 = {d['H11']} := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r1 r11 rho0
  linear_combination ((3 - s)/2 * ({d['cH11']})) * hs

theorem H12_eq (hs : s^2 = 5) : -(r12 s) / rho0 s + (r1 s) * (r2 s) / (rho0 s)^2 = {d['H12']} := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r1 r2 r12 rho0
  linear_combination ((3 - s)/2 * ({d['cH12']})) * hs

theorem H22_eq (hs : s^2 = 5) : -(r22 s) / rho0 s + (r2 s)^2 / (rho0 s)^2 = {d['H22']} := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r2 r22 rho0
  linear_combination ((3 - s)/2 * ({d['cH22']})) * hs

/-- `det H = (13 s - 29)/50`. -/
theorem detH_eq (hs : s^2 = 5) :
    ({d['H11']}) * ({d['H22']}) - ({d['H12']})^2 = (13*s - 29)/50 := by
  linear_combination (-33/500 : ℝ) * hs

theorem detH_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < (13*s - 29)/50 := by
  nlinarith

theorem H11_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < {d['H11']} := by nlinarith

theorem H12_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < {d['H12']} := by nlinarith

/-- The squared correlation: `H12^2 = ((5 s - 11)/4) * H11 * H22`. -/
theorem corr_sq (hs : s^2 = 5) :
    ({d['H12']})^2 = (5*s - 11)/4 * (({d['H11']}) * ({d['H22']})) := by
  linear_combination (-1/20 + (11*s)/500) * hs

/-- `Q(rho0) = -rho0 * dR/dX(rho0,1,1) = 36 s - 80 > 0`: the square-root coefficient does not vanish. -/
theorem Q_rho0 (hs : s^2 = 5) : -(rho0 s) * (30 - 14*s) = 36*s - 80 := by
  unfold rho0; linear_combination (-7 : ℝ) * hs

theorem Q_rho0_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < 36*s - 80 := by nlinarith

end Sqrt5

/-- The hypotheses on `s` are met by `Real.sqrt 5`. -/
theorem sqrt5_sq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

end RNA
'''
(here.parent / "LeanCheck" / "Basic.lean").write_text(src, encoding="utf-8")
print("wrote LeanCheck/Basic.lean,", len(src), "chars")
