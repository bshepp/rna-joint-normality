/-
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
variable {K : Type*} [Field K]

/-- The discriminant of Bu-Kauers-Zeilberger, Theorem 2. -/
def R (X x z : K) : K :=
  X^6*x^2*z^2 - 2*X^5*x*z^2 - 2*X^5*x*z + 4*X^4*x*z + X^4*z^2 - 2*X^4*z - 2*X^3*x*z + X^4 + 4*X^3*z - 4*X^3 - 2*X^2*z + 6*X^2 - 4*X + 1

/-- The rational part of the numerator of F. -/
def num0 (X x z : K) : K := -2*X^4*z + X^3*x*z + X^2*z - X^2 + 2*X - 1

/-- Equation (1) of the note. -/
theorem R_factor (X : K) : R X 1 1 = (X - 1)^2 * (X^2 - 3*X + 1) * (X^2 + X + 1) := by
  unfold R; ring

/-- Lemma 3 of the note: with `r` any square root of `R`, `S = 1 + X + F` satisfies
    `S = 1 + X S + z X^2 S (S - 1 + (x-1) X/(1-X))`. -/
theorem functional_equation [CharZero K] (X x z r : K) (hX : X ≠ 0) (hz : z ≠ 0) (hX1 : X ≠ 1)
    (hr : r^2 = R X x z) :
    (1 + X + (num0 X x z + r) / (2*X^2*z*(X-1))) =
      1 + X * (1 + X + (num0 X x z + r) / (2*X^2*z*(X-1)))
        + z*X^2 * (1 + X + (num0 X x z + r) / (2*X^2*z*(X-1)))
          * ((1 + X + (num0 X x z + r) / (2*X^2*z*(X-1))) - 1 + (x-1)*X/(1-X)) := by
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
  linear_combination (19/64 - (23*s)/32 + (9*s^2)/16 - (5*s^3)/32 + s^4/64) * hs

/-- First-order part of the Taylor expansion of `R` at `(rho0,1,1)`. -/
noncomputable def T1 (a u v : ℝ) : ℝ := a*(30 - 14*s) + (152 - 68*s)*u + (58 - 26*s)*v

/-- Second-order part. -/
noncomputable def T2 (a u v : ℝ) : ℝ :=
  a^2*(143/2 - (61*s)/2) + (161 - 72*s)*u^2 + (351 - 157*s)*u*v + (123/2 - (55*s)/2)*v^2 + a*((391 - 175*s)*u + (192 - 86*s)*v)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Remainder of the Taylor expansion, after division by `t^3`. -/
noncomputable def T3 (t a u v : ℝ) : ℝ :=
  62*a^3 - 28*a^3*s + 420*a^2*u - 188*a^2*s*u + 369*a*u^2 - 165*a*s*u^2 + 256*a^2*v - 114*a^2*s*v + 894*a*u*v - 400*a*s*u*v + 322*u^2*v - 144*s*u^2*v + 170*a*v^2 - 76*a*s*v^2 + 199*u*v^2 - 89*s*u*v^2 + a^6*t^7*u^2*v^2 + t*((53*a^4)/2 - (25*a^4*s)/2 + 242*a^3*u - 108*a^3*s*u + (705*a^2*u^2)/2 - (315*a^2*s*u^2)/2 + 176*a^3*v - 78*a^3*s*v + 945*a^2*u*v - 423*a^2*s*u*v + 738*a*u^2*v - 330*a*s*u^2*v + (387*a^2*v^2)/2 - (173*a^2*s*v^2)/2 + 503*a*u*v^2 - 225*a*s*u*v^2 + 161*u^2*v^2 - 72*s*u^2*v^2) + t^2*(5*a^5 - 3*a^5*s + 79*a^4*u - 35*a^4*s*u + 180*a^3*u^2 - 80*a^3*s*u^2 + 64*a^4*v - 30*a^4*s*v + 532*a^3*u*v - 238*a^3*s*u*v + 705*a^2*u^2*v - 315*a^2*s*u^2*v + 116*a^3*v^2 - 52*a^3*s*v^2 + 525*a^2*u*v^2 - 235*a^2*s*u*v^2 + 369*a*u^2*v^2 - 165*a*s*u^2*v^2) + t^3*(a^6 + 14*a^5*u - 6*a^5*s*u + (105*a^4*u^2)/2 - (45*a^4*s*u^2)/2 + 12*a^5*v - 6*a^5*s*v + 169*a^4*u*v - 75*a^4*s*u*v + 360*a^3*u^2*v - 160*a^3*s*u^2*v + (77*a^4*v^2)/2 - (35*a^4*s*v^2)/2 + 290*a^3*u*v^2 - 130*a^3*s*u*v^2 + (705*a^2*u^2*v^2)/2 - (315*a^2*s*u^2*v^2)/2) + t^4*(2*a^6*u + 9*a^5*u^2 - 3*a^5*s*u^2 + 2*a^6*v + 30*a^5*u*v - 12*a^5*s*u*v + 105*a^4*u^2*v - 45*a^4*s*u^2*v + 7*a^5*v^2 - 3*a^5*s*v^2 + 90*a^4*u*v^2 - 40*a^4*s*u*v^2 + 180*a^3*u^2*v^2 - 80*a^3*s*u^2*v^2) + t^5*(a^6*u^2 + 4*a^6*u*v + 18*a^5*u^2*v - 6*a^5*s*u^2*v + a^6*v^2 + 16*a^5*u*v^2 - 6*a^5*s*u*v^2 + (105*a^4*u^2*v^2)/2 - (45*a^4*s*u^2*v^2)/2) + t^6*(2*a^6*u^2*v + 2*a^6*u*v^2 + 9*a^5*u^2*v^2 - 3*a^5*s*u^2*v^2)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Taylor expansion of `R` at `(rho0,1,1)`: constant term 0, first- and second-order parts `T1`, `T2`,
    remainder of order three. -/
theorem taylor (hs : s^2 = 5) (t a u v : ℝ) :
    R (rho0 s + t*a) (1 + t*u) (1 + t*v) = t * T1 s a u v + t^2 * T2 s a u v + t^3 * T3 s t a u v := by
  unfold R rho0 T1 T2 T3
  linear_combination (19/64 + (119*a*t)/16 + (261*a^2*t^2)/16 + (25*a^3*t^3)/2 + (15*a^4*t^4)/4 + (935*t*u)/32 + (577*a*t^2*u)/8 + (573*a^2*t^3*u)/8 + 35*a^3*t^4*u + (15*a^4*t^5*u)/2 + (1915*t^2*u^2)/64 + (1035*a*t^3*u^2)/16 + (885*a^2*t^4*u^2)/16 + (45*a^3*t^5*u^2)/2 + (15*a^4*t^6*u^2)/4 + (373*t*v)/32 + (153*a*t^2*v)/4 + (393*a^2*t^3*v)/8 + 30*a^3*t^4*v + (15*a^4*t^5*v)/2 + (135*t^2*u*v)/2 + (1317*a*t^3*u*v)/8 + (639*a^2*t^4*u*v)/4 + 75*a^3*t^5*u*v + 15*a^4*t^6*u*v + (1915*t^3*u^2*v)/32 + (1035*a*t^4*u^2*v)/8 + (885*a^2*t^5*u^2*v)/8 + 45*a^3*t^6*u^2*v + (15*a^4*t^7*u^2*v)/2 + (771*t^2*v^2)/64 + (517*a*t^3*v^2)/16 + (549*a^2*t^4*v^2)/16 + (35*a^3*t^5*v^2)/2 + (15*a^4*t^6*v^2)/4 + (1225*t^3*u*v^2)/32 + (185*a*t^4*u*v^2)/2 + (705*a^2*t^5*u*v^2)/8 + 40*a^3*t^6*u*v^2 + (15*a^4*t^7*u*v^2)/2 + (1915*t^4*u^2*v^2)/64 + (1035*a*t^5*u^2*v^2)/16 + (885*a^2*t^6*u^2*v^2)/16 + (45*a^3*t^7*u^2*v^2)/2 + (15*a^4*t^8*u^2*v^2)/4 + s^4*(1/64 + (t*u)/32 + (t^2*u^2)/64 + (t*v)/32 + (t^2*u*v)/16 + (t^3*u^2*v)/32 + (t^2*v^2)/64 + (t^3*u*v^2)/32 + (t^4*u^2*v^2)/64) + s^3*(-5/32 - (3*a*t)/16 - (7*t*u)/16 - (3*a*t^2*u)/8 - (9*t^2*u^2)/32 - (3*a*t^3*u^2)/16 - (3*t*v)/8 - (3*a*t^2*v)/8 - (15*t^2*u*v)/16 - (3*a*t^3*u*v)/4 - (9*t^3*u^2*v)/16 - (3*a*t^4*u^2*v)/8 - (7*t^2*v^2)/32 - (3*a*t^3*v^2)/16 - (t^3*u*v^2)/2 - (3*a*t^4*u*v^2)/8 - (9*t^4*u^2*v^2)/32 - (3*a*t^5*u^2*v^2)/16) + s^2*(9/16 + (25*a*t)/16 + (15*a^2*t^2)/16 + (11*t*u)/4 + (35*a*t^2*u)/8 + (15*a^2*t^3*u)/8 + (35*t^2*u^2)/16 + (45*a*t^3*u^2)/16 + (15*a^2*t^4*u^2)/16 + (29*t*v)/16 + (15*a*t^2*v)/4 + (15*a^2*t^3*v)/8 + (99*t^2*u*v)/16 + (75*a*t^3*u*v)/8 + (15*a^2*t^4*u*v)/4 + (35*t^3*u^2*v)/8 + (45*a*t^4*u^2*v)/8 + (15*a^2*t^5*u^2*v)/8 + (21*t^2*v^2)/16 + (35*a*t^3*v^2)/16 + (15*a^2*t^4*v^2)/16 + (55*t^3*u*v^2)/16 + 5*a*t^4*u*v^2 + (15*a^2*t^5*u*v^2)/8 + (35*t^4*u^2*v^2)/16 + (45*a*t^5*u^2*v^2)/16 + (15*a^2*t^6*u^2*v^2)/16) + s*(-23/32 - (77*a*t)/16 - (25*a^2*t^2)/4 - (5*a^3*t^3)/2 - (169*t*u)/16 - (181*a*t^2*u)/8 - (35*a^2*t^3*u)/2 - 5*a^3*t^4*u - (315*t^2*u^2)/32 - (285*a*t^3*u^2)/16 - (45*a^2*t^4*u^2)/4 - (5*a^3*t^5*u^2)/2 - (41*t*v)/8 - (121*a*t^2*v)/8 - 15*a^2*t^3*v - 5*a^3*t^4*v - (389*t^2*u*v)/16 - (203*a*t^3*u*v)/4 - (75*a^2*t^4*u*v)/2 - 10*a^3*t^5*u*v - (315*t^3*u^2*v)/16 - (285*a*t^4*u^2*v)/8 - (45*a^2*t^5*u^2*v)/2 - 5*a^3*t^6*u^2*v - (149*t^2*v^2)/32 - (173*a*t^3*v^2)/16 - (35*a^2*t^4*v^2)/4 - (5*a^3*t^5*v^2)/2 - (55*t^3*u*v^2)/4 - (225*a*t^4*u*v^2)/8 - 20*a^2*t^5*u*v^2 - 5*a^3*t^6*u*v^2 - (315*t^4*u^2*v^2)/32 - (285*a*t^5*u^2*v^2)/16 - (45*a^2*t^6*u^2*v^2)/4 - (5*a^3*t^7*u^2*v^2)/2)) * hs

/-- Taylor coefficients of the implicit solution `rho(e^σ, e^τ)` at the origin. -/
noncomputable def r1 : ℝ := -5/2 + (11*s)/10
noncomputable def r2 : ℝ := -1 + (2*s)/5
noncomputable def r11 : ℝ := -1/2 + (11*s)/50
noncomputable def r12 : ℝ := 1/2 - (11*s)/50
noncomputable def r22 : ℝ := 3/4 - (33*s)/100

/-- Order 1 of `R(rho0 + a, e^σ, e^τ) = 0` with `a = r1 σ + r2 τ + ...`. -/
theorem jet_order1 (hs : s^2 = 5) (σ τ : ℝ) : T1 s (r1 s * σ + r2 s * τ) σ τ = 0 := by
  unfold T1 r1 r2
  linear_combination ((-77*σ)/5 - (28*τ)/5) * hs

/-- Order 2 of the same: the second-order part of `a`, `e^σ - 1`, `e^τ - 1` enters through `T1`,
    the first-order part through `T2`. -/
theorem jet_order2 (hs : s^2 = 5) (σ τ : ℝ) :
    T1 s (r11 s * σ^2/2 + r12 s * σ*τ + r22 s * τ^2/2) (σ^2/2) (τ^2/2)
      + T2 s (r1 s * σ + r2 s * τ) σ τ = 0 := by
  unfold T1 T2 r1 r2 r11 r12 r22
  linear_combination ((2409*σ^2)/40 + (59*σ*τ)/2 + (15*τ^2)/4 + s*((-7381*σ^2)/200 - (671*σ*τ)/25 - (122*τ^2)/25)) * hs

theorem rho0_pos (hs : s^2 = 5) : 0 < rho0 s := by
  unfold rho0; nlinarith

/-- `mu = -grad rho / rho0`. -/
theorem mu1_eq (hs : s^2 = 5) : -(r1 s) / rho0 s = 1 - (2*s)/5 := by
  have h := (rho0_pos s hs).ne'
  rw [div_eq_iff h]; unfold r1 rho0
  linear_combination (-1/5) * hs

theorem mu2_eq (hs : s^2 = 5) : -(r2 s) / rho0 s = 1/2 - s/10 := by
  have h := (rho0_pos s hs).ne'
  rw [div_eq_iff h]; unfold r2 rho0
  linear_combination (-1/20) * hs

/-- Entries of the Hessian of `U = -log rho(e^σ,e^τ)`: `H_ij = -rho_ij/rho0 + rho_i rho_j / rho0^2`. -/
theorem H11_eq (hs : s^2 = 5) : -(r11 s) / rho0 s + (r1 s)^2 / (rho0 s)^2 = 2 - (22*s)/25 := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r1 r11 rho0
  linear_combination ((3 - s)/2 * (-1/2 + (11*s)/50)) * hs

theorem H12_eq (hs : s^2 = 5) : -(r12 s) / rho0 s + (r1 s) * (r2 s) / (rho0 s)^2 = 1/2 - (11*s)/50 := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r1 r2 r12 rho0
  linear_combination ((3 - s)/2 * (-1/8 + (11*s)/200)) * hs

theorem H22_eq (hs : s^2 = 5) : -(r22 s) / rho0 s + (r2 s)^2 / (rho0 s)^2 = s/50 := by
  have h := (rho0_pos s hs).ne'
  rw [div_add_div _ _ h (pow_ne_zero 2 h), div_eq_iff (mul_ne_zero h (pow_ne_zero 2 h))]
  unfold r2 r22 rho0
  linear_combination ((3 - s)/2 * (1/40 - s/200)) * hs

/-- `det H = (13 s - 29)/50`. -/
theorem detH_eq (hs : s^2 = 5) :
    (2 - (22*s)/25) * (s/50) - (1/2 - (11*s)/50)^2 = (13*s - 29)/50 := by
  linear_combination (-33/500 : ℝ) * hs

theorem detH_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < (13*s - 29)/50 := by
  nlinarith

theorem H11_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < 2 - (22*s)/25 := by nlinarith

theorem H12_pos (hs : s^2 = 5) (h0 : 0 < s) : 0 < 1/2 - (11*s)/50 := by nlinarith

/-- The squared correlation: `H12^2 = ((5 s - 11)/4) * H11 * H22`. -/
theorem corr_sq (hs : s^2 = 5) :
    (1/2 - (11*s)/50)^2 = (5*s - 11)/4 * ((2 - (22*s)/25) * (s/50)) := by
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
