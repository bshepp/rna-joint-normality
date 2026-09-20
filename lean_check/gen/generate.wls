(* Generates the long polynomial expressions used in LeanCheck/Basic.lean.
   s stands for Sqrt[5]; every identity is reduced modulo s^2 - 5 and the quotient is handed to
   Lean's `linear_combination`, so Lean's kernel (not Mathematica) certifies the result. *)
R[X_, x_, z_] := X^6 x^2 z^2 - 2 X^5 x z^2 - 2 X^5 x z + 4 X^4 x z + X^4 z^2 - 2 X^4 z - 2 X^3 x z + X^4 +
   4 X^3 z - 4 X^3 - 2 X^2 z + 6 X^2 - 4 X + 1;
rho0 = (3 - s)/2;
red[e_] := PolynomialRemainder[Expand[e], s^2 - 5, s];
quo[e_] := PolynomialQuotient[Expand[e], s^2 - 5, s];
lean[e_] := ToString[e, InputForm];

(* (B) Taylor expansion of R at (rho0,1,1) *)
full = Expand[R[rho0 + a, 1 + u, 1 + v]];
T = red[full];
deg[m_] := Total[Exponent[m, {a, u, v}]];
terms = MonomialList[T, {a, u, v}];
byDeg = Table[Total[Select[terms, deg[#] == d &]], {d, 0, 10}];
Print["TAYLOR_CONST = ", byDeg[[1]]];
out = <||>;
out["taylor1"] = lean[Collect[byDeg[[2]], {a, u, v}]];
out["taylor2"] = lean[Collect[byDeg[[3]], {a, u, v}]];
Tsc = Expand[(T /. {a -> t a, u -> t u, v -> t v})];
T3rem = Expand[(Tsc - t byDeg[[2]] - t^2 byDeg[[3]])/t^3];
Print["Taylor remainder polynomial: ", PolynomialQ[T3rem, {t, a, u, v, s}]];
out["taylor3"] = lean[Collect[T3rem, t]];
out["taylorq"] = lean[quo[(full /. {a -> t a, u -> t u, v -> t v}) - Tsc]];

(* (C) the 2-jet of the implicit solution rho(e^sigma, e^tau) *)
c[i_, j_, k_] := Coefficient[Coefficient[Coefficient[T, a, i], u, j], v, k] /. {a -> 0, u -> 0, v -> 0};
sol = Solve[{c[1, 0, 0] r1 + c[0, 1, 0] == 0, c[1, 0, 0] r2 + c[0, 0, 1] == 0,
    c[1, 0, 0] r11/2 + c[0, 1, 0]/2 + c[2, 0, 0] r1^2 + c[1, 1, 0] r1 + c[0, 2, 0] == 0,
    c[1, 0, 0] r12 + 2 c[2, 0, 0] r1 r2 + c[1, 1, 0] r2 + c[1, 0, 1] r1 + c[0, 1, 1] == 0,
    c[1, 0, 0] r22/2 + c[0, 0, 1]/2 + c[2, 0, 0] r2^2 + c[1, 0, 1] r2 + c[0, 0, 2] == 0}, {r1, r2, r11, r12, r22}][[1]];
(* write each as p + q s *)
toField[e_] := Module[{ep = e /. s -> Sqrt[5], em = e /. s -> -Sqrt[5]},
   RootReduce[(ep + em)/2] + RootReduce[(ep - em)/(2 Sqrt[5])] s];
rs = toField /@ ({r1, r2, r11, r12, r22} /. sol);
Print["r = ", rs];
Do[out[{"r1", "r2", "r11", "r12", "r22"}[[i]]] = lean[rs[[i]]], {i, 5}];
(* order-1 and order-2 conditions, stated through T1 and T2 *)
T1f[a_, u_, v_] = byDeg[[2]]; T2f[a_, u_, v_] = byDeg[[3]];
o1 = T1f[rs[[1]] sigma + rs[[2]] tau, sigma, tau];
o2 = T1f[rs[[3]] sigma^2/2 + rs[[4]] sigma tau + rs[[5]] tau^2/2, sigma^2/2, tau^2/2] + T2f[rs[[1]] sigma + rs[[2]] tau, sigma, tau];
Print["order conditions reduce to 0: ", red /@ {o1, o2}];
out["o1q"] = lean[quo[o1]]; out["o2q"] = lean[quo[o2]];

(* (D) mu and H from the jet *)
{q1, q2, q11, q12, q22} = rs;
mu1 = toField[-q1/rho0]; mu2 = toField[-q2/rho0];
H11 = toField[-q11/rho0 + q1^2/rho0^2]; H12 = toField[-q12/rho0 + q1 q2/rho0^2]; H22 = toField[-q22/rho0 + q2^2/rho0^2];
Print["mu = ", {mu1, mu2}, "  H = ", {H11, H12, H22}, "  det = ", toField[H11 H22 - H12^2]];
Do[out[k[[1]]] = lean[k[[2]]], {k, {{"mu1", mu1}, {"mu2", mu2}, {"H11", H11}, {"H12", H12}, {"H22", H22}}}];
out["cmu1"] = lean[quo[-q1 - mu1 rho0]]; out["cmu2"] = lean[quo[-q2 - mu2 rho0]];
out["cH11"] = lean[quo[-q11 rho0 + q1^2 - H11 rho0^2]];
out["cH12"] = lean[quo[-q12 rho0 + q1 q2 - H12 rho0^2]];
out["cH22"] = lean[quo[-q22 rho0 + q2^2 - H22 rho0^2]];
Print["remainders (all 0): ", red /@ {-q1 - mu1 rho0, -q2 - mu2 rho0, -q11 rho0 + q1^2 - H11 rho0^2, -q12 rho0 + q1 q2 - H12 rho0^2, -q22 rho0 + q2^2 - H22 rho0^2}];
(* rho0 root certificate *)
out["rootq"] = lean[quo[R[rho0, 1, 1]]];
Print["root remainder (must be 0): ", red[R[rho0, 1, 1]]];
Export["gen_out.json", out, "JSON"];
