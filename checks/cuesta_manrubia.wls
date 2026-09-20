(* Cross-check against Cuesta & Manrubia, J. Theor. Biol. 419 (2017) 375-382, arXiv:1607.04435, Sec. 3.3.
   Their discriminant, eq. (33) with T_m(z,u) of eq. (41):
     Delta = [(1-z)(1 - z^2 w + z^(2s) w^s) + z^(2s) w^s T_m(z,u)]^2 - 4 z^(2s) w^s (1 - z^2 w + z^(2s) w^s),
     T_m(z,u) = (1 - u z^m)/(1 - z).
   (i)  s = m = 1 must be the Bu-Kauers-Zeilberger model: (1-z)^2 Delta == R.
   (ii) s = 2, m = 3 must reproduce their eq. (47): means 0.286472 n, 0.0378631 n; covariances 0.0650779, 0.0115908, -0.00274347. *)
R = X^6 x^2 z^2 - 2 X^5 x z^2 - 2 X^5 x z + 4 X^4 x z + X^4 z^2 - 2 X^4 z - 2 X^3 x z + X^4 + 4 X^3 z - 4 X^3 - 2 X^2 z + 6 X^2 - 4 X + 1;
delta[s_, m_] := Module[{T = (1 - u Z^m)/(1 - Z)},
   ((1 - Z) (1 - Z^2 w + Z^(2 s) w^s) + Z^(2 s) w^s T)^2 - 4 Z^(2 s) w^s (1 - Z^2 w + Z^(2 s) w^s)];
d11 = Together[(1 - Z)^2 delta[1, 1]];
Print["(i) (1-Z)^2 Delta_{1,1} == R(X->Z, x->u, z->w): ", Expand[d11 - (R /. {X -> Z, x -> u, z -> w})] === 0];

hess[P_] := Module[{z0, ans, ser, c1, c2, sol1, sol2, a1, a2, a11, a12, a22, e, p, h},
   z0 = First[SortBy[Select[Z /. NSolve[(P /. {w -> 1, u -> 1}) == 0, Z, WorkingPrecision -> 40], Abs[Im[#]] < 10^-30 && Re[#] > 0 &], Abs]];
   z0 = Re[z0];
   ans = z0 + e (a1 p + a2 h) + e^2 (a11 p^2/2 + a12 p h + a22 h^2/2);
   ser = Normal[Series[P /. {Z -> ans, w -> Exp[e p], u -> Exp[e h]}, {e, 0, 2}]];
   sol1 = First[Solve[Thread[DeleteCases[Flatten[CoefficientList[Coefficient[ser, e, 1], {p, h}]], _?(# === 0 &)] == 0], {a1, a2}]];
   sol2 = First[Solve[Thread[DeleteCases[Flatten[CoefficientList[Coefficient[ser, e, 2] /. sol1, {p, h}]], _?(# === 0 &)] == 0], {a11, a12, a22}]];
   {a1, a2, a11, a12, a22} = {a1, a2, a11, a12, a22} /. sol1 /. sol2;
   {z0, {-a1/z0, -a2/z0}, {-a11/z0 + a1^2/z0^2, -a22/z0 + a2^2/z0^2, -a12/z0 + a1 a2/z0^2}}];
Print["(ii) s=2,m=3: {z*, {mu_p, mu_h}, {S_pp, S_hh, S_ph}} = ", N[hess[Numerator[Together[delta[2, 3]]]], 7]];
Print["     published:                                     {0.540857, {0.286472, 0.0378631}, {0.0650779, 0.0115908, -0.00274347}}"];
Print["(iii) s=1,m=1 by the same code: ", N[hess[Numerator[Together[delta[1, 1]]]], 10]];
Print["     this note (order: basepairs, hairpins): {0.3819660113, {0.2763932023, 0.1055728090}, {0.04472135955, 0.03226017980, 0.008065044950}}"];
