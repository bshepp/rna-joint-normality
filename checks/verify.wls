(* A9 (Bu-Kauers-Zeilberger RNA conjecture): exact checks behind the quasi-power proof.
   Run: wolframscript -file verify.wls
   Everything is exact (RootReduce / FullSimplify over Q(sqrt5)); N[] only for display. *)

R = X^6 x^2 z^2 - 2 X^5 x z^2 - 2 X^5 x z + 4 X^4 x z + X^4 z^2 - 2 X^4 z - 2 X^3 x z + X^4 +
    4 X^3 z - 4 X^3 - 2 X^2 z + 6 X^2 - 4 X + 1;
num0 = -2 X^4 z + X^3 x z + X^2 z - X^2 + 2 X - 1;
den = 2 X^2 z (X - 1);
F = (num0 + Sqrt[R])/den;

(* ---- 1. external validation: brute-force enumeration of secondary structures ---- *)
(* structures on lo..hi: non-crossing matchings with j - i >= 2; returned as lists of pairs *)
ClearAll[st];
st[lo_, hi_] /; hi < lo := {{}};
st[lo_, hi_] := st[lo, hi] = Join[
   st[lo + 1, hi],
   Flatten[Table[
     Flatten[Outer[Join[{{lo, j}}, #1, #2] &, st[lo + 1, j - 1], st[j + 1, hi], 1], 1],
     {j, lo + 2, hi}], 1]];
hairpins[s_] := With[{paired = Flatten[s]},
   Count[s, {i_, j_} /; NoneTrue[Range[i + 1, j - 1], MemberQ[paired, #] &]]];
wt[n_] := Total[x^hairpins[#] z^Length[#] & /@ st[1, n]];

nmax = 14;
ser = Normal[Series[F, {X, 0, nmax}]];
ok1 = And @@ Table[Expand[Coefficient[ser, X, n] - wt[n]] === 0, {n, 2, nmax}];
Print["[1] F matches brute force for 2<=n<=", nmax, ": ", ok1,
  "   (counts: ", Table[Length[st[1, n]], {n, 2, nmax}], ")"];
Print["    [X^0]F, [X^1]F = ", Coefficient[ser, X, 0], ", ", Coefficient[ser, X, 1],
  "  (formula omits n=0,1; irrelevant asymptotically)"];

(* ---- 2. singularities at x=z=1 ---- *)
R1 = R /. {x -> 1, z -> 1};
Print["[2] R(X,1,1) = ", Factor[R1]];
rts = X /. Solve[R1 == 0, X];
Print["    roots and moduli: ", {#, N[Abs[#], 12]} & /@ DeleteDuplicates[rts]];
rho0 = (3 - Sqrt[5])/2;
Print["    rho0 root: ", Simplify[R1 /. X -> rho0] === 0, "   simple: ",
  Simplify[D[R1, X] /. X -> rho0] =!= 0, "   rho0 = ", N[rho0, 15]];

(* ---- 3. sqrt coefficient does not vanish ---- *)
Rtilde = Simplify[-rho0 D[R1, X] /. X -> rho0];
den0 = Simplify[den /. {X -> rho0, z -> 1}];
Print["[3] Rtilde(rho0) = ", Rtilde, " = ", N[Rtilde, 12], " ;  DEN(rho0) = ", den0, " = ", N[den0, 12]];

(* ---- 4. Hessian of U(s,t) = -Log rho(e^s,e^t), by a second-order Taylor ansatz ---- *)
ans = rho0 + e (a1 s + a2 t) + e^2 (a11 s^2/2 + a12 s t + a22 t^2/2);
ser2 = Normal[Series[R /. {X -> ans, x -> Exp[e s], z -> Exp[e t]}, {e, 0, 2}]];
c1 = CoefficientList[Coefficient[ser2, e, 1], {s, t}] // Flatten // DeleteCases[#, 0] &;
sol1 = First[Solve[Thread[RootReduce[c1] == 0], {a1, a2}]];
c2 = CoefficientList[Coefficient[ser2, e, 2] /. sol1, {s, t}] // Flatten // DeleteCases[#, 0] &;
sol2 = First[Solve[Thread[c2 == 0], {a11, a12, a22}]];
{r1, r2, r11, r12, r22} = RootReduce[{a1, a2, a11, a12, a22} /. sol1 /. sol2];
mu = RootReduce[{-r1/rho0, -r2/rho0}];
H = RootReduce[{{-r11/rho0 + r1^2/rho0^2, -r12/rho0 + r1 r2/rho0^2}, {-r12/rho0 + r1 r2/rho0^2, -r22/rho0 + r2^2/rho0^2}}];
Print["[4] mu = ", ToRadicals[mu], " = ", N[mu, 12]];
Print["    H  = ", ToRadicals[H], " = ", N[H, 12]];
Print["    det H = ", ToRadicals[RootReduce[Det[H]]], " = ", N[Det[H], 12]];
corr = RootReduce[H[[1, 2]]/Sqrt[H[[1, 1]] H[[2, 2]]]];
Print["    corr = ", ToRadicals[corr], " = ", N[corr, 12]];
claims = {mu[[1]] - (1 - 2/Sqrt[5]), mu[[2]] - (5 - Sqrt[5])/10, H[[1, 1]] - (2 - 22/(5 Sqrt[5])),
   H[[2, 2]] - 1/(10 Sqrt[5]), corr - Sqrt[5 Sqrt[5] - 11]/2};
ok4 = (RootReduce[#] === 0) & /@ claims;
Print["    matches Theorem 3 {EX, EZ, VarX, VarZ, Corr}: ", ok4];

(* ---- 5. numerical sanity: exact moments at finite n vs limits ---- *)
nn = 200;
(* cheaper: coefficients of derivatives at s=t=0 *)
mom[i_, j_] := SeriesCoefficient[Series[D[F /. {x -> Exp[s], z -> Exp[t]}, {s, i}, {t, j}] /. {s -> 0, t -> 0}, {X, 0, nn}], nn];
a0 = mom[0, 0]; ex = mom[1, 0]/a0; ez = mom[0, 1]/a0;
vx = mom[2, 0]/a0 - ex^2; vz = mom[0, 2]/a0 - ez^2; cxz = mom[1, 1]/a0 - ex ez;
Print["[5] n=", nn, ": EX/n, EZ/n, VarX/n, VarZ/n, Corr = ", N[{ex/nn, ez/nn, vx/nn, vz/nn, cxz/Sqrt[vx vz]}, 8]];


(* ---- 6. leading constant of the proof: f_n ~ (-B0/(2 Sqrt[Pi])) rho0^-(n+2) (n+2)^(-3/2) ---- *)
B0 = Sqrt[Rtilde]/(2 (rho0 - 1));
Do[With[{a = SeriesCoefficient[Series[F /. {x -> 1, z -> 1}, {X, 0, m}], m]},
   Print["[6] n=", m, ": a(n)/prediction = ", N[a/((-B0/(2 Sqrt[Pi])) rho0^-(m + 2) (m + 2)^(-3/2)), 10]]], {m, {100, 200, 400}}];


(* ---- 7. second-order check: grad W(0) vs the O(1) terms of E[X_n], E[Z_n] in BKZ Theorem 3 ---- *)
(* b = -beta/(2 Sqrt[Pi] rho^2), beta = Sqrt[Q(rho)]/(2 z (rho-1)), Q(rho) = -rho D[R,X] at X=rho *)
logb = (1/2) Log[-X D[R, X]] - Log[2 z (1 - X)] - 2 Log[X] /. {x -> Exp[s], z -> Exp[t]};  (* up to an additive constant *)
gradW = RootReduce[{D[logb, s] + r1 D[logb, X], D[logb, t] + r2 D[logb, X]} /. {X -> rho0, s -> 0, t -> 0}];
bkz = RootReduce[{(1 - 2/Sqrt[5]) (7/4 + 11 Sqrt[5]/20), ((5 - Sqrt[5])/10) (-5/8 - 13 Sqrt[5]/40)}];
ok7 = (RootReduce[gradW - bkz] === {0, 0});
Print["[7] grad W(0) = ", ToRadicals[gradW], " = ", N[gradW, 10], " ; equals BKZ constant terms: ", ok7];
(* ratio in the normalization of Lemma 5 (n^(-3/2), rho0^-n) *)
bb = -B0/(2 Sqrt[Pi] rho0^2);
With[{m = 400}, Print["    f_n/(b rho0^-n n^-3/2) at n=400: ", N[SeriesCoefficient[Series[F /. {x -> 1, z -> 1}, {X, 0, m}], m]/(bb rho0^-m m^(-3/2)), 8]]];
Print[If[ok1 && And @@ ok4 && ok7, "ALL OK", "MISMATCH"]];
