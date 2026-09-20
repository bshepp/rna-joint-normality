(* Independent derivation of Theorem 2: first-vertex decomposition
   S = 1 + X S + z X^2 S (S - 1 + (x-1) X/(1-X)),  and the claim F = S - 1 - X. *)
R = X^6 x^2 z^2 - 2 X^5 x z^2 - 2 X^5 x z + 4 X^4 x z + X^4 z^2 - 2 X^4 z - 2 X^3 x z + X^4 + 4 X^3 z - 4 X^3 - 2 X^2 z + 6 X^2 - 4 X + 1;
F = (-2 X^4 z + X^3 x z + X^2 z - X^2 + 2 X - 1 + Sqrt[R])/(2 X^2 z (X - 1));
S = F + 1 + X;
Print["functional equation residual: ", FullSimplify[S - (1 + X S + z X^2 S (S - 1 + (x - 1) X/(1 - X)))]];
