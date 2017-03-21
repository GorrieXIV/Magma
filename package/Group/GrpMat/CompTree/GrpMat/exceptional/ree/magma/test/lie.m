// Constructs 2G2 as a subgroup of G2 as a group of Lie type, then obtain
// it as a matrix group in natural rep

m := 1;
K<xi> := GF(3, 2 * m + 1);
q := #K;
R := RootDatum("G2" : Isogeny := "SC", Signs := [-1, -1, 1, 1]);
G2st := GroupOfLieType(R, K);
rho := StandardRepresentation(G2st);
G2mat := Image(rho);

t := 3^m;
A := AutomorphismGroup(G2st);
fld := FieldAutomorphism(G2st, iso<K -> K | x :-> x^t, y :-> y^t>);
diag := A ! DiagramAutomorphism(G2st, Sym(2) ! (1, 2));
phi := diag * fld;

alpha := elt<G2st | <1, xi^t>, <2, xi>, <3, xi^(t + 1)>, <4, xi^(2 * t + 1)>>;
phi(alpha) eq alpha;

beta := elt<G2st | <3, xi^t>, <5, xi>>;
phi(beta) eq beta;

gamma := elt<G2st | <4, xi^t>, <6, xi>>;
phi(gamma) eq gamma;

tau := elt<G2st | 3, 5>;
phi(tau) eq tau;

ReeMat := sub<Generic(G2mat) | rho([alpha, beta, gamma, tau])>;
print SimpleGroupName(ReeMat);

