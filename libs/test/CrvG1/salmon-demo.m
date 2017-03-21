

MC := MonomialCoefficient;
Deriv := Derivative;

// The package "g1invariants.m" uses different scaling for the
// invariants and covariants, from those in Salmon's book.
// We wrap our functions to give Salmon's scalings.

function SalmonInvariants(cubic)
  c4,c6 := Explode(cInvariants(cubic));
  S := (-1/6^4)*c4;
  T := (1/18^3)*c6;
  return S,T;
end function; 

function SalmonHessian(cubic)
  H := Hessian(cubic);
  return (-1/108)*H`Equation;
end function;

function SalmonContravariants(cubic)
  P,Q := Contravariants(cubic);
  P := (-1/54)*P`Equation;
  Q := (1/324)*Q`Equation;
  return P,Q;
end function;

function SalmonCovariants(cubic)
  Z,X,Y := Explode(CoveringCovariants(cubic));
  U := Equations(cubic)[1];
  c4,c6 := Explode(cInvariants(cubic));  
  T := (1/(2^8*3^8))*(64*X - 24*c6*U^2);
  J := (1/(2^2*3^12))*Y;
  return T,J;
end function;

// Computing the invariants

B<a,b,c,a2,a3,b1,b3,c1,c2,m> := PolynomialRing(Rationals(),10);
U := GenusOneModel(3,[a,b,c,3*a2,3*a3,3*b1,3*b3,3*c1,3*c2,6*m]);
S,T := SalmonInvariants(U);

// Checking Salmon's expression for the Hessian

R := Parent(U`Equation);
Hmat := Matrix(R,3,3,[(1/6)*Deriv(Deriv(U`Equation,R.i),R.j):i,j in [1..3]]);
Hpolys := [Hmat[i[1],i[2]]:i in [[1,1],[2,2],[3,3],[2,3],[3,1],[1,2]]];
aa,bb,cc,ff,gg,hh := Explode(Hpolys);
H := aa*bb*cc + 2*ff*gg*hh - aa*ff^2 - bb*gg^2 - cc*hh^2;
assert SalmonHessian(U) eq H;

// Checking the relationship between the Hessian and the invariants

BB<la,mu> := PolynomialRing(B,2);
U := ChangeRing(U,BB);
S,T := SalmonInvariants(U);
H := SalmonHessian(U);
HH := SalmonHessian(GenusOneModel(la*U`Equation + 6*mu*H));
lala := -2*S*la^2*mu - T*la*mu^2 + 8*S^2*mu^3;
mumu := la^3 + 12*S*la*mu^2 + 2*T*mu^3;
assert HH eq lala*U`Equation + mumu*H;

// The invariants and covariants of a cubic in Hesse form

U := HesseModel(3,[1,6*m]);
S,T := SalmonInvariants(U);
H := SalmonHessian(U);
P,Q := SalmonContravariants(U);
assert T^2 + 64*S^3 eq (1 + 8*m^3)^3;
assert Discriminant(U) eq -3^9*(T^2 + 64*S^3);

// Checking Salmon's expressions for the covariants

Theta,J := SalmonCovariants(U);
R<x,y,z> := Parent(U`Equation);
assert Theta eq 3*m^3*(1+2*m^3)*(x^3+y^3+z^3)^2 
               - m*(1-20*m^3-8*m^6)*(x^3+y^3+z^3)*x*y*z
               - 3*m^2*(1-20*m^3-8*m^6)*x^2*y^2*z^2
               - (1+8*m^3)^2*(y^3*z^3+z^3*x^3+x^3*y^3);

assert Theta eq m^3*(2+m^3)*U^2 - m*(1+2*m^3)*U*H + 3*m^2*H^2
               - (1+8*m^3)^2*(y^3*z^3+z^3*x^3+x^3*y^3)
and J eq (1+8*m^3)^3*(y^3-z^3)*(z^3-x^3)*(x^3-y^3)
and J^2 eq 4*Theta^3 + T*U^2*Theta^2 
 + Theta*(-4*S^3*U^4 + 2*S*T*U^3*H - 72*S^2*U^2*H^2 - 18*T*U*H^3 + 108*S*H^4)
 - 16*S^4*U^5*H - 11*S^2*T*U^4*H^2 - 4*T^2*U^3*H^3 + 54*S*T*U^2*H^4
 - 432*S^2*U*H^5 - 27*T*H^6
where U := U`Equation;

// Taking invariant and covariants of linear combinations

U := ChangeRing(U,BB);
H := SalmonHessian(U);
P,Q := SalmonContravariants(U);

SS,TT := SalmonInvariants(GenusOneModel(la*U`Equation + 6*mu*H));
assert SS eq S*la^4 + T*la^3*mu - 24*S^2*la^2*mu^2 - 4*S*T*la*mu^3 - (T^2 + 48*S^3)*mu^4;
assert TT eq T*la^6 - 96*S^2*la^5*mu - 60*S*T*la^4*mu^2 - 20*T^2*la^3*mu^3 + 240*S^2*T*la^2*mu^4 - 48*(S*T^2 + 96*S^4)*la*mu^5 - 8*(72*S^3*T + T^3)*mu^6;

SS,TT := SalmonInvariants(GenusOneModel(la*P + mu*Q));
assert 6^4*SS eq (192*S^3 - T^2)*la^4 + 768*S^2*T*la^3*mu 
    + 216*(3*S*T^2 - 64*S^4)*la^2*mu^2 + 216*(T^3 - 64*T*S^3)*la*mu^3
    - 1296*(5*S^2*T^2 + 64*S^5)*mu^4;
assert -18^3*TT eq (T^3 + 576*S^3*T)*la^6 + 288*(5*S^2*T^2 - 192*S^5)*la^5*mu
    + 540*(3*S*T^3 - 320*S^4*T)*la^4*mu^2 + 540*(T^4 - 448*S^3*T^2)*la^3*mu^3
    - 19440*(7*S^2*T^3 - 64*S^5*T)*la^2*mu^4 
    - 11664*(3*S*T^4 - 32*S^4*T^2 + 2048*S^7)*la*mu^5
    - 5832*(T^5 + 40*S^3*T^3 + 2560*S^6*T)*mu^6;
R := T^2 + 64*S^3;
RR := TT^2 + 64*SS^3;
assert 3^9*RR eq R^2*(S*la^4 + T*la^3*mu + 72*S^2*la^2*mu^2 
                 + 108*S*T*la*mu^3 + 27*(T^2 - 16*S^3)*mu^4)^3;

HH := SalmonHessian(GenusOneModel(la*P + mu*Q));
lala := T*la^3 + 144*S^2*la^2*mu + 324*S*T*la*mu^2 + 108*(T^2-16*S^3)*mu^3;
mumu := -(4*S*la^3 + 3*T*la^2*mu + 144*S^2*la*mu^2 + 108*S*T*mu^3);
assert 108*HH eq lala*P + mumu*Q;

PP,QQ := SalmonContravariants(GenusOneModel(la*U`Equation + 6*mu*H));
assert PP eq P*la^3 + Q*la^2*mu - 12*S*P*la*mu^2 + 4*(S*Q-T*P)*mu^3;
assert QQ eq Q*la^5 - 60*S*P*la^4*mu - 30*T*P*la^3*mu^2 - 10*T*Q*la^2*mu^3
        + 120*(2*S^2*Q - S*T*P)*la*mu^4 + 24*(S*T*Q - (T^2 + 24*S^3)*P)*mu^5;

PP,QQ := SalmonContravariants(GenusOneModel(la*P + mu*Q));
assert 54*PP eq la^3*(8*S^2*U - T*H) + 18*la^2*mu*(S*T*U + 8*S^2*H) 
  + 9*la*mu^2*((T^2-32*S^3)*U + 12*S*T*H) 
  - 54*mu^3*(4*S^2*T*U - (T^2 + 32*S^3)*H)
and -324*QQ eq la^5*(16*S^2*T*U + (T^2 + 192*S^3)*H)
  + 30*la^4*mu*(S*(T^2 - 64*S^3)*U + 16*S^2*T*H)
  + 15*la^3*mu^2*(T*(T^2 - 320*S^3)*U + 48*S*T^2*H)
  - 270*la^2*mu^3*(16*S^2*T^2*U - T*(T^2-64*S^3)*H)
  - 1620*la*mu^4*(S*T^3*U + 4*S^2*(T^2 - 64*S^3)*H)
  - 324*mu^5*((T^4 + 24*T^2*S^3 + 512*S^6)*U - 6*S*T*(T^2 + 128*S^3)*H)
where U := U`Equation;

/***********************************************************************

The following output may have once been produced

> load "salmon-demo.m";
Loading "salmon-demo.m"
The general ternary cubic

a*x^3 + 3*a2*x^2*y + 3*a3*x^2*z + 3*b1*x*y^2 + 6*m*x*y*z + 3*c1*x*z^2 + b*y^3 + 3*b3*y^2*z + 3*c2*y*z^2 + 
c*z^3

has invariants

S = a*b*c*m - a*b*c1*c2 - a*c*b1*b3 + a*b1*c2^2 + a*b3^2*c1 - a*b3*c2*m - b*c*a2*a3 + b*a2*c1^2 + b*a3^2*c2
- b*a3*c1*m + c*a2^2*b3 - c*a2*b1*m + c*a3*b1^2 - a2^2*c2^2 + a2*a3*b3*c2 + a2*b1*c1*c2 - 3*a2*b3*c1*m + 
2*a2*c2*m^2 - a3^2*b3^2 + a3*b1*b3*c1 - 3*a3*b1*c2*m + 2*a3*b3*m^2 - b1^2*c1^2 + 2*b1*c1*m^2 - m^4

and

T = a^2*b^2*c^2 - 6*a^2*b*c*b3*c2 + 4*a^2*b*c2^3 + 4*a^2*c*b3^3 - 3*a^2*b3^2*c2^2 - 6*a*b^2*c*a3*c1 + 
4*a*b^2*c1^3 - 6*a*b*c^2*a2*b1 + 6*a*b*c*a2*b3*c1 + 12*a*b*c*a2*c2*m + 6*a*b*c*a3*b1*c2 + 12*a*b*c*a3*b3*m 
+ 12*a*b*c*b1*c1*m - 20*a*b*c*m^3 - 12*a*b*a2*c1*c2^2 + 18*a*b*a3*b3*c1*c2 - 24*a*b*a3*c2^2*m - 
12*a*b*b1*c1^2*c2 - 24*a*b*b3*c1^2*m + 36*a*b*c1*c2*m^2 + 4*a*c^2*b1^3 + 18*a*c*a2*b1*b3*c2 - 
24*a*c*a2*b3^2*m - 12*a*c*a3*b1*b3^2 - 12*a*c*b1^2*b3*c1 - 24*a*c*b1^2*c2*m + 36*a*c*b1*b3*m^2 - 
12*a*a2*b1*c2^3 + 6*a*a2*b3^2*c1*c2 + 12*a*a2*b3*c2^2*m + 6*a*a3*b1*b3*c2^2 - 12*a*a3*b3^3*c1 + 
12*a*a3*b3^2*c2*m + 24*a*b1^2*c1*c2^2 + 24*a*b1*b3^2*c1^2 - 60*a*b1*b3*c1*c2*m + 12*a*b1*c2^2*m^2 + 
12*a*b3^2*c1*m^2 - 12*a*b3*c2*m^3 + 4*b^2*c*a3^3 - 3*b^2*a3^2*c1^2 + 4*b*c^2*a2^3 - 12*b*c*a2^2*a3*c2 - 
24*b*c*a2^2*c1*m - 12*b*c*a2*a3^2*b3 + 18*b*c*a2*a3*b1*c1 + 36*b*c*a2*a3*m^2 - 24*b*c*a3^2*b1*m + 
24*b*a2^2*c1^2*c2 + 24*b*a2*a3^2*c2^2 + 6*b*a2*a3*b3*c1^2 - 60*b*a2*a3*c1*c2*m - 12*b*a2*b1*c1^3 + 
12*b*a2*c1^2*m^2 - 12*b*a3^3*b3*c2 + 6*b*a3^2*b1*c1*c2 + 12*b*a3^2*b3*c1*m + 12*b*a3^2*c2*m^2 + 
12*b*a3*b1*c1^2*m - 12*b*a3*c1*m^3 - 3*c^2*a2^2*b1^2 - 12*c*a2^3*b3*c2 + 24*c*a2^2*a3*b3^2 + 
6*c*a2^2*b1*b3*c1 + 12*c*a2^2*b1*c2*m + 12*c*a2^2*b3*m^2 + 6*c*a2*a3*b1^2*c2 - 60*c*a2*a3*b1*b3*m + 
12*c*a2*b1^2*c1*m - 12*c*a2*b1*m^3 + 24*c*a3^2*b1^2*b3 - 12*c*a3*b1^3*c1 + 12*c*a3*b1^2*m^2 + 8*a2^3*c2^3 -
12*a2^2*a3*b3*c2^2 - 12*a2^2*b1*c1*c2^2 - 27*a2^2*b3^2*c1^2 + 36*a2^2*b3*c1*c2*m - 24*a2^2*c2^2*m^2 - 
12*a2*a3^2*b3^2*c2 - 6*a2*a3*b1*b3*c1*c2 + 36*a2*a3*b1*c2^2*m + 36*a2*a3*b3^2*c1*m - 12*a2*a3*b3*c2*m^2 - 
12*a2*b1^2*c1^2*c2 + 36*a2*b1*b3*c1^2*m - 12*a2*b1*c1*c2*m^2 - 36*a2*b3*c1*m^3 + 24*a2*c2*m^4 + 8*a3^3*b3^3
- 27*a3^2*b1^2*c2^2 - 12*a3^2*b1*b3^2*c1 + 36*a3^2*b1*b3*c2*m - 24*a3^2*b3^2*m^2 - 12*a3*b1^2*b3*c1^2 + 
36*a3*b1^2*c1*c2*m - 12*a3*b1*b3*c1*m^2 - 36*a3*b1*c2*m^3 + 24*a3*b3*m^4 + 8*b1^3*c1^3 - 24*b1^2*c1^2*m^2 +
24*b1*c1*m^4 - 8*m^6.

These polynomials have 25 and 103 terms respectively.

It is usually more covenient to work with the ternary cubic

x^3 + 6*m*x*y*z + y^3 + z^3.

It has invariants

S = -m^4 + m
T = -8*m^6 - 20*m^3 + 1

Hessian

H = -m^2*x^3 + (2*m^3 + 1)*x*y*z - m^2*y^3 - m^2*z^3

and contravariants

P = m*x^3 + (-4*m^3 + 1)*x*y*z + m*y^3 + m*z^3
Q = (-10*m^3 + 1)*x^3 + (-24*m^5 - 30*m^2)*x*y*z + (-10*m^3 + 1)*y^3 + (-10*m^3 + 1)*z^3.

*********************************************************************/







