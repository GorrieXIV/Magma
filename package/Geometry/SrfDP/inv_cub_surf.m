freeze;

/* Invariant theory of cubic surfaces 

   See Dolgachev's classical algebraic geometry and Salmon's books for the background.

   The algorithms require characteristic > 5 or zero

Functions in this file:
=======================

IsCubicSurface(f) : Checks the input

rec_eval(pol, arg, index) : Recursive Horner-Type evaluation for polynomials

rec_diff(op, arg, index) : Recursive application of differential operator to polynomial

dual_wedge_iso(arg) : Isomorphism of wedge-product and dual space

T_plane_curve(f) : T-invariant of plane cubic curve

S_plane_curve(f) : S-invariant of plane cubic curve

EvaluateTransferToContravariant(f, inv, arg) : Numeric Clebsch-Transfer of invariants to contravariants

InterpolateContravariant(f, inv, deg) : Computes a polynomial representation of a contravariant given by
                                        a user program for numeric evaluation

Intrinsics in this file:
========================

NumericClebschTransfer(f :: RngMPolElt, inv :: UserProgram, arg :: SeqEnum) -> RngElt


ApplyContravariant(cont :: MPolElt, cov :: MPolElt) -> MPolElt : Appies differential operator to polynomial

ContravariantsOfCubicSurface(f :: RngMPolElt) -> SeqEnum : Contravariants of cubic surface by Clebsch-Transfer

ClebschSalmonInvariants(f :: RngMPolElt) -> SeqEnum, RngElt
 
LinearCovariants(f :: RngMPolElt) -> SeqEnum : Salmon's 4 linear Convariants

ClassicalCovariantsOfCubicSurface(f :: RngMPolElt) -> SeqEnum : 4 classical covariants

SkewInvariant100(f :: RngMPolElt) -> RngElt : Degree 100 skew invariant

CubicSurfaceFromClebschSalmon(inv :: SeqEnum) -> RngMPolElt : Cubic surface to the given invariants 
                                                             (unique for stable points) 

PentahedronIdeal(f :: RngMPolElt) -> RngMPol : Ideal descibing the faces of the pentahedron

*/

/* Once and for all - check the input */
IsCubicSurface := function(f)
 if Degree(f) ne 3 then return false; end if;
 if not IsHomogeneous(f) then return false; end if;
 if Rank(Parent(f)) ne 4 then return false; end if;
 if Characteristic(Parent(f)) in [2,3,5] then 
  printf"Characteristic 2,3,5 not implemented.\n"; 
  return false; 
 end if;
 return true; 
end function;

/* Recursive Horner-Type evaluation of differential operator. Index is the first remaining variable */
rec_diff := function(op, arg, index)
 if op eq 0 then return 0; end if;

 op_l := Coefficients(op, index);
 res := 0; tmp := arg;

 if index eq Rank(Parent(op)) then
  for i := 1 to #op_l do
   res := res + tmp * MonomialCoefficient(op_l[i],1);
   tmp := Derivative(tmp,index);
  end for;
 else
  for i := 1 to #op_l do
   res := res + $$(op_l[i], tmp, index+1);
   tmp := Derivative(tmp,index);
  end for;
 end if;
 return res;
end function;

/* Given 2 Polynomials. Interpret op as a differential operator. Apply it to arg */
intrinsic ApplyContravariant(cont :: MPolElt, cov :: MPolElt) -> MPolElt
  {Interprets the contravariant cont as a diffierential operator (i.e. x gets d/dx).
   Applies this operator to the covariant cov.}

 require IsCoercible(Parent(cov), cont) : "Arguments incompatible."; /* Operator and argument must be compatible. */
  
 return Parent(cov)!rec_diff(cont, cov, 1);
end intrinsic;



/* Compute the inverse of the isomorphism
      \phi^(-1): (K^n)^dual -> \Wedge^(n-1) (K^n)                
   given by the determinant
      \phi:       \Wedge^(n-1) (K^n)  -> (K^n)^dual
                  (x_1,..,x_{n-1})   |-> (v |-> det(v, x_1,..,x_{n-1}))        
 */
dual_wedge_iso := function(arg)
 if arg eq [0 : i in [1..#arg]] then return [arg : i in [1..#arg-1]]; end if;
 bm := BasisMatrix(Kernel(Transpose(Matrix([arg]))));
 ind := Min([i : i in [1..#arg] | arg[i] ne 0]);
 vgl := [0 : i in [1..#arg]];
 vgl[ind] := 1;
 det := Determinant(Matrix([vgl] cat RowSequence(bm)));
 sp := arg[ind];

 letzter := bm[NumberOfRows(bm)];
 letzter := (sp / det) * letzter;
 bm[NumberOfRows(bm)] := letzter;

 return bm;
end function;


/* Given an invariant inv of a form (as a user program that evaluates it) 
   this routine evaluates the corresponding contravariant of the 
   form f at the point arg. 
   
   Note the shift of dimensions: 
        if f = 0 is a surface then inv is invariant of a curve of same degree */
intrinsic NumericClebschTransfer(f :: RngMPolElt, inv :: UserProgram, arg :: SeqEnum) -> RngElt
{Numeric evaluation of a contravariant of f in the point arg. 
 The contravariant is constructed by Clebsch-transfer from the invariant inv.}
  
 require Rank(Parent(f)) eq #arg : "Number of variables must be equalt to the length of the argument."; 
 require IsHomogeneous(f) : "f must be a homogeneous form."; 

 if arg eq [0 : i in arg] then return 0; end if;

 r0 := BaseRing(Parent(f)); 
 n := Rank(Parent(f));

 bm := dual_wedge_iso(arg);
 r_sub := PolynomialRing(r0,n - 1);
 subs := [&+[bm[i][j] * r_sub.i : i in [1..n-1]] : j in [1..n]];

 return inv(Evaluate(f,subs)); 
end intrinsic;
 
/* Invariant T of a plane cubic curve. Its symbolic representation is 
   (123) (124) (235) (316) (456)^2

   See Salmon: Higher plane curves (1879) S.193 for details. */
T_plane_curve := function(f)

 /* 6th tensor power of the initial polynomial ring */
 r0 := BaseRing(Parent(f));
 r18 := PolynomialRing(r0,18); 
 /* Symbolic method requires f \otimes ... \otimes f but we postpone to expand the tensor product.
    Its representation as a polynomial in 18 variables is not practical as it would have 64000000 terms.

    Representation of the invariant as a polynomial would require 38760 terms.
 */
 fac := [Evaluate(f,[r18.(i+3*j) : i in [1..3]]) : j in [0..5]]; 

/* Apply (456) to the tensor product, this affects only the last 3 factors */
 res1 := Derivative(fac[4],10) * (Derivative(fac[5],14) * Derivative(fac[6],18)
                                 -Derivative(fac[5],15) * Derivative(fac[6],17))
       - Derivative(fac[4],11) * (Derivative(fac[5],13) * Derivative(fac[6],18)
                                 -Derivative(fac[5],15) * Derivative(fac[6],16))
       + Derivative(fac[4],12) * (Derivative(fac[5],13) * Derivative(fac[6],17)
                                 -Derivative(fac[5],14) * Derivative(fac[6],16));
/* 120 terms in res1 */

/* Apply (456) again */
 t1 := Derivative(res1,10); t2 := Derivative(res1,11); t3 := Derivative(res1,12);
 res2 := Derivative(Derivative(t1,14),18) - Derivative(Derivative(t1,15),17)
       - Derivative(Derivative(t2,13),18) + Derivative(Derivative(t2,15),16)
       + Derivative(Derivative(t3,13),17) - Derivative(Derivative(t3,14),16);  
/* 27 terms in res2 */
  
/* Apply (316). Thus factor 1 and 3 come into play */
 res3 := Derivative(res2, 16) * (Derivative(fac[3],8) * Derivative(fac[1],3)
                                -Derivative(fac[3],9) * Derivative(fac[1],2))
       - Derivative(res2, 17) * (Derivative(fac[3],7) * Derivative(fac[1],3)
                                -Derivative(fac[3],9) * Derivative(fac[1],1))
       + Derivative(res2, 18) * (Derivative(fac[3],7) * Derivative(fac[1],2)
                                -Derivative(fac[3],8) * Derivative(fac[1],1));
/* 270 Terms in res3 */

/* Apply (235). Factor 2 is the latest */
 t1 := Derivative(res3,7); t2 := Derivative(res3,8); t3 := Derivative(res3,9);
 res4 := Derivative(fac[2],4) * (Derivative(t2,15) - Derivative(t3,14))
       - Derivative(fac[2],5) * (Derivative(t1,15) - Derivative(t3,13))
       + Derivative(fac[2],6) * (Derivative(t1,14) - Derivative(t2,13)); 
/* 324 Terms in res4 */ 

/* The operators (124) and (123) remain. */
 t1 := Derivative(res4,1); t2 := Derivative(res4,2); t3 := Derivative(res4,3);
 res5 := Derivative(Derivative(t1,5),12) - Derivative(Derivative(t1,6),11)
       - Derivative(Derivative(t2,4),12) + Derivative(Derivative(t2,6),10)
       + Derivative(Derivative(t3,4),11) - Derivative(Derivative(t3,5),10);
/* 6 Terms in res5 */
 t1 := Derivative(res5,1); t2 := Derivative(res5,2); t3 := Derivative(res5,3);
 res6 := Derivative(Derivative(t1,5),9) - Derivative(Derivative(t1,6),8)
       - Derivative(Derivative(t2,4),9) + Derivative(Derivative(t2,6),7)
       + Derivative(Derivative(t3,4),8) - Derivative(Derivative(t3,5),7);
 
 return MonomialCoefficient(res6,1);
end function;

/* Invariant S of a plane cubic curve.
   Symbolic representation of S: (123) (234) (341) (412) */
S_plane_curve := function(f)
 r0 := BaseRing(Parent(f));
 r12 := PolynomialRing(r0,12); 
 fac := [Evaluate(f,[r12.(i+3*j) : i in [1..3]]) : j in [0..3]];

/* Apply (123) */ 
 res1 := Derivative(fac[1],1) * (Derivative(fac[2],5)*Derivative(fac[3],9) 
                                -Derivative(fac[2],6)*Derivative(fac[3],8))
       - Derivative(fac[1],2) * (Derivative(fac[2],4)*Derivative(fac[3],9)
                                -Derivative(fac[2],6)*Derivative(fac[3],7))
       + Derivative(fac[1],3) * (Derivative(fac[2],4)*Derivative(fac[3],8)
                                -Derivative(fac[2],5)*Derivative(fac[3],7));
/* 120 Terms in res1 */

/* Apply (234) */
 t1 := Derivative(res1,4); t2 := Derivative(res1,5); t3 := Derivative(res1,6);
 res2 := Derivative(fac[4],10) * (Derivative(t2,9) - Derivative(t3,8))
       - Derivative(fac[4],11) * (Derivative(t1,9) - Derivative(t3,7))
       + Derivative(fac[4],12) * (Derivative(t1,8) - Derivative(t2,7));
/* 324 Terms in res2 */

/* Apply (341) */
 t1 := Derivative(res2,7); t2 := Derivative(res2,8); t3 := Derivative(res2,9);
 res3 := Derivative(Derivative(t1,11),3) - Derivative(Derivative(t1,12),2)
       - Derivative(Derivative(t2,10),3) + Derivative(Derivative(t2,12),1)
       + Derivative(Derivative(t3,10),2) - Derivative(Derivative(t3,11),1); 
/* 6 Terms in res3 */

/* Apply (412) */
 t1 := Derivative(res3,10); t2 := Derivative(res3,11); t3 := Derivative(res3,12);
 res4 := Derivative(Derivative(t1,2),6) - Derivative(Derivative(t1,3),5)
       - Derivative(Derivative(t2,1),6) + Derivative(Derivative(t2,3),4)
       + Derivative(Derivative(t3,1),5) - Derivative(Derivative(t3,2),4);

 return MonomialCoefficient(res4,1);
end function;

/* Given a variety f = 0 and a routine that evaluates a contravariant of degree deg.
   This routine computes a polynomial representation of the contravariant */
InterpolateContravariant := function(f, inv, deg)
 assert Rank(Parent(f)) eq 4; /* Only the surface case is implemented */
 assert deg in [4,6];         /* Only degree 4 and 6 are implemented */
 
 rz := Parent(f);
 r0 := BaseRing(rz);
 mon := Monomials(&+[rz.i : i in [1..Rank(rz)]]^deg);

/* Random lists of knots for the interpolation */
 if deg eq 4 then
  arg := [[i1,i2,i3,i4] : i1,i2,i3,i4 in [0,1,2] | i1+i2+i3+i4 in [4,5] ];
 else
  arg := [[i1,i2,i3,i4] : i1,i2,i3,i4 in [1,2,3,0,-1,-2,-3] | 
                         (i1+2*i2+3*i3+4*i4)  eq 2 and (i1 + i2+i3+i4) mod 7 ne 2 ] 
         cat [[i1,i2,i3,i4] : i1,i2,i3,i4 in [1,2,0] | (i1+i2+i3+i4) eq 5]
         cat [[2,-1,2,4], [3,3,2,1]];
 
 end if;
 sol,ker := Solution(Matrix([[Evaluate(f,pt) : pt in arg] : f in mon]),
                     Vector([NumericClebschTransfer(f, inv, pt) : pt in arg]));
 assert Dimension(ker) eq 0;
 return &+[mon[i] * sol[i] : i in [1..#mon]];
end function;

/* Initial Contravariants of degree and order 4 resp. 6 and the dual surface. */
intrinsic ContravariantsOfCubicSurface(f :: RngMPolElt) -> SeqEnum
{Contravariants S, T (class and degree 4 and 6), 
 and the dual surface (as a degree 12 contravariant) of the cubic surface f.}

 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5."; 

 S1 := InterpolateContravariant(f, S_plane_curve, 4); 

 T1 := InterpolateContravariant(f, T_plane_curve, 6);
 return [S1,T1, (S1^3 - 6*T1^2)];
end intrinsic;

/* Salmons generators of the invariant ring */
intrinsic ClebschSalmonInvariants(f :: RngMPolElt) -> SeqEnum, RngElt
{Clebsch-Salmon invariants and discriminant of the cubic surface f.}

 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5."; 

/* r0 := FieldOfFractions(BaseRing(Parent(f))); */

 S1 := InterpolateContravariant(f, S_plane_curve, 4); 
 
 hes := Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..4]] : j in [1..4]]));

 I_8 := 2^(-11) * 3^(-9) * MonomialCoefficient(ApplyContravariant(S1,hes),1);
 C6_2 := ApplyContravariant(S1,f^2);             /* quadratic covariant */
 
 C10_0_2 := ApplyContravariant(C6_2, S1);        /* quadratic contravariant */ 

 I_16 := 2^(-30)*3^(-22)* MonomialCoefficient(ApplyContravariant(C6_2,C10_0_2),1);

 C14_2_0 := ApplyContravariant(C10_0_2, hes);  /* quadratic covariant */
 I_24 := MonomialCoefficient(ApplyContravariant(C10_0_2,C14_2_0),1)/(2^41 * 3^33);

 C_11_1 := ApplyContravariant(C10_0_2,f); /* linear covariant of  order 11 */
 /* 2^20 * 3^15 * (Salomons first linear covariant)  */

 my_I_32 := MonomialCoefficient(ApplyContravariant(C10_0_2, C_11_1^2),1);     
 I_32 := (I_16^2 - 2^(-60) * 3^(-44) * my_I_32)*(2/5);   /* Salmon's representative */
 my_I_40 := MonomialCoefficient(ApplyContravariant(S1, C_11_1^2 * C14_2_0),1); 
 I_40 := -1/100*I_8*I_32 - 1/50*I_16*I_24 - 1/(2^72*3^53*5^2)*my_I_40; /* Salmon's representative */
 return [I_8, I_16, I_24, I_32, I_40], -3^27*(((I_8^2-64*I_16)^2)-2^11*(8*I_32 + I_8 * I_24)); 
end intrinsic;


/* Salmon's 4 linear covariants */
intrinsic LinearCovariantsOfCubicSurface(f :: RngMPolElt) -> SeqEnum
{Salomons linear covariants of degree 11, 19, 27, 43  of the cubic surface f.}

 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5."; 

 r4 := PolynomialRing(FieldOfFractions(BaseRing(Parent(f))),4);

 S1 := InterpolateContravariant(r4!f, S_plane_curve, 4); 
 
 hes := r4!Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..4]] : j in [1..4]]));

 I_8 := 2^(-11) * 3^(-9) * MonomialCoefficient(ApplyContravariant(S1,hes),1);
 C6_2 := ApplyContravariant(S1,r4!f^2);             /* quadratic covariant */
 
 C10_0_2 := ApplyContravariant(C6_2, S1);        /* quadratic contravariant */ 

 I_16 := 2^(-30)*3^(-22)* MonomialCoefficient(ApplyContravariant(C6_2,C10_0_2),1);

 C14_2_0 := ApplyContravariant(C10_0_2, hes);  /* quadratic covariant */
 I_24 := MonomialCoefficient(ApplyContravariant(C10_0_2,C14_2_0),1)/(2^41 * 3^33);

 C_11_1 := ApplyContravariant(C10_0_2,r4!f) / 15045919506432; /* linear covariant of  order 11 */
 /* 2^20 * 3^15 * (Salomons first linear covariant)  */

 C_13_0_1 := ApplyContravariant(ApplyContravariant(S1, r4!f*hes), S1); /* linear Contravariant */

 /* A linear covariant of order 19 */ 
 C_19_1 := ApplyContravariant(C_13_0_1, C6_2); /* a linear covariant */
 C_19_1 := (C_19_1 + 80621568 * 15045919506432 * I_8 * C_11_1) / 12130256226103339253760;
           /* Salmon's representative for this order. */

 /* A linear covariant of order 27 */
 C_27_1 := ApplyContravariant(C_13_0_1, ApplyContravariant(C_13_0_1, r4!f)) / (2^42 * 3^33);
 C_27_1 := C_11_1 * I_16 + (C_27_1 - 2 * C_11_1 * I_8^2 - 10*I_8 * C_19_1) / 200;
 /* Salmon's representative for this order. */

 /* A linear covariant of order 43 */
 C_43_1 :=  ApplyContravariant(C_13_0_1,ApplyContravariant(C_13_0_1,ApplyContravariant(C_13_0_1,hes)))
            / (2^68 * 3^53);

 /* Salmon's representative for this order. */
 C_43_1 := -1/1000 * C_43_1 - 1/200 * I_8^2 * C_27_1 + I_16 * C_27_1 
           + 1/1000 * C_19_1 * I_8^3 -1/10 * I_8 * I_16 * C_19_1 - I_24 * C_19_1 
           + 1/200 * C_11_1 * I_8^2 * I_16 + 3/20 * C_11_1 * I_8 * I_24;
  
 return [C_11_1, C_19_1, C_27_1, C_43_1];
end intrinsic;


intrinsic SkewInvariant100(f :: RngMPolElt) -> RngElt
{Degree 100 skew invariant of the cubic surface f.}

 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5."; 
 cov := LinearCovariantsOfCubicSurface(f);

 r := Parent(cov[1]);
 
 return Determinant(Matrix([[MonomialCoefficient(l,r.i) : l in cov] : i in [1..4]])); 
end intrinsic;


intrinsic CubicSurfaceFromClebschSalmon(inv :: SeqEnum) -> RngMPolElt
{Cubic surface with prescribed Clebsch-Salmon invariants. (Assuming the last invariant to be non-zero.)}
  
 require (#inv eq 5) : "5 invariants must be specified.";   /* 5 numbers required */
 require (inv[5] ne 0) : "The last invariant can not be zero."; /* Surface must have a proper pentahedron */

 r4 := PolynomialRing(FieldOfFractions(Parent(inv[1])),4);
 r1 := PolynomialRing(FieldOfFractions(Parent(inv[1])));

 penta_pol := Polynomial([- inv[5]^2, inv[3]*inv[5], - (inv[3]^2 - inv[1] * inv[5])/4,+ inv[4],- inv[2], 1]);

 if Discriminant(penta_pol) eq 0 then /* repetitions in the penthedral coefficients */
  ppr := Roots(penta_pol);
  root_count := &+[a[2] : a in ppr];
  co_rat := &cat [[r[1] : i in [1..r[2]]] : r in ppr];
  if root_count eq 5 then /* All roots are rational. No desent is necessary */
   return &+[co_rat[i]*r4.i^3 : i in [1..4]] - co_rat[5]*(r4.1 + r4.2 + r4.3 + r4.4)^3;
  end if;
/* Multiple roots, but not all roots rational.
   Possible cases  3 linear (at least on double), 1 quadratic factor. 
                   double linear, 1 cubic factor.
                   1 linear, double quadratic factors.  

   Do the descent with the non-linear factor first */
  fac := Factorization(penta_pol); 
  nl := fac[#fac][1];
  my_ring := quo<r1 | ideal<r1 | nl>>;
  r4e := PolynomialRing(my_ring,4);
  lf := &+[r4e.i * my_ring.1^(i-1) : i in [1..Degree(nl)]];
  cf := my_ring.1 * lf^3;
  mon := Monomials(cf); co := Coefficients(cf);
  part := &+[Trace(co[i]) * r4!mon[i] : i in [1..#mon]];
  tr_lf := &+[r4.i * Trace(my_ring.1^(i-1)) : i in [1..Degree(nl)]];
  if fac[#fac][2] eq 2 then 
   part := part + Evaluate(part,[r4.3,r4.4,0,0]);
   tr_lf := tr_lf + Evaluate(tr_lf,[r4.3,r4.4,0,0]);
  end if; 
/* Need root_count linear. Their sum must be -tr_lf */  
  lfl := [r4.i : i in [6-root_count..4]]; 
  if #lfl eq 0 then lfl := [-tr_lf]; else Append(~lfl, -tr_lf - &+lfl);  end if;
  return part + &+[lfl[i]^3 * co_rat[i] : i in [1..root_count]];
 end if;
/* All roots are simple. Trace construction will word and do a descent if necessary. */
 my_ring := quo<r1 | ideal<r1 | penta_pol>>;
 r4e := PolynomialRing(my_ring,4);
 
 tr_l := [[Trace(my_ring.1^i)] :  i in [0..4]];
 bm := BasisMatrix(Kernel(Matrix(tr_l)));
 lf := &+[ bm[i,j] * r4e.i * my_ring.1^(j-1) : i in [1..4], j in [1..5]];
 cf := my_ring.1 * lf^3;
 mon := Monomials(cf); co := Coefficients(cf);

 return &+[r4!mon[i] * Trace(co[i]) : i in [1..#co]]; 
end intrinsic;


intrinsic ClassicalCovariantsOfCubicSurface(f :: RngMPolElt) -> SeqEnum
{A list of classical covariants of the cubic surface f.
 The first is the Hessian. 
 The next two are classicaly called T and theta.
 The last is a surface of degree 9 meeting f exactly in its 27 lines.}
 
 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5.";
 
 hes_mat := Matrix([[Derivative(Derivative(f,i),j) : i in [1..4]] : j in [1..4]]);
 hes_det := Determinant(hes_mat);
 
 T := 0;
 for i := 1 to 4 do 
  for j := 1 to 4 do
   T := T + Determinant(RemoveRowColumn(hes_mat,i,j))*(-1)^(i+j+1) * Derivative(Derivative(hes_det,i),j);
  end for;
 end for; 
 
 tm := Matrix(Parent(f),5,5,[0 : i in [1..25]]);
 tm := InsertBlock(tm,hes_mat,1,1);
 for i := 1 to 4 do 
  tm[5,i] := Derivative(hes_det,i);
  tm[i,5] := Derivative(hes_det,i);
 end for;
 
 theta := Determinant(tm);
 
 return([hes_det, T, theta, theta - 4*T*hes_det]);
end intrinsic;


/* In general a cubic surface can be written as l_1^3 + .. + l_5^3.
   The l_i are the faces of the pentahedron. We compute the l_i up to scalars.
   I.e. we compute {l_i} as a cluster in the dual space. 

   Note the scalars are unique up the 3rd roots of unity. 
   To determine the scalars is pure linear algebra.                                */
intrinsic PentahedronIdeal(f :: RngMPolElt) -> RngMPol
{Ideal defining the faces (as points in the dual space) of the pentahedron of the general cubic surface f.}

 require IsCubicSurface(f) : "Argument is not a cubic surface in characteristic > 5.";

 r4 := Parent(f); vars := [r4.i : i in [1..4]]; mon2 := Monomials((&+vars)^2);
 pd := [ApplyContravariant(op, f) : op in mon2];
 mat := Matrix([[MonomialCoefficient(qq,m) : m in vars] : qq in pd]);
 bm := BasisMatrix(Kernel(mat));
 assert NumberOfRows(bm) eq 6;
 bas := [&+[bm[i,j] * mon2[j] : j in [1..10]] : i in [1..NumberOfRows(bm)]];

/* Tensor the kernel with <d/dx,.., d/dw> */
 bas_tp := [qq * v : v in vars, qq in bas]; 
 mon3 := Monomials((&+vars)^3);
 mat := Matrix([ [MonomialCoefficient(qq,a)  : a in mon3] : qq in bas_tp]);
/* Compute the kernel of tensor product maped to the space of all diff-ops. */
 km_2 := BasisMatrix(Kernel(mat));
/* rewrite the basis of the kernel as tensors. We only need the factors in the first kernel */
 dkl := [&+[km_2[k,l + 4 *j]*bas[j+1] : j in [0..5]] : k in [1..NumberOfRows(km_2)], l in [1..4]];

 id := ideal<r4 | dkl>;

 return id;
end intrinsic;


