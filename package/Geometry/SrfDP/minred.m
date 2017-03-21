freeze;

/**************************************************************************
* Minimization and reduction routines for degree 3 and 4 Del Pezzos
*
* Stephan Elsenhans, March 2011
**************************************************************************/


intrinsic MinimiseReduce(S :: SrfDelPezzo) ->  SrfDelPezzo, Mtrx
{Minimize and reduce the del Pezzo surface S (of degree 3 or 4)}

 require Degree(S) in [3,4] : "Only degree 3 and 4 implemented.\n";

 return MinimizeReduce(S);
end intrinsic;


intrinsic MinimizeReduce(S :: SrfDelPezzo) ->  SrfDelPezzo, Mtrx
{"} // "
 require Degree(S) in [3,4] : "Only degree 3 and 4 implemented.\n";

 if Degree(S) eq 3 then
  eqn := Equation(S);
  mul := LCM([Denominator(a) : a in Coefficients(eqn)]);
  eq2,tr := MinimizeReduceCubicSurface(PolynomialRing(IntegerRing(),4)!(mul * eqn));
  S_mr := InternalDelPezzoSurface(AmbientSpace(S),[eq2]);
  S_mr`Degree := 3;
  return S_mr, tr;
 end if;
 if Degree(S) eq 4 then
  eqn := Equations(S);
  mul := [LCM([Denominator(a) : a in Coefficients(tmp)]) : tmp in eqn];
  r5 := PolynomialRing(IntegerRing(),5);
  eq2,tr := MinimizeReduceDeg4delPezzo([r5!(mul[i] * eqn[i]) : i in [1..#eqn]]);
  S_mr := InternalDelPezzoSurface(AmbientSpace(S),eq2);
  S_mr`Degree := 4;
  return S_mr, tr;
 end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////////////
// Auxiliary routines

/* Given a zero-dimensional ideal in a multivarible Polynomial Ring and a field.
   This routine returns a list of all Points of this ideal  */

/* The affine case */
GbToPoints := function(gb, tail)
 local up, spez, i, j, rt, f, res;

 if #gb eq 0 then return [tail]; end if;
 up := gb[#gb]; /* This polynomial is univariate */
 suc,up := IsUnivariate(gb[#gb], #gb);
 assert suc;  /* ideal is triangular and zero-dimensional */
 rt := Roots(up);
 res := [];
 for i := 1 to #rt do
  spez := [Evaluate(gb[j], #gb, rt[i][1]) : j in [1..#gb-1]];
  res := res cat $$(spez,[rt[i][1]] cat tail);
 end for;
 return res;
end function;

/* All points defined over nf will be returned */
PointsOfIdeal := function(id, nf)
 local tri, erg, i, gb, up, r_nf;

 erg := [];
 if 1 in id then return erg; end if;

 tri := TriangularDecomposition(Radical(id));
 for i := 1 to #tri do
  gb := GroebnerBasis(tri[i]);
  r_nf := PolynomialRing(nf,Rank(Parent(gb[1])));
  erg := erg cat GbToPoints([r_nf!f : f in gb], []);
 end for;
 return erg;
end function; 

/* Computes a vector in the kernel of the floating-point matrix m
   The routine rounds m to a singular matrix.                        */
MyKernelVector := function(m)
 local i,j,k,pz,ps, p_ind, tmp, m1,m2, res;
/* printf "Computing kernel\n"; */
 p_ind := [];
 for i := 1 to Min((#m)-1, #(m[1])) do
/* search for a pivot element */  
  pz := i; ps := 1; while ps in p_ind do ps := ps + 1; end while;
  for j := i to #m do
   for k := 1 to #(m[1]) do
    if (not k in p_ind) and (AbsoluteValue(m[j][k]) gt AbsoluteValue(m[pz][ps])) then
     pz := j; ps := k;
    end if;
   end for;
  end for;
  if (AbsoluteValue(m[pz][ps]) gt 0) then
   tmp := m[pz]; m[pz] := m[i]; m[i] := tmp; /* the i-th line is now the pivot-line */
/* We eleminiate the ps column */ 
   for j := i+1 to #m do
    m1 := m[i][ps]; m2 := m[j][ps];
    tmp := Sqrt(AbsoluteValue(m1)^2 + AbsoluteValue(m2)^2);
    m1 := m1 / tmp; m2 := m2 / tmp;
    for l := 1 to #m[1] do
     tmp := m[i][l];
     m[i][l] := ComplexConjugate(m1) * tmp + ComplexConjugate(m2) * m[j][l];
     m[j][l] := m2 * tmp - m1 * m[j][l];
    end for;
   end for; 
   Append(~p_ind,ps);
  end if;
 end for; 
 res := [Parent(m[1][1])! 0 : i in [1..#(m[1])]];
 for i := 1 to #m[1] do if not i in p_ind then res[i] := 1; end if; end for;
 if #p_ind eq #m[1] then res[p_ind[#p_ind]] := 1; Remove(~p_ind, #p_ind); end if;

 for i := #p_ind to 1 by -1 do
  tmp := 0;
  for j := 1 to #res do tmp := tmp + res[j] * m[i][j]; end for;
  res[p_ind[i]] := - tmp / m[i][p_ind[i]];
 end for; 

 return res;
end function;


////////////////////////////////////////////////////////////////////////////////
/* Degree 4

  Minimization for degree 4 del Pezzo surfaces. 
  For the reduction step we use a routine that is already available. 

  The minimization step treats only some of the weight-vector. 
  Thus it is not complet but in practice this is already helpful.

   given a sequence of 2 quadrics in P^4 we compute a superset of the set of primes 
   that allow an improvement.   
*/

declare verbose MinRedDeg4delPezzo, 1;

ImprovablePrimesDeg4delPezzo := function(gll)
 local mat, r2, i,j,r;
 
 r2 := PolynomialRing(IntegerRing(),1);
 r := Parent(gll[1]); 

 mat := ZeroMatrix(r2,5,5);
 for i := 1 to 5 do
  for j := 1 to 5 do
   mat[i,j] := MonomialCoefficient(gll[1],r.i * r.j) * r2.1 + MonomialCoefficient(gll[2],r.i * r.j) * 1;
  end for;
 end for;
 for i := 1 to 5 do mat[i,i] := 2 * mat[i,i]; end for;
 id := ideal<r2 | Minors(mat,4) >;
 id := ChangeOrder(id, "grevlex");
 gb := GroebnerBasis(id: Homogenize:=false);
 if TotalDegree(gb[#gb]) ne 0  then printf"Surface is singular."; return []; end if;
 n := IntegerRing()!gb[#gb];

 for i := 1 to 5 do
  for j := 1 to 5 do
   mat[i,j] := MonomialCoefficient(gll[1],r.i * r.j) * 1 + MonomialCoefficient(gll[2],r.i * r.j) * r2.1;
  end for;
 end for;
 for i := 1 to 5 do mat[i,i] := 2 * mat[i,i]; end for;
 
 id := ideal<r2 | Minors(mat,4) >;
 id := ChangeOrder(id, "grevlex");
 gb := GroebnerBasis(id: Homogenize:=false);
 if TotalDegree(gb[#gb]) ne 0 then printf "Surface is singular."; return[]; end if;
 n := Lcm(n,IntegerRing()!gb[#gb]);
 
 return PrimeDivisors(n);
end function;

SaturateQuadrics := function(gll)
 local mon, mat, f, i, j, d1,d2;
 
 mon := Monomials((&+[Parent(gll[1]).i : i in [1..5]])^2);

 mat := Matrix([[MonomialCoefficient(f,i) : i in mon] : f in gll]);
 d1 := AbsoluteValue(Determinant(Lattice(mat)));
 mat := Saturation(mat);
 d2 := AbsoluteValue(Determinant(Lattice(mat)));  
/*printf "Disciminants %o %o\n" d1,d2;*/
 return  d1 div d2,[&+[mat[i][j] * mon[j] : j in [1..#mon]] : i in [1..2]];
end function;

LinearFactors := function(id_l)
 local i, gb, res, f, j;

 res := [];
 for i := 1 to #id_l do
  for j := i to #id_l do
   gb := GroebnerBasis(id_l[i] meet id_l[j]);
   for f in gb do 
    if TotalDegree(f) eq 1 then  Append(~res, f); end if;
   end for;
  end for;
 end for;
 return res;
end function;

/* Weight-vector (0,0,0,0,1) -- the case of reducible reduction */
TrySplitCase := function(gll,p) 
 local r5, subs, res, pd, lf, i,j, tmp;

 r5 := PolynomialRing(GF(p),5); 
  
 pd := PrimaryDecomposition(ideal<r5 | gll>);
 lf := LinearFactors(pd);
 for i := 1 to #lf do
  j := 1; 
  while MonomialCoefficient(lf[i],r5.j) ne 1 do
   j := j + 1;
  end while;
  subs := [Parent(gll[1]).k : k in [1..5]];
  subs[j] := p*Parent(gll[1]).j -  
              &+[Parent(gll[1]).k *IntegerRing()!MonomialCoefficient(lf[i],r5.k) : k in [1..5] | k ne j];
  tmp := [Evaluate(gll[i],subs) : i in [1..2]];

  suc, tmp := SaturateQuadrics(tmp); 
  if suc ne 1 then
/*   printf "Split case for p = %o\n",p;  */
   return tmp, subs;
  end if;
 end for;
 
 return gll, [Parent(gll[1]).i : i in [1..5]];
end function;

/* Some cases of the weight vectors (0,0,0,0,1), (0,0,0,1,1), (0,1,1,1,1) and (0,1,1,1,1) */
TryConeCase := function(gll,p)
 local m1, m2, k1,k2, bm, ck,r,e1,e2,e3, tmp, suc, subs, f; 

 r := Parent(gll[1]);
 m1 := ZeroMatrix(GF(p),5,5);
 m2 := ZeroMatrix(GF(p),5,5);
 for i := 1 to 5 do
  for j := 1 to 5 do
   m1[i,j] := GF(p)!MonomialCoefficient(gll[1],r.i * r.j);
   m2[i,j] := GF(p)!MonomialCoefficient(gll[2],r.i * r.j);
  end for;
 end for;
 for i := 1 to 5 do m1[i,i] := 2 * m1[i,i]; m2[i,i] := 2 * m2[i,i]; end for;

 ck := Kernel(m1) meet Kernel(m2);
 if Dimension(ck) gt 0 then
  bm := BasisMatrix(ck);
  bm := Matrix([[IntegerRing()! bm[i,j] : i in [1..Rank(bm)]]: j in [1..5]]); 
/* Compute a basis of Z^5 such that the first elements generate ck mod p */
  e1,e2,e3 := SmithForm(bm);
  e2 := e2^(-1);
  subs := [&+[e2[i,j] * r.j : j in [1..5]] : i in [1..5]];  
  for j := 5 to 2 by -1 do
   subs := [Evaluate(f,j,p*r.j) : f in subs];
   tmp := [Evaluate(f,subs) : f in gll]; 
   suc, tmp := SaturateQuadrics(tmp);
   if suc ge p^(2*(6-j)) then 
/*    printf "Cone case for p = %o j = %o\n",p,j;  */
    return tmp, subs; 
   end if;
  end for;  
 end if;
 return gll, [r.i : i in [1..5]];
end function;

LocalMinimizeStepDeg4delPezzo := function(gll, p)
 local res,subs;

 _,res := SaturateQuadrics(gll);

 res, subs := TryConeCase(res, p);
 return res, subs;

 res, subs := TrySplitCase(res, p); 
 if subs ne [Parent(gll[1]).i : i in [1..5]] then
  return res, subs;
 end if;

end function;

intrinsic MinimizeDeg4delPezzo(f :: SeqEnum, p :: RngIntElt) -> SeqEnum, Mtrx
{Given a degree 4 del Pezzo surface defined by 2 quartics with integral coefficients 
and a prime p, this computes a partial local minimization at p.}

 gll := f;
 subs_tot := [Parent(gll[1]).i : i in [1..5]];
 repeat
  gll, subs := LocalMinimizeStepDeg4delPezzo(gll,p);
  if subs ne  [Parent(gll[1]).i : i in [1..5]] then
   vprintf MinRedDeg4delPezzo, 1:"Success\n";
  end if;
  subs_tot := [Evaluate(subs_tot[j], subs) : j in [1..5]];
 until subs eq [Parent(gll[1]).i : i in [1..5]];

/* Simplify transformation by using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(subs_tot[j],Parent(f[1]).i) : j in [1..#subs]] 
                    : i in [1..Rank(Parent(f[1]))]]));
 Lat := Transpose(Lat);

 res := [f[i]^Lat : i in [1..#f]];
 _,res := SaturateQuadrics(res); /* refine the lattic of quadratic forms */

 return res, Lat; 
end intrinsic;

MinimizeDeg4delPezzo := function(gll)
 local pl, subs, subs_tot, i;

 vprintf MinRedDeg4delPezzo, 1:"Computing bad primes.\n"; 
 pl := ImprovablePrimesDeg4delPezzo(gll);
 vprintf MinRedDeg4delPezzo, 1:"Bad primes %o.\n",pl; 

/* pl; */
 subs_tot := [Parent(gll[1]).i : i in [1..5]];

 for i := 1 to #pl do
  vprintf MinRedDeg4delPezzo, 1:"Trying local minimization for p = %o\n",pl[i];
  repeat
   gll, subs := LocalMinimizeStepDeg4delPezzo(gll,pl[i]);
   if subs ne  [Parent(gll[1]).i : i in [1..5]] then
    vprintf MinRedDeg4delPezzo, 1:"Success\n";
   end if;
   subs_tot := [Evaluate(subs_tot[j], subs) : j in [1..5]];
  until subs eq [Parent(gll[1]).i : i in [1..5]];
 end for; 

 return gll, subs_tot;
end function;


intrinsic MinimizeReduceDeg4delPezzo(f :: SeqEnum) -> SeqEnum, Mtrx
{Given a list of 2 quadrics that define a smooth degree 4 del Pezzo surfaces, this 
 routine returns a list of 2 quadrics with small coefficients that define the same 
 surface. The second returnvalue is the transformation matrix used.}

 vprintf MinRedDeg4delPezzo, 1:"Minimizing surface\n"; 
 res, subs := MinimizeDeg4delPezzo(f);

 vprintf MinRedDeg4delPezzo, 1:"Reducing surface\n";   
/* Simplify transformation from the minimization by using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(subs[j],Parent(f[1]).i) : j in [1..#subs]] 
                    : i in [1..Rank(Parent(f[1]))]]));
 Lat := Transpose(Lat);

 res := [f[i]^Lat : i in [1..#f]];
 _,res := SaturateQuadrics(res); /* refine the lattic of quadratic forms */
 
 res, m1, m2 := ReduceQuadrics(res);
 m1 := Transpose(m1);
 return [Parent(f[1])!res[i] : i in [1..#res]], Lat * m1;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////////
// IsSmooth and BadPrimes for general hypersurfaces

intrinsic IsSmoothHyperSurface(f :: RngMPolElt) -> BoolElt
{Test smoothness of the hypersurface given by f } 
 local c_r, chart, s_loc, subs, akt, i;
 
 require IsHomogeneous(f): "Homogenous polynomial expected.";

 c_r := PolynomialRing(FieldOfFractions(BaseRing(Parent(f))),Rank(Parent(f)));

 for akt := 1 to Rank(c_r) do
  s_loc := ideal<c_r | [f, Parent(f).akt - 1] cat [ Derivative(f,i) : i in [1..Rank(c_r)]]>; 
  if not 1 in s_loc then
   return false;
  end if; 
 end for;
 return true;
end intrinsic;

/* Compute all primes of bad reduction */
intrinsic BadPrimes(f :: RngMPolElt) -> SeqEnum
 {Computes primes of bad reduction of the hypersuface defined by the polynomial f}

 r := Rank(Parent(f));
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f);
 end if;
 require integral: "Polynomial with integral coefficients expected."; 

 require IsHomogeneous(f): "Homogenous polynomial expected.";
 require IsSmoothHyperSurface(f): "Surface is singular.";

 pr := 1;
 for i := 1 to Rank(Parent(f)) do
  id := ideal<Parent(f) | [Parent(f).i-1, f] cat 
        [Derivative(f,j) : j in [1..Rank(Parent(f))] | j ne i] >;
  id := ChangeOrder(id, "grevlex");
  gb := GroebnerBasis(id: Homogenize:=false);
  assert gb[#gb] in IntegerRing(); 
  pr := LCM(pr,IntegerRing()!gb[#gb]);
 end for; 
 return PrimeDivisors(pr);
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
// Minimization and reduction for cubic surfaces over Q

declare verbose MinRedCubSurf,2;

/* Minimization for cubic surfaces --  5 weight vectors have to be treated.  */

/* The reducible case */
SubsForLFac := function(fac, rk, p)
 local lf, tran,j,i;

 lf := rk!fac;
 j := 1;
 while MonomialCoefficient(lf, rk.j) ne 1 do j := j+1; end while;
 tran := [rk.i : i in [1..4]];
 tran[j] := Evaluate(2 * Parent(lf).j - lf,j,p*rk.j);
 
 return tran;
end function;

TestRedMinimization := function(f,p)
 local tran, res, tmp;

/* Weight vector 0,0,0,1 -- meaning reducible reduction -- test it */
 fac := Factorization(PolynomialRing(GF(p),4)!f);
 for tmp in fac do 
  if TotalDegree(tmp[1]) eq 1 then
   tran := SubsForLFac(tmp[1], Parent(f), p);
   res := Evaluate(f,tran);
   gcd := GCD(Coefficients(res));
   assert ((gcd mod p) eq 0); /* Equation gets divisible by the transformation */
   res := res div gcd;
   return true,res,tran;
  end if;
 end for;
 return false, 0,0;
end function;

/* The case of singular lines */
ListSingularLines := function(f)
 local sing,lines,pd,i,gb,tmp;  

 lines := [];
 sing := ideal<Parent(f) | f, Derivative(f,1), Derivative(f,2), Derivative(f,3), Derivative(f,4)>; 
 pd := PrimaryDecomposition(Radical(sing));
 for i := 1 to #pd do
  gb := GroebnerBasis(pd[i]);
  if #gb eq 2 and &and [Degree(tmp) eq 1 : tmp in gb] then Append(~lines,gb); end if;
 end for;
 return lines;
end function;

/* Moves singlar line to rk.1 = rk.2 = 0 

   The lines is given by 2 linear equations over GF(p). 
   The resulting transformations is defined in rk.       */
NormalizeLine := function(line, rk)
 local i,j,tran, k,perm,c;

  i := 1;  
  while MonomialCoefficient(line[1],Parent(line[1]).i) ne 1 do i := i+1; end while;
  j := i+1;
  while MonomialCoefficient(line[2],Parent(line[2]).j) ne 1 do j := j+1; end while;
 /* We replace the i-th variable using the first and the j-th variable using the second equation. */

  tran := [rk.i : i in [1..4]];
  for k := 1 to 4 do 
   if i ne k then
    tran := [Evaluate(akt,i,rk.i - rk.k*IntegerRing()!
              MonomialCoefficient(line[1],Parent(line[1]).k)) : akt in tran];
   end if;
  end for; 
  for k := 1 to 4 do
   if j ne k then
    tran := [Evaluate(akt,j,rk.j - rk.k*IntegerRing()!
               MonomialCoefficient(line[2],Parent(line[2]).k)) : akt in tran];
   end if;
  end for;

  perm := [rk!0 : k in [1..4] ];
  c := 3;
  for k := 1 to 4 do 
   if k eq i then perm[k] := rk.1; else
    if k eq j then perm[k] := rk.2; else
     perm[k] := rk.c; c := c + 1;
    end if;
   end if;
  end for;
  tran := [Evaluate(akt,perm) : akt in tran];
 return(tran);
end function;

PointsOnLine := function(line)
 local tran,res,i,j,rj, akt;
 
 tran := NormalizeLine(line, PolynomialRing(IntegerRing(),4));
 res := []; 
 for i := 0 to 1 do
  if i eq 0 then rj := [1]; else rj := BaseRing(Parent(line[1])); end if;
  for j in rj do
   Append(~res,[BaseRing(Parent(line[1]))!Evaluate(akt,[0,0,i,j]) : akt in tran]);
  end for;
 end for;
 return res; 
end function;

CritPointsOnLine := function(line,f,p)
 local r2, akt, tran, rf, fac, res, r2p, gcd, tmp, i;

 r2 := PolynomialRing(IntegerRing(),2);
 tran := NormalizeLine(line, PolynomialRing(IntegerRing(),4));
 tran := [Evaluate(akt,[0,0,r2.1,r2.2]) : akt in tran]; 
 rf := Evaluate(f,tran);
 gcd := GCD(Coefficients(rf));
 assert (gcd mod p) eq 0;  /* Equation is zero mod p but not mod p^2 on the line */
 assert (gcd mod (p^2)) ne 0;  
 rf := rf div p;
 r2p := PolynomialRing(GF(p),2);
 fac := Factorization(r2p!rf); 
 res := [];
 for akt in fac do
  if Degree(akt[1]) eq 1 then
   tmp := [MonomialCoefficient(akt[1],r2p.2), -MonomialCoefficient(akt[1],r2p.1)];
   Append(~res,[Evaluate(tran[i],tmp) : i in [1..4]]);
  end if;
 end for;
 return res;
end function;

/* The homogeneous case */
GroebnerBasisToPoint := function(gb) 
 local akt, mat, ker;

 if (#gb eq 3) and Max([TotalDegree(akt) : akt in gb]) eq 1 then
  mat := Matrix([[MonomialCoefficient(f,Parent(f).k) : k in [1..4]] : f in gb]);
  ker := BasisMatrix(Kernel(Transpose(mat)));
  assert Rank(ker) eq 1; /* Just a projective point */
  return true, [ker[1,k] : k in [1..4]];
 end if; 

 return false,[0,0,0,0];
end function;

ListIsolatedSingularPoints := function(f)
 local res,gen,i,sing,pd,j,suc,pt;
 
 res := []; 
 sing := ideal<Parent(f) | [f] cat [Derivative(f,i) : i in [1..4]]  /* gen cat [Parent(f).i - 1]*/>;
 pd := PrimaryDecomposition(sing);
 for j := 1 to #pd do 
  suc,pt := GroebnerBasisToPoint(GroebnerBasis(Radical(pd[j])));
  if suc then Append(~res,pt); end if;
 end for;  
 return(res);
end function;

/* Compute a unimodlar substitution, that evaluates on [1,0,0,0] to pt */
NormalizePoint := function(pt,rk)
 local subs, i, j, akt, perm;

 i := 1; 
 while pt[i] eq 0 do i := i + 1; end while;
 subs := [ IntegerRing()!(pt[1]*pt[i]^(-1))*rk.i,IntegerRing()!(pt[2]*pt[i]^(-1))*rk.i,
           IntegerRing()!(pt[3]*pt[i]^(-1))*rk.i,IntegerRing()!(pt[4]*pt[i]^(-1))*rk.i ];
 for j := 1 to 4 do if j ne i then subs[j] := subs[j] + rk.j; end if; end for;
 if i ne 1 then
  perm := [rk.1, rk.2, rk.3, rk.4];
  perm[i] := rk.1;
  perm[1] := rk.i;
  subs := [Evaluate(akt,perm) : akt in subs];
 end if;
 return subs;
end function;

ListCriticalPoints :=  function(f, lines, p)
 local crit_pnt,rp3, gb,pt,akt, suc;
 
 crit_pnt := ListIsolatedSingularPoints(PolynomialRing(GF(p),4)!f);
 for line in lines do
  if p le 3 then
   crit_pnt := crit_pnt cat PointsOnLine(line);
  else
   crit_pnt := crit_pnt cat CritPointsOnLine(line,f,p);
  end if;
 end for;

 if IsIrreducible(PolynomialRing(GF(p),4)!f) and (not IsIrreducible(PolynomialRing(GF(p^3),4)!f)) then
/* We have 3 conjugate planes */
  rp3 := PolynomialRing(GF(p^3),4);
  fac := Factorization(rp3!f);
  gb := GroebnerBasis(ideal<rp3 | [akt[1] : akt in fac]>);
  suc, pt := GroebnerBasisToPoint(gb);
  if suc then
   if &and [akt in GF(p) : akt in pt] then
    Append(~crit_pnt, [GF(p)!akt : akt in pt]);
   end if;
  end if;
 end if;
 return crit_pnt;
end function;

/* f is an intermediate result:
   - treated with the wight-vector (0,1,1,1)
   - divided by p^2  

  We have to try, weather (0,0,1,1) gives us a gcd of p^2 or
                          (0,1,1,2) gives us a gcd of p^4.
*/
TryToComplete := function(f,p) 
 local fac, rp, l_fac, q_fac, tmp, ttc_2, gcd_2, sing, gb, i, tran, res, gcd, triv, tran_2, ttc, suc; 

 vprintf MinRedCubSurf,2:"Try to complete for weight vectors (0,1,2,2) and (0,2,2,3).\n";   

/* As we can go back to the beginning form ttc_1 with the weight-vector (0,0,0,1), we must be reducible */
 rp := PolynomialRing(GF(p),4);
 fac := Factorization(rp!f);
 triv := [tmp : tmp in fac | tmp[1] eq rp.1];
 assert #triv gt 0; /* Using the trivial factor we get back to the beginning */
 if triv[1][2] ge 2 then
 /* printf"Trivial factor is multiple\n";  */
  return false,0,0; /* The trivial factor must have multiplicity 1, or no improvement is possible */
 end if;  
 
 l_fac := [tmp[1] : tmp in fac | (TotalDegree(tmp[1]) eq 1) and (tmp[1] ne rp.1)];
 q_fac := [tmp[1] : tmp in fac | TotalDegree(tmp[1]) eq 2]; 

 l_fac := [tmp : tmp in l_fac | tmp ne rp.1]; /* Throw it away */
 if (#q_fac gt 0) or (#l_fac eq 2) then /* Only the (0,1,2,2)-case is possible */
  q_fac := &*(q_fac cat l_fac);
  assert TotalDegree(q_fac) eq 2; /* The remaining degree 2 factor */
  sing := ideal<rp | [q_fac] cat [Derivative(q_fac,i) : i in [1..4]]>;
  gb := GroebnerBasis(Radical(sing));
 
  if (#gb eq 2) and (Max([Degree(i) : i in gb]) eq 1) then
   tran := NormalizeLine(gb,Parent(f));
   tran := [Evaluate(Evaluate(tmp,1,p*Parent(f).1),2,p*Parent(f).2) : tmp in tran];
   res := Evaluate(f,tran);
   gcd := GCD(Coefficients(res));
   
   assert ((gcd mod p) eq 0); /* Singular line is on the surface */
/*   printf "gcd %o found\n",gcd; */
   if (gcd mod p^2) eq 0 then
    vprintf MinRedCubSurf,2:"Success\n";
    return true, res div gcd, tran;
   end if;
  end if;
  return false,0,0; /* No improvement possible */ 
 end if;

/* printf"Multiple linear factor found %o\n",l_fac;  */
  
/* Now we have a remaining linear factor of multiplicity 2 */ 
 tran := SubsForLFac(l_fac[1], Parent(f), p);
  
 ttc := Evaluate(f,tran);
 gcd := GCD(Coefficients(ttc));
 assert gcd mod p eq 0; /* This factor p is automatic  */
 if gcd mod p^2 eq 0 then
  vprintf MinRedCubSurf,2:"Success\n";
  return true, ttc div gcd, tran;
 end if;
 ttc := ttc div p;
 suc, res, tran_2 := TestRedMinimization(ttc,p);
 if suc then
  vprintf MinRedCubSurf,2:"Success\n";
  return true,res, [Evaluate(tmp,tran_2) : tmp in tran];
 end if; 
 
/* Now we are finished with the wight vector (0,1,2,2). 
   (0,2,2,3) is only possible if ttc is modulo p the union of 3 conjugate planes that have a common line. 
   If one plane is definied over GF(p) then we are already done.   */

/* printf "Intermediate equation %o\n",ttc; */
 sing := ideal<rp | [ttc] cat [Derivative(ttc,i) : i in [1..4]]>;
 gb := GroebnerBasis(Radical(sing));

 if (#gb eq 2) and (Max([Degree(i) : i in gb]) eq 1) then
  tran_2 := NormalizeLine(gb,Parent(f));
  tran_2 := [Evaluate(Evaluate(tmp,1,p*Parent(f).1),2,p*Parent(f).2) : tmp in tran_2];
  
  ttc_2 := Evaluate(ttc,tran_2);
  gcd := GCD(Coefficients(ttc_2));
  assert ((gcd mod p) eq 0); /* The singular line is on the surface */
  if (gcd mod p^2) eq 0 then /* Maybe this never happens. */
   vprintf MinRedCubSurf,2:"Success\n";
   return true, res div gcd, [Evaluate(tmp,tran_2) : tmp in tran];
  end if;  
  ttc_2 := ttc_2 div p;
  fac := Factorization(rp!ttc_2);
  for tmp in fac do
   if TotalDegree(tmp[1]) eq 1 then
    tran_3 := SubsForLFac(tmp[1], Parent(f), p); 
    ttc_3 := Evaluate(ttc_2,tran_3);
    gcd := GCD(Coefficients(ttc_3));
    assert ((gcd mod p) eq 0); /* This factor p is automatic  */
    if gcd mod p^2 eq 0 then
     tran := [Evaluate(tmp,tran_2) : tmp in tran];
     vprintf MinRedCubSurf,2:"Success\n";
     return true, ttc_3 div gcd, [Evaluate(tmp,tran_3) : tmp in tran];
    end if; 
   end if; 
  end for; 
 end if;   
 return false,0,0;
end function;

/* Returns a better equation and the applied substitution */
LocalMinimization := function(f,p) 
 local suc,res,tran, lines, gcd, crit_pnt, ttc, tran_2, i;

 vprintf MinRedCubSurf,2:"Trying reducible reduction\n";
 suc,res,tran := TestRedMinimization(f,p);
 if suc then 
  vprintf MinRedCubSurf,2:"Success using weight vector (0,0,0,1). \n";
  return res, tran; 
 end if;
/* Now we assume that the reduction of the surface is irreducible over GF(p)
   only singular points and lines are possible */

/* Weight vector 0,0,1,1 -- meaning reduction with singular line -- test it */
/* printf "Trying (0,0,1,1)\n"; */
 vprintf MinRedCubSurf,2:"Searching for singluar lines\n";
 lines := ListSingularLines(PolynomialRing(GF(p),4)!f);
 vprintf MinRedCubSurf,2:"%o singular lines found.\n",#lines;
 for line in lines do 
  tran := NormalizeLine(line, Parent(f));      tran := [Evaluate(akt,1,p*Parent(akt).1) : akt in tran];
  tran := [Evaluate(akt,2,p*Parent(akt).2) : akt in tran];
  res := Evaluate(f,tran);
  gcd := GCD(Coefficients(res));
  if (gcd mod (p^2)) eq 0 then
   vprintf MinRedCubSurf,2:"Success using weight vector (0,0,1,1). \n";   
   res := res div gcd;
   return res,tran;
  end if;
 end for;
/* when we arrive here, then the surface is irreducible and no singular line is mod p^2 contained in f = 0 */

 vprintf MinRedCubSurf,2:"Searching for critical points. \n";
 crit_pnt := ListCriticalPoints(f,lines,p);
 vprintf MinRedCubSurf,2:"%o critical points found. \n",#crit_pnt;
/* crit_pnt; */
/* printf"Trying remaining weight-vectors\n"; */
 for i := 1 to #crit_pnt do
  tran := NormalizePoint(crit_pnt[i], Parent(f));
/*  printf "Normalize singular point by %o\n",tran;  */
  tran := [Evaluate(akt,[Parent(f).1, Parent(f).2*p, Parent(f).3*p, Parent(f).4*p]) : akt in tran];
  res := Evaluate(f, tran);
  gcd := GCD(Coefficients(res));
/*  printf "gcd %o found\n",gcd; */
  if gcd mod p^3 eq 0 then
   vprintf MinRedCubSurf,2:"Success using weight vector (0,1,1,1). \n";   
   return (res div gcd),tran;
  end if;
  if gcd mod p^2 eq 0 then
   suc,ttc,tran_2 := TryToComplete(res div gcd,p);
   if suc then 
    return ttc, [Evaluate(akt,tran_2) : akt in tran];
   end if;
  end if; 
 end for; 
 return f, [Parent(f).i : i in [1..4]];
end function;

/* Compute all primes that have to be tested. This is a subset of all bad primes. 
   We avoid primes that only give Singularities of Type A_1 as these can be very 
   big an slow down the factorization step. 

   Note that a cubic surface that has only A_1 singularities is stable.
*/
ImprovablePrimes := function(gl)
 local r3, chart, id, gb, tmp, subs, tf;

 tf := 1;
 r3 := PolynomialRing(IntegerRing(),3);
 for subs in [[1,r3.1,r3.2,r3.3], [r3.1,1,r3.2,r3.3], [r3.1,r3.2,1,r3.3], [r3.1,r3.2,r3.3,1]] do
  chart := Evaluate(gl,subs);
  id := ideal<r3 | [chart] cat [Derivative(chart,i) : i in [1..3]] cat 
         [6*Determinant(Matrix([[Derivative(Derivative(chart,i),j) : i in [1..3]] : j in [1..3] ]))]>;
  id := ChangeOrder(id, "grevlex");
  gb := GroebnerBasis(id: Homogenize:=false);
  if TotalDegree(gb[#gb]) ne 0 then
   return false,0;
  end if;
  tf := LCM(tf,IntegerRing()!gb[#gb]);
 end for;
 vprintf MinRedCubSurf,2:"Starting factorization\n";
 return true,PrimeDivisors(tf);
end function;

/* Code for the reduction algorithm */



PentaederIndices := function(sing_pt)
 local ind,i,j,k,l, dl, dm; 

 ind := [[i,j,k,l] : i,j,k,l in [1..10] | (i lt j) and (j lt k) and (k lt l)];
 dl := [AbsoluteValue(Determinant(Matrix([sing_pt[i] : i in j]))) : j in ind];

 dm := [Max([dl[j] : j in [1..#dl] | #(Set(ind[j]) meet Set(i)) eq 0]) : i in ind];
 ParallelSort(~dm,~ind);
/* The 5 smallest entries define the pentahedron */
 if dm[6] lt dm[5]*10^20 then
 /* printf"Insufficient precision for pentaheder-reconstruction\n"; */
  return false,ind;  
 end if;
 return true, ind;
end function; 

TryReduceCubicSurface := function(gl)
 local r4, hes, dim, i,j,k,l,m,n, nf, sing, sing_pt, r4c, r4r, bas, mat, mon, lf, cf, pc, nl, dl, dm, suc, prec; 

/* printf"Starting reduction\n"; */
 r4 := PolynomialRing(RationalField(),4);

/* The kernel surface */
 hes := r4!Determinant(Matrix([[Derivative(Derivative(gl,i),j) : i in [1..4]] : j in [1..4]]));
  
 if not IsIrreducible(hes) then
  return false,[Parent(gl).i : i in [1..4]];  
 end if;
 sing := [ ideal< r4 | [r4.1-1] cat [Derivative(hes,i) : i in [1..4]] >,
           ideal< r4 | [r4.1, r4.2-1] cat [Derivative(hes,i) : i in [1..4]] >,
           ideal< r4 | [r4.1, r4.2, r4.3-1] cat [Derivative(hes,i) : i in [1..4]] >,
           ideal< r4 | [r4.1, r4.2, r4.3, r4.4-1] cat [Derivative(hes,i) : i in [1..4]] > ];
 dim := -1;
 for i := 1 to 4 do
  j := Dimension(sing[i]);
  dim := Max(j,dim);
 end for;
 if not (dim eq 0) then /* Singular curves -- do not know how to find the pentahedron */
  return false,[Parent(gl).i : i in [1..4]];  
 end if;

 prec := 20 + Round(Max([Log(1 + AbsoluteValue(i)) : i in Coefficients(gl)]));
 repeat
  prec := prec * 2;
  vprintf MinRedCubSurf,2:"Computing pentahedra with floating-point precision %o.\n",prec;
  sing_pt := &cat [PointsOfIdeal(sing[i], ComplexField(prec)) : i in [1..4] | sing[i] ne ideal<r4|1> ];

  if not (#sing_pt eq 10) then /* Not 10 singular points -- do not know how to find the pentahedron */
   return false,[Parent(gl).i : i in [1..4]]; 
  end if;
  suc, nl := PentaederIndices(sing_pt);
 until suc; 

 r4c := PolynomialRing(ComplexField(prec),4);
 lf := [];
/* printf "Computing linear forms \n"; */
 for i := 1 to 5 do
  bas := MyKernelVector([sing_pt[j] : j in [1..10] | not j in nl[i]]);
  Append(~lf,&+[bas[j] * r4c.j : j in [1..4]]);
 end for;
/* printf "Computing pentahedral coefficients \n"; */
/* Now we need the correct scaling of the linear forms */
 mat := [[ComplexField(prec)!0 : i in [1..6]] : j in [1..20]];
 mon := Monomials((r4.1+r4.2+r4.3+r4.4)^3);
 for j := 1 to 5 do
  cf := lf[j]^3;
  for i := 1 to #mon do
   mat[i][j] := MonomialCoefficient(cf,r4c!mon[i]);
  end for;
 end for;
 for i := 1 to #mon do
  mat[i][6] := MonomialCoefficient(r4!gl,mon[i]);
 end for; 
/* [[ComplexField(10)!mat[i][j] : j in [1..6]] : i in [1..20]]; */
 bas := MyKernelVector(mat);
 bas := [bas[i] / bas[6] : i in [1..6]]; 
 lf := [lf[i] * bas[i]^(1/3) : i in [1..5]];
 /* now lf[1]^3 + lf[2]^3 +.. + lf[5]^3 is close to gl */

 r4r := PolynomialRing(RealField(prec),4);
 qf := 0;
 for i := 1 to #lf do
  qf := qf + (Re(Evaluate(lf[i],[1,0,0,0])) * r4r.1 + Re(Evaluate(lf[i],[0,1,0,0])) * r4r.2 
            + Re(Evaluate(lf[i],[0,0,1,0])) * r4r.3 + Re(Evaluate(lf[i],[0,0,0,1])) * r4r.4)^2
           + (Im(Evaluate(lf[i],[1,0,0,0])) * r4r.1 + Im(Evaluate(lf[i],[0,1,0,0])) * r4r.2
            + Im(Evaluate(lf[i],[0,0,1,0])) * r4r.3 + Im(Evaluate(lf[i],[0,0,0,1])) * r4r.4)^2;
 end for;
/* printf"Running LLL\n"; */
 lat := Lattice(IdentityMatrix(RealField(prec),4),SymmetricMatrix(qf));
 vprintf MinRedCubSurf,2:"Running LLL\n";
 _,tran := LLL(lat);
/* tran := [tran[1,i] * Parent(gl).1 + tran[2,i] * Parent(gl).2 
        + tran[3,i] * Parent(gl).3 + tran[4,i] * Parent(gl).4: i in [1..4]]; */
 return  true, tran;
end function;

intrinsic MinimizeCubicSurface(f :: RngMPolElt, p :: RngIntElt) -> RngMPolElt, Mtrx
{Given a cubic surface over the rationals, this returns a model (isomorphic over Q) 
whose invariants are minimized at p.  The transformation matrix is also returned.}

 r := Rank(Parent(f));
 require r eq 4: "Polynomial in 4 variables expected."; 
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f*Denominator(f));
 end if;
 require integral: "Polynomial over the integers or rationals expected."; 

 require (Degree(f) eq 3) and IsHomogeneous(f) : "Homogeneous cubic polynomial expected.";

 res := f div GCD(Coefficients(f));
 tran := [Parent(f).i : i in [1..4]];
 repeat
  res,t_neu := LocalMinimization(res,p);
 /*  printf"Transformation %o found\n",t_neu; */
  tran := [Evaluate(akt,t_neu) : akt in tran];
 until (t_neu eq [Parent(f).i : i in [1..4]]);

/* Simplify transformation by using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(tran[j],Parent(f).i) : j in [1..#tran]] : i in [1..Rank(Parent(f))]]));
 Lat := Transpose(Lat);

 res := f^Lat;
 res := res div GCD(Coefficients(res));
 
 return res, Lat;
end intrinsic;

intrinsic ReduceCubicSurface(f :: RngMPolElt) -> RngMPolElt, Mtrx
{A reduced model of the cubic surface defined by the polynomial f
(which must have integral coefficients).  The transformation matrix
is also returned.}

 r := Rank(Parent(f));
 require r eq 4: "Polynomial in 4 variables expected."; 
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f);
 end if;
 require integral: "Polynomial with integral coefficients expected."; 
 
 require IsHomogeneous(f) and (Degree(f) eq 3):  
  "Homogenous cubic polynomial expected.";

 mon := Monomials((Parent(f).1 + Parent(f).2 + Parent(f).3 + Parent(f).4)^3);
 vprintf MinRedCubSurf,1:"Reducing cubic surface\n";

 suc,t_neu := TryReduceCubicSurface(f);  
 while not suc do
  vprintf MinRedCubSurf,1:"Degenerated pentahedra trying a surface close to the initial one.\n";
  suc,t_neu := TryReduceCubicSurface(f * 10^20 + &+[Random([-2..2]) * u : u in mon]);  
 end while;
 t_neu := Transpose(t_neu);
 res := f^t_neu;

 return res, t_neu;
end intrinsic;

intrinsic MinimizeReduceCubicSurface(f :: RngMPolElt) -> RngMPolElt, Mtrx
{Given a smooth cubic surface with integral coefficients, 
 this returns a model (isomorphic over Q) with small coefficients.
 The transformation matrix is also returned.}

 r := Rank(Parent(f));
 require r eq 4: "Polynomial in 4 variables expected."; 
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f*CoefficientDenominator(f));
 end if;
 require integral: "Polynomial over the integers or rationals expected."; 
 
 require IsHomogeneous(f) and (Degree(f) eq 3):  
  "Homogenous cubic polynomial expected.";

 vprintf MinRedCubSurf,1:"Computing improveable places.\n";

 stab, bp := ImprovablePrimes(f);
 
 require stab:"Surface has hard singularities.";

 res := f div GCD(Coefficients(f));
 
 tran := [Parent(f).i : i in [1..4]];
 for i := 1 to #bp do
  vprintf MinRedCubSurf,1:"Local Minimization for p = %o\n",bp[i];
  repeat
   res,t_neu := LocalMinimization(res,bp[i]);
 /*  printf"Transformation %o found\n",t_neu; */
   tran := [Evaluate(akt,t_neu) : akt in tran];
  until (t_neu eq [Parent(f).i : i in [1..4]]);
 end for;

/* Simplify Transformation obtained by the minimization algorithm using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(tran[j],Parent(f).i) : j in [1..#tran]] : i in [1..Rank(Parent(f))]]));
 Lat := Transpose(Lat);

 res := f^Lat;
 res := res div GCD(Coefficients(res));

 res, t_neu := ReduceCubicSurface(res);
    
 return res, Lat * t_neu;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//   Minimization and reduction for plane quartics

declare verbose PlaneQuartic, 1;

TryReducibleReduction := function(f,p)
 local fac, lf, act, j, subs,res, gcd, gcd_l, res_l, subs_l;

 res_l := []; gcd_l := []; subs_l := [];
 fac := Factorization(PolynomialRing(GF(p),3)!f);
 lf := [i[1] : i in fac | (TotalDegree(i[1]) eq 1)];
/* linear factors -- test weight vector [0,0,1] */
 for act in lf do
  j := 1; 
  while MonomialCoefficient(act,Parent(act).j) ne 1 do j := j+1; end while;
  subs := [Parent(f).i : i in [1..3]];
  subs[j] := -(Parent(f)!act) + (p + 1)*Parent(f).j;
  res := Evaluate(f,subs);
  gcd := GCD(Coefficients(res));
  assert gcd mod p eq 0;
  Append(~res_l, res div gcd);
  Append(~gcd_l, gcd); 
  Append(~subs_l, subs);
 end for; 
 return res_l, subs_l, gcd_l;
end function;

NormalizePoint := function(pt, p, r)
 local subs, j,i, rep;

 j := 1; while pt[j] eq 0 do j := j + 1; end while;
 rep := [pt[i] / pt[j] : i in [1..3]];
 subs := [IntegerRing()!rep[i] * r.1 : i in [1..3] ]; /* Move rep[i] to [1,0,0] */
 if j eq 1 then
  subs[2] := subs[2] + p*r.2; subs[3] := subs[3] + p*r.3;
 end if;
 if j eq 2 then
  subs[1] := subs[1] + p*r.2; subs[3] := subs[3] + p*r.3;
 end if;
 if j eq 3 then
  subs[1] := subs[1] + p*r.2; subs[2] := subs[2] + p*r.3;
 end if;
 return subs;
end function;

LocalMinimizationStepPlaneQuartic := function(f, p)
 local  res_l, subs_l, gcd_l, ind, i,j,k,m, res_l2, subs_l2, gcd_l2, zz, co, ker, bm, para, S, cpt, subs, nl;

 res_l, subs_l, gcd_l := TryReducibleReduction(f,p);
 ind := [j : j in [1..#gcd_l] | gcd_l[j] mod p^2 eq 0];
 if #ind gt 0 then
  vprintf PlaneQuartic,1:"Weight vector (0,0,1)\n";
  return res_l[ind[1]], subs_l[ind[1]];
 end if;

/* Reducible case does not work -- try weight vector (0,1,3): */
 fac := Factorization(PolynomialRing(GF(p),3)!f);

 lf := [i[1] : i in fac | (TotalDegree(i[1]) eq 1)];
/* Search for critical points on lines -- try weight vector [0,1,3] */
 for act in lf do
/* Parametrize the line */
  zz := PolynomialRing(IntegerRing(),2);
  co := Matrix([[MonomialCoefficient(act,Parent(act).i)] : i in [1..3]]);
  ker := Kernel(co);
  assert Dimension(ker) eq 2;
  bm := BasisMatrix(ker);
  para := [ &+[(IntegerRing()!bm[j,i]) * zz.j : j in [1..2]] : i in [1..3]];
  S := Scheme(ProjectiveSpace(GF(p),1), [Evaluate(f,para) div p] cat 
                                        [Evaluate(Derivative(f,i),para) : i in [1..3]]);
/* Scheme of critical points */
  cpt := Points(S);
  for i := 1 to #cpt do
   pt := [cpt[i][j] : j in [1..2]];
   pt := [Evaluate(para[k],pt) : k in [1..3]];
   subs := NormalizePoint(pt, p, Parent(f));
   ttc := Evaluate(f,subs);
   gcd := GCD(Coefficients(ttc));
   assert (gcd mod (p^2) eq 0);
   if gcd mod p^3 eq 0 then
    vprintf PlaneQuartic,1: "Weight vector (0,1,1)\n";
    return ttc div gcd, subs;
   end if; 
   res_l, subs_l, gcd_l := TryReducibleReduction(ttc div gcd,p);
   for j := 1 to #res_l do
    if gcd_l[j] mod p^5 eq 0 then
     vprintf PlaneQuartic,1: "Weight vector (0,1,2)\n";
     return res_l[j], [Evaluate(subs[k],subs_l[j]) : k in [1..3]];
    end if;
    res_l2, subs_l2, gcd_l2 := TryReducibleReduction(res_l[j],p);
    for k := 1 to #res_l2 do
     if (gcd_l[j] * gcd_l2[k]) mod p^6 eq 0 then
      subs := [Evaluate(subs[m],subs_l[j]) : m in [1..3]];
      subs := [Evaluate(subs[m],subs_l2[k]) : m in [1..3]];
      vprintf PlaneQuartic,1:"Weight vector (0,1,3)\n";
      return res_l2[j], subs;
     end if;
    end for;
   end for;
  end for;
 end for;

/* Complete weight vector [0,1,1] -- critical point is no longer on a rational line  
   The double of a smooth conic does not lead to a critical point.  */
 if fac[1][2] eq 2 and TotalDegree(fac[1][1]) eq 2 then
/* Singular point of double conic */
  S := Scheme(ProjectiveSpace(GF(p),2),[fac[1][1]] cat [Derivative(fac[1][1],i) : i in [1..3]]);
 else
  nl := &*([fac[i][1] : i in [1..#fac] | TotalDegree(fac[i][1]) gt 1] cat [1]); 
/* Singular point, but not on a line -- Points on lines are alreaddy treated. */
  S := Scheme(ProjectiveSpace(GF(p),2),[nl] cat [Derivative(fac[1][1],i) : i in [1..3]]);   
 end if;
 cpt := Points(S); 
 for i := 1 to #cpt do
  subs := NormalizePoint([cpt[i][k] : k in [1..3]], p, Parent(f));
  res := Evaluate(f,subs);
  gcd := GCD(Coefficients(res));
  assert (gcd mod p eq 0);
  if gcd mod p^3 eq 0 then
   vprintf PlaneQuartic,1: "Weight vector (0,1,1)\n";
   return res div gcd, subs;
  end if; 
 end for;

 return f, [Parent(f).i : i in [1..3]]; 
end function;


/* Compute all primes of very bad reduction */
ImproveablePrimes := function(f)
 local i,j,k, r2, charts, hes, pr; 

 r2 := PolynomialRing(IntegerRing(),2);

 charts := [Evaluate(f,[1,r2.1, r2.2]), Evaluate(f,[r2.1, 1,r2.2]),Evaluate(f,[r2.1, r2.2, 1])];
 
 pr := 1;
 for i := 1 to 3 do
  hes := Determinant(Matrix([[Derivative(Derivative(charts[i],j),k) : j in [1..2]] : k in [1..2]]));
  id  := ideal<r2 | [charts[i], hes] cat  [Derivative(charts[i],j) : j in [1..2]] >;
  id := ChangeOrder(id,"grevlex");
  gb := GroebnerBasis(id: Homogenize := false);
  assert gb[#gb] in IntegerRing(); 
  pr := LCM(pr,IntegerRing()!gb[#gb]);
 end for;
/* pr;  */

 return PrimeDivisors(pr);
end function;


ReducePlaneQuartic := function(f)
 local hes,id,i,j,pl, CC, q, mt, subs, res, prec, mul;

 mul := 3;
 prec := Round(100 + 4 * Log(1+Max([AbsoluteValue(i) : i in Coefficients(f)])));
 repeat
  mul := mul^2;
  vprintf PlaneQuartic,1: "Starting reduction using precision %o\n",prec; 
  CC := ComplexField(prec);
  hes := Determinant(Matrix([[Derivative(Derivative(f,i),j) : i in [1..3]] : j in [1..3]]));

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1 - 1 >;
  i := GroebnerBasis(id);
  pl := PointsOfIdeal(id,CC);

  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  id := ideal<PolynomialRing(RationalField(),3) | hes, f, Parent(f).1, Parent(f).2, Parent(f).3-1 >;
  pl := pl cat PointsOfIdeal(id,CC);
  pts := [Vector([ChangePrecision(pl[i][j], prec div 2) : j in [1..3]]) : i in [1..#pl]];
  vprintf PlaneQuartic,1:"Computing covariant\n"; 
  _,_,Trr := ReduceCluster(pts : eps := 10^(-prec div  20));
/*  Tr := ChangeRing(Tr, RealField(prec));
  Tr := (Tr + Transpose(Tr))/2;
  Trr, U1 := LLLGram(Tr); */
  subs := [&+[Parent(f).i * Trr[i,j] : i in [1..3]] : j in [1..3]]; 
  res :=  Evaluate(f,subs);
 
  prec := prec * 2;
 until Max([AbsoluteValue(a) : a in Coefficients(res)]) le mul * Max([AbsoluteValue(a) : a in Coefficients(f)]);
  
 if Max([AbsoluteValue(a) : a in Coefficients(res)]) ge Max([AbsoluteValue(a) : a in Coefficients(f)]) then
  vprintf PlaneQuartic,1:"Reduction without effect %o\n",res;
  return f,[Parent(f).i : i in [1..3]];
 end if;

 return Evaluate(f,subs),subs;
end function;

intrinsic MinimizePlaneQuartic(f :: RngMPolElt, p :: RngIntElt) -> RngMPolElt, Mtrx
{Given a plane quartic curve this routine will compute a locally minimized model of the curve.
The new model and the transformation matrix are returned.}

 r := Rank(Parent(f));
 require r eq 3: "Polynomial in 3 variables expected."; 
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f*Denominator(f));
 end if;
 require integral: "Polynomial over the integers or rationals expected."; 
 
 require (Degree(f) eq 4) and IsHomogeneous(f) : "Homogeneous polynomial of degree 4 expected.";
 
 subs := [Parent(f).i : i in [1..3]];
 res := f div GCD(Coefficients(f));
 repeat
  res,subs_n := LocalMinimizationStepPlaneQuartic(res,p);
  subs := [Evaluate(a,subs_n) : a in subs];
 until  subs_n eq [Parent(f).i : i in [1..3]];

/* Simplify transformation by using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(subs[j],Parent(f).i) : j in [1..#subs]] : i in [1..Rank(Parent(f))]]));
 Lat := Transpose(Lat);
 res := f^Lat;
 res := res div GCD(Coefficients(res));

 return res, Lat;
end intrinsic;

intrinsic MinimizeReducePlaneQuartic(f :: RngMPolElt) -> RngMPolElt, Mtrx
{Minimization and reduction of a plane quartic curve with integral coefficients.
 Returns an isomorphic quartic with small coefficients, and the transformation matrix.}

 r := Rank(Parent(f));
 require r eq 3: "Polynomial in 3 variables expected."; 
 type := Type(BaseRing(Parent(f)));
 integral := type eq RngInt;
 if type eq FldRat then
  integral, f := IsCoercible(PolynomialRing(Integers(),r), f*Denominator(f));
 end if;
 require integral: "Polynomial over the integers or rationals expected."; 
 
 require IsSmoothHyperSurface(f) : "Curve is singular.";
 require (Degree(f) eq 4) and IsHomogeneous(f) : "Homogeneous polynomial of degree 4 expected.";
 
 subs := [Parent(f).i : i in [1..3]];
 res := f div GCD(Coefficients(f));
 for p in [2,3,5] do
  vprintf PlaneQuartic,1: "Local minimization for p = %o\n",p;
  repeat
   res,subs_n := LocalMinimizationStepPlaneQuartic(res,p);
   subs := [Evaluate(a,subs_n) : a in subs];
  until  subs_n eq [Parent(f).i : i in [1..3]];
 end for;  
 vprintf PlaneQuartic,1: "Computing bad primes.\n";
 bp := ImproveablePrimes(res);
 for p in bp do
  vprintf PlaneQuartic,1: "Local minimization for p = %o\n",p;
  repeat
   res,subs_n := LocalMinimizationStepPlaneQuartic(res,p);
   subs := [Evaluate(a,subs_n) : a in subs];
  until  subs_n eq [Parent(f).i : i in [1..3]];
 end for;

/* Simplify Transformation obtained by the minimization algorithm using LLL */
 Lat := LLL(Matrix([[MonomialCoefficient(subs[j],Parent(f).i) : j in [1..#subs]] : i in [1..Rank(Parent(f))]]));
 Lat := Transpose(Lat);
 res := f^Lat;
 res := res div GCD(Coefficients(res));

/* Final reduction step */
 res, Trr := ReducePlaneCurve(res);

 return res, Lat*Trr;
end intrinsic;


