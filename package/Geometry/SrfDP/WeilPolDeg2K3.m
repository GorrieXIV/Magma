freeze;

/***********************************************************************************************

  WeilPolDeg2K3.m

  Computes WeilPolynomial of models of degree 2 K3 surfaces.

  Code is base on p-adic methods of K. Kedlaya and D. Harvey.

  intrinsics in this file:
  
  WeilPolynomialOfDegree2K3Surface(f6: KnownFactor := false) 

  NonOrdinaryPrimes(f6 :: RngMPolElt, lim :: RngIntElt)
  

  Stephan Elsenhans, 2015
 ***********************************************************************************************/ 

declare verbose Degree2K3, 2;

/* r a : multi-variable polynomial ring. 
   p   : prime. 
   deg : degree of the form 

  This function lists the Monomials for Basis of the domain of the matrix in the Hasse-Witt matrix.  */

function ListExponentsForBasis(r,p,deg)
 assert deg mod (p-1) eq 0;
 lim := deg div (p-1);

 rk := Rank(r);
 
 res0 := [ [i ] : i in [0.. lim] ]; 
 for i := 2 to rk - 1 do
  res0 := [ Append(a,b) : b in [0..lim - &+a], a in res0];
 end for;
 res := [Append(a, lim - &+ a) : a in res0 ];

 e1 := [a : a in res | not 0 in a];
 e2 := [a : a in res | 0 in a];
  
 return [e1] cat [ [a : a in e2 | #[t : t in a | t eq 0] eq i] : i in [1..rk-1]];
end function;

/* r  : number of points mod m
        for a surface over F_p^e
   bb : second Betti-number of the surface. 
        We assume h^1 and h^3 to be zero!
   
   The function returns all the possible number of points that are compatible with the input data and the 
   Deligne-Weil bound. */
function InWeilBound(r,m,p,e,bb)
 mitte := 1 + p^e + p^(2*e);
 lo := mitte - bb * p^e;
 hi := mitte + bb * p^e;
 start := lo - (lo mod m) + (r mod m);
 akt := start;
 res := [];
 while akt le hi do
  if akt ge lo then Append(~res,akt); end if;
  akt := akt + m;
 end while;
 return res;
end function;

// p-adic extrapolation of the number of points. See D. Harvey's paper.
// Note that the denominator of m_inv will always be a power of 2.
function Extrapolation(sum_l, p, d, bb, shift)
 mat := Matrix(Rationals(),[[ Binomial(2*n-1 + 2 * shift,k) : k in [0..#sum_l-1]] : n in [1..#sum_l]]);
 m_inv := mat^-1;
 res := &+[m_inv[1,i] * Integers()!sum_l[i] : i in [1..#sum_l]]; 
 res := Integers()!(Integers(p^#sum_l)!(res + p^(2*d) + p^d + 1)); 
 res := InWeilBound(res,p^#sum_l,p,d, bb);
 return res;
end function;


function ApproximateNumberOfPoints(f6,  p, prec, f_deg, bb)
 shift := 0;
 while  (2  * shift + 1)*(p - 1) div 2 lt prec do
  shift := shift + 1;
 end while;
 if shift gt 0 then
  vprint Degree2K3, 1: "Using shift = ",shift;
 end if;

 mat_ring := Integers(p^prec); 
 vprintf Degree2K3, 2: "Domain of coefficients: %o\n",mat_ring;

 r_uni := PolynomialRing(mat_ring);
 r_top := PolynomialRing(r_uni);
 spez := Evaluate(f6,[1,r_uni.1,r_top.1]);
 t0 := Cputime();
 p1 := spez^((p-1) div 2);
 p2 := p1^2;
 p4 := p2^2;
 tr_ll := [];
 if shift gt 0 then
  pow_alt := p1 * p2^(shift - 1);
  pow_akt := pow_alt * p2;
 else
  pow_akt := p1;
  pow_alt := p1;
 end if;
 pow_time := Cputime() - t0;
 mat_time := 0;
 build_mat_time := 0;
 for j := 1 + shift to prec + shift do 
  vprintf Degree2K3, 1: "Computing approximation %o\n", j-shift;
  t0 := Cputime();
  if j gt 1 + shift then 
   pow_alt0 := pow_akt; 
   if j gt 4 then pow_akt := pow_alt * p4; else pow_akt := pow_akt * p2; end if; 
   pow_alt := pow_alt0;
  end if;
  pow_time := pow_time + Cputime() - t0;

  cc := [Coefficients(a) : a in Coefficients(pow_akt)];
//  Degree(pow_akt), Degree(f6)*(2*j-1) * ((p-1) div 2);
  bas_des0 := ListExponentsForBasis(Parent(f6),p,Degree(f6)*((2*j-1) * ((p-1) div 2)));
  tr_l := [ mat_ring!0 : i in [1..f_deg]];
  for kk := 1 to #bas_des0 do
   vprintf Degree2K3, 2: "Size of matrix %o x %o. ",#bas_des0[kk], #bas_des0[kk];
   t0 := Cputime();   
   mat := Matrix([[(Min(ee) lt 0) or (ee[1]+1 gt #cc) or (ee[2] + 1 gt #cc[ee[1]+1]) 
                      select 0 else cc[ee[1]+1][ee[2]+1] 
                      where ee is [p * b[k] - a[k] : k in [1..3]]
                  : a in bas_des0[kk]] : b in bas_des0[kk]]);
   build_mat_time := build_mat_time + Cputime() - t0;
   vprintf Degree2K3, 2: "Number of zeros: %o\n", #[1 : i,j in [1..#bas_des0[kk]] | mat[i,j] eq 0];
   t0 := Cputime();
   mpl := [mat,mat^2];
   Append(~mpl,mpl[2]^2);
   ex_lmm := [1,2,4];
   if f_deg gt 6 then
    if f_deg le 10 then
     ex_lmm := [1,2,4,5];
     Append(~mpl, mpl[3] * mat);
    else
     assert f_deg le 14;
     ex_lmm := [1, 2, 4, 6, 7];
     Append(~mpl, mpl[3] * mpl[2]);
     Append(~mpl, mpl[4] * mat);
    end if;
   end if;
   for i := 1 to f_deg do
    e1 := Index(ex_lmm,i);
    if e1 gt 0 then
     mtr := Trace(mpl[e1]);
    else
     ind := [[k1,k2] : k1,k2 in [1..#ex_lmm] | ex_lmm[k1] + ex_lmm[k2] eq i][1];
     mtr := TraceOfProduct(mpl[ind[1]], mpl[ind[2]]); 
    end if;

/* The algorithm counts points on affine charts separately. 
   As the lower dimensional charts result in blocks of the matrix of the top dimensional chart, 
   the following is correct: */
    tr_l[i] := tr_l[i] + [(p^i-1)^2, (p^i-1)^2 + (p^i-1),(p^i-1)^2 + 2*(p^i-1) + 1][kk] * mtr;
   end for;
   mat_time := mat_time + Cputime() - t0; 

  end for;
  vprint Degree2K3, 2: "Traces mod p: ",[Integers()!a mod p : a in tr_l];
  Append(~tr_ll,tr_l); 
 end for;
// tr_ll contains the p-adic approximations of the traces of Frobenius
 
 delete mat; delete mpl; delete p1; delete p2; delete p4; delete pow_akt; delete pow_alt; delete pow_alt0; 

 vprint Degree2K3, 1: "Calling extrapolation"; 
 vprint Degree2K3, 1: pow_time,"sec for polynomial arithmitic";
 vprint Degree2K3, 1: mat_time,"sec for matrix arithmetic"; 
 vprint Degree2K3, 1: build_mat_time,"sec for matrix building"; 
 
 return  [Extrapolation([a[d] : a in tr_ll], p, d, bb, shift)  : d in [1..f_deg]];
end function;


// Count points of w^2 = f_6 for all primes in [p_min, p_max] over the finite fields
// F_p^d for d = 1..f_deg
function CountPoints(f6,p_min, p_max,f_deg, bb)
 assert p_min gt 2;
 assert Rank(Parent(f6)) eq 3;
 assert f_deg + 1 le p_min div 2;

 pzl := [];
 res := [];
 p := NextPrime(p_min-1);
 rr := Parent(f6);
 
 repeat
  vprint Degree2K3, 1: "Doing p = ",p;
  Append(~pzl,p);
  
  Append(~res, ApproximateNumberOfPoints(f6, p , f_deg + 1, f_deg, bb));  

  p := NextPrime(p);
 until p gt p_max;

 return res, pzl;
end function;

// Given w^2 = f6. We compute a factor of the WeilPolynomial that excludes all the contributions of the singularities.  
// In case a factor of the WeilPolynomial is known, it can be added to the computations
function WeilPolynomialOfModel(f6,p, deg: KnownFactor := false)
 assert IsHomogeneous(f6);
 assert Degree(f6) eq 6;
 assert p gt 2;
 assert IsPrime(p);
 assert deg le 22;

 qq := PolynomialRing(Rationals());
 if KnownFactor cmpeq false then KnownFactor := qq.1 - p; end if;
 
 f_deg := (deg - Degree(KnownFactor)) div 2 + 1;
 prec := f_deg; 
 if p lt 11 then prec := prec + 1; end if;
 vprint Degree2K3, 1: "starting with p-adic precision",prec;
 repeat
  
  anzl := ApproximateNumberOfPoints(f6,  p, prec, f_deg, deg - 1); // A list of possible number of points
  assert &and [#a gt 0 : a in anzl];
  
  wpl := [];
  tmp := CartesianProduct([Set(a) : a in anzl]); 
  vprint Degree2K3, 1: #tmp," possibilities for traces by congruence conditions and Weil bound.";
  for cc in tmp do   
   trll := [ cc[i] - 1 - p^(2*i) : i in [1..#anzl]];
   wpl := wpl cat FrobeniusTracesToWeilPolynomials(trll, p, 2, deg : KnownFactor := KnownFactor);
  end for;
  assert #wpl gt 0; 
  vprintf Degree2K3, 1: "Result in %o Weil polynomials by absolute value of roots test.\n",#wpl;
 
  f_deg := f_deg + 1;
  prec := prec + 1;
  if #wpl ne 1 then
   vprintf Degree2K3, 1: "Increasing precision to %o\n",prec;
  end if;
 until #wpl eq 1;
 return wpl[1];
end function;

/*********************************************************************************************

  p-adic point counting is done. 

 *********************************************************************************************

  Now we analyze the singuliarities for their contribution to the weil polynomials.

 *********************************************************************************************/

// Given a list of points. Write it as a list of orbits by the action of Frobenius.
function FrobeniusOrbits(pl, p)
 
 assert &and [1 in a : a in pl]; // points have to be normalized for this orbit algorithm
 
 ind := [];
 res := [];
 for i := 1 to #pl do
  if not i in ind then
   akt := [];
   tt := pl[i];
   repeat
    Append(~akt,tt); 
    Append(~ind, Index(pl,tt));
    tt := [ a^p : a in tt];
   until tt eq pl[i];
   Append(~res,akt);
  end if;
 end for;
 return res;
end function;

// Affine chart of w^2 = f6 with center pt.
function AffineChart(f6,pt)
 assert Evaluate(f6,ElementToSequence(pt)) eq 0;
 
 ff := Parent(pt[1]);
 a3 := PolynomialRing(ff,3);
 subs := [a3!pt[1], pt[2],pt[3]];
 ind := 1;
 while subs[ind] eq 0 do ind := ind + 1; end while;  
 cnt := 1;
 for i := 1 to 3 do
  if i ne ind then
   subs[i] := subs[i] + a3.cnt;
   cnt := cnt + 1;
  end if;
 end for;
 assert cnt eq 3;
  
 return Evaluate(f6,subs) - a3.3^2;
end function;

/* Computes the rank of the sublattice in pic generated by the exceptional divisors of all the singularities. 
   Returns false in case the reduction of w^2 = f6 mod p has singularities that are not of type A,D or E. 
   Otherwiese: Returns true and the rank */
function SingularRank(f6,p)

 vprint Degree2K3, 1: "Checking for singularities.";
  
 S := Scheme(ProjectiveSpace(GF(p),2) ,f6);
 sing := SingularPointsOverSplittingField(S);
 vprintf Degree2K3, 1: "%o singular points found.\n", #sing;

 orbs := FrobeniusOrbits([ElementToSequence(a) : a in sing],p); 

 zz := PolynomialRing(Integers());
 sing_fac := zz!1;
 res := 0;
 for orb in orbs do 

  aff := AffineChart(f6, orb[1]);
  e1,e2,e3 := IsSimpleSurfaceSingularity(Surface(AffineSpace(BaseRing(Parent(aff)),3),aff)![0,0,0]);
  if not e1 then
   vprintf Degree2K3, 1: "Singularity obove %o is not ADE.\n",orb[1];
   return false, _, _;
  end if;
  vprintf Degree2K3, 2: "Treating singularity of type %o_%o above %o.",e2,e3, orb[1];
  if #orb gt 1 then 
   vprintf Degree2K3, 2: "Frobenius orbit has length %o.\n",#orb;
  else
   vprintf Degree2K3, 2: "\n";
  end if;
  
  res := res + e3 * #orb;
  if e2 eq "A" then
   l := #orb;
   if e3 eq 1 then 
    sing_fac := sing_fac * (zz.1^l - p^l);
   else
    hc := HomogeneousComponents(aff);
    assert hc[1] eq 0 and hc[2] eq 0;
    fac := Factorization(PolynomialRing(GF(p,l),3)!hc[3]);
    assert fac[1][2] eq 1;  // Contradiction to result from singularity analysis.
    if #fac eq 2 then
     sing_fac := sing_fac * (zz.1^l-p^l)^e3;     
    else
     sing_fac := sing_fac * (zz.1^l + p^l)^(e3 div 2) * (zz.1^l-p^l)^(e3 - e3 div 2);
    end if;
   end if;
  else // D or E singularity
   vprintf Degree2K3, 1: "Singularity is too complex. Can not compute Frobenius action on exceptional divisors.\n";
   vprintf Degree2K3, 2: "Orbit of length %o of singularities of type %o_%o.\n",#orb,e2,e3;
   sing_fac := zz!0;
  end if;
 end for;    
 if sing_fac eq 0 then
  return true, res, sing_fac;
 end if;
 return true, res, sing_fac;
end function;

intrinsic NumbersOfPointsOnDegree2K3Surface(f6 :: RngMPolElt,p :: RngIntElt,d :: RngIntElt) -> SeqEnum
{Counts the number of points on the K3 surface w^2 = f6(x,y,z) over F_p,..,F_p^d.  
Here, f6 is a sextic form that can be coerced to F_p[X,Y,Z].}

 r := Parent(f6);

 suc, f6 := IsCoercible(PolynomialRing(GF(p),3),f6);
 require suc : "f6 does not define a form over F_p"; 
 
 require IsPrime(p) : "p must be a prime.";     
 require Rank(r) eq 3 : "Branch locus must be in P^2.";    
 require Degree(f6) eq 6 : "Branch locus must be of degree 6.";
 require IsHomogeneous(f6) : "Branch locus must be in P^2."; 
 require p gt 2 : "Characteristic 2 case is not covered.";
 require IsSquarefree(f6) : "Branch locus must be reduced.";

 IsK3, SRank,SFac := SingularRank(f6,p);

 if not IsK3 then
  require false : "Surface is too singular to be treated.";
 end if;

 prec := d;
 repeat
  prec := prec + 1;
  anzl := ApproximateNumberOfPoints(PolynomialRing(Integers(),3)!f6,  p, prec, d, 21);
  assert &and [#a gt 0 : a in anzl];
 until &and [#a eq 1 : a in anzl];
 return &cat anzl;
end intrinsic;
 
intrinsic WeilPolynomialOfDegree2K3Surface(f6 :: RngMPolElt: KnownFactor := false) -> RngUPolElt, RngUPolElt
{The Weil polynomial of the K3 surface w^2 = f6(x,y,z). Here, f6 is a sextic form in F_p[X,Y,Z].  
 The Weil polynomial is returned as two factors. The first factor is obtained for a naive point 
 count on the potentially singular model. The second factor corresponds to the Frobenius action 
 on the space spanned by exceptional divisors obtained by desingularization.  

 In case the singularities are not of ADE type both return values will be zero. In case the Galois
 action on the singularities is to complex for the current implementation the second return value is zero.}

 r := Parent(f6);
 fp := BaseRing(r);
 e1,p := IsFinite(fp);
 require e1 : "Surface must be over a finite field.";           
 require IsPrime(p) : "Surface must be over prime field.";     
 require Rank(r) eq 3 : "Branch locus must be in P^2.";    
 require Degree(f6) eq 6 : "Branch locus must be of degree 6.";
 require IsHomogeneous(f6) : "Branch locus must be in P^2."; 
 require p gt 2 : "Characteristic 2 case is not covered.";
 require IsSquarefree(f6) : "Branch locus must be reduced.";

 IsK3, SRank,SFac := SingularRank(f6,p);

 if not IsK3 then
  return 0,0;
 end if;

 Fac := WeilPolynomialOfModel(PolynomialRing(Integers(),3)!f6,p, 22 - SRank: KnownFactor := KnownFactor);

 return Parent(SFac)!Fac,SFac;
end intrinsic;

intrinsic WeilPolynomialOfDegree2K3Surface(f6 :: RngMPolElt, p :: RngIntElt: KnownFactor := false) -> RngUPolElt, RngUPolElt
{The Weil polynomial of the K3 surface w^2 = f6(x,y,z) mod p as two factors. Here, f6 is a sextic form in Q[X,Y,Z]. }

 return  WeilPolynomialOfDegree2K3Surface(PolynomialRing(GF(p),3)!f6: KnownFactor := KnownFactor);
end intrinsic;

intrinsic NonOrdinaryPrimes(f6 :: RngMPolElt, lim :: RngIntElt) -> SeqEnum
{The odd non-ordinary primes of the K3 surface w^2 = f6 up to lim.}

 r := Parent(f6);
 qq := BaseRing(r);
 require Rank(r) eq 3 : "Branch locus must be in P^2.";    
 require Degree(f6) eq 6 : "Branch locus must be of degree 6.";
 require IsHomogeneous(f6) : "Branch locus must be in P^2."; 
 require IsSquarefree(f6) : "Branch locus must be reduced.";
 require qq cmpeq Rationals() or qq cmpeq Integers() : "Surface must be defined over Q.";

 f6 := PolynomialRing(Integers(),3)!(f6 * LCM([Denominator(a) : a in Coefficients(f6)]));
 r := Parent(f6);
 if lim lt 3 then
  return [];
 end if;

 res := [];
 if MonomialCoefficient(f6,(r.1 * r.2 * r.3)^2) mod 3 eq 0 then
  Append(~res,3);
 end if; 

 if lim lt 5 then
  return res;
 end if;

 offsets_2 := [[i,j,-i-j] : i,j in [-7..4] | i+j gt -3];
 offsets_3 := [[i,j,-i-j] : i,j in [-9..6] | not [i,j,-i-j] in offsets_2 and (i+j)  gt -5  ];

 vprintf Degree2K3, 1: "Working with #offsets_2 = %o, #offsets_3 = %o\n",#offsets_2,#offsets_3;

 i_center := Index(offsets_2,[0,0,0]); 

// Use (d/dx_i) (f^{n+1}) = (n+1) f^n (d/dx_i) f  to create relations of coefficients
/* Index ordering
   1st: offsets_2 of f^{n+1}
   2nd: offsets_3 \ offsets_2 of f^n
   3rd: offsets_2 of f^n                           

   We have to treat n as a variable! 
   As everything is linear in n we have a constant and a linear term. Each is represented by one matrix.       */

 r_seq := [];
 qq := PolynomialRing(Rationals());
 n := qq.1;
 for i := 1 to 3 do
  col := Coefficients(Derivative(f6,i));
  exl := [Exponents(a) : a in Monomials(Derivative(f6,i))];
  for j := 1 to #offsets_2 do
   act := [qq!0 : i in [1..2*#offsets_2 + #offsets_3]];
   ex := [2*(n+1) + offsets_2[j][1], 2*(n+1) + offsets_2[j][2], 2*(n+1) + offsets_2[j][3]];
   mul := ex[i];
   ex[i] := ex[i] - 1;
   act[j] := - mul;
   for k := 1 to #exl do
    exm := [ex[1] - exl[k][1] - 2* n, ex[2] - exl[k][2] - 2*n, ex[3] - exl[k][3] - 2*n];
    ii := Index(offsets_2, exm); 
    if ii eq 0 then 
     ii := Index(offsets_3, exm); 
     if ii eq 0 then continue j; end if; // Coefficient out of range. Can't use this relation.
     act[ii + #offsets_2] := (n+1) * col[k];
    else
     act[ii + #offsets_2 + #offsets_3] := (n+1) * col[k];
    end if;
   end for; 
   Append(~r_seq,act);
  end for;
 end for; 

 mat0 := Matrix([[Coefficient(a,0) : a in b ] : b in r_seq]);
 mat1 := Matrix([[Coefficient(a,1) : a in b ] : b in r_seq]); 

// Coefficients of f6^2 
 f12 := f6^2;
 co_n := Vector(Rationals(),[Min(a) lt -4 select 0 else MonomialCoefficient(f12,Monomial(r,[4+k : k in a])) 
           : a in offsets_2]);
 
 
 ex := 2;
 vprintf Degree2K3, 1: "Initialization for non-ordinary primes done.\n";

 repeat
   vprintf Degree2K3, 2: ".";
  if IsPrime(2*ex+1) then
   if Integers()!co_n[i_center] mod (2*ex+1) eq 0 then
    Append(~res,2*ex+1);
   end if;
  end if;
  m2 := EchelonForm(mat0 + ex * mat1);
  r2 := Transpose(Submatrix(m2,
                  1,1+ #offsets_2 + #offsets_3, #offsets_2, #offsets_2));
  assert &and [m2[i,i] eq 1 : i in [1..#offsets_2]];
  assert &and [m2[i,j] eq 0 : i in [1..#offsets_2], j in [1..#offsets_2 + #offsets_3] | i ne j]; 

  co_n := co_n * r2;
  ex := ex + 1;
  if ex mod 50 eq 0 then
   vprintf Degree2K3, 1: "%o no-primes up to %o so far.\n",#res,2*ex;
  end if;
 until 2*ex + 1 gt lim;

 return res;
end intrinsic;


