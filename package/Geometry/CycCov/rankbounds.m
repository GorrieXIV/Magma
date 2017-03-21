freeze;
//
//
// rankbounds.m
// Brendan Creutz
// Feb 2012
//
// 
// Functions for computing lower (via point search)
// and upper (via descent) bounds for the Mordell-Weil
// ranks of Jacobians of cyclic covers of P^1
//
// 
// Currently for q-cyclic covers over the q-th cyclotomic field
// 


//First two functions give the (x-T) map on divisors.
//This is used to check linear independence of points in some cases
muOfTors := function(factor,cofactor,lc,q);
  //determines the image of the divisor sum (x,0) as x runs over roots a factor of f.
  sign,w := Max([(q-1)*Degree(factor),Degree(cofactor)]);
  if w eq 1 then
    return (-1)^sign*(factor-(lc*cofactor)^(q-1));
  else
    return (-1)^sign*(cofactor^(q-1)-lc*factor);
  end if;
end function; //muOfTors

mumap := function(m,f,q);
 lcf := LeadingCoefficient(f);
 fm := 1/lcf*f;
 ff := [g[1] : g in Factorization(fm)];
 A := Domain(m);
 T := A.1;
 mu := function(poly);
  fh := Factorization(poly);
  hs := [h[1] : h in fh ];
  hs := [ LCM([Denominator(c) : c in Coefficients(h)])*h : h in hs ];
  exps := [h[2] : h in fh ];
  toSum := [Codomain(m)|];
  for h in hs do
    if f mod h ne 0 then
      Append(~toSum,m((-1)^Degree(h)*Evaluate(h,T)));
    else
      hwithhtilde := muOfTors(h,lcf*(f div h), lcf,q);
      Append(~toSum,m(Evaluate(hwithhtilde,T)));
    end if;
  end for;
  return &+toSum;
 end function;
 return mu;
end function; //mumap;

DivSearch := function(f,q,d,B,stop);
 // Search for effective divisors of degree d on y^q = f
 // in fields up to stop and points over these up to B
  DB := NumberFieldDatabase(d);
  Divisors := [];
  num := stop;
  ct := 0;

  for k in DB do
    num -:= 1;
    ct +:= 1;
    if num eq 0 then
      break;
    end if;
    fk := Polynomial([ k !c : c in Coefficients(f) ]);
    rp := RationalPoints(fk,q : Bound := B);
    rp := { P : P in rp | not IsCoercible(Rationals(),P[1]) or not IsCoercible(Rationals(),P[2])};
    if #rp gt 0 then
      Divisors cat:= [ CharacteristicPolynomial(P[1]) : P in rp ];
    end if;
  end for;
  return Divisors;
end function;


JacCycCovRankBounds := function(f,q,OnlyUpper); 
// computes bounds for the rank of the Jacobian
// of the cyclic cover y^q=f(x)
// returns: r_lower, r_upper, [generators]

//if Evaluate(f,0) eq 0 then 
//  f := Evaluate(f,Parent(f).1+1);
//  printf "Curve ramifies above 0, model changed to y^%o = %o.\n",q,f;
//end if;



degree := Degree(f);
genus := degree mod q eq 0 select Integers()!((degree - 2)*(q-1)/2) 
else Integers()!((degree-1)*(q-1)/2);

k_0 := BaseRing(Parent(f));
H := CyclotomicPolynomial(q);
fH := { g[1] : g in Factorization(H,k_0) };
if exists{ g : g in fH | Degree(g) eq 1 } then
  k := k_0;
else
  k := ext<k_0 | Random(fH)>;
  assert #Roots(H,k) eq q-1;
end if;

if q eq 2 then
  X := HyperellipticCurve(f);
  J := Jacobian(X);
  SelJ,AtoASqmodk := TwoSelmerGroupNew(J);
  S_dim := Ngens(SelJ);
  r_tors := S_dim - J`TwoSelmerRank;    
  SfakePic1 := J`TwoSelmerSet;
  ASqmodktoA := Inverse(AtoASqmodk);
else
  S_dim,SfakeJ,SfakePic1,r_tors,ASqmodktoA,muJktors,toVec,FB := PicnDescent(f,q : Safety := 0);
  J := 0;
  if Type(SfakePic1[2]) ne SetEnum then
    SfakePic1 := {SfakePic1[2]};
  else
    SfakePic1 := {};
  end if; 
end if;

//First compute the upper bound:
r_upper := S_dim - r_tors;
//rank J(k)/phiJ(k) + rank Sha[phi] = r_upper.
if #SfakePic1 eq 0 then
  // this means Pic1 is empty (and may represent an element of Sha)
  isSha := HasIndexOneEverywhereLocally(f,q);
  if isSha then 
    r_upper -:= 2;
  else
    if q eq 2 and genus mod 2 eq 1 then
      printf "WARNING: upper bound is only an upper bound for the rank of Pic^0(X)/2*Pic^0(X).\n";
    end if;
    if q eq 2 and genus mod 2 eq 0 then 
      if IsOdd(J) then
        r_upper -:= 1;
	vprintf Selmer, 1: "Sha is odd ==> Rank(J(k)) le %o.\n", r_upper;
        //PIC^(g-1) is an element of SHA and #SHA = 2*square
      end if;
    end if;
  end if;
end if;
rankk_upper := (q-1)*r_upper;
rankk0_upper := Integers()! (rankk_upper*Degree(k_0)/Degree(AbsoluteField(k)));
//This is the upper bound for the rank.
if rankk0_upper eq 0 then
  return 0,0,0,J;
end if;

if OnlyUpper then
  return rankk0_upper;
end if;

if q eq 2 and genus eq 2 and BaseField(J) cmpeq Rationals() then
  rpJ := RationalPoints(J : Bound := 1000);
  generators := ReducedBasis(rpJ);
  return #generators,r_upper,generators,J;
else
  //Point search on the Jacobian is not implemented.
  //Points themselves may not be implemented.
  //For the time being all of this is switched off for q ne 2
  //if q ne 2 and Degree(f) mod q ne 0 then 
  //  return 0, rankk0_upper,[],0;
  //end if;
  //For now we use the (x-T) map to test
  //for independence in J(k)/phi(J(k))
  mu := mumap(Inverse(ASqmodktoA),f,q);
  facts := [ g[1] : g in Factorization(f) ];
  Foundim1 := false;
  if Degree(f) mod q ne 0 then
    im1 := Domain(ASqmodktoA)!0;
    Foundim1 := true;
  elif exists(d1){ g : g in facts | Degree(g) mod q ne 0 } then
    dd := Integers()!((GF(q)!Degree(d1))^(-1));
    im1 := dd*mu(d1);
    Foundim1 := true;
  else
    im1 := Domain(ASqmodktoA)!0;
  end if;
  ImageOfTorsion := sub< Domain(ASqmodktoA) |
     [ mu(g) - Degree(g)*im1 : g in facts ]>;
  DimUknownTorsion := r_tors - Ngens(ImageOfTorsion);
   // this is the dimension of the subgroup of
   // the Selmer group which is generated by torsion
   // which we have not explicitly found.
  A := Parent(f);
  T := A.1;
  Divs := {* A| *};
  rpX := RationalPoints(f,q : Bound := 1000);
  //printf "ratpoints = %o.\n",rpX;
  if Degree(f) mod q eq 0 then
    Divs := Divs join {* T - P[1]/P[3] : P in rpX | P[3] ne 0 *};
  else
    Divs := Divs join {* T - P[1]/P[3] : P in rpX | P[3] ne 0 *};  
  end if;
  //printf "Divs = %o.\n",Divs;
  if #rpX gt 0 then
    if not Foundim1 then
      Foundim1 := true;
      if exists(P_inf){ P : P in rpX | P[3] cmpeq 0} then
        //use this as the base point.
      else
        im1 := mu(Random(Divs));
      end if;
    end if;
    ImageOfDivs := sub< Domain(ASqmodktoA) |
      [ mu(g) - im1 : g in Divs ]>;
    // Now check if this matched the upper bound...
    r_L := Ngens(ImageOfDivs) 
         - Ngens(ImageOfDivs meet ImageOfTorsion)
         - DimUknownTorsion;
    if r_L eq rankk0_upper then 
      return r_L, rankk0_upper, Divs, J;
    end if;
  else
    ImageOfDivs := sub< Domain(ASqmodktoA) | Domain(ASqmodktoA) ! 0>;
  end if;
  degs := Degree(f) mod q eq 0 select genus + 1 else genus;
  for deg in [2..degs] do
    //printf "Searching for divisors of degree %o. Time:",deg;
    Ddeg := DivSearch(f,q,deg,Ceiling(40/deg),Ceiling(100/deg));
    Ddeg := {* P : P in Ddeg | IsIrreducible(P) *}; 
    Divs := Divs join Ddeg;
    if deg mod q ne 0 then
      if not Foundim1 and exists(d1){P : P in Ddeg} then
        dd := Integers()!((GF(q)!Degree(d1))^(-1));
        im1 := dd*mu(d1);
      end if;
    end if;
    ImageOfDivs := sub< Domain(ASqmodktoA) |
        [mu(g) - deg*im1 : g in Ddeg] cat 
        [ g : g in Generators(ImageOfDivs) ]>;
    // Check again
    r_L := Ngens(ImageOfDivs)
         - Ngens(ImageOfDivs meet ImageOfTorsion)
         - DimUknownTorsion;
    if r_L eq rankk0_upper then 
      return r_L, rankk0_upper, Divs,J;
    end if;
  end for; 
  
  return Max([0,r_L]), rankk0_upper,Divs,J;
end if;

end function; //JacCycCovRankBounds 

intrinsic RankBounds(f :: RngUPolElt, q :: RngIntElt : ReturnGenerators := false) -> RngIntElt, RngIntElt
{Lower and upper bounds for the Mordell-Weil rank of the Jacobian 
of the cyclic cover defined by y^q = f}
r_L, r_U, Divs := JacCycCovRankBounds(f,q,false);
if ReturnGenerators then
  return r_L, r_U, [* D : D in Divs *];
else
  return r_L, r_U;
end if;
end intrinsic;

intrinsic RankBound(f :: RngUPolElt, q :: RngIntElt) -> RngIntElt
{An upper bound on the Mordell-Weil rank of the Jacobian 
of the curve defined by y^q = f over a number field)}
R := JacCycCovRankBounds(f,q,true);
return R;
end intrinsic;




