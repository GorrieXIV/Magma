freeze;

import "GalInvar.m" : check, SLPRGg, SqrtDiscInvChar2Old;
import "Galois.m" : get_tschirni_R;

function MyApply(p, f)
 return Evaluate(f,[Parent(f).(i^p) : i in [1..Rank(Parent(f))]]);
end function;

intrinsic CombineInvariants(IR::Rng, G::GrpPerm, H1::Tup, H2::Tup, H3::GrpPerm) -> RngSLPolElt
  {Combines invariants for two subgoups H1 and H2 of G to obtain an invariant for a third subgroup over the coefficient ring IR.}
  //H1 := <GrpPerm, RngSLPolElt, RngUPolElt>, same for H2
  // I hope the subgroups need not be maximal, but I don't know...

  i1 := H1[2];
  if #H1 eq 2 then
    t1 := Polynomial([0,1]);
  else
    t1 := H1[3];
  end if;
  H1 := H1[1];

  i2 := H2[2];
  if #H2 eq 1 then
    t2 := Polynomial([0,1]);
  else
    t2 := H2[3];
  end if;
  H2 := H2[1];

  m1, I1 := CosetAction(G, H1);
  m2, I2 := CosetAction(G, H2);
  H12 := H1 meet H2;
  require Core(G, H12) subset H3:
    "3rd subgroup is not in the span of the first two, combination not possible";
  m3, I3 := CosetAction(G, H12);

// Coercion 
  if BaseRing(Parent(i1)) cmpne BaseRing(Parent(i2)) then
   if BaseRing(Parent(i1)) cmpeq Integers() then 
    typ := i1`GalInvType; 
    i1 := Evaluate(i1,[Parent(i2).k : k in [1..Rank(Parent(i2))]]); 
    i1`GalInvType := typ;
   end if;
   if BaseRing(Parent(i2)) cmpeq Integers() then 
    typ := i2`GalInvType;
    i2 := Evaluate(i2,[Parent(i1).k : k in [1..Rank(Parent(i1))]]); 
    i2`GalInvType := typ;
   end if;
  end if;


  if Index(G, H1) eq 2 and Index(G, H2) eq 2 and Index(G, H3) eq 2 then
    // TODO: the same approach can work in index p if the p-th roots of unity
    // are present (the transforming part is more complicated!)
    // and a similar, weaker approach will even work without them
    repeat
      p1 := Random(G);
    until not p1 in H1;
    repeat
      p2 := Random(G);
    until not p2 in H2;

    if Characteristic(IR) eq 2 then
	if i1`GalInvType eq "SqrtDisc" then
	    i1 := SqrtDiscInvChar2Old(Rank(Parent(i1)));
	end if;
	if i2`GalInvType eq "SqrtDisc" then
	    i2 := SqrtDiscInvChar2Old(Rank(Parent(i2)));
	end if;
 	if MyApply(p1, i1) eq i1 + 1 and MyApply(p2, i2) eq i2 + 1 then
if not IsExport() then
"\n\nDoes this ever happen? Nicole would like to know";
i1`GalInvType;
i2`GalInvType, "\n\n\n";
end if;
	    i := i1 + i2;
	else 
            i := i2*MyApply(p1, i1) + i1*MyApply(p2, i2);
 	end if;
    else 
	s1 := IsInvariant(SLPRGg(IR, i1), p1:Sign := true);
	if not s1 then i1 -:= MyApply(p1, i1); end if;
	assert IsInvariant(SLPRGg(IR, i1), p1:Sign);
	s2 := IsInvariant(SLPRGg(IR, i2), p2:Sign := true);
	if not s2 then i2 -:= MyApply(p2, i2); end if;
	assert IsInvariant(SLPRGg(IR, i2), p2:Sign);
/*
"CombineInvariants incompatibility:";
Parent(i1);
Parent(i2);
if assigned i1`GalInvType then
i1`GalInvType;
else
i1;
end if;
if assigned i2`GalInvType then
i2`GalInvType;
else
i2;
end if;
*/
	i := i1*i2;
    end if;
    i`GalInvType := "F1F2Inv";
    assert forall{x : x in Generators(H3) | IsInvariant(SLPRGg(IR, i), x)};
    assert exists{x : x in Generators(G) | not IsInvariant(SLPRGg(IR, i), x)};
    return i;
  end if;

  D, inc, proj := DirectProduct(I1, I2);
  h1 := hom<I3 -> I1 | [ I3.i@@m3@m1 : i in [1..Ngens(I3)]]>;
  h2 := hom<I3 -> I2 | [ I3.i@@m3@m2 : i in [1..Ngens(I3)]]>;
  h := hom<I3 -> D | 
       [ (I3.i@h1@inc[1])*(I3.i@h2@inc[2]) : i in [1..Ngens(I3)]]>;
 
  DD := Image(h);     

  h1 := sub<DD|Generators(H1)@m3@h>;
  h2 := sub<DD|Generators(H2)@m3@h>;
  h3 := sub<DD|Generators(H3)@m3@h>;

  res := [];

  assert DD ne h3;
  assert h3 subset DD;
  assert IsMaximal(DD, h3);

  iu := GaloisGroupInvariant(IR, DD, h3);
  // "inner Invar:", iu;
  U := sub<G|Kernel(m3), Generators(h3)@@h@@m3>;
  Zx := PolynomialRing(Integers());
  Zx := Parent(t1);
  t := Zx.1;

  if Characteristic(Zx) eq 0 then
    K := GF(NextPrime(2^23));
  else
    K := CoefficientRing(CoefficientRing(Zx));
    K := quo<PolynomialRing(K) | RandomIrreduciblePolynomial(K, Ceiling(Log(Characteristic(K), 2^23)))>;
  end if;

  all_t := {t};
    assert IsIdentical(Parent(i1), Parent(i2));
    par_i := SLPolynomialRing(CoefficientRing(t1), Rank(Parent(i1)) : Global);
  repeat
    R := [Random(K) : x in [1..Degree(G)]];
//    "current Tschirn: ", t;
    l1 := [Evaluate(i1, [Evaluate(t1, par_i.(i^s)) : i in [1..Rank(Parent(i1))]]) : s in Transversal(G, H1)];
    l2 := [Evaluate(i2, [Evaluate(t2, par_i.(i^s)) : i in [1..Rank(Parent(i2))]]) : s in Transversal(G, H2)];
    g := Evaluate(iu, [Evaluate(t, x) : x in l1 cat l2]);
    if not assigned g`GalInvType then
      g`GalInvType := "Other";
    end if;

//    t := Polynomial(CoefficientRing(t), [Random(3) : x in [1..Minimum(#all_t, Degree(G))]] cat [1]);
    t := get_tschirni_R(IR, 3, Minimum(#all_t, Degree(G)), all_t, iu`GalInvType);
    Include(~all_t, t);
    if not IsExport() then 
	if #all_t gt 500 then
	    #all_t;
	    all_t;
	  error "too many Tschirni's in CombineInvariants";
	end if;
    end if;
//THIS COERCION DOESN'T ALWAYS WORK
//K;
//CoefficientRing(Parent(g));
//SLPolynomialRing(K, Rank(Parent(g)) : Global)!
//g;
    e := {Evaluate(Evaluate(g, [SS.i : i in [1 .. Rank(Parent(g))]], Coercion(BaseRing(Parent(g)), SS)), PermuteSequence(R, s)) : s in Transversal(G, U)} where SS := SLPolynomialRing(K, Rank(Parent(g)) : Global);
    //e := {Evaluate(SLPolynomialRing(K, Rank(Parent(g)) : Global)!g, PermuteSequence(R, s)) : s in Transversal(G, U)};
    ind := #G/#U;
//ind, e;
  until #e eq ind;
  return g;
end intrinsic;

