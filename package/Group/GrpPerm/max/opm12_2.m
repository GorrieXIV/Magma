freeze;
//functions for finding maximal subgroups of almost simple extensions of
//O^+(12,2) and O^-(12,2).

import "orthreds.m" : IsotropicStabOmega, NonDegenStabOmega, NSPointStabOmega;
import "orthimprims.m" : OrthImprim, OrthStabOfHalfTS;
import "superfield.m" : GammaOsOdd, GammaOdimEven, GammaUMeetOmega;

L33_2 := function()
return
MatrixGroup<12,GF(2)|
Matrix(GF(2),12,12,\[1,0,1,0,0,0,0,0,0,1,1,1,0,1,0,0,0,
0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,1,0,0,
0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,
0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,
0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,0,0,
0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
0,1]),
Matrix(GF(2),12,12,\[0,1,0,0,0,0,0,0,1,0,0,0,1,0,0,1,1,
1,0,0,1,0,1,0,1,1,0,1,1,1,0,0,1,0,1,1,0,1,1,0,0,0,
1,0,1,1,0,1,1,1,0,1,0,0,0,1,1,1,1,0,0,0,0,0,1,0,1,
0,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,1,0,0,1,1,
0,1,1,0,1,1,0,1,1,1,0,0,0,1,1,0,1,1,0,0,0,0,0,0,1,
1,0,0,0,1,1,1,1,1,0,0,0,0,1,1,0,1,1,1,1,1,0,0,0,1,
0,0]),
Matrix(GF(2),12,12,\[1,1,1,1,0,1,1,0,1,1,0,1,1,0,0,1,0,
0,1,0,1,0,0,0,0,0,0,0,1,1,0,1,0,0,0,1,0,1,1,0,1,0,
0,1,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,0,0,0,1,1,1,0,0,
1,0,0,1,1,0,0,1,1,0,0,0,0,0,1,0,1,0,1,0,1,0,0,1,1,
1,1,0,0,1,1,1,0,1,1,1,1,0,0,1,1,0,1,1,1,0,1,1,0,1,
0,0,1,0,1,1,1,1,0,0,1,1,0,0,1,0,0,0,1,0,0,0,0,0,0,
1,1]) /*order=11232=2^5*3^3*13*/>;
end function;

A13 := function()
return
MatrixGroup<12,GF(2)|
Matrix(GF(2),12,12,\[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,
0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,
0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,
0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,
0,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,
0,1]),
Matrix(GF(2),12,12,\[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,
0,0,0,1,1,0,1,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,
0,0,1,0,0,0,0,0,0,0,1,0,1,1,0,0,0,0,0,0,0,0,1,0,0,
1,1,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,1,1,0,1,
1,0,0,0,0,0,1,1,1,1,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,
0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,1,1,1,0,0,0,0,0,1,0,
0,0]) /*order=2^9*3^5*5^2*7*11*13*/>;
end function;

/*************************************************************************/

/***************************************************************************/

function OPlus12_2Identify(group: max:= true, Print:=0)
  A := PSOPlus(12,2);
  S := Socle(A);
  iss, gens := StandardGenerators(S,"O12p2");
  if not iss then error "Standard generator error in O^+(12,2)"; end if;
  ims := [A | gens[1], gens[2]];
  S := sub< A | ims >; //socle of A
  for g in Generators(A) do if not g in S then
    A := sub< A | ims[1], ims[2], g >;
  end if; end for;
  F, phi := FPGroupStrong(S);

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is O^+(12,2):[%o]\n", aut; end if;
  iss, gens := StandardGenerators(soc,"O12p2");
  if not iss then error "Standard generator error in O^+(12,2)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b];
  for g in Generators(group) do
     if not g in sub<group|newgens> then Append(~newgens,g); end if;
  end for;
  group := sub<group|newgens>;
  //we need to find images of generators in standard copy
  homom :=  hom< soc -> A | ims >;
  for i in [3..Ngens(group)] do
    g := group.i;
    conjim := homom(soc.1^g);
    isc, h := IsConjugate(A,A.1,conjim);
    if not isc then error "Conjugation error in Aut(O^+(12,2))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(O^+(12,2))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;

  //Now for the maximals.  We work down the table in the book
  //These are subgroups of OmegaPlus(12,2), so we need a homomorphism
  iss, gens := StandardGenerators(OmegaPlus(12,2),"O12p2");
  om := sub< GL(12,2) | gens >;
  omtoA := hom< om->A | [A.1,A.2] >;
  
  //C1s
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,1,1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,2,1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,3,1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,4,1)));
  if aut eq 2 then
    Append(~maximals, omtoA(IsotropicStabOmega(12,2,5,1)));
  end if;
  if aut eq 1 then
    G := omtoA(IsotropicStabOmega(12,2,6,1));
    maximals cat:= [G,G^A.3];
  end if;

  Append(~maximals, omtoA(NonDegenStabOmega(12,2,1,2,-1)));
  Append(~maximals, omtoA(NonDegenStabOmega(12,2,1,4,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(12,2,1,4,-1)));
  Append(~maximals, omtoA(NSPointStabOmega(12,2,1)));

  //C2s
  Append(~maximals, omtoA(OrthImprim(12,2,1,2,-1)));
  Append(~maximals, omtoA(OrthImprim(12,2,1,6,1)));
  Append(~maximals, omtoA(OrthImprim(12,2,1,6,-1)));
  if aut eq 1 then
    G := omtoA(OrthStabOfHalfTS(12,2));
    maximals cat:= [G,G^A.3];
  end if;

  //C3s
  if aut eq 1 then
    G := omtoA(GammaOdimEven(12,2,1));
    maximals cat:= [G,G^A.3];
  end if;
  Append(~maximals, omtoA(GammaOsOdd(12,2,3,1)));
  if aut eq 1 then
    G := omtoA(GammaUMeetOmega(12,2));
    maximals cat:= [G,G^A.3];
  end if;

  return homom, A, maximals, F, phi;
end function;

function OMinus12_2Identify(group: max:= true, Print:=0)
  A := PSOMinus(12,2);
  S := Socle(A);
  iss, gens := StandardGenerators(S,"O12m2");
  if not iss then error "Standard generator error in O^-(12,2)"; end if;
  ims := [A | gens[1], gens[2]];
  S := sub< A | ims >; //socle of A
  for g in Generators(A) do if not g in S then
    A := sub< A | ims[1], ims[2], g >;
  end if; end for;
  F, phi := FPGroupStrong(S);

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is O^-(12,2):[%o]\n", aut; end if;
  iss, gens := StandardGenerators(soc,"O12m2");
  if not iss then error "Standard generator error in O^-(12,2)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b];
  for g in Generators(group) do
     if not g in sub<group|newgens> then Append(~newgens,g); end if;
  end for;
  group := sub<group|newgens>;
  //we need to find images of generators in standard copy
  homom :=  hom< soc -> A | ims >;
  for i in [3..Ngens(group)] do
    g := group.i;
    conjim := homom(soc.1^g);
    isc, h := IsConjugate(A,A.1,conjim);
    if not isc then error "Conjugation error in Aut(O^-(12,2))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(O^-(12,2))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;

  //Now for the maximals.  We work down the table in the book
  //These are subgroups of OmegaPlus(12,2), so we need a homomorphism
  iss, gens := StandardGenerators(OmegaMinus(12,2),"O12m2");
  om := sub< GL(12,2) | gens >;
  omtoA := hom< om->A | [A.1,A.2] >;
  
  //C1s
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,1,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,2,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,3,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,4,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(12,2,5,-1)));

  Append(~maximals, omtoA(NonDegenStabOmega(12,2,-1,10,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(12,2,-1,4,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(12,2,-1,8,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(12,2,-1,6,1)));
  Append(~maximals, omtoA(NSPointStabOmega(12,2,-1)));

  //C2s
  Append(~maximals, omtoA(OrthImprim(12,2,-1,4,-1)));

  //C3s
  Append(~maximals, omtoA(GammaOdimEven(12,2,-1)));
  Append(~maximals, omtoA(GammaOsOdd(12,2,3,-1)));

  //C9s
  if aut eq 1 then
    G := omtoA(L33_2());
    maximals cat:= [G,G^A.3];
  end if;
  Append(~maximals, omtoA(A13()));

  return homom, A, maximals, F, phi;
end function;
