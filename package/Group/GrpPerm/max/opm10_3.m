freeze;
//functions for finding maximal subgroups of almost simple extensions of
//O^+(10,3) and O^-(10,3).

import "orthreds.m" : IsotropicStabOmega, NonDegenStabOmega, NSPointStabOmega;
import "orthimprims.m" : OrthImprim, OrthStabOfHalfTS, OrthStabOfHalfND;
import "superfield.m" :GammaOsOdd, GammaOdimOdd, GammaOdimEven, GammaUMeetOmega;

O10p3 := function()
//has standard generators
return
MatrixGroup<10,GF(3)|
Matrix(GF(3),10,10,\[2,2,0,1,2,2,2,2,2,1,2,2,0,2,0,2,2,
1,2,2,2,1,1,2,1,1,1,1,1,2,2,1,0,0,0,2,2,1,2,2,2,1,
0,2,1,2,2,1,2,2,2,1,0,2,2,1,0,1,0,2,1,2,0,1,2,2,0,
2,2,1,0,0,0,0,0,0,0,1,0,0,2,1,0,2,1,1,1,1,2,2,1,2,
0,1,2,2,2,2,2,2]),
Matrix(GF(3),10,10,\[0,0,1,1,1,2,2,2,0,1,2,2,1,2,2,0,1,
2,0,1,2,0,1,1,1,1,1,2,1,1,2,2,0,1,1,0,0,0,0,0,0,1,
1,0,0,1,0,0,0,1,2,0,1,0,0,0,2,0,2,0,1,1,2,0,2,2,1,
0,0,2,1,0,0,1,1,1,2,1,0,0,1,2,0,1,2,2,1,2,1,2,1,2,
2,0,2,1,0,0,0,1]),
Matrix(SparseMatrix(GF(3),10,10,\[
1,10,2, 1,2,1, 1,3,1, 1,4,1, 1,5,1, 1,6,1, 1,7,1, 1,8,1, 1,9,1, 1,1,2])),
DiagonalMatrix(GF(3),[2,2,2,2,2,1,1,1,1,1])
/*order=2^18*3^20*5^2*7*11^2*13*41*/>;
end function;

O10m3 := function()
//has standard generators
return
MatrixGroup<10,GF(3)|
Matrix(GF(3),10,10,\[0,0,1,0,0,2,1,1,1,1,1,0,1,1,0,2,1,
2,2,1,1,2,2,1,0,2,1,2,2,1,2,0,1,1,0,2,1,1,1,1,0,0,
0,0,1,0,0,0,0,0,1,0,2,0,0,2,2,2,2,2,2,2,0,1,0,0,1,
1,1,0,2,0,1,0,0,2,1,2,1,1,1,1,0,2,0,0,0,2,0,0,2,1,
2,2,0,1,2,1,1,0]),
Matrix(GF(3),10,10,\[2,2,2,2,0,1,1,1,0,0,0,2,0,2,2,0,1,
2,1,1,0,2,1,0,2,0,0,0,2,2,1,0,1,2,2,0,2,1,1,2,2,0,
1,1,1,0,1,0,0,1,1,2,1,2,0,2,1,0,0,1,1,0,0,1,2,2,1,
2,2,1,2,1,0,0,2,1,0,1,1,2,2,2,0,0,2,2,2,2,2,2,2,2,
1,0,2,0,1,0,0,2]),
Matrix(SparseMatrix(GF(3),10,10,\[
1,10,2, 1,2,1, 1,3,1, 1,4,1, 1,5,1, 1,6,1, 1,7,1, 1,8,1, 1,9,1, 1,1,2])),
Matrix(GF(3),10,10,\[2,0,0,2,1,2,1,2,2,0,2,0,2,2,0,0,2,
0,0,1,0,0,1,1,2,0,1,0,0,1,1,1,2,0,0,1,0,2,1,2,0,0,
0,0,1,2,0,1,0,2,1,0,1,1,1,1,2,0,0,1,2,0,1,0,0,2,2,
2,1,1,1,2,0,2,0,2,1,1,1,0,1,0,1,0,0,0,2,0,2,0,0,2,
2,1,0,2,2,0,1,0])
/*order=2^19*3^20*5^2*7*13*41*61*/>;
end function;

A12 := function()
return
MatrixGroup<10,GF(3)|
Matrix(GF(3),10,10,\[0,0,1,1,0,2,1,2,1,0,2,1,1,2,0,0,0,
1,1,2,0,0,1,2,0,2,1,1,0,1,1,0,2,1,0,2,1,0,2,2,2,0,
1,0,1,1,2,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,
2,0,2,2,0,1,2,0,0,0,2,1,2,0,0,0,0,0,0,0,0,1,0,1,0,
2,1,0,0,0,2,2,2]),
Matrix(GF(3),10,10,\[1,0,0,2,1,2,0,0,2,1,1,2,2,0,1,2,1,
1,2,1,1,0,1,0,2,0,0,2,2,1,0,2,1,2,0,2,1,1,0,1,0,1,
1,1,2,0,2,0,1,2,1,1,2,0,1,1,0,0,2,0,2,2,0,2,2,1,2,
1,0,0,0,0,1,2,0,0,1,1,0,1,1,2,0,0,0,2,1,0,0,0,2,0,
0,1,1,0,2,2,2,2]) /*order=239500800=2^9*3^5*5^2*7*11*/>;
end function;

S43 := function()
return
MatrixGroup<10, GF(3) |
Matrix(GF(3),10,10,\[0,0,2,1,1,0,0,2,2,0,2,1,2,1,1,1,1,
2,2,2,1,2,1,0,2,1,0,2,2,2,2,2,2,1,2,0,2,0,1,0,2,0,
1,0,1,2,2,2,1,1,1,0,1,2,2,1,0,1,1,0,1,1,0,2,0,2,1,
0,1,1,1,1,1,0,1,1,2,1,2,2,1,2,1,1,0,0,2,2,1,0,2,1,
1,1,2,1,2,1,2,0]),
Matrix(GF(3),10,10,\[1,2,0,2,0,2,2,1,1,1,0,0,0,2,2,0,2,
1,1,2,1,0,2,1,2,2,1,0,0,1,2,2,1,1,2,1,1,2,0,1,0,0,
0,2,1,0,0,2,2,1,1,2,0,1,2,1,1,2,2,2,2,1,0,1,0,1,1,
1,1,1,1,2,0,2,0,2,2,2,0,0,2,1,0,2,2,2,0,2,1,2,2,1,
2,2,0,2,2,1,1,0]) /*order=51840=2^7*3^4*5*/>;
end function;

/***************************************************************************/

function OPlus10_3Identify(group: max:= true, Print:=0)
  
  //since standard generators take a while to find, we've stored them already
  //for the standard copy!
  A := O10p3();
  A := OrbitImage(A,sub<V|V.1>) where V:=VectorSpace(A);
  ims := [A | A.1, A.2];
  S := sub< A | ims >; //socle of A
  F, phi := FPGroupStrong(S);

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is O^+(10,3):[%o]\n", aut; end if;
  iss, gens := StandardGenerators(soc,"O10p3");
  if not iss then error "Standard generator error in O^+(10,3)"; end if;
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
    if not isc then error "Conjugation error in Aut(O^+(10,3))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(O^+(10,3))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;
  imhom := Image(homom);

  //need to identify type
  type := 
   aut eq 1 select "om" else
   aut eq 2 and A.3 in imhom select "gam" else
   aut eq 2 and A.4 in imhom select "del" else
   aut eq 2 select "gamdel" else
   "cgo";

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;

  //Now for the maximals.  We work down the table in the book
  //These are subgroups of OmegaPlus(10,3), so we need a homomorphism
  om := O10p3(); 
  om := sub< GL(10,3) | om.1, om.2 >;
  omtoA := hom< om->A | [A.1,A.2] >;
  
  //C1s
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,1,1)));
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,2,1)));
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,3,1)));
  if not type in {"om","del"} then
    Append(~maximals, omtoA(IsotropicStabOmega(10,3,4,1)));
  end if;
  if type in {"om","del"} then
    G := omtoA(IsotropicStabOmega(10,3,5,1));
    maximals cat:= [G, G^A.3];
  end if;

  if type in {"om","gam"} then
    G := omtoA(NonDegenStabOmega(10,3,1,9,0));
    maximals cat:= [G, G^A.4];
  end if;
  if not type in {"om","gam"} then
    Append(~maximals, omtoA(NonDegenStabOmega(10,3,1,2,1)));
  end if;
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,1,2,-1)));
  if type in {"om","gam"} then
    G := omtoA(NonDegenStabOmega(10,3,1,7,0));
    maximals cat:= [G, G^A.4];
  end if;
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,1,4,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,1,4,-1)));

  //C2s
  Append(~maximals, omtoA(OrthStabOfHalfND(10,3)));

  //C3s
  Append(~maximals, omtoA(GammaOdimOdd(10,3,1)));

  //C9s
  if type in {"om","gam"} then
    G := omtoA(A12());
    maximals cat:= [G, G^A.4];
  end if;

  return homom, A, maximals, F, phi;
end function;

function OMinus10_3Identify(group: max:= true, Print:=0)
  
  //since standard generators take a while to find, we've stored them already
  //for the standard copy!
  A := O10m3();
  A := OrbitImage(A,sub<V|V.1>) where V:=VectorSpace(A);
  ims := [A | A.1, A.2];
  S := sub< A | ims >; //socle of A
  F, phi := FPGroupStrong(S);

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is O^-(10,3):[%o]\n", aut; end if;
  iss, gens := StandardGenerators(soc,"O10m3");
  if not iss then error "Standard generator error in O^-(10,3)"; end if;
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
    if not isc then error "Conjugation error in Aut(O^-(10,3))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(O^-(10,3))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;
  imhom := Image(homom);

  //need to identify type
  type := 
   aut eq 1 select "om" else
   aut eq 2 and A.4^2 in imhom select "so" else
   aut eq 2 and (A.3 in imhom or A.3*A.4^2 in imhom) select "gam" else
   aut eq 2 select "delgam2" else
   aut eq 4 and A.3 in imhom select "go" else
   aut eq 4 and A.3*A.4 in imhom select "delgam4" else
   aut eq 4 select "del" else
   "cgo";

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;

  //Now for the maximals.  We work down the table in the book
  //These are subgroups of OmegaMinus(10,3), so we need a homomorphism
  om := O10m3(); 
  om := sub< GL(10,3) | om.1, om.2 >;
  omtoA := hom< om->A | [A.1,A.2] >;
  
  //C1s
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,1,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,2,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,3,-1)));
  Append(~maximals, omtoA(IsotropicStabOmega(10,3,4,-1)));

  if type in {"om","so","gam","go"} then
    G := omtoA(NonDegenStabOmega(10,3,-1,9,0));
    maximals cat:= [G, G^A.4];
  end if;
  if not type in {"om","so","gam","go"} then
    Append(~maximals, omtoA(NonDegenStabOmega(10,3,-1,2,1)));
  end if;
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,-1,8,1)));
  if type in {"om","so","gam","go"} then
    G := omtoA(NonDegenStabOmega(10,3,-1,7,0));
    maximals cat:= [G, G^A.4];
  end if;
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,-1,4,1)));
  Append(~maximals, omtoA(NonDegenStabOmega(10,3,-1,6,1)));

  //C2s
  if type in {"om","so","gam","go"} then
    G := omtoA(OrthImprim(10,3,-1,1,0));
    maximals cat:= [G, G^A.4];
  end if;
  if not type in {"om","so","gam","go"} then
    Append(~maximals, omtoA(OrthImprim(10,3,-1,2,-1)));
  end if;
  if type in {"om","so","gam","go"} then
    G := omtoA(OrthImprim(10,3,-1,5,0));
    maximals cat:= [G, G^A.4];
  end if;


  //C3s
  if type in {"om","so","delgam2","delgam4"} then
    G := omtoA(GammaOdimOdd(10,3,-1));
    maximals cat:= [G, G^A.4];
  end if;
  Append(~maximals, omtoA(GammaUMeetOmega(10,3)));

  //C9s
  if type in {"om","so"} then
    G := omtoA(S43());
    maximals cat:= [G, G^A.3, G^A.4, G^(A.3*A.4)];
  end if;

  return homom, A, maximals, F, phi;
end function;
