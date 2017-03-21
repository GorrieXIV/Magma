freeze;
import "unitreds.m": IsotropKStab, NonisotropKStab;
import "unitimps.m": StandardUnitImps, UnitImpHalfDim;
import "superfield.m": GammaSU;
import "subfield.m": OrthsInSU, SpInSU;
 

/*
Code to identify and get maximal subgroups of almost simple groups with
socle U(5,4)
*/

U53Identify := function(group:max:=true,Print:=0)
  A := PGammaU(5,3);
  S := Socle(A);
  iss, gens := StandardGenerators(S, "U53");
  if not iss then error "Standard generator error in U(5,3)"; end if;
  ims := [A | gens[1], gens[2]];
  S := sub< A | ims >;
  F, phi := FPGroupStrong(S);
  for g in Generators(A) do if not g in S then
    A := sub<A | ims[1],ims[2],g >; break;
  end if; end for;

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is U(5,3):[%o]\n", aut; end if;

  iss, gens := StandardGenerators(soc, "U53");
  if not iss then error "Standard generator error in U(5,3)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b ];
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
    if not isc then error "Conjugation error in Aut(U(5,3))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(U(5,3))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;
    
  //Now for the maximals.  We work down the table in the book
  //These are subgroups of SU(5,3), so we need a homomorphism
  iss, gens := StandardGenerators(SU(5,3),"U53":Projective:=true);
  uni := sub< GL(5,9) | gens >;
  unitoA := hom< uni->A | [A.1,A.2] >;

  //C1s
  Append(~maximals, unitoA(IsotropKStab(5,3,1)));
  Append(~maximals, unitoA(IsotropKStab(5,3,2)));
  Append(~maximals, unitoA(NonisotropKStab(5,3,1)));
  Append(~maximals, unitoA(NonisotropKStab(5,3,2)));

  //C2s
  Append(~maximals, unitoA(StandardUnitImps(5,3,1)));
  
  //C3s
  Append(~maximals, unitoA(GammaSU(5,3,5)));

  //C5
  Append(~maximals, unitoA(OrthsInSU(5,3))); 

  return homom, A, maximals, F, phi;
end function;

/*
Code to identify and get maximal subgroups of almost simple groups with
socle U(7,2)
*/

U72Identify := function(group:max:=true,Print:=0)
  A := PGammaU(7,2);
  S := Socle(A);
  iss, gens := StandardGenerators(S, "U72");
  if not iss then error "Standard generator error in U(7,2)"; end if;
  ims := [A | gens[1], gens[2]];
  S := sub< A | ims >;
  F, phi := FPGroupStrong(S);
  for g in Generators(A) do if not g in S then
    A := sub<A | ims[1],ims[2],g >; break;
  end if; end for;

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is U(7,2):[%o]\n", aut; end if;

  iss, gens := StandardGenerators(soc, "U72");
  if not iss then error "Standard generator error in U(7,2)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b ];
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
    if not isc then error "Conjugation error in Aut(U(7,2))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(U(7,2))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;
    
  //Now for the maximals.  We work down the table in the book
  //These are subgroups of SU(7,2), so we need a homomorphism
  iss, gens := StandardGenerators(SU(7,2),"U72":Projective:=true);
  uni := sub< GL(7,4) | gens >;
  unitoA := hom< uni->A | [A.1,A.2] >;

  //C1s
  Append(~maximals, unitoA(IsotropKStab(7,2,1)));
  Append(~maximals, unitoA(IsotropKStab(7,2,2)));
  Append(~maximals, unitoA(IsotropKStab(7,2,3)));
  Append(~maximals, unitoA(NonisotropKStab(7,2,1)));
  Append(~maximals, unitoA(NonisotropKStab(7,2,2)));
  Append(~maximals, unitoA(NonisotropKStab(7,2,3)));

  //C2s
  Append(~maximals, unitoA(StandardUnitImps(7,2,1)));
  
  //C3s
  Append(~maximals, unitoA(GammaSU(7,2,7)));

  return homom, A, maximals, F, phi;
end function;

/*
Code to identify and get maximal subgroups of almost simple groups with
socle U(8,2)
*/

U82Identify := function(group:max:=true,Print:=0)
  A := PGammaU(8,2);
  S := Socle(A);
  iss, gens := StandardGenerators(S, "U82");
  if not iss then error "Standard generator error in U(8,2)"; end if;
  ims := [A | gens[1], gens[2]];
  S := sub< A | ims >;
  F, phi := FPGroupStrong(S);
  for g in Generators(A) do if not g in S then
    A := sub<A | ims[1],ims[2],g >; break;
  end if; end for;

  soc := Socle(group);
  aut := Index(group, soc);
  if Print gt 1 then printf "group is U(8,2):[%o]\n", aut; end if;

  iss, gens := StandardGenerators(soc, "U82");
  if not iss then error "Standard generator error in U(8,2)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b ];
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
    if not isc then error "Conjugation error in Aut(U(8,2))"; end if;
    CG := Centraliser(A,conjim);
    ce := h;
    isc, h := IsConjugate(CG,A.2^ce,homom(soc.2^g));
    if not isc then error "Conjugation error in Aut(U(8,2))"; end if;
    ce := ce*h;
    Append(~ims,ce);
  end for;
  homom :=  hom< group -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;
    
  //Now for the maximals.  We work down the table in the book
  //These are subgroups of SU(8,2), so we need a homomorphism
  iss, gens := StandardGenerators(SU(8,2),"U82":Projective:=true);
  uni := sub< GL(8,4) | gens >;
  unitoA := hom< uni->A | [A.1,A.2] >;

  //C1s
  Append(~maximals, unitoA(IsotropKStab(8,2,1)));
  Append(~maximals, unitoA(IsotropKStab(8,2,2)));
  Append(~maximals, unitoA(IsotropKStab(8,2,3)));
  Append(~maximals, unitoA(IsotropKStab(8,2,4)));
  Append(~maximals, unitoA(NonisotropKStab(8,2,1)));
  Append(~maximals, unitoA(NonisotropKStab(8,2,2)));
  Append(~maximals, unitoA(NonisotropKStab(8,2,3)));

  //C2s
  Append(~maximals, unitoA(StandardUnitImps(8,2,1)));
  Append(~maximals, unitoA(StandardUnitImps(8,2,4)));
  Append(~maximals, unitoA(UnitImpHalfDim(8,2)));
  
  //C5
  Append(~maximals, unitoA(SpInSU(8,2)));

  return homom, A, maximals, F, phi;
end function;
