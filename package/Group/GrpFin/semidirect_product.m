freeze;

/*
>From D.F.Holt@warwick.ac.uk Thu Mar  4 03:18:11 2010

This is a slightly improved version of a SemidirectProduct function.

SemidirectProduct := function(K,H,phi)
 semidirect product of K by H using homomorphism phi:H->Aut(K)

It works in theory for all types of finite groups, but if H and K are
not both permutation groups then it will just return something of large
degree using regular representations.

There should be a different version for the case when they are both GrpPC
that returns GrpPC, but I will leave that for someone else unless there is
an urgent demand! That should be routine to write.

When H and K are both permutation groups, it now tries a bit harder to find
a perm rep of the semidirect product G of reasonably low degree. It also
returns the injection maps K->G and H->G.

I have not tested it very thoroughly! I would of course be interested in
any feedback if anyone should use it.

*/

RegularSemidirectProduct := function(K,H,phi : maxdeg:=100000 )
 /* semidirect product of K by H using homomorphism phi:H->Aut(K)
  * H needs to be a permutation group.
  */
  local psi, hnp, rho, A, pr, P, faithful, Kelts, deg, gens, gen, dK, dH,
        pg, G, m1, m2;
  //determine whether phi is faithful - need to do this in perm rep of Aut(K)
  hnp := Type(H) ne GrpPerm;
  if hnp then
    if #H gt maxdeg then
      error "H too large large for regular action.";
    end if;
    psi, H := CosetAction(H,sub<H|>);
    phi := psi^-1 * phi;
  end if;
  A := Codomain(phi);
  rho, P := PermutationRepresentation(A);
  pr := hom< H->P | [ H.i @ phi @ rho : i in [1..Ngens(H)]] >;
  faithful := #Kernel(pr) eq 1;
  dK := #K; dH := Degree(H);
  deg := faithful select dK else dK + dH; 
  // "Degree of semidirect product will be", deg;
  if deg gt maxdeg then
    error "Degree is too large. Increase maxdeg";
  end if;
  Kelts := {@ k : k in K @};
  gens := [Sym(deg) |];
  // Generators of K first - given by right action
  for g in [K.i : i in [1..Ngens(K)]] do
    gen := [ Position(Kelts, Kelts[i]*g) : i in [1..dK] ];
    if not faithful then gen cat:= [dK+i: i in [1..dH]]; end if;
    Append(~gens,gen);
  end for; 
  // Now generators of H
  for g in [H.i : i in [1..Ngens(H)]] do
    pg := phi(g);
    gen := [ Position(Kelts, Kelts[i] @ pg) : i in [1..dK] ];
    if not faithful then gen cat:= [dK+i^g: i in [1..dH] ]; end if;
    Append(~gens,gen);
  end for; 
  G := sub< Sym(deg) | gens >;
  m1 := hom< K->G | [G.i : i in [1..Ngens(K)]] >;
  m2 := hom< H->G | [G.(i+Ngens(K)) : i in [1..Ngens(H)]] >;
  if hnp then m2 := psi*m2; end if;
  return G, m1, m2;
end function;
  
intrinsic SemidirectProduct(K::Grp, H::Grp, phi::Map : MaxDeg:=1000000, UseRegular := false ) -> Grp, Map, Map
{The semidirect product of K by H using homomorphism phi:H->Aut(K), Also returns maps embedding K and H into the result }

  local faithful, OK, stabs, repslist, dK, dS, dH, dom, ct,
        deg, gens, gen, pg, A, rho, P, pr, Ielts, gg, G, m1, m2;

  if UseRegular then
    return RegularSemidirectProduct(K,H,phi:maxdeg:=MaxDeg);
  end if;

  if ISA(Type(K), GrpPC) and ISA(Type(H), GrpPC) then
    G := Extension(K, H, [H.i @ phi: i in [1..NPCgens(H)]]);
    m1 := hom< K->G | [G.(i+NPCgens(H)) : i in [1..NPCgens(K)]] >;
    m2 := hom< H->G | [G.i : i in [1..NPCgens(H)]] >;
    return G, m1, m2;
  end if;

  if not ISA(Type(K), GrpPerm) or not ISA(Type(H), GrpPerm) then
    // "Using regular representation of normal subgroup";
    return RegularSemidirectProduct(K,H,phi:maxdeg:=MaxDeg);
  end if;

  OK := Orbits(K);
  stabs := [ Stabiliser(K,o[1]) : o in OK ];
  deg := &+[ Index(K,Normaliser(K,S)) : S in stabs ];
  if deg ge #K then
    // "Using regular representation of normal subgroup";
    return RegularSemidirectProduct(K,H,phi:maxdeg:=MaxDeg);
  end if;

  repslist := stabs;
  ct := 0;
  while ct lt #repslist do
    ct+:=1;
    S := repslist[ct];
    for T in [ S @ phi(H.i) : i in [1..Ngens(H)] ] do
      if forall{ R : R in repslist | not IsConjugate(K,R,T) } then
        Append(~repslist, T);
        deg +:= Index(K,Normaliser(K,S));
        if deg ge #K then
          // "Using regular representation of normal subgroup";
          return RegularSemidirectProduct(K,H,phi:maxdeg:=MaxDeg);
        end if;
      end if;
    end for;
  end while;

  A := Codomain(phi);
  rho, P := PermutationRepresentation(A);
  pr := hom< H->P | [ H.i @ phi @ rho : i in [1..Ngens(H)]] >;
  dH := Degree(H);
  if #&meet{ Core(K,Normaliser(K,T)) : T in repslist } eq 1 then
    //we can define the representation on the conjugates of repslist
    // "Using conjugation action on stabilisers";
    I := sub< P | [ A.i @ rho : i in [1..Ngens(A)] | IsInner(A.i) ] >;
    faithful := #sub< P | I, Image(pr) > eq #I * #H;
    dom := &join{@ {@ T^r : r in Transversal(K,T) @} :  T in repslist @};
    dS := #dom;
    deg := faithful select dS else dS + dH; 
    gens := [Sym(deg) |];
    // Generators of K first
    for g in [K.i : i in [1..Ngens(K)]] do
      gen := [ Position(dom, dom[i]^g) : i in [1..dS] ];
      if not faithful then gen cat:= [dS+i: i in [1..dH]]; end if;
      Append(~gens,gen);
    end for; 
    // Now generators of H
    for g in [H.i : i in [1..Ngens(H)]] do
      pg := phi(g);
      gen := [ Position(dom, dom[i] @ pg) : i in [1..dS] ];
      if not faithful then gen cat:= [dS+i^g: i in [1..dH] ]; end if;
      Append(~gens,gen);
    end for; 
    G := sub< Sym(deg) | gens >;
    m1 := hom< K->G | [G.i : i in [1..Ngens(K)]] >;
    m2 := hom< H->G | [G.(i+Ngens(K)) : i in [1..Ngens(H)]] >;
    return G, m1, m2;
  end if;

  //Next try embedding into wreath product of K and H
  faithful := #Kernel(pr) eq 1;
  I := Image(pr);
  dK := Degree(K);
  dS := #I * dK;
  if dS ge #K then
    //degree too large
    // "Using regular representation of normal subgroup";
    return RegularSemidirectProduct(K,H,phi:maxdeg:=MaxDeg);
  end if;

  // "Using wreath product type representation";
  Ielts := {@ i : i in I @};
  deg := faithful select dS else dS + dH; 
  if deg gt MaxDeg then
    error "Degree is too large. Increase MaxDeg";
  end if;
  //points in range [(i-1)*dS+1 .. i*dS] are images of points [1..dS] under
  //Ielts[i]^-1. 
  gens := [Sym(deg) |];
  // Generators of K first
  for g in [K.i : i in [1..Ngens(K)]] do
    gen := &cat[ [ p^(g @ (Ielts[i] @@ rho)) + (i-1)*dK : p in [1..dK] ] :
                                                            i in [1..#I] ];
    if not faithful then gen cat:= [dS+i: i in [1..dH]]; end if;
    Append(~gens,gen);
  end for; 
  // Now generators of H
  for g in [H.i : i in [1..Ngens(H)]] do
    gg := pr(g^-1);
    gen := &cat[ [p + (Position(Ielts,gg*Ielts[i]) - 1)*dK : p in [1..dK] ] :
                                                            i in [1..#I] ];
    if not faithful then gen cat:= [dS+i^g: i in [1..dH] ]; end if;
    Append(~gens,gen);
  end for; 
  G := sub< Sym(deg) | gens >;
  m1 := hom< K->G | [G.i : i in [1..Ngens(K)]] >;
  m2 := hom< H->G | [G.(i+Ngens(K)) : i in [1..Ngens(H)]] >;
  return G, m1, m2;

end intrinsic;
