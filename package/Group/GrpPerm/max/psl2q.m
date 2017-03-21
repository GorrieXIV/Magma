freeze;
 
/************************************************************************/
//here we have some almost simple group with socle PSL(2, q), where q
//= p^e. Full aut grp is (C_2 \times C_e) if q is odd, and C_e
//if q is even. 

function WhichGroup(group, p, e)

  assert IsPrime(p);
  assert e gt 3; //we have done PSL(2, p), PSL(2, p^2) and
                 //PSL(2, p^3) as special cases. 

  // If e is even and q is odd then there are 2 copies of PSL(2,
  // p^{e/2}).2 that fuse in PGL; therefore we need more details about
  // which group in PGammaL we have. 
 
  if IsEven(e) and IsOdd(p) then
    subfield_copies:= 2;    
  else
    subfield_copies:= 1;
  end if;
  
  //"computing group order";
  o:= #group;
  order_psl:= #PSL(2, p^e);
  if o eq order_psl then
    return subfield_copies, group;
  end if;
    
  //"computing socle subgroup";
  psl:= Socle(group);
  if subfield_copies eq 1 then
    return 1, psl;
  end if;

  quot, f:= quo<group|psl>;

  if IsOdd(#quot) then
    return 2, psl;
  end if;

  if not IsCyclic(quot) then //must contain diagonal automorphism.
    return 0, psl;
  end if;

  //we now know that we have a copy of PSL which has two maximal
  //PSL(2, q_0)s in it, extended by a group of even order. The only
  //question is whether all of the automorphism group corresponds to
  //field automorphisms (in which case there will be two copies of the
  //subfield group) or not. We distinguish between the case where all
  //automorphisms are field automorphisms from the others by looking
  //to see if the Sylow 2-subgroup contains multiple classes of
  //involutions that are conjugate only to themselves.

  //"computing syl2";
  s:= SylowSubgroup(group, 2);
  
  //"computing classes";
  cls:= Classes(s);
  central_invols:= [x : x in cls | x[1] eq 2 and x[2] eq 1];
  if #central_invols eq 3 then
    return 2, psl;
  elif #central_invols eq 1 then
    return 0, psl;
  else
    "error in which group";
    return 0, _;
  end if;
end function;

/*************************************************************/

function GetImprim(q)
  z:= PrimitiveElement(GF(q));
  m1:= SL(2, q)![z, 0, 0, z^-1];
  m2:= SL(2, q)![0, 1, -1, 0];
  return sub<SL(2, q)|m1, m2>;
end function;


/**************************************************************/
//trying a randomised version to make the semilinear
//dihedral group, as this actually proved faster before 
//than the deterministic approach.

function GetSemilin(group, q)
  proc:= RandomProcess(group);
  got_seed_invol:=false;
  while not got_seed_invol do
    x:= Random(proc);
    o:= Order(x);
    d, r:= Quotrem(o, 2);
    if r eq 0 then
        invol:= x^d;
        assert Order(invol) eq 2;
        got_seed_invol:= true;
    end if;
  end while;

  if IsEven(q) then 
    goal_order:= q+1;
  else
    goal_order:= (q+1) div 2;
  end if;
  made_semilin:= false;
  while not made_semilin do
    y:= invol^Random(proc);
    if Order(invol*y) eq goal_order then
        made_semilin:= true;
    end if;
  end while;
  return sub<group|invol, y>;
end function;

/***************************************************************/

//we make SL(2, p^f) (possibly extended by an involution) inside
//SL(2, p^e).
function GetSubfield(p, e, f)
  
  sl:= SL(2, p^e);
  gens:= SetToSequence(Generators(SL(2, p^f)));
  newgens:= [];

  for i in [1..#gens] do
     Append(~newgens, sl!Eltseq(gens[i]));
  end for;

  //We now extend by an involution if p is odd and e/f is even.
  if IsEven(e div f) and IsOdd(p) then
    z:= PrimitiveElement(GF(p^e));
    if p^f mod 4 eq 1 then
      fac:= Factorisation(p^e - 1);
      two_power:= 2^fac[1][2];
      power:= ((p^e - 1) div two_power);
      Append(~newgens, sl!DiagonalMatrix([z^power, z^(-power)]));
    else
      i:= z^((p^e - 1) div 4);
      Append(~newgens, sl!DiagonalMatrix([-i, i]));
    end if;
  end if;
  return sub<sl|newgens>;
end function;

/***********************************************************************/
//The main function. q is a prime power, where the power is greater
//than 3. group satisfies PSL(2, q) \leq group \leq PGammaL(2,
//q). function returns a list of the maximal subgroups of group.
//no other restrictions on q.

forward MakeHomomGeneral;
function L2qIdentify(group, q: max:= true, Print:=0)

  fac:= Factorisation(q);
  assert #fac eq 1;
  p:= fac[1][1];
  e:= fac[1][2];

  
  //"making standard copy";
  gl:= GL(2,q);
  sl:= SL(2, q);
  apsl := PGammaL(2,q);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  subfield_copies, soc:= WhichGroup(group, p, e);
  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */
  newgens := [ group | Random(soc), Random(soc) ];
  while sub < soc | newgens > ne soc do
    x:=Random(soc);
    while x in sub < soc | newgens > do x:=Random(soc); end while;
    Append(~newgens,x);
  end while;
  soc := sub < soc | newgens >;
  for g in Generators(group) do
   if not g in sub< group | newgens > then Append(~newgens,g); end if;
  end for;
  group := sub< group | newgens >;
  homom, soc, dh
      := MakeHomomGeneral(group, 2, p, e, psl, apsl, factor : Print:=0);
  //dh := Domain(homom);
  //ngs := 2;
  //while dh.(ngs+1) in Socle(dh) do ngs+:=1; end while;

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ dh.i @ homom : i in [1..Ngens(soc)] ]>);
  newgens := [ apsl | dh.i @ homom : i in [1..Ngens(dh)] ];
  for g in Generators(apsl) do
   if not g in sub< apsl | newgens > then Append(~newgens,g); end if;
  end for;
  apsl := sub< apsl | newgens >;

  z:= PrimitiveElement(GF(q));
  if subfield_copies eq 2 then
    outer_invol:= GL(2, q)![z, 0, 0, 1];
  end if;

  maximals:= [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducible"; end if;
  Append(~maximals, Stabiliser(psl, 1));

  if Print gt 1 then print "Getting imprimitive"; end if;
  Append(~maximals, GetImprim(q)@factor);

  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GetSemilin(psl, q));

  if Print gt 1 then print "Getting subfield"; end if;
  divs:= [x : x in Divisors(e) | IsPrime(x)];
  for x in divs do
    power:= e div x;
    if (not x eq 2) or (subfield_copies eq 1) then
      if not p^power eq 2 then
        Append(~maximals, GetSubfield(p, e, power)@factor);
      end if;
    elif subfield_copies eq 2 then
      grp:= GetSubfield(p, e, power);
      grp2:= grp^outer_invol;  
      Append(~maximals, grp@factor);
      Append(~maximals, grp2@factor);
    end if;
  end for;

  return homom, apsl, maximals, F, phi;
end function;
 
/* The following function uses the black-box SL recognition code to set up an
 * isomorphism between an unknown group isomorphic to PSL(d,p^e) and
 * the standard copy.
 * Input parameters:
 * group is the almost simple group, where it is  known that
 * Socle(group) ~= PSL(d,p^e).
 * psl < apsl where apsl is the standard copy of Aut(PSL(d,p^e)).
 * factor is a homomorphism from the standard copy of GL(d,p^e) to apsl.
 * homom (group->apsl), socle and group are returned, where group is the same
 * group but with generators redefined to make those of socle come first.
 */
// the Black-Box constructive recognition code.
MakeHomomGeneral := function(group, d, p, e, psl, apsl, factor : Print:=0)
  local works, GtoSL, SLtoG, mat, homom, ims,
    g, newgens, subsoc, subgp, pslgens, imgens, CG, ce, isc, h, socle;

  if not IsProbablyPerfect(group) then
    soc := Socle(group);
  else
    soc:= group;
  end if;

  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */
  if Ngens(soc) gt 2 then
    newgens := [ group | Random(soc), Random(soc) ];
    subsoc := sub<soc|newgens>; 
    RandomSchreier(subsoc);
    while subsoc ne soc do
      x:=Random(soc);
      while x in subsoc do 
        x:=Random(soc); 
      end while;
      Append(~newgens,x); 
      subsoc := sub<soc|newgens>; 
      RandomSchreier(subsoc);
    end while;
    soc := subsoc;
  else newgens := [ group | soc.1, soc.2 ];
  end if;    

  subgp := soc;
  for g in Generators(group) do
   if not g in subgp then 
     Append(~newgens,g);
     subgp := sub< group | newgens >; 
     RandomSchreier(subgp);
   end if;
  end for;
  group := subgp;

  works := false;
  while not works do
    works, GtoSL, SLtoG := RecogniseSL(soc,d,p^e);
  end while;

  pslgens := [];
  for  i in [1..Ngens(soc)] do
    mat := GtoSL(soc.i);
    Append(~pslgens,mat@factor);
  end for;
  //Now identify images of all generators of group in apsl.
  ims := pslgens;
  for i in [Ngens(soc)+1..Ngens(group)] do
    g := group.i;
    CG := apsl; ce := Id(apsl);
    for j in [1.. #pslgens] do
      mat := GtoSL(soc.j^g);
      isc, h := IsConjugate(CG,pslgens[j]^ce,mat@factor);
      if not isc then error "Conjugation error in Aut(PSL(d,q))"; end if;
      CG := Centraliser(CG,mat@factor);
      ce := ce*h;
    end for;
    Append(~ims,ce);
  end for;
  return hom< group -> apsl | ims >, soc, group;
end function;
