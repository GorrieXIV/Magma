freeze;

//////////////////////////////
// Automorphisms
//////////////////////////////
// All Extensions
//////////////////////////////
// Class Fields
//////////////////////////////

/////////////////////////////////////////////////////////////////////////////
// Automorphisms
/////////////////////////////////////////////////////////////////////////////

declare attributes Map:LocalAutoGenerators;
declare attributes Map:LocalRingMap;

function eval_automorphism(x, gens, pos)
    if pos eq #gens then
        return x;
    end if;

    R := Parent(x);
    P := PolynomialRing(R);
    return Evaluate(
        P ! [eval_automorphism(i, gens, pos + 1) : i in Eltseq(x)], gens[pos]
    );
end function;

/*
  <example>
    S := pAdicRing(3, 50);
    S := ext<S|x^5-3>;
    S := ext<S|CyclotomicPolynomial(5)>;
    assert #Automorphisms(S) eq 20;
  </example>  

    should have 20 - but the 1st extension (of degree 5) has none.
    This is the reason for the more delicate approach using the
    Codomain(S) to find roots in, so Continuations will
    extend maps ?? -> S wich works since S is a spitting field.

    Also: GaloisImage can only be used for absolute unramified fields.
    In the relative case, it can only find (in general) the relative
    automorphisms!
*/      

intrinsic Continuations(m::Map, L::RngPad) -> SeqEnum
{Let m: R -> R be an automorphism of a p-adic ring.
Let L be an extension of R.  Return the continuations of m to L.}

    R := BaseRing(L);
    f := DefiningPolynomial(L);
    
    if R ne Domain(m) then
      return Flat([Continuations(mm, L): mm in Continuations(m,R)]);
    end if;

    S := Codomain(m);
    
    res := [];
    if Degree(L, R) eq 1 then
	curr := map<L -> S | x :-> S ! m(R ! x)>;
	curr`LocalAutoGenerators := ChangeUniverse(m`LocalAutoGenerators, S);
	Append(~res, curr);
    elif IsInertial(f) and Domain(m) eq PrimeRing(L) then
      //CF: in general, if m is the identity on the coefficient ring
      //    this method is (would be) legal.
        gens := ChangeUniverse(m`LocalAutoGenerators, S);
        r := L.1;
        for i in [1..Degree(L)] do 
            curr_gens := Insert(gens, 1, r);
            curr := map<L -> S | x :-> S!eval_automorphism(x, curr_gens, 1)>;
            curr`LocalAutoGenerators := curr_gens;
//"curr_gens",curr_gens;
            Append(~res, curr);
            r := GaloisImage(r, 1);
        end for;
    else 
        P := PolynomialRing(S);
        gens := ChangeUniverse(m`LocalAutoGenerators, S);
	roots := Roots(P ! [m(x) : x in Eltseq(f)]);
	i := 0;
	repeat 
	    i +:= 1;
	until i gt #roots or IsWeaklyEqual(roots[i][1], L.1);
	if i le #roots then
	    ri := roots[i];
	    Remove(~roots, i);
	    Insert(~roots, 1, ri);
	end if;
        for r in roots do
            curr_gens := Insert(gens, 1, r[1]); 
            curr := map<L -> S | x :-> eval_automorphism(x, curr_gens, 1)>;
            curr`LocalAutoGenerators := curr_gens;
//"curr_gens",curr_gens;    
            Append(~res, curr);
        end for;
    end if;
    return res;
"res",[IsWeaklyEqual(m(Domain(m).1), Domain(m).1) : m in res];

end intrinsic;


intrinsic Automorphisms(L::RngPad, K::RngPad: Into := false) -> SeqEnum
{Return the automorphisms of the local ring L over K. Automorphisms are returned as a sequence of maps}
  if Into cmpeq false then
    Into := L;
  end if;

    if L eq K then
        curr_gens := [Into ! 1];
        curr := map<L -> Into | x :-> eval_automorphism(x, curr_gens, 1)>;
//"curr_gens",curr_gens;              
        curr`LocalAutoGenerators := curr_gens;
        return [curr];
    end if;
//"L",L;
//"BaseRing(L)",BaseRing(L);
    R := BaseRing(L);
    require R ne L : "Argument 1 must be an extension of argument 2";
    maps := Automorphisms(R,K : Into := Into);

    res := [];
        for m in maps do
           res cat:= Continuations(m,L); 
        end for;
    return res;
"maps",[IsWeaklyEqual(m(Domain(m).1), Domain(m).1) : m in maps];
"maps",[m(Domain(m).1)  : m in maps];
"res",[m(Domain(m).1)  : m in res];
end intrinsic;


intrinsic Automorphisms(L::RngPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
  return Automorphisms(L, PrimeRing(L));
end intrinsic;


function eval_field_automorphism(x, m)
    F := Parent(x);
    R := RingOfIntegers(F);
    pi := UniformizingElement(F);

    xv := Valuation(x);
    xu := ShiftValuation(x, -xv);
    return (F ! m(UniformizingElement(R)))^xv * F ! m(R ! xu);
end function;

function construct_field_map(L, m)
    res := map<L -> L | x :-> eval_field_automorphism(x, m)>;
    res`LocalRingMap := m;
    return res;
end function;

//intrinsic Continuations(m::Map, L::FldPad) -> Map
//{Let m: R -> R be an automorphism of a p-adic field.
//Let L be an extension of R.  Return the continuations of m to L.}
//    maps := Continuations(m,RingOfIntegers(L));
//    return [construct_field_map(L, m) : m in maps];
//end intrinsic;

intrinsic Automorphisms(L::FldPad,K::FldPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
    maps := Automorphisms(RingOfIntegers(L),RingOfIntegers(K));
    return [construct_field_map(L, m) : m in maps];
end intrinsic;

intrinsic Automorphisms(L::FldPad) -> SeqEnum
{Return the automorphisms of the local ring L. Automorphisms are returned as a sequence of maps}
    maps := Automorphisms(RingOfIntegers(L));
    return [construct_field_map(L, m) : m in maps];
end intrinsic;


function auto_eq(m1, m2)
    return m1`LocalAutoGenerators eq m2`LocalAutoGenerators;
end function;

function auto_mult(m1, m2)
    gens1 := m1`LocalAutoGenerators;
    gens2 := m2`LocalAutoGenerators;
    gens := [];
    for i in [1..#gens1] do
        Append(~gens, eval_automorphism(gens1[i], gens2, 1));
    end for;

    L := Universe(gens1);
    m := map<L -> L | x :-> eval_automorphism(x, gens, 1)>;
    m`LocalAutoGenerators := gens;
    return m;
end function;

intrinsic AutomorphismGroup(L::RngPad,K::RngPad: Abelian:= false) -> Grp, Map, PowMapAut
{Return the automorphism group of L/K as a permutation group}
    
    maps := Automorphisms(L,K); // maps[1] need not be identity
    assert auto_eq(auto_mult(maps[1],maps[1]),maps[1]);

    if not Abelian then
      G, m1 := GenericGroup
      (maps : Mult := auto_mult, Eq := auto_eq ,Id := maps[1] //WRONG! MW, Fixed NS
      );
      m2, G2 := CosetAction(G, sub<G|>);
      m := Inverse(m2) * m1;
      return
        G2,
        map<
            G2 -> PowerStructure(Map) | g :-> m(g), h :-> h @@ m
        >,Aut(L);
    else
       G, m1 := GenericGroup
	(maps : Mult := auto_mult, Eq := auto_eq, Id := maps[1] //WRONG! MW, Fixed NS
      );
      //if not IsAbelian(G) then 
      //  error "AutomorphismGroup: ERROR, you claimed the group is abelian, this is not the case.";
      //end if;
      m2, G2 := CosetAction(G, sub<G|>);
      m := Inverse(m2) * m1;
      Gab, mab := AbelianGroup(G2); 
      return
        Gab,
        map<
            Gab -> PowerStructure(Map) | g :-> m(g @@ mab), h :-> mab(h @@ m)
        >,Aut(L);
    end if;
end intrinsic;

intrinsic AutomorphismGroup(L::RngPad) -> GrpPerm, Map, PowMapAut
{Return the automorphism group of L as a permutation group}
  G,m := AutomorphismGroup(L,PrimeRing(L));
  return G,m;
end intrinsic;

intrinsic AutomorphismGroup(L::FldPad,K::FldPad: Abelian:= false) -> Grp, Map, PowMapAut
{Return the automorphism group of L over K as a permutation group}
    G, m := AutomorphismGroup(RingOfIntegers(L),RingOfIntegers(K):Abelian:=Abelian);

    return
        G,
        map<
            G -> PowerStructure(Map) |
            g :-> construct_field_map(L, m(g)),
            h :-> h`LocalRingMap @@ m
        >, Aut(L);
end intrinsic;

intrinsic AutomorphismGroup(L::FldPad) -> Grp, Map, PowMapAut
{Return the automorphism group of L as a permutation group}
  G,m := AutomorphismGroup(L,PrimeField(L));
  return G,m,Aut(L);
end intrinsic;




///////////////////////////////////////////////////////////////////////////////////
// used in ClassField

function Fe(R)
  
  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));
  
  F := [];
  for i := 1 to Floor(p*e/(p-1)) do
    if i mod p ne 0 then
      Append(~F,i);
    end if;
  end for;
    
  return F;
    
end function;



function rel_mat_map_map(Rel, FG_U, U, S)
  m := Coercion(S,U);
  cols := #Rel[1];
  SRel := Rel;
  for rel in Generators(S) do
    //    Parent((m(rel)));
    Append(~SRel,Eltseq((m(rel))@@FG_U));
  end for;
  M := Matrix(SRel);
  H,T := HermiteForm(M);
  return Submatrix(H,1,1,cols,cols);
end function;        

function rel_mat_map(U_R)
//intrinsic rel_mat_map(U_R) -> .
//{this map returns the canonical matrix representing a subgroup of K*
//with respect to UnitGroupGenerators}
  R := Codomain(U_R);
//"R",R;
  U := Domain(U_R);
  Sgens := Reverse(UnitGroupGenerators(R));
//"Sgens",Sgens;
  FG := FreeAbelianGroup(#Sgens);
//"FG",FG;
  FG_U := hom< FG->U | [<FG.i,Sgens[i]@@U_R>:i in [1..#Sgens]]>;
//UU := quo<U|[Sgens[i]@@U_R:i in [1..#Sgens]]>;
//"UU",UU;
//"FG_U",FG_U;
//"Image(FG_U)",Image(FG_U);
//"U",U;  
  FG_Ugens := [U.i@@FG_U: i in [1..#Generators(U)]];
//FG_Ugens;
//[<FG.i,Sgens[i]@@U_R>:i in [1..#Sgens]]; 
  Rel:=[];
  for i in [1..#Sgens] do
    line := [0:g in Sgens];
    line[i] := Order(Sgens[i]@@U_R);
    Append(~Rel,line);
  end for;
  for rel in Relations(U) do
    es := Eltseq(LHS(rel));
    Append(~Rel, Eltseq(&+[es[i]*FG_Ugens[i]:i in [1..#es]]));
  end for;
  
  cols := #Generators(FG);
  matalg := Parent(Submatrix(Matrix(Rel),1,1,cols,cols));
  sbgrps := Parent(sub<U|U.1>);

  return map<sbgrps->matalg| S :-> rel_mat_map_map(Rel, FG_U, U, S)>;
end function;


function list_mat_reduce(L,M) //-> .
//{M must be in HNF}
  
  n := #L;
  for i := 1 to n do
    if Abs(L[i]) ge Abs(M[i][i]) then
      f := Floor(L[i]/M[i][i]);
      L := [ Integers()!(L[j]-f*M[i][j]): j in [1..n]];
    end if;  
  end for; 
    
  return L;
    
end function;




//////////

function elt_rep_map_map(Rel, FG_U, U, U_R, elt)
  //m := Coercion(S,U);
  SRel := Rel;
  elt_rep := Eltseq(elt@@U_R@@FG_U);
  return list_mat_reduce(elt_rep, Rel);
end function;        

function elt_rep_map(U_R)
//intrinsic elt_rep_map(U_R) -> .
//{this map returns the canonical matrix representing a subgroup of K*
//with respect to UnitGroupGenerators}
  R := Codomain(U_R);
  U := Domain(U_R);
  Sgens := Reverse(UnitGroupGenerators(R));
//  Sgens;
//  m := Coercion(S,U);
  FG := FreeAbelianGroup(#Sgens);
//  FG;
  FG_U := hom< FG->U | [<FG.i,Sgens[i]@@U_R>:i in [1..#Sgens]]>;
  FG_Ugens := [U.i@@FG_U: i in [1..#Generators(U)]];
//FG_Ugens;
//[<FG.i,Sgens[i]@@U_R>:i in [1..#Sgens]]; 
  Rel:=[];
  for i in [1..#Sgens] do
    line := [0:g in Sgens];
    line[i] := Order(Sgens[i]@@U_R);
    Append(~Rel,line);
  end for;
  for rel in Relations(U) do
    es := Eltseq(LHS(rel));
    Append(~Rel, Eltseq(&+[es[i]*FG_Ugens[i]:i in [1..#es]]));
  end for;
  line := [0:g in Sgens];
  line[1] := Precision(R);
  Append(~Rel,line);

  cols := #Generators(FG);
  MRel := Submatrix(HermiteForm(Matrix(Rel)),1,1,cols,cols);
//MRel;
  seqs := Parent(Rel[1]);
  //matalg := Parent(Submatrix(Matrix(Rel),1,1,cols,cols));
  //sbgrps := Parent(sub<U|U.1>);

  return map< R -> seqs| elt :-> elt_rep_map_map(MRel, FG_U, U, U_R, elt)>;
end function;
////////////////////////////////////////////////////////////////////////////////////  

intrinsic IsNormal(L::RngPad,K::RngPad) -> .
{True if L over K is a normal extension}
  f := InertiaDegree(L,K);
  n := Degree(L,K);
  if f eq n then
//"n+";
    return true;
  end if;
  phi := DefiningPolynomial(L,K);
  Ly := PolynomialRing(L); y := Ly.1;
  if #Roots(Ly!phi) eq Degree(L,K) then
//"n+";
    return true;
  end if;
//"n-";  
  return false;
end intrinsic;

intrinsic IsNormal(L::RngPad) -> .
{True if L is a normal extension}
  return IsNormal(L,PrimeRing(L));
end intrinsic;

intrinsic IsNormal(L::FldPad,K::FldPad) -> .
{True if L over K is a normal extension}
  return IsNormal(RingOfIntegers(L),RingOfIntegers(K));
end intrinsic;

intrinsic IsNormal(L::FldPad) -> .
{True if L is a normal extension}
  return IsNormal(RingOfIntegers(L));
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////  




/////////////////////////////////////////////////////////////////////////////////////////////


function full_precision(f)
  Rt := Parent(f);
  R := CoefficientRing(Rt);
  pi := UniformizingElement(R);
  S := quo<R|pi^R`DefaultPrecision>;
  St := PolynomialRing(S);
  return Rt!St!f;
end function;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
// krasner 
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
intrinsic OreConditions(R::FldPad, n::RngIntElt, j::RngIntElt) -> BoolElt
{}

  require n ge 1: "n must be positive"; if n eq 1 then return false; end if;
  b := j mod n;
  return Minimum(Valuation(R!b),Valuation(R!n))*n le j and
         j le Valuation(R!n)*n;

end intrinsic;


intrinsic OreConditions(R::RngPad, n::RngIntElt, j::RngIntElt) -> BoolElt
{Return whether R has a totally ramified extension of degree n with
 discriminant valuation n+j-1}

  require n ge 1: "n must be positive"; if n eq 1 then return false; end if;
  b := j mod n;
  return Minimum(Valuation(R!b),Valuation(R!n))*n le j and
         j le Valuation(R!n)*n;
end intrinsic;

function possible_discriminants(R, n)
//intrinsic possible_discriminants(R, n) -> .
//{return a list of discriminants (in the form of j) of all extension of degree n of R}

  discs := [];
  top := Valuation(R!n)*n;
  for j := 0 to top do // needs to start at j=0, MW
    if OreConditions(R,n,j) then Append(~discs,j); end if;
  end for;
  return discs;  
end function;
// bah, ore is for totally ramified...

intrinsic PossibleDiscriminants(R::RngPad, n::RngIntElt) -> RngIntElt
{Returns a list of possible discriminants of all totally ramified extensions
 of degree n of R. The discriminants are represented by integers j such that
 the valuation of the discriminants of the extensions is n+j-1.}
  return possible_discriminants(R, n);
end intrinsic;


////////////////////////////////////////////////////////////////////////////////

function number_of_extensions(p,e,f,n,j) 
  a := j div n;
  b := j mod n;
//p,e,f,n,j;    
  if b eq 0 then
    sum := 0;
    for i := 1 to Floor(a/e) do
      sum := sum+e*n/p^i;
    end for;
    sum := Integers()!sum;
    return n*(p^f)^sum;   
  else
    sum := 0;
    for i := 1 to Floor(a/e) do
       sum := sum+e*n/p^i;
    end for;
    sum := Integers()!sum;
    sum := sum+Floor((j-Floor(a/e)*e*n-1)/p^(Floor(a/e)+1));
    return n*(p^f-1)*(p^f)^sum;
  end if;
end function;


intrinsic NumberOfExtensions
(R::RngPad, n::RngIntElt : E:=0,F:=0, vD:=-1,j:=-1, Galois:=false) -> RngIntElt
{The number of extensions of degree n of the local ring R, 
 with given ramification index E, inertia degree F.
 When F is 1, can also restrict to discriminant valuation vD,
 and this can also be specified by j with vD=n+j-1.
 If Galois := true only normal extensions are counted.}

  deg:=Degree(R); f:=InertiaDegree(R); e:=RamificationIndex(R); p:=Prime(R);
 
  if E ne 0 and F ne 0 then
   if F*E ne n then error "NumberOfExtensions: F*E must equal n"; end if;
   end if;
 
  if E eq 0 and F eq 0 then
   require vD eq -1 and j eq -1: "vD and j must be -1 when E,F not given";
   return &+[NumberOfExtensions(R,n: E:=e,Galois:=Galois) : e in Divisors(n)];
   end if;

  if E gt 0 then
   require n mod E eq 0: "NumberOfExtensions: ERROR, E must divide n.";
   F := n div E; end if; 

  // one unramified extension for given degree.
  if F eq n then return 1; end if;
 
  if F ne 1 and j ne -1 then error
   "j must be -1 (unspecified) for extensions with F not equal to 1"; end if; 
  if F ne 1 and vD ne -1 then error
   "vD must be -1 (unspecified) for extensions with F not equal to 1"; end if; 
  if vD ne -1 then J := vD-n+1;
   if j ne -1 and J ne j then
    error "NumberOfExtensions: ERROR, varargs vD and j are not compatible.";
    end if;
    j := J;
  end if;

  if j ne -1 and not OreConditions(R, n, j) then return 0; end if;
            
//----------------------------------------------------------
// galois case

  if Galois then
    if n eq p then
      num := 0;
      if j eq Valuation(R!n)*n then
        if HasPRoot(R) then
          return p*(p^f)^e; 
        else
          return 0;
        end if;
      elif j ne -1 then
        return p*(p^(e*f)-1)/p-1;      
      else
        num :=p*(p^(e*f)-1)/(p-1)*(#possible_discriminants(R, n)-1);
        if HasPRoot(R) then
          num := num+p*(p^f)^e;
        end if;
        return num;
      end if;
    elif n eq p^2 then 
      if j ne -1 then
        error "NumberOfExtensions: Sorry, this case is not implemented yet.";
      end if;
      if F eq p then
        return (p^(e*f)-1)/(p-1)+p^(e*f)-1;
      elif F eq 1 then // the semicolons here look dodgy... MW
        return p^2*(p^(e*f)-1)/(p-1)*(p^(e*f-1)-1)/(p^2-1);+p^(e*f+1)*(p^(e*f)-1)/(p-1);
      else 
        return (p^(e*f)-1)/(p-1)+p^(e*f)-1+
               p^2*(p^(e*f)-1)/(p-1)*(p^(e*f-1)-1)/(p^2-1);+p^(e*f+1)*(p^(e*f)-1)/(p-1);
       end if;  
    end if;
    error "NumberOfExtensions: Sorry, this case has not been implemented yet.";
  end if;
 
//-------------------------------------------------------------
// general case
   
  if F gt 0 then f := f*F;
    if n mod F ne 0 then error "NumberOfExtensions: ERROR, F must divide n.";
    end if; n := n div F; end if;
 
  if j ne -1 then
    return number_of_extensions(p,e,f,n,j);
  else
    return &+[Integers()|number_of_extensions(p,e,f,n,j) :
			j in possible_discriminants(R,n)];
  end if;

end intrinsic;

////////////////////////////////////////////////////////////////////////////
// HasRoot over an extension and IsIsomorphic
// not used, CF
//intrinsic HasRoot(f::RngUPolElt, R::Rng) -> BoolElt, RngElt
//{True if f has a root in R}
//   Ry := PolynomialRing(R); y := Ry.1;
//   return HasRoot(Ry!f);
//end intrinsic;
// not used, CF
//intrinsic Roots(f::RngUPolElt, R::Rng) -> [RngElt]
//{Computes the roots of f in R}
//   Ry := PolynomialRing(R); y := Ry.1;
//   coercible, g := IsCoercible(Ry,f);
//   if not coercible then
//     error "Roots: ERROR, incompatible input";
//   else
//     return Roots(g);
//   end if;
//end intrinsic;


function primitive_elt(S)
  repeat
    a := Random(S);
    if Valuation(a) eq 0 then
      f := CharacteristicPolynomial(a, PrimeRing(S));
    else
      f := 0;
    end if;
  until f ne 0;
  return a, f;
end function;
function is_isomorphic(R,S)
//{True if the p-adic rings R and S are isomorphic}

  if not Prime(R) eq Prime(S) then 
    return false;
  end if;

  if not InertiaDegree(R, PrimeRing(R)) eq InertiaDegree(S, PrimeRing(S)) then 
    return false; 
  end if;

  if not Degree(R, PrimeRing(R)) eq Degree(S, PrimeRing(S)) then 
    return false;
  end if;

//CF:????
//  if InertiaDegree(R, PrimeRing(R)) eq Degree(R, PrimeRing(R)) then
//    return true;
//  end if;

  if R eq S then 
    return true;
  end if;

  if Valuation(Discriminant(R, PrimeRing(R))) ne Valuation(Discriminant(S, PrimeRing(S))) then
    return false;
  end if;
  
  // TODO use distance as another cheap check.  
  prec := Minimum(S`DefaultPrecision,R`DefaultPrecision); 
  //"prec",prec; 
  R := ChangePrecision(R,prec);
  S := ChangePrecision(S,prec);
  _, f := primitive_elt(Integers(S));
  f := Polynomial(R, f);
  //"IsIsomorphic: Looking for roots of",f;  
  //Roots(f);
  ret :=  HasRoot(f);

  return ret;
end function;

intrinsic IsIsomorphic(R::RngPad,S::RngPad) -> BoolElt 
{True if the p-adic rings R and S are isomorphic}
  return is_isomorphic(S,R);
end intrinsic;
 
intrinsic IsIsomorphic(R::FldPad,S::FldPad) -> BoolElt
{True if the p-adic rings R and S are isomorphic}
  return is_isomorphic(S,R);
end intrinsic;

intrinsic IsIsomorphic(f::RngUPolElt, g::RngUPolElt) -> BoolElt
{True if the extensions generated by f and g over the common coefficient ring 
are isomrphic}

  R := CoefficientRing(Parent(f));
  S := CoefficientRing(Parent(g));
  prec := Minimum(S`DefaultPrecision,R`DefaultPrecision); 
  //"prec",prec; 
  R := ChangePrecision(R,prec);
  S := ChangePrecision(S,prec);
  if R ne S then
    error "IsIsomorphic: polynomials must have the same coefficient ring";
  end if;
  
  Rex := ext<R|f>;
  Rexz := PolynomialRing(Rex); z := Rexz.1;
  gg := Rexz!g;

  ret :=  HasRoot(gg);

  return ret;
  
end intrinsic;

////////////////////////////////////////////////////////////////////////////
// distance between two eisenstein polynomials of the same discriminant

intrinsic Distance(f::RngUPolElt, g::RngUPolElt) -> RngIntElt
{Distance between two Eisenstein polynomials over a local Ring/Field 
of the same degree and discriminant}

// check padic

  if not IsEisenstein(f) or not IsEisenstein(g) then 
    error "Distance: ERROR, the polynomials must be Eisenstein";
  end if;

  if Valuation(Discriminant(f)) ne Valuation(Discriminant(g)) then
    error "Distance: ERROR, the polynomials must have the same discriminant";
  end if;
  
  if Degree(f) ne Degree(g) then
    error "Distance: ERROR, the polynomials must have the same degree";
  end if;
  
  n := Degree(f);
  fs := Eltseq(f);
  gs := Eltseq(g);
  min, pos := Minimum([Valuation(fs[i]-gs[i])+(i-1)/n: i in [1..n]]);
  return min;
  
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// extensions of degree p with b=0

function delta(R, res_sys)

  F := ResidueClassField(R);
  p := Prime(R);
  Fy := PolynomialRing(F); y := Fy.1;
  for d in res_sys do
    g := y^p-y+F!d;
    if IsIrreducible(g) then
      return d;
    end if;
  end for;
  error "AllExtensions: are you sure the field contains the p-th roots of unity ?";
end function;

function deg_p_b_eq_0(R, galois)

  hasproot :=  HasPRoot(R);  

  if galois and not hasproot then return []; end if;
//R;
  e := RamificationIndex(R);
  f := InertiaDegree(R);
  p := Prime(R);
  pi := UniformizingElement(R);

  L0 := [ r : r in [1..(Ceiling(p*e/(p-1))-1)] | r mod p ne 0];
  
  res_sys := ResidueSystem(R);
  if hasproot then
    d := delta(R, res_sys);
  end if;
  phi_list := [];
  C := CartesianPower([1..#res_sys], #L0);

  Rx := PolynomialRing(R); x := Rx.1;

  for c in C do
    phi := x^p+pi;
    phi := phi + &+[ res_sys[c[i]]*pi^(L0[i]+1) : i in [1..#L0]];     
    if hasproot then
      for k := 0 to p-1 do
      Append(~phi_list, phi+k*d*pi^(Integers()!(p*e/(p-1))+1));
      end for;
    else
      Append(~phi_list,phi);
    end if;
  end for; 
  return phi_list;
end function;

////////////////////////////////////////////////////////////////////////////
// extensions of degree p, uses deg_p_b_eq_0 for b=0

function deg_p_b_ne_0_is_galois(R, j, z)
  
  p := Prime(R);
  a := j div p;
  b := j mod p;
//"a",a;
//"b",b;

  if (a+b) mod (p-1) ne 0 then return false, 0; end if;

  F := ResidueClassField(R);
  Fy := PolynomialRing(F); y := Fy.1;
  zz := F!z;  
//Factorization(y^(p-1)+(-1)^(a*p+1)*b*(zz));
  //if IsIrreducible(y^(p-1)+(-1)^(a*p+1)*b*(zz)) then return false, 0; end if; 
  if not HasRoot(y^(p-1)+(-1)^(a*p+1)*b*(zz)) then return false, 0; end if; 

  res_sys := ResidueSystem(R);

  for d in res_sys do
    g := y^p+(-1)^(a*p+1)*b*(zz)*y+F!d;
//b*(zz)*y;
//"a",a;
//"b",b;
//zz;
//g;
//Factorization(g);
    if IsIrreducible(g) then
//"irreducible:",g;
      return true, d;
    end if;
  end for;
  error "AllExtensions: oh, oh, the whole theory of extensions of degree p is wrong";

end function;


function deg_p_j(R, j, galois)
//"j",j;
  p := Prime(R);
  a := j div p;
  b := j mod p;
  
  if b eq 0 then return deg_p_b_eq_0(R, galois); end if;

  e := RamificationIndex(R);
  f := InertiaDegree(R);
  pi := UniformizingElement(R);

  Rx := PolynomialRing(R); x := Rx.1;
  L0 := [ r : r in [1..(Ceiling((a*p+b)/(p-1))-1)] | (b+r) mod p ne 0];
//"L0",L0,Ceiling(a*p+b*e/(p-1))-1;

  res_sys := ResidueSystem(R);
  C := CartesianPower([1..#res_sys], #L0);
  phi_list := [];
//"res_sys",res_sys; 
  for s := 2 to #res_sys do
    phi1 := x^p+res_sys[s]*pi^(a+1)*x^b+pi;
    is_galois, d := deg_p_b_ne_0_is_galois(R, j, res_sys[s]);
    if #L0 eq 0 then
      if is_galois then
        t := Integers()!(a+(a+b)/(p-1));
        for k := 0 to p-1 do
          Append(~phi_list, phi1+k*d*pi^(t+1));
        end for;
      elif not galois then
        Append(~phi_list, phi1);
      end if;      
    else
      for c in C do
//"c",c;
        phi2 := phi1 + &+[ res_sys[c[i]]*pi^(L0[i]+1) : i in [1..#L0]];
        if is_galois then
          t := Integers()!(a+(a+b)/(p-1));
          for k := 0 to p-1 do
            Append(~phi_list, phi2+k*d*pi^(t+1));
          end for;
        elif not galois then
          Append(~phi_list, phi2);
        end if;      
      end for;
    end if;
  end for;
 
  return phi_list;
end function;

function all_ram_extensions_of_deg_p_j(R, j, galois)
  return [TotallyRamifiedExtension(R,f): f in deg_p_j(R, j, galois)];
end function;

//////////////////////////////////////////////////////////////////////////////////////////

function deg_p(R, galois)

  p := Prime(R);

  discs := possible_discriminants(R, p);
//discs;
  exts := [];
  for j in discs do
    Append(~exts,deg_p_j(R, j, galois));
  end for;
  return exts;
return galois;
end function;

function all_ram_extensions_of_deg_p(R, galois)
  return [TotallyRamifiedExtension(R,f): f in Flat(deg_p(R, galois))];
end function;


//////////////////////////////////////////////////////////////////////////////////////////

function is_isomorphic_in_list(f,L) // k extension // L list of extensions
  for l in L do lx := PolynomialRing(l);
    if HasRoot(lx!f) then return true; end if; end for;
  return false;
end function;

function generates_number_of_extensions(k)
  kx := PolynomialRing(k); f := DefiningPolynomial(k); //  "root finding";
  n := #Roots(kx!f);  return Degree(f) div n;
end function;

function minimal_coefficient_valuations(R, pm, j)
  a,b := Quotrem(j,pm);
  l := [2];
  for i in [1..pm-1] do
    if i le b then 
      Append(~l,Maximum(2+a-Valuation(R!i),1));
    else 
      Append(~l,Maximum(1+a-Valuation(R!i),1));
    end if;
  end for;
  return l;
end function;

function all_ram_extensions_of_deg_p_m_j(R, pm, j)
//"all_ram_extensions_of_deg_p_m_j",R, pm, j;
  L := [];
  a,b := Quotrem(j,pm);
  res_sys := ResidueSystem(R);
  Rx := PolynomialRing(R); x := Rx.1;
  pi := UniformizingElement(R);
  l := minimal_coefficient_valuations(R, pm, j);
//"l :: ",l;

  exts_number :=  NumberOfExtensions(R, pm : E:=pm, j:=j, Galois:=false);
//"exts_number: ",exts_number;

  c := Ceiling(1+2*j/pm);
  range := c-Minimum(l);
  res_pow := CartesianPower(res_sys,pm*range);
  exts_found := 0;
  b_exp := Maximum(1+a-Valuation(R!b),1);
  for r in res_pow do
//"r :: ",r;
    h := x^pm+&+[&+[x^(i-1)*r[(pm-i+1)+(j-1)*pm]*pi^(l[i]+j-1):i in [1..pm]]:j in [1..range]];
    for rconst in [2..#res_sys] do
      g := h + pi*res_sys[rconst];
      if b eq 0 then
        f := g;
//"f :: ",f, "disc :: ",Valuation(Discriminant(f));
        if not is_isomorphic_in_list(f,L) then
          k := TotallyRamifiedExtension(R,f);
          Append(~L,k);
//"L ::",L;
          exts_found := exts_found+generates_number_of_extensions(k);
//"exts_found :: ";exts_found;
          if exts_found ge exts_number then
            return L;
          end if;
        end if;
      else
        for rb in [2..#res_sys] do
          f := g + x^b*pi^b_exp*res_sys[rb];
//"f :: ",f, "disc :: ",Valuation(Discriminant(f));
          if not is_isomorphic_in_list(f,L) then
            k := TotallyRamifiedExtension(R,f);
            Append(~L,k);
//"L ::",L;
            exts_found := exts_found+generates_number_of_extensions(k);
//"exts_found :: ";exts_found;
            if exts_found ge exts_number then
              return L;
            end if;
          end if;
        end for;
      end if;
    end for;
  end for;
  error "Internal accounting problem with all_ram_extensions_of_deg_p_m_j";
end function;

//////////////////////////////////////////////////////////////////////////////////////////

function primitive_element(R)
// a representative of a generator of the multiplicative group of the
// residue class field.

   Ry := PolynomialRing(R); y := Ry.1;
   rcf := ResidueClassField(R);
   rho := PrimitiveElement(rcf);
   zeta := (R!rho)^(Prime(R)^Precision(R));
   return zeta;

end function;

function tamely_ramified(R, n, Galois)

   p := Prime(R);
   pi := UniformizingElement(R);
   f := InertiaDegree(R);
   q := p^f;
   g := GCD(n,q-1);
   m := n div g;
   if Galois and m ne 1 then 
     return [];
   end if;
   
   Ry := PolynomialRing(R); y := Ry.1;
   zeta := primitive_element(R);
   ret := [];
   for r := 0 to g-1 do
     Append(~ret,y^n+zeta^r*pi);
   end for;
   return ret;
end function;

function all_tamely_ramified_extensions(R, n, Galois)
  return [TotallyRamifiedExtension(R,f): f in tamely_ramified(R, n, Galois)];
end function;
  
//////////////////////////////////////////////////////////////////////////////////////////

function remove_isomorphic(exts)
  axts := [exts[1]];
  for ext in exts do
    add := true;
    for axt in axts do
      if add eq true then
        if IsIsomorphic(axt,ext) then
          add := false;
        end if;
      end if;
    end for;
    
    if add eq true then
//"+";
      Append(~axts,ext);
else
//"-";
      end if;
  end for;
  return axts;
end function;

//////////////////////////////////////////////////////////////////////////////////////////

intrinsic AllExtensions(R::RngPad, n::RngIntElt :
			E:=0, F:=0, Galois := false, vD:=-1, j:=-1 ) -> []
{Returns all extensions (up to isomorphism) of degree n of the p-adic ring R,
 with given ramification degree E and inertia degree F (zero for arbitrary).
 When E or F is given, can also restrict to discriminant valuation vD,
 and in the case where F is 1 this can also be specified by j with vD=n+j-1.
 If Galois := true only normal extensions are returned.}

  if n eq 1 then return [R]; end if;
  require Precision(R) lt Infinity() :
   "The ring needs to be a finite precision ring";
  deg:=Degree(R); f:=InertiaDegree(R); e:=RamificationIndex(R); p:=Prime(R);

  if E ne 0 and F ne 0 then
    if F*E ne n then error "AllExtensions: F*E must equal n"; end if; end if;
   if E ne 0 then 
    if n mod E ne 0 then error "AllExtensions: E must divide n."; end if;
    F := n div E;
  end if;
  if F ne 0 then 
    if n mod F ne 0 then error "AllExtensions: F must divide n."; end if;
    E := n div F;
  end if;

  if E eq 0 and F eq 0 and j ne -1 then
   error "AllExtensions: cannot have j ne -1 when E and F are both 0"; end if;
  if E eq 0 and F eq 0 and vD ne -1 then // maybe this is over-careful now
   error "AllExtensions: cannot have vD ne -1 when E and F are both 0"; end if;

  if E eq 0 and F eq 0 then exts:=[];
   vprint ClassField,2: "AllExtensions: of degree",n; IndentPush();    
   for F in Divisors(n) do
    nexts:=Flat(AllExtensions(R,n:F:=F,Galois:=Galois,vD:=vD));
    Append(~exts,nexts); end for;
   IndentPop(); exts:=Flat(exts); return exts; end if;
  
  if F ne 1 and j ne -1 then error
   "j must be -1 (unspecified) for extensions with F not equal to 1"; end if; 
  if vD ne -1 and j ne -1 and j ne vD-n+1 then
   error "AllExtensions: vD and j not compatible."; end if;
  if vD ne -1 then j:=vD-n+1; end if; if j ne -1 then vD:=j+n-1; end if;
  if E eq 1 and vD gt 0 then return []; end if;
  if F eq 1 and vD ge 0 and not OreConditions(R,n,vD-n+1)
   then return []; end if;
  if vD ne -1 and vD mod F ne 0 then return []; end if;

  vprint ClassField,1: "AllExtensions: E =",E," F =",F," vD =",vD," j =",j;

  exts := [];
  if F gt 1 then // totally unramified part
   vprint ClassField,2: "AllExtensions: unramified part of degree",F;
    IndentPush();    
    exts := AllExtensions(UnramifiedExtension(R,F),n div F:
			  E:=E,F:=1,Galois:=Galois,vD:=vD div F);
    IndentPop(); return exts; end if;

  if E ne p^Valuation(E,p) then // tamely ramified part
    vprint ClassField,2:
    "AllExtensions: tamely ramified Part of degree", E div p^Valuation(E,p);
    // tamely ramified only
    if GCD(E,p) eq 1 then //"tame";
     if false and j ge 0 then return []; // MW: I don't understand j>=0?
      else return all_tamely_ramified_extensions(R,E,Galois); end if;
    else // also a wild part
      tame_E := E div p^Valuation(E,p);
      IndentPush();    
      exts := Flat([AllExtensions(L,E div tame_E:
				  E:=E div tame_E,F:=1,Galois:=Galois,j:=j):
               L in  all_tamely_ramified_extensions(R,tame_E,Galois)]);
      IndentPop();
      if Galois then 
        exts := [ext:ext in exts|IsNormal(ext,R)];
      end if;
     vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
      return exts;
    end if;  
  end if;

  // wildly ramified degree p 
  if E eq p then
    if j eq -1 then
      vprint ClassField,2:
      "AllExtensions: normal, wildly ramified part of degree",n;
      exts := Flat(all_ram_extensions_of_deg_p(R, Galois));
     vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
      return exts;
    else
      vprint ClassField,2:
      "AllExtensions: normal, wildly ramified part of degree",n," and j =",j;
      exts := all_ram_extensions_of_deg_p_j(R, j, Galois);
     vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
      return exts;
    end if;
  end if;

  // normal degree p^m 
  if Galois then
    vprint ClassField,2:
    "AllExtensions: normal, wildly ramified part of degree ",n;
    if j eq -1 then
      IndentPush();    
      exts := Flat([AllExtensions
                    (L,E div p:E:=E div p,F:=1,Galois:=Galois,j:=j):
             L in all_ram_extensions_of_deg_p(R, Galois)]);
      IndentPop();
      vprint ClassField,2:"AllExtensions:",#exts,"extensions found";      
      vprint ClassField,2:"AllExtensions: checking for normality ...";      
      exts := [ext:ext in exts|IsNormal(ext,R)];
      vprint ClassField,2:"AllExtensions: removing isomorphic extensions ...";
      exts := remove_isomorphic(exts);
     // vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
      return exts;
    else
      "AllExtensions: this case has not been implemented yet.";
    end if;
  end if;
  
  // general p^m
  if j eq -1 then
    vprint ClassField,2:"AllExtensions: wildly ramified part of degree ",n;
    exts := [];
    IndentPush();    
    for j in possible_discriminants(R,n) do // why not call all_ram_extens?
      Append(~exts,AllExtensions(R,n : E:=n,j:=j)); end for;
    IndentPop();
    //vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
    return exts;
  else
    vprint ClassField,2:
    "AllExtensions: wildly ramified part of degree ",n," and j =",j;
    exts := all_ram_extensions_of_deg_p_m_j(R,n,j);
    //vprint ClassField,2:"AllExtensions:",#exts,"extensions found";   
    return exts;
  end if;

  error "AllExtensions: this case has not been implemented yet.";
end intrinsic;


intrinsic AllExtensions(R::FldPad, n::RngIntElt :
			E:=0, F:=0, Galois := false, vD:=-1, j:=-1 ) -> []
{Returns all extensions of degree n of the p-adic ring R, with given
 ramification degree E and inertia degree F (zero for arbitrary).
 When E or F is given, can also restrict to discriminant valuation vD,
 and in the case where F is 1 this can also be specified by j with vD=n+j-1.
 If Galois := true only normal extensions are returned.}
  require Precision(R) lt Infinity() :
   "The field needs to be a finite precision field";
  return AllExtensions(Integers(R),n:E := E, F:= F,Galois:=Galois,vD:=vD,j:=j);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////

intrinsic Discriminant(S::FldPad, R::FldPad) -> RngPadElt
{}
//CF: we cannot (currently) use
// Discriminant(DefiningPolynomial(S, R));
// as DefiningPolynomial return non-squarefree polynomials.
// Example:
//  Q2:=pAdicField(2,40);
//  T:=UnramifiedExtension(Q2,2);
//  R := PolynomialRing(T); z := R.1;
//  E:=ext<T|z^3-2>;
//  Discriminant(E,Q2);
// DefiningPolynomial(E, Q2) is CharPoly(E2.1, Q2) and this is NOT
// primitive over Q2. 

  d := S!1;
  exp:=1;
  while Degree(S, R) ne 1 do
    d := Discriminant(DefiningPolynomial(S))^exp*Norm(d);
    exp:=exp*Degree(S); S := CoefficientRing(S); // MW Aug 2015
  end while;
  return d;
end intrinsic;
intrinsic Discriminant(S::RngPad, R::RngPad) -> RngPadElt
{Discriminant of the extension S/R}
  d := S!1;
  exp:=1;
  while Degree(S, R) ne 1 do
    d := Discriminant(DefiningPolynomial(S))^exp*Norm(d);
    exp:=exp*Degree(S); S := CoefficientRing(S); // MW Aug 2015
  end while;
  return d;
end intrinsic;


intrinsic Discriminant(R::RngPad) -> RngPadElt
{Discriminant of R/BaseRing(R)}
  return Discriminant(DefiningPolynomial(R));
end intrinsic;


intrinsic HasRootOfUnity(L::RngPad, n::RngIntElt) -> BoolElt
{Return whether the local ring or field L contains the n-th roots of unity}
 
  p := Prime(L);
  if p eq n then 
    return HasPRoot(L);
  end if;
  
  error "sorry not implemented yet";
end intrinsic;


intrinsic Composite(R::RngPad,S::RngPad) -> RngPad
{The composite of R and S.  R and S must be normal.}

  if not IsNormal(R) or not IsNormal(S) then 
    error "CompositeFields: R and S must be normal";
  end if;

  Ry := PolynomialRing(R); y := Ry.1;
  phi := DefiningPolynomial(S);
  if not IsCoercible(Ry,phi) then
    error "IsCoercible: the defining polynomial of S must be coercible into R[x].";
  end if;
  
  _,_,cert := Factorization(Ry!phi:Extensions:=true);
 
  return cert[1]`Extension;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// NormGroup, NormEquation
////////////////////////////////////////////////////////////////////////////////
intrinsic NormGroup(R::FldPad,m::Map) -> GrpAb, Map
{The norm group of R as a subgroup of the unit group of its base field/ring B; m : UnitGroup(B) -> B}
//"NormGroup: begin";
  gens := UnitGroupGenerators(R);
  B := Codomain(m);
  U := Domain(m);
  Ugens := [ Norm(g,B)@@m : g in gens];
  S, mS := sub<U | Ugens>;
//"NormGroup: end";
  return S, mS;
end intrinsic;

intrinsic NormGroup(R::RngPad,m::Map) -> GrpAb, Map
{"}
//"NormGroup: begin";
  gens := UnitGroupGenerators(R);
  B := Codomain(m);
  U := Domain(m);
  Ugens := [ Norm(g,B)@@m : g in gens];
  S, mS := sub<U | Ugens>;
//"NormGroup: end";
  return S, mS;
end intrinsic;


intrinsic IsAbelian(L::FldPad,K::FldPad) -> BoolElt
{True if L over K is an abelian extension}
  U, m := UnitGroup(K);
  N := NormGroup(L,m); 
  if Degree(L,K) eq Index(U,N) then 
    return true;
  elif Degree(L,K) gt Index(U,N) then
    return false;
  else
    error "IsAbelian: ERROR, index of norm group is too large";
  end if;
  
end intrinsic;

intrinsic NormEquation(R::FldPad,m::Map,b::RngElt) -> BoolElt, RngElt
{Given the map m : UnitGroup(B) -> B and an element b in B, this solves Norm(a) = b for a in R}
  bool, b := IsCoercible(Codomain(m), b);
  require bool: "The third argument is not in the codomain of the second argument";

  gens := UnitGroupGenerators(R:Raw:=true);
  B := Codomain(m);
  U := Domain(m);
  F := FreeAbelianGroup(#gens);
  mF := hom<F -> U|[ Norm(g,B)@@m : g in gens]>;
  if not b@@m in Image(mF) then
    return false, _;
  else 
    aFseq := Eltseq(b@@m@@mF);
    a := &*[gens[i]^aFseq[i]: i in [1..#gens]];
    return true, a;
   // , Kernel(mF); 
  end if; 
end intrinsic;

intrinsic NormEquation(R::RngPad,m::Map,b::RngElt) -> BoolElt, RngElt
{"}
  bool, b := IsCoercible(Codomain(m), b);
  require bool: "The third argument is not in the codomain of the second argument";

  gens := UnitGroupGenerators(R:Raw:=true);
  B := Codomain(m);
  U := Domain(m);
  F := FreeAbelianGroup(#gens);
  mF := hom<F -> U|[ Norm(g,B)@@m : g in gens]>;
  if not b@@m in Image(mF) then
    return false, _;
  else 
    aFseq := Eltseq(b@@m@@mF);
    a := &*[gens[i]^aFseq[i]: i in [1..#gens]];
    return true, a;
   // , Kernel(mF); 
  end if; 
end intrinsic;


intrinsic NormKernel(m1::Map,m2::Map) -> GrpAb
{m1 : UnitGroup(R1) -> R1,
 m2 : UnitGroup(R2) -> R2.  Return the kernel of the Norm map from
UnitGroup(R1) to UnitGroup(R2)}
  
  R1 := Codomain(m1);
  U1 := Domain(m1);
      
  R2 := Codomain(m2);
  U2 := Domain(m2);

  nrgens1 := #Generators(U1);
  m :=  hom<U1 -> U2 |[ Norm(m1(U1.i),R2)@@m2 : i in [1..nrgens1]]>;
  return Kernel(m);

end intrinsic;


intrinsic Norm(m1::Map,m2::Map,G::GrpAb) -> GrpAb
{m1 : UnitGroup(R1) -> R1,
 m2 : UnitGroup(R2) -> R2,
 R1 extension of R2,
 G subgroup of UnitGroup(R1).
 Returns Norm(G).} 
 
  R2 := Codomain(m2);
  U2 := Domain(m2);
     
  S, mS := sub< U2|[ Norm(m1(g),R2)@@m2 : g in Generators(G)]>;
  return S,mS;

end intrinsic;


intrinsic NormEquation(m1::Map,m2::Map,G::GrpAb) -> GrpAb, Map
{m1 : UnitGroup(R1) -> R1,
 m2 : UnitGroup(R2) -> R2,
 R1 extension of R2,
 G subgroup of UnitGroup(R2).  
 Tries to find a subgroup S of UnitGroup(R1) such that
 Norm(S,m2) is G.}

  R1 := Codomain(m1);
  U1 := Domain(m1);

  R2 := Codomain(m2);
  U2 := Domain(m2);
 
  nrgens1 := #Generators(U1);
//"U1",U1;
//"U2",U2;
//[ <U1.i,Norm(m1(U1.i),R2)@@m2> : i in [1..nrgens1]];
  m := hom<U1 -> U2 |[ <U1.i,Norm(m1(U1.i),R2)@@m2> : i in [1..nrgens1]]>;

  normimage := Image(m); // check whether G in Norm(R1)
  if not &and[g in normimage : g in Generators(G)] then
    error "NormEquation: ERROR, G must be contained in Norm(R1).";
  end if;
  //"blase";
  ker := Kernel(m);    
  if not m(ker) eq sub<U2 | U2.0> then // check whether Norm(ker) = {1}
    error "NormEquation: ERROR in computation of kernel.";
  end if;
//"kernel",ker;
//"kernel index", Index(U1,ker);  
  Sgens := [U1!g: g in Generators(ker)];
//"kernel gens", [U1!g: g in Generators(ker)];  
//"norms of kernel gens in G ?",[Norm(m1(g))@@m2 in G: g in Generators(ker)];
//"other gens",[g@@m : g in Generators(G)];  
//"norms of other gens in G ?",[Norm(m1(G.i@@m))@@m2 in G: i in [1..#Generators(G)]];
//"differences of elts", [ Valuation(m2(G.i)-Norm(m1(G.i@@m),R2)): i in [1..#Generators(G)]];
//Sgens cat:= [g@@m : g in Generators(G)];
  Sgens cat:= [G.i@@m : i in [1..#Generators(G)]];;
  S, mS := sub<U1|Sgens>;
//"norms of Sgens in G ?",[Norm(m1(g))@@m2 in G: g in Sgens];
//"norms of S gens in G ?",[Norm(m1(g))@@m2 in G: g in Generators(S)];
//"[U2:G]",Index(U2,G);
//"[U1:Norm^-1(G)]",Index(U1,S);
//"[U2:Norm(Norm^-1(G))]",Index(U2,Norm(m1,m2,S));
//"G",G;
//"Norm(Norm^-1(G))",S;
//"S subset G"; S subset G;
//"G subset S"; G subset S;
//"S/G", quo<S|sub<S|[S!g: g in Generators(G)]>>;
  return S, mS;

end intrinsic;


intrinsic NormGroupDiscriminant(m::Map,G::GrpAb) -> RngIntElt
{The valuation of the discriminant of the class field corresponding to the 
subgroup G of the unit group of a local ring/field}
// very slow and not smart at all.
// TODO speedup
// OK for degree p
// TODO should return pi^discval

  R := Codomain(m);
  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));
  U := Domain(m);
  
  Q, mQ := quo<U|G>;
//#Q; 
  if #Q eq p then
    gens := PrincipalUnitGroupGenerators(R);
    levs := [ Valuation(g-1) : g in gens | mQ(g@@m) ne  Q.0];
//"levs",levs;
    v := Maximum(levs);
    vprint ClassGroup,3: "NormGroupDiscriminant: ramification number",v;
    discval := (p-1)*(v+1);
    return discval;
  end if;

//error "grosse scheisse";

  Qexp := Exponent(Q);
  maxlevelbound := Floor(p*e/(p-1))+e*Qexp;
  
  Rgens := [m(g) : g in Generators(G)];
  
  i := 1;
  discval := 0;
  hiU := 1;
  print "NormGroupDiscriminant";
  repeat
    hiU1 := hiU;  
    Ui, mi := UnitGroup(R,i);
    Gi := sub<Ui|[g@@mi : g in Rgens]>;
    hiU := Index(Ui,Gi);
    discval := discval+i*(hiU-hiU1);
    "+",i,"*(",hiU,"-",hiU1,") =",discval;
    i +:=1;
  until i eq maxlevelbound;
  //until hiU eq hiU1;
  return discval;

end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
//
//////////////////////////////////////////////////////////////////////////////////
/*
function traces_from_poly(Phi) 

  n := Degree(Phi);
  
  t := function(i)
    if i lt 0 then
      return 0;
    else
      return Coefficient(Phi,i);
    end if;
  end function;
  
  S := [];

  for k := 1 to n do
    Sk := -k*t(n-k);
    for i := 1 to Minimum(n,k-1) do
      Sk := Sk - t(n-i)*S[k-i];
    end for;
    Append(~S,Sk);
  end for;
  return S;
end function;

poly_from_traces := function(S)

  n := #S;
  Tn := [];
  
  for k := 1 to n do
    Tnk := -S[k];
    for i := 1 to k-1 do
      Tnk := Tnk - Tn[i]*S[k-i];
    end for;
    Tnk := Tnk div k;
    Append(~Tn,Tnk);
  end for;
  Tn := Reverse(Tn);
  Append(~Tn,Parent(S[1])!1);
  return PolynomialRing(Parent(S[1]))!Tn;
  
end function;

function chi(Phi, traces_Phi, theta)
  
  n := Degree(Phi);
  S := [];

  pow := 1;
  for i := 1 to n do
    pow := pow*theta mod Phi;
    Si := 0;
    Si := n*Coefficient(pow,0);
    for j := 1 to Degree(pow) do
      if Coefficient(pow,j) ne 0 then
        Si +:= traces_Phi[j]*Coefficient(pow,j);
      end if;
    end for;
    Append(~S,Si);
  end for;
  return Parent(Phi)!poly_from_traces(S);
end function;
*/
////////////////////////////////////////////////////////////////////////////////////////////////


function class_field_degree_p(m, G, j)
//deg_p_j(R, j, galois)
//"j",j;
  
  Q := Codomain(m);
  R := Integers(Q);
  U := Domain(m);

  p := Prime(R);
  a := j div p;
  b := j mod p;
  v := j div (p-1);


  relation_matrix := rel_mat_map(m);

  //if b eq 0 then return deg_p_b_eq_0(R, galois); end if;

  e := RamificationIndex(R);
  f := InertiaDegree(R,PrimeRing(R));
  pi := UniformizingElement(R);

//"ClassField: e =",e," f =",f," a =",a," b =",b;

  Rx := PolynomialRing(R); x := Rx.1;
  L0 := [ r : r in [1..(Ceiling((a*p+b)/(p-1))-1)] | (b+r) mod p ne 0];
  FE := Fe(R);
//"ClassField: L(0) =", L0; 
//"ClassField: Fe =",FE;
//"L0",L0,Ceiling(a*p+b*e/(p-1))-1;

  res_sys := ResidueSystem(R);
  
  //C := CartesianPower([1..#res_sys], #L0);
  
  //phi_list := [];
  
  rel_mat_G := relation_matrix(G);
  vprint ClassField,2:"ClassField: relation matrix of G",rel_mat_G;
  // find the relevant column of the relation matrix
  for i in [1..NumberOfColumns(rel_mat_G)] do
    if rel_mat_G[i][i] ne 1 then
      pos_j := i;
    end if;
  end for;

//"res_sys",res_sys; 
  if b eq 0 then // pure case
    level_nr := Floor((pos_j-3)/f)+1;
//"level_nr",    level_nr;
    phi := x^p+pi;
    K := TotallyRamifiedExtension(Q, phi);
    rel_mat_K := relation_matrix(NormGroup(K,m));
     d := delta(R, res_sys);
  else
    level_nr := Floor((pos_j-3)/f)+1;
    success := false;
    vprint ClassField,2:"ClassField: unit level",FE[level_nr],"- coefficient of x ^",b;
    pos := 2+(level_nr-1)*f+1;
    for i := 2 to #res_sys do
      is_galois, d := deg_p_b_ne_0_is_galois(R, j, res_sys[i]);
      if is_galois then
        phi := x^p+res_sys[i]*pi^(a+1)*x^b+pi;
        vprint ClassField,2:"ClassField: trying",phi;
        K := TotallyRamifiedExtension(Q, phi);
        rel_mat_K := relation_matrix(NormGroup(K,m));
        vprint ClassField,2:"ClassField: with group",rel_mat_K;
        if Submatrix(rel_mat_K,pos,pos_j,f,1) eq Submatrix(rel_mat_G,pos,pos_j,f,1) then
          //rel_mat_K[pos_j][pos_j] eq rel_mat_K[pos_j][pos_j] then
          s := i;
          success := true;
          vprint ClassField,2:"ClassField: unit level",FE[level_nr],"- DONE";
          break;
        end if;
      end if;
    end for;
    if not success then error "ClassField: ERROR, no approximation found"; end if;
  end if;

  for l in L0 do
  //"l",l;
    level_nr -:= 1;
    vprint ClassField,2:"ClassField: unit level",FE[level_nr],"- const term exp",l+1;
    pos := 2+(level_nr-1)*f+1;
    if  Submatrix(rel_mat_K,pos,pos_j,f,1) eq Submatrix(rel_mat_G,pos,pos_j,f,1) then
       // phi already does the job for this step
       vprint ClassField,2:"ClassField: unit level",FE[level_nr],"- DONE";
    else
      success := false;
      for i := 2 to #res_sys do
        rho := res_sys[i];
        tmp_phi := phi + rho*pi^(l+1);
        vprint ClassField,2:"ClassField: trying",tmp_phi;      
        K := TotallyRamifiedExtension(Q, tmp_phi);
        NG := NormGroup(K,m);
        rel_mat_K := relation_matrix(NG);
        vprint ClassField,2:"ClassField: with group",rel_mat_K;
        if  Submatrix(rel_mat_K,pos,pos_j,f,1) eq Submatrix(rel_mat_G,pos,pos_j,f,1) then
      //rel_mat_K[2+level_nr][pos_j] eq rel_mat_K[pos_j][pos_j] then
          phi := tmp_phi;
          success := true;
          vprint ClassField,2:"ClassField: unit level",FE[level_nr],"- DONE";
          //print "ClassField: Level#",level_nr,"done";
          break;
        end if;
      end for;  
      if not success then error "ClassField: ERROR, no approximation found"; end if;
    end if;   
  end for;  

  // TODO direct computation of the additional coefficient.
  // const := Coefficient(phi,0);
  // needs representation sorted by level. 
  
  level_nr -:= 1;
  vprint ClassField,2:"ClassField: norm pi - const term exp",v+1;
  if  Submatrix(rel_mat_K,1,pos_j,f,1) eq Submatrix(rel_mat_G,1,pos_j,f,1) then
    // phi already does the job for this step
    vprint ClassField,2:"ClassField: norm pi - DONE";
  else         
    success := false;
    for k := 1 to p-1 do
      tmp_phi := phi +  k*d*pi^(v+1);
      vprint ClassField,2: "ClassField: trying",pi+k*d*pi^(v+1);
      K := TotallyRamifiedExtension(Q, tmp_phi);
      rel_mat_K := relation_matrix(NormGroup(K,m));
      vprint ClassField,2:"ClassField: with group",rel_mat_K;
      if  Submatrix(rel_mat_K,1,pos_j,f,1) eq Submatrix(rel_mat_G,1,pos_j,f,1) then
    //rel_mat_K[2+level_nr][pos_j] eq rel_mat_K[pos_j][pos_j] then
        phi := tmp_phi;
        success := true;
        vprint ClassField,2:"ClassField: norm pi - DONE";
        break;
      end if;
     end for;  
    if not success then error "ClassField: ERROR, no approximation found"; end if;
  end if;

  return K;

  /*



  
    is_galois, d := deg_p_b_ne_0_is_galois(R, j, res_sys[s]);
    if #L0 eq 0 then
      if is_galois then
        t := Integers()!(a+(a+b)/(p-1));
        for k := 0 to p-1 do
          Append(~phi_list, phi1+k*d*pi^(t+1));
        end for;
//      elif not galois then
//        Append(~phi_list, phi1);
      end if;      
    else
      for c in C do
//"c",c;
        phi2 := phi1 + &+[ res_sys[c[i]]*pi^(L0[i]+1) : i in [1..#L0]];
        if is_galois then
          t := Integers()!(a+(a+b)/(p-1));
          for k := 0 to p-1 do
            Append(~phi_list, phi2+k*d*pi^(t+1));
          end for;
        //elif not galois then
        //  Append(~phi_list, phi2);
        end if;      
      end for;
    end if;
  end for;
 
  return phi_list;
*/


end function;


function class_field_p_m(m, G : brute := false)
//intrinsic class_field_p_m(m::Map,G::GrpAb:brute := false) -> .
//{Let K be a p-adic field and U,m:=UnitGroup(K).
//Let G be a subgroup of U of finite index.
//Return a list of extensions of K, containing the class fields 
//corresponding to the cyclic factors of U/G}
  
  R := Codomain(m);
  U := Domain(m);
  p := Prime(R);
  B := BaseRing(R);
  e := RamificationIndex(R,B);
  
  Q, mQ := quo<U | G>;

  vprint ClassField, 2:"ClassField: corresponding to", G;
  vprint ClassField, 2:"ClassField: over\n", R;
 
  if Order(Q) eq 1 then
    vprint ClassField, 2:"ClassField: trivial case";
    return R;
  end if;

  if Order(Q) eq Infinity() then 
    error "ClassField: group must have finite index in the unit group";
  end if;

  
  relation_matrix_map := rel_mat_map(m);
  relation_matrix := relation_matrix_map(G);
  vprint ClassField, 3:"ClassField: relation matrix",relation_matrix;
  
  if Order(Q) eq p then
    discval :=  NormGroupDiscriminant(m,G);
    j := discval-p+1;
    vprint ClassField, 2: "ClassField: over", R;
    vprint ClassField, 2: "ClassField: computing class field of degree",p;
    vprint ClassField, 2: "ClassField: and valuation of discriminant",discval;
    return class_field_degree_p(m, G, j);
  end if;

  // use extension of R rather than towers of extensions - 
  // this yields faster unit group computations

  if IsCyclic(Q) then
    //IndentPush();
    vprint ClassField, 2: "ClassField: computing class field of degree",Order(Q);
    h := Q.1@@mQ;
    Hgens := [U!g: g in Generators(G)] cat [h*p];
    H := sub< U | Hgens>;
    if Index(U,H) ne p then
    //relation_matrix(H),"=?=",relation_matrix(G);
      error "ClassField: ERROR, a wrong subgroup was computed.";
    end if;
    //IndentPush();
    K := class_field_p_m(m,H);
    //IndentPop();
    eK := RamificationIndex(K, PrimeRing(K));
    //(p+1)*p*e/(p-1); 
    //unitprec := Integers()!Minimum(Precision(K),Ceiling((p+1)*p*eK/(p-1)));
    //unitprec := Integers()!Minimum(Precision(K),Ceiling((p+1)*p*eK));
    unitprec := Precision(K);
    vprint ClassField, 3:"ClassField: using precision",unitprec;
    IndentPush();
      UK, mUK := UnitGroup(K);
    IndentPop();
    GK := NormEquation(mUK,m,G);
    //print "ClassField: Solution of norm equation:";
    relation_matrix := rel_mat_map(mUK);
    //print relation_matrix(GK); 
    //print GK;
    //printf "ClassField: Subgroup with index %o of:", Index(UK,GK);
    //print UK;
    //print "ClassField: with generators:";
    //print [mUK(UK.i): i in [1..#Generators(UK)]];
    //print "ClassField: with generators:";
    //print PrincipalUnitGroupGenerators(K);
    if Norm(mUK,m,GK) ne G then
//"N(UK)",Norm(mUK,m,UK); 
//"norm",Norm(mUK,m,GK);
//"group",G;
      error "ClassField: ERROR, solution of NormEquation is false.";
    end if;
      if Index(UK,GK) eq p then
        //IndentPush();
           L := class_field_p_m(mUK, GK);
        //IndentPop();
      else
        L := class_field_p_m(mUK, GK);
      end if;
      //IndentPop();
    return L;
  end if;

  // split up the extension into several cyclic extensions
  error "ClassField: SORRY, this case has not been implemented yet";
  
end function;

/////////////////////////////////////////////////////////////////////////////////

intrinsic ClassField(m::Map,G::GrpAb:brute := false) -> .
{Let K be a p-adic field and U,m:=UnitGroup(K).
Let G be a subgroup of U of finite index.
Return a list of extensions of K, containing the class fields 
corresponding to the cyclic factors of U/G}
  
  R := Codomain(m);
  U := Domain(m);
  p := Prime(R);
  B := BaseRing(R);
  e := RamificationIndex(R,B);
  
  Q, mQ := quo<U | G>;

  vprint ClassField, 2:"ClassField: corresponding to", G;
  vprint ClassField, 2:"ClassField: over\n", R;
 
  if Order(Q) eq 1 then
    vprint ClassField, 2:"ClassField: trivial case";
    return R;
  end if;

  if Order(Q) eq Infinity() then 
    error "ClassField: group must have finite index in the unit group";
  end if;
 
//"Q",Q;  
  
  if not IsCyclic(Q) then
    Qgens := [q@@mQ : q in Generators(Q)];
    Ggens := [U!g: g in Generators(G)];
    Hlist := [ ];
    for i in [1..#Qgens] do
      Hgens := Remove(Qgens,i) cat Ggens;
      H := sub<U | Hgens>;
      Append(~Hlist, H);
    end for;
    vprint ClassField,3:"Class Field:",Hlist;  
    return [ClassField(m,H):H in Hlist];
  end if;
    
  relation_matrix_map := rel_mat_map(m);
  relation_matrix := relation_matrix_map(G);
  vprint ClassField, 3:"ClassField: relation matrix",relation_matrix;

  unram_deg := relation_matrix[1][1];
  if unram_deg ne 1 then
    vprint ClassField, 2:"ClassField: computing unramified extension of degree",
                         unram_deg;
    R_u := UnramifiedExtension(R,unram_deg);
  else // no unramified extension
    R_u := R;    
  end if;

  tameram_deg := relation_matrix[2][2];
  if tameram_deg ne 1 then
    Ugen := UnitGroupGenerators(R_u);
    zeta := Ugen[#Ugen-1];
    pi := Ugen[#Ugen];
    Rx := PolynomialRing(R_u); x := Rx.1;
    pol := x^tameram_deg + zeta^relation_matrix[1][2]*pi;
    vprint ClassField, 2:"ClassField: tamely ramified extension generated by",pol;
    K := TotallyRamifiedExtension(R_u,pol);
  else
    K := R_u;
  end if;
 
  if Order(Q) eq tameram_deg*unram_deg then
      return K;
  elif unram_deg*tameram_deg ne 1 then
      eK := RamificationIndex(K, PrimeRing(K));
      //unitprec := Integers()!Minimum(Precision(K),(p+1)*p*eK/(p-1));
      //unitprec := Integers()!Minimum(Precision(K),(p+1)*p*eK);
      unitprec := Precision(K);
      vprint ClassField, 3:"ClassField: using precision",unitprec;
      IndentPush();
        //UK, mUK := UnitGroup(K,unitprec);
        UK, mUK := UnitGroup(K);
      IndentPop();
      GK := NormEquation(mUK,m,G);
      relation_matrix := rel_mat_map(mUK);
      if Norm(mUK,m,GK) ne G then
        error "ClassField: ERROR, solution of NormEquation is false.";
      end if;
      return class_field_p_m(mUK, GK);
  else
      return class_field_p_m(m,G);
  end if;
end intrinsic;
