freeze;

/****************************************************************************
maps.m

Oct 2002, Nils Bruin

Non-trivial operations on scheme maps

****************************************************************************/

function Combine(L)
  if #L eq 1 then
    return [[l]:l in L[1]];
  else
    M:=$$(L[2..#L]);
    return [ [a] cat l : a in L[1], l in M];
  end if;
end function;

intrinsic IsInvertible(phi::MapSch:Maximal:=false)->BoolElt,MapSch

  {Determines if phi is birationally invertible. If it is, then true is
  returned, together with the inverse map (knowing about the original map as
  its inverse). If not, false is returned. Presently, domain and codomain
  should be irreducible. It uses a Groebner basis computation, so is
  potentially expensive. If Maximal is provided, the inverse returned (if any)
  will have multiple patches installed to maximize its domain of definition. This
  is not guaranteed to be really maximal. It just makes the extension that is easy
  from the computed data. Use AlternativePatches to get more.}

  if assigned phi`Inverse then
  return true,phi`Inverse;
  end if;

  X:=Domain(phi);
  Y:=Codomain(phi);
  
  if #Components(phi) eq 1 then 
      input_phi := phi;
  end if;
  phi:=Expand(phi);

  //Presently, we assume X and Y are irreducible, i.e., if we have
  //an affine patch Xa of X with Dimension(Xa) eq Dimension(X), then
  //there is no component of X at infinity. A better, but slightly more
  //expensive test would apply for equidimensional X: As soon has we have a
  //patch Xa of X such that HyperPlaneAtInfinity(Ambient(Xa)) meet X
  //has dimension smaller than X, we know there's no component at infinity.
  
  if IsAffine(X) then
    Xa:=X;
    XaPC:=IdentityMap(X);
  else
    require #Gradings(X) eq 1:
      "Domain is only allowed to have 1 grading.";
    require exists(Xa){AffinePatch(X,i): i in [1..Length(X)]|
       HasAffinePatch(X,i) and (Dimension(AffinePatch(X,i)) eq Dimension(X))}:
         "None of the standard patches seems to work for X";
    XaPC:=iso<Xa->X|DefiningPolynomials(f),InverseDefiningPolynomials(f) : Check := false >
      where f:=ProjectiveClosureMap(Ambient(Xa));
  end if;
  
  if IsAffine(Y) then
    Ya:=Y;
    YaPC:=IdentityMap(Y);
  else
    require #Gradings(Y) eq 1:
      "Codomain is only allowed to have 1 grading.";
    require exists(Ya){AffinePatch(Y,i): i in [1..Length(Y)]|
       HasAffinePatch(Y,i) and (Dimension(AffinePatch(Y,i)) eq Dimension(Y))}:
         "None of the standard patches seems to work for Y";
    YaPC:=iso<Ya->Y|DefiningPolynomials(f),InverseDefiningPolynomials(f) : Check := false >
        where f:=ProjectiveClosureMap(Ambient(Ya));
  end if;
  
  XatoYa:=XaPC*phi*Inverse(YaPC);
  
  fs:=Parent([[FieldOfFractions(Parent(Xa.1))|]])!
                                          AllDefiningPolynomials(XatoYa);
  
  //although we want to eliminate the first variables eventually, we only
  //want to do that on one component of the graph. To find that component,
  //we need to eliminate the last variables first. That explains the present
  //order. We'll change it later to the other way around.
  
  A:=PolynomialRing(BaseRing(Xa),Length(Xa)+Length(Ya),"elim",
             [Length(Xa)+1..Length(Xa)+Length(Ya)]);
  xA:=[A.i:i in [1..Length(Xa)]];
  yA:=[A.i:i in [Length(Xa)+1..Length(Xa)+Length(Ya)]];
  xXa:=[Xa.i: i in [1..Length(Xa)]] cat [0: i in [1..#yA]];
  yYa:=[0: i in [1..#xA]] cat [Ya.i: i in [1..Length(Ya)]];
  J:=ideal<A | [Evaluate(g,xA):g in DefiningEquations(Xa)] cat
              [Evaluate(g,yA):g in DefiningEquations(Ya)] cat
              &cat[[Evaluate(Denominator(f[i]),xA)*yA[i]-
                    Evaluate(Numerator(f[i]),xA):
                  i in [1..#yA]]:f in fs]>;
                  
  //Remove unwanted component
  
  badJ:=ideal<A|[Evaluate(g,xA):g in DefiningEquations(BaseScheme(XatoYa))] cat
              [Evaluate(g,yA):g in DefiningEquations(Ya)]>;
/* mch 04/05 - the below ColonIdeal operation should be a Saturation.
    The two are only equivalent for sure if we know that J is reduced.
    However even for a map between integral affine schemes, J may not
    be reduced and the function with ColonIdeal can be wrong if the
    map is given by rational functions -
    e.g. F := GF(3^4); s := F.1; A2<x,y> := AffineSpace(F,2);
         Xa := Scheme(A2,x^4+s^24*y^3+1);
	 Ya := Scheme(A2,y^2-x);
	 XatoYa := map<Xa->Ya|[(x/(y+s^72))^2,x/(y+s^72)]>;
    - here XatoYa is a birational map but using ColonIdeal instead of
     Saturation -> IsInvertible(XatoYa) returns false.
     
  //Jpr:=ColonIdeal(J,badJ);
*/
  Jpr := Saturation(J,badJ);
  if Ideal(Domain(XatoYa)) ne ideal<Universe(xXa) |
       [Evaluate(g,xXa): g in Basis(EliminationIdeal(Jpr,Seqset(xA)))]> then
    //print "Computed component does not project back to domain.";
    return false,_;
  end if;
        
  Jpr:=ChangeOrder(Jpr,"elim",[1..#xA]);
  
  //We take a Groebner basis & reverse it
  //We sort out the basis elements in the following way:
  //L[i] contains all elements from bs that have degree 1 in xA[i] and
  //degree 0 in xA[j] for j in [1..i-1].
  
  bs:=Reverse(GroebnerBasis(Jpr));
  L:=[[]:i in [1..#xA]];
  for v in Reverse([1..#xA]) do
    L[v]:=[g: g in bs | Degree(g,v) eq 1 and
                  forall{ i : i in [1..v-1] | Degree(g,i) eq 0}];
  end for;

  if exists{b:b in L|#b eq 0} then
    "Groebner basis for generic graph component fails triangularity.",bs;
    return false,_;
  end if;

  img:=[b:b in bs | forall{i: i in [1..#xA] | Degree(b,i) eq 0}];
  img:=[Evaluate(f,yYa):f in img];
  if Ideal(Scheme(Ambient(Ya),img)) ne Ideal(Ya) then
    //print "Map does not seem to be dominant.";
    return false,_;
  end if;
  
  //if only one patch is required, throw away the other equations.
    
  if not(Maximal) then
    L:=[[l[#l]]:l in L];
  end if;

  L:=Combine(L);

  R:=[];
  for j in [1..#L] do
    sol:=ChangeUniverse(xA cat yA,FieldOfFractions(A));
    for v in Reverse([1..#xA]) do
      f:=L[j][v];
      assert Degree(f,v) eq 1;
      fsol:=Evaluate(f,sol);
      if Type(fsol) eq FldFunRatMElt then
        num:=Numerator(fsol);
        den:=Denominator(fsol);

        // The denominator better be irrelevant. 
        assert Degree(den,v) eq 0;
      else
        num:=fsol;
      end if;
      sol[v]:=-Term(num,v,0)/Term(num,v,1)*xA[v];
    end for;
    R[#R+1]:=[MyEval(f,yYa):f in sol[1..#xA]];
  end for;
  
  YatoXa:=map<Ya->Xa|R : Check := false >;
  fi:=AllDefiningPolynomials(Inverse(YaPC)*YatoXa*XaPC);
  phi_inv := Prune(iso<Y->X|fi,AllDefiningPolynomials(phi) : Check := false >);
  if assigned input_phi then
      input_phi`Inverse := phi_inv;
  end if;
  return true, phi_inv;
end intrinsic;

function ExpandedComposition(f,g)
  if HasKnownInverse(f) and HasKnownInverse(g) then
    return iso<Domain(f)->Codomain(g)|
      [[MyEval(gjk,fi):gjk in gj] :
        fi in AllDefiningPolynomials(f), gj in AllDefiningPolynomials(g)],
      [[MyEval(fjk,gi):fjk in fj] :
        gi in AllInverseDefiningPolynomials(g), fj in AllInverseDefiningPolynomials(f)] : Check := false >;
  else
    return map<Domain(f)->Codomain(g)|
      [[MyEval(gjk,fi):gjk in gj] :
        fi in AllDefiningPolynomials(f), gj in AllDefiningPolynomials(g)] : Check := false >;
  end if;
end function;

intrinsic Prune(f::MapSch)->MapSch
  {Returns a map with superfluous defining equations removed. If an inverse is
   known, then this is preserved but not pruned.}
  require #Components(f) eq 1: "Map must be in expanded form";
  L:=AllDefiningPolynomials(f);
  phi:=map<Domain(f)->Codomain(f)|L[1] : Check := false >;
  for l in L[2..#L] do
    phinew:=map<Domain(f)->Codomain(f)|AllDefiningPolynomials(phi) cat[l] : Check := false >;
    if not(IsEmpty(Difference(BaseScheme(phi),BaseScheme(phinew)))) then
      phi:=phinew;
    end if;
    if IsEmpty(BaseScheme(phi)) then
      break;
    end if;
  end for;
  if HasKnownInverse(f) then
    return iso<Domain(f)->Codomain(f)|
      AllDefiningPolynomials(phi),AllInverseDefiningPolynomials(f) : Check := false >;
  else
    return phi;
  end if;
end intrinsic;

intrinsic Expand(phi::MapSch)->MapSch
  {Given a map in factored form, returns the expansion of the map. If
  alternative equations are available, then these are combined. The result has
  both the map and a possible inverse pruned}
  
  L:=Components(phi);
  psi:=L[1];
  if #L eq 1 then
    psi:=Prune(psi);
    if HasKnownInverse(psi) then
      psi:=Inverse(Prune(Inverse(psi)));
    end if;
  end if;  
  for f in L[2..#L] do
    psi:=Prune(ExpandedComposition(psi,f));
    if HasKnownInverse(psi) then
      psi:=Inverse(Prune(Inverse(psi)));
    end if;
  end for;
  return psi;
end intrinsic;

intrinsic AlternativePatches(XatoYa::MapSch)->MapSch
  {Given a map between affine schemes, computes a number of patches that
   extend the map to a larger domain of definition.}
  Xa:=Domain(XatoYa);
  Ya:=Codomain(XatoYa);
  require IsAffine(Xa) and IsAffine(Ya):
    "Domain and Codomain have to be affine";
  /* print "We want all def. polynomials of",XatoYa; */
  /* print "Here comes the error ..."; */
  /* AllDefiningPolynomials(XatoYa); */

  fs:=Parent([[FieldOfFractions(Parent(Xa.1))|]])!
                                          AllDefiningPolynomials(XatoYa);
  A:=PolynomialRing(BaseRing(Xa),Length(Xa)+Length(Ya),"elim",
             [Length(Xa)+1..Length(Xa)+Length(Ya)]);
  xA:=[A.i:i in [1..Length(Xa)]];
  yA:=[A.i:i in [Length(Xa)+1..Length(Xa)+Length(Ya)]];
  xXa:=[Xa.i: i in [1..Length(Xa)]] cat [0: i in [1..#yA]];
  yYa:=[0: i in [1..#xA]] cat [Ya.i: i in [1..Length(Ya)]];
  J:=Ideal([Evaluate(g,xA):g in DefiningEquations(Xa)] cat
              [Evaluate(g,yA):g in DefiningEquations(Ya)] cat
              &cat[[Evaluate(Denominator(f[i]),xA)*yA[i]-
                    Evaluate(Numerator(f[i]),xA):
                  i in [1..#yA]]:f in fs]);

  badJ:=Ideal([Evaluate(g,xA):g in DefiningEquations(BaseScheme(XatoYa))]);
/* mch - 04/05 - replaced below ColonIdeal with Saturation as in the
   IsInvertible function. See comments there.
   
  //Jpr:=ColonIdeal(J,badJ);
*/
  Jpr:=Saturation(J,badJ);
  
  bs:=Reverse(GroebnerBasis(Jpr));
  L:=[[]:i in [1..#yA]];
  for v in Reverse([1..#yA]) do
    L[v]:=[g: g in bs | Degree(g,yA[v]) eq 1 and
                  forall{ i : i in [1..v-1] | Degree(g,yA[i]) eq 0}];
  end for;
 
  L:=Combine(L); 

  R:=[];
  for j in [1..#L] do
    sol:=ChangeUniverse(xA cat yA,FieldOfFractions(A));
    for v in Reverse([1..#yA]) do
      f:=L[j][v];
      assert Degree(f,yA[v]) eq 1;
      fsol:=Evaluate(f,sol);
      if Type(fsol) eq FldFunRatMElt then
        num:=Numerator(fsol);
        den:=Denominator(fsol);

        // The denominator better be irrelevant. 
        assert Degree(den,yA[v]) eq 0;
      else
        num:=fsol;
      end if;
      sol[#xA+v]:=-Term(num,yA[v],0)/Term(num,yA[v],1)*yA[v];
    end for;
    R[#R+1]:=[MyEval(f,xXa):f in sol[#xA+1..#xA+#yA]];
  end for;
  if HasKnownInverse(XatoYa) then
    return map<Xa->Ya| AllDefiningPolynomials(XatoYa) cat R,
                       AllInverseDefiningPolynomials(XatoYa) : Check := false >;
  else
    return map<Xa->Ya| AllDefiningPolynomials(XatoYa) cat R : Check := false >;
  end if;
end intrinsic;

intrinsic Extend(phi::MapSch)->MapSch
  {Use groebner basis methods to extend the rational map phi to a domain of
   definition that is as large as possible}
  if IsAffine(Domain(phi)) and IsAffine(Codomain(phi)) then
    return Prune(AlternativePatches(phi));
  elif IsProjective(Domain(phi)) and IsAffine(Codomain(phi)) then
    L:=Gradings(Domain(phi));
    require #L eq 1: "Only implemented for spaces with one grading";
    L:=L[1];
    phinew:=phi;
    for i in [1..#L] do
      if L[#L+1-i] eq 1 then //only takes lines at infinity with grading 1
        Xa:=AffinePatch(Domain(phi),i);
        PCA:=ProjectiveClosureMap(Ambient(Xa));
        PC:=map<Xa->Domain(phi)|DefiningPolynomials(PCA),
                                InverseDefiningPolynomials(PCA) : Check := false >;
        aphi:=PC*phi;
        if not(IsEmpty(BaseScheme(aphi))) then
          phinew:=Prune(map<Domain(phi)->Codomain(phi)|
             AllDefiningPolynomials(phinew) cat 
             AllDefiningPolynomials(Inverse(PC)*AlternativePatches(aphi)) : Check := false >);
        end if;
      end if;
    end for;
    if HasKnownInverse(phi) then
      return map<Domain(phi)->Codomain(phi)|AllDefiningPolynomials(phinew),
                                            AllInverseDefiningPolynomials(phi) : Check := false >;
    else
      return phinew;
    end if;
  else
    L:=Gradings(Codomain(phi));
    require #L eq 1: "Only implemented for spaces with one grading";
    L:=L[1];
    phinew:=phi;
    for i in [1..#L] do
      if L[#L+1-i] eq 1 then //only takes lines at infinity with grading 1
        Ya:=AffinePatch(Codomain(phi),i);
        PC:=Restriction(ProjectiveClosureMap(Ambient(Ya)),Ya,Codomain(phi));
        PCi:=Restriction(Inverse(ProjectiveClosureMap(Ambient(Ya))),
                     Codomain(phi),Ya);
        phia:=phi*PCi;
        if not(IsEmpty(BaseScheme(phia))) then
          phinew:=Prune(map<Domain(phi)->Codomain(phi)|
             AllDefiningPolynomials(phinew) cat 
             AllDefiningPolynomials(Extend(phia)*PC) : Check := false >);
        end if;
      end if;
    end for;
    if HasKnownInverse(phi) then
      return map<Domain(phi)->Codomain(phi)|AllDefiningPolynomials(phinew),
                                            AllInverseDefiningPolynomials(phi) : Check := false >;
    else
      return phinew;
    end if;
  end if;
end intrinsic;

/***** Expand + other functions for graph maps - mch 10/09 *****************/

function ExpandedGraphMapComposition(f,g)
    If := f`GraphIdeal;
    Ig := g`GraphIdeal;
    m := Length(Domain(f));
    n := Length(Codomain(f));
    l := Length(Codomain(g));
    P := PolynomialRing(BaseRing(If),m+n+l,"grevlex");
    hm1 := hom<Generic(If)->P |[P.i : i in [1..m+n]]>;
    hm2 := hom<Generic(Ig)->P |[P.i : i in [m+1..m+n+l]]>;
    I1 := ideal<P|[hm1(b) : b in Basis(If)]>;
    I2 := ideal<P|[hm2(b) : b in Basis(Ig)]>;
    I := I1 + I2;
    // find a y variable of codomain(f) which doesn't contain
    // the image of f and saturate wrt it
    i := 1; R := Generic(If);
    while i le n do
	if not IsInRadical(R.(m+i),If) then break; end if;
	i +:= 1;
    end while;
    assert i le n;
    I := ColonIdeal(I,P.(m+i));
    // eliminate the "middle" variables
    B := EasyBasis(I);
    B1 := [F : F in B | &and[e[i] eq 0 : i in [m+1..m+n]] 
			where e is Exponents(LeadingTerm(F))];
    P1 := PolynomialRing(BaseRing(If),m+l,"grevlex");
    hm := hom<P -> P1 | [P1.i : i in [1..m]] cat [0 : i in [m+1..m+n]] cat
		[P1.i : i in [m+1..m+l]]>;
    I := ideal<P1|[hm(b) : b in B1]>;
    return SchemeGraphMap(Domain(f),Codomain(g),I);
end function;

intrinsic Expand(phi::MapSchGrph)-> MapSchGrph
{ Given a graph map in factored form, returns the expansion of the map. }

    L := Components(phi);
    psi := L[1];
    if #L eq 1 then return psi; end if;
    bk := HasKnownInverse(psi);
    for f in L[2..#L] do
	psi:=ExpandedGraphMapComposition(psi,f);
	if bk then
	    bk and:= HasKnownInverse(f);
	end if;
    end for;
    if bk then
	psi`KnownBirat := true;
	psi`IsBirat := true;
    end if;
    return psi;
  
end intrinsic;

function MapFromGraph(yEqns,I,swap)

    R := Generic(Universe(yEqns));
    n := Rank(I);
    m := Rank(R)-n;

    S := Generic(I);
    F := FieldOfFractions(S);
    subs := (swap select [F!1 : i in [1..m]] cat [F.i : i in [1..n]]
	else [F.i : i in [1..n]] cat [F!1 : i in [1..m]]);
    N := (swap select 0 else n); 
    //hm := hom<R->F | [F.i : i in [1..n]] cat [1 : i in [1..m]]>;
    
    // get equations one at a time: first for y_(m-1)/y_m, then
    // for y_(m-2)/y_m etc - not nice!
    for i := m-1 to 1 by -1 do
	eqns := [e : e in yEqns | Exponents(LeadingTerm(e))[N+i] eq 1];
	y_eqn := eqns[#eqns];
	E,F := Explode(Coefficients(y_eqn,R.(N+i)));
	yi := -Evaluate(E,subs)/Evaluate(F,subs);
	subs[N+i] := yi;
    end for;
    map_eqns := [subs[i] : i in [N+1..N+m]];
    return map_eqns;
 
end function;

function toSchemeMap(f)
    
    // get forward equations
    Igr := f`GraphIdeal;
    B := GroebnerBasis(Igr);
    I := Ideal(Domain(f));
    yEqns := [f : f in B | &+[e[i] : i in [Rank(I)+1..Rank(Igr)]] eq 1
			where e is Exponents(LeadingTerm(f))];
    map_eqns := MapFromGraph(yEqns,I,false);

    // get inverse equations if map is known invertible
    if HasKnownInverse(f) then
	//NB. As usual, it is assumed that Igr is saturated wrt the
	// domain variables. If f has been set to be known invertible
	// it is required that it has also been saturated wrt the
        // codomain variables.
	Pgr := Generic(Igr);
	m := Rank(Pgr)-Rank(I);
	hm := hom<Pgr -> Pgr |[Pgr.i : i in [m+1..Rank(Pgr)]] cat
	   [Pgr.i : i in [1..m]]> ;
	B := GroebnerBasis(ideal<Pgr|[hm(b) : b in B]>);
	yEqns := [f : f in B | &+[e[i] : i in [m+1..Rank(Igr)]] eq 1
			where e is Exponents(LeadingTerm(f))];
	inv_eqns := MapFromGraph(yEqns,Ideal(Codomain(f)),false);
	return map<Domain(f) -> Codomain(f) | map_eqns, inv_eqns : Check := false>;	
    else
	return map<Domain(f) -> Codomain(f) | map_eqns : Check := false>;
    end if;

end function;

intrinsic SchemeGraphMapToSchemeMap(phi::MapSchGrph) -> MapSch
{ Converts a scheme graph map to a conventional scheme map }

    L := Components(phi);
    L1 := [toSchemeMap(f) : f in L];
    if #L eq 1 then
	return L1[1];
    else
	f := L1[1];
	for g in L1 do f := f*g; end for;
	return f;
    end if;

end intrinsic;

function grph_map_inverse(f)
// produce the inverse graph map of a graph map which is already
// known invertible (and is domain + codomain graph saturated)

    n := Length(Domain(f));
    m := Length(Codomain(f));
    Igr := f`GraphIdeal;
    Pgr := Generic(Igr);

    // "swap" domain + codomain variables
    hm := hom<Pgr -> Pgr |[Pgr.i : i in [m+1..n+m]] cat
           [Pgr.i : i in [1..m]]> ;
    Igri := ideal<Pgr|[hm(b) : b in Basis(Igr)]>;
    finv := SchemeGraphMap(Codomain(f),Domain(f),Igri);
    finv`KnownBirat := true; finv`IsBirat := true;
    return finv;
    
end function;

function grph_map_is_inv(f)
// f is a non-composite graph map with dim(Domain) = dim(Codomain)
//  [=> codomain is irreducible, as the domain is by assumption].
//  checks whether f is birational and, if so, returns the inverse.
//  Also makes sure that the graph ideal of f & its inverse is
//  codomain saturated.

    n := Length(Domain(f));
    m := Length(Codomain(f));

    Igr := f`GraphIdeal;
    Pgr := Generic(Igr);
    Y := Codomain(f);

    // codomain saturate wrt appropriate variable
    i := 1; R := CoordinateRing(Ambient(Y));
    while i le Rank(R) do
	if not IsInRadical(R.i,Ideal(Y)) then break; end if;
	i +:= 1;
    end while;
    assert i le Rank(R);
    Igr := ColonIdeal(Igr,Pgr.(n+i));

    // "swap" domain + codomain variables and look for the
    // existence of defining equations for the inverse
    hm := hom<Pgr -> Pgr |[Pgr.i : i in [m+1..n+m]] cat
	   [Pgr.i : i in [1..m]]> ;
    Igri := ideal<Pgr|[hm(b) : b in Basis(Igr)]>;
    B := GroebnerBasis(Igri);
    yEqns := [F : F in B | &+[e[i] : i in [m+1..m+n]] eq 1
			where e is Exponents(LeadingTerm(F))];
    min_vars := [Min([i : i in [m+1..m+n] |e[i] eq 1]) where
	e is Exponents(LeadingTerm(F)) : F in yEqns];
    min_vars := Sort(Setseq(Seqset(min_vars)));
    assert min_vars[#min_vars] ne m+n;
    if #min_vars lt n-1 then
	return false,_;
    end if;

    // Here we know that Igr contains eqns of the form
    //  x_i *Fi(y) + x_(i+1)*F(i+1)(y) + .. x_n*Fn(y) for 1 <= i <= n
    //  with Fi(y) not in Ideal(Y) => birational inverse eqns exist.
    InternalGrphIdealSet(f,Igr); // make sure graph ideal of f is cod sat
    f`KnownBirat := true; f`IsBirat := true;
    finv := SchemeGraphMap(Y,Domain(f),Igri);
    finv`KnownBirat := true; finv`IsBirat := true;
    return true,finv;

end function;

intrinsic IsInvertible(phi::MapSchGrph)->BoolElt,MapSchGrph

  {Determines if phi is birationally invertible. If it is, then true is
  returned, together with the inverse map. If phi is a composite map and 
  all components aren't already known invertible, then phi is first expanded.}

  if HasKnownInverse(phi) then
    L := [ grph_map_inverse(f) : f in Components(phi) ];
    Reverse(~L);
    if #L eq 1 then
	return true,L[1];
    else
	f := L[1];
	for g in L do f := f*g; end for;
	return true,f;
    end if;
  end if;

  X:=Domain(phi);
  Y:=Codomain(phi);
  if Dimension(X) ne Dimension(Y) then
    return false,_;
  end if;
  phi := Expand(phi);
  return grph_map_is_inv(phi);

end intrinsic;
  
intrinsic Restriction(f::MapSchGrph,X::Sch,Y::Sch : Check:=true ) -> MapSchGrph
{The restriction of f to the scheme X in its domain and Y in its codomain}

    booX := (X eq Domain(f));
    booY := (Y eq Codomain(f));
    if booX and booY then return f; end if;
    if Check then
      require (booX or (X subset Domain(f))) and (booY or (Y subset Codomain(f))):
          "Second argument must lie inside the domain of the first and " *
                  "third argument must lie inside the codomain of the first";
      if not booY then
          require f(X) subset Y:
              "Image of second argument under the first must lie in the third";
      end if;
    end if;
    Pgr := Generic(f`GraphIdeal);
    Igr :=  ideal<Pgr| Basis(f`GraphIdeal)>;
    PX := CoordinateRing(Ambient(X));
    n := Rank(PX);

    if not booX then
	hmX := hom<PX -> Pgr | [Pgr.i : i in [1..n]]>;
	Igr +:= ideal<Pgr|[hmX(b) : b in Basis(Ideal(X))]>;
    end if;

    if not booY then
	hmY := hom<PY -> Pgr | [Pgr.i : i in [n+1..n+Rank(PY)]]> where
		PY is CoordinateRing(Ambient(Y));
	Igr +:= ideal<Pgr|[hmY(b) : b in Basis(Ideal(Y))]>;
    end if;

    // saturate wrt appropriate X var
    i := 1;
    while i le n do
        if not IsInRadical(PX.i,Ideal(X)) then break; end if;
        i +:= 1;
    end while;
    assert i le n;
    Igr := ColonIdeal(Igr,Pgr.i);

    return SchemeGraphMap(X,Y,Igr);
   
end intrinsic;

