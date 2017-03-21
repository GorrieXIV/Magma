freeze;

/******************************************************************************
 *
 * etalealg.m
 *
 * date:   26/6/2001
 * author: Nils Bruin
 *
 * Some routines to work with algebras of the form A=K[x]/F(x), where K is a
 * number field and F is a square free polynomial.
 *
 ******************************************************************************/


/***********************************

   CHANGES: 

   2009-10, Steve: 
            Copied in version of AbsoluteAlgebra(A::RngUPolRes:Fields:={})
            from Michael Stoll that works over finite fields
            
   2005-12, Steve: 
      
            - Added the "front end" of AbsoluteAlgebra that takes a 
              RngMPolRes instead of a RngUPolRes


                                             ***********************************/



declare attributes RngUPolRes: AbsoluteMap,LocalData;

declare verbose EtaleAlg, 1;

RFLocalData:=recformat<TwoSelmerMap,TwoSelmerMapComponents>;

import "localdata.m":GetLocalData,StoreLocalData;

/**
 ** AbsoluteAlgebra
 **
 ** The biggie! This routine decomposes an algebra into field extensions of its
 ** base field. It represents those fields as absolute extensions.
 ** It takes an optional list of suggested fields. If it finds it needs a field
 ** isomorphic to one of the suggested fields, it will use that one.
 **/

// returns OptimizedRepresentation(AbsoluteField(K))
// but avoids unnecessary hard factorization
function opt_abs(K)
  if IsAbsoluteField(K) then
    return OptimizedRepresentation(K);
  end if;
  Kabs  := AbsoluteField(K);
  ZK    := Integers(K);
  ZKabs := Integers(Kabs);
assert assigned K`MaximalOrder;
assert assigned Kabs`MaximalOrder;
  return OptimizedRepresentation(AbsoluteField(K));
end function;

intrinsic AbsoluteAlgebra(A::RngMPolRes:Fields:={})->SetCart,Map
  {Given a semi-simple algebra over an absolute number field or the rationals,
  returns the isomorphic direct sum of absolute fields as a cartesian product
  and the isomorphism to this product. The optional parameter Fields
  enables the user to suggest representations of the absolute fields. If this
  function needs a field isomorphic to one occurring in the supplied
  list, then it will use the given field. Otherwise it will construct a field
  itself. The isomorphism is returned as a second argument. If called twice on
  the same algebra, it will recompute if the Fields argument is given.
  Otherwise it will return the result computed the first time.}

  // Find a primitive element of A
  d := Dimension(A);
  vars := [ A.i : i in [1..Rank(A)] ];
  prim := A.1;
  while Degree(MinimalPolynomial(prim)) ne d do
     i := Random( [1..Rank(A)] );
     prim +:= Random({1,-1})*A.i;
  end while;

  pol := MinimalPolynomial(prim);
  P := PolynomialRing( BaseRing(A) );
  AA := quo< P | P!pol >;          // Univariate version of A
  AAtoA := iso< AA -> A | prim >;
  // to get the inverse, apparently we need to express AAtoA as a map 
  // between the underlying vector spaces
  VA, AtoVA := VectorSpace(A);
  VAA := VectorSpace(BaseRing(AA), d);
  AAtoVAA := map< AA -> VAA | aa :-> VAA! Eltseq(aa) >;
  VAAtoAA := map< VAA -> AA | v :-> AA! Eltseq(v) >;
  VAAtoVA := hom< VAA -> VA | [VAAtoVA(VAA.i) : i in [1..d]] 
                         where VAAtoVA := VAAtoAA*AAtoA*AtoVA >;
  VAtoVAA := Inverse(VAAtoVA);
  AtoAA := iso< A -> AA | a :-> VAAtoAA(VAtoVAA(AtoVA(a))) >;
  Aabs, AAtoAabs := AbsoluteAlgebra(AA : Fields:=Fields );
  AisoAabs := map< A -> Aabs | 
                  a :-> AAtoAabs(AtoAA(a)),
                  aabs :-> AAtoA( Inverse(AAtoAabs)(aabs) ) >;
  return Aabs, AisoAabs;
end intrinsic;

intrinsic AbsoluteAlgebra(A::RngUPolRes:Fields:={})->SetCart,Map
{"} // "
  // Computations here are expensive and what we compute is canonical,
  // so we store the info in an attribute. Note that when this routine is
  // called with "Fields" set to some non-empty set, then the user probably
  // had a good reason for wanting to use those fields, so then we recompute too
  // (and store the result for future reference)

  if Fields ne {} or not(assigned(A`AbsoluteMap)) then
    F:=Modulus(A);
    vprint EtaleAlg: "Computing field decomposition of",A;
    require Discriminant(F) ne 0:
      "Algebra should be semisimple";

    //determine the irreducible components of A (there are "r" of them)
    fct:=[f[1]: f in Factorisation(F)];
    vprint EtaleAlg: "Modulus factors as",fct;
    r:=#fct;
    K:=BaseRing(A);

    //due to current restrictions, the ground field of A should be an absolute
    //number field (yes *number field*. Rationals won't do)
    if ISA(Type(K),FldRat) or ISA(Type(K),FldAlg) then
      require Type(K) eq FldRat or IsAbsoluteField(K) : "Not implemented over relative number fields";

      //irreducible components represented as a relative extension of K
      RelFld:=[NumberField(f:DoLinearExtension:=true): f in fct];

      //for absolute representations, try to use presupplied fields. This
      //allows precomputed classgroup information to be used in future
      //computations. Otherwise, for degree 1 extensions just take the ground
      //field. In the rest of the situations, take an OptimisedRepresentation
      //of an absolute field.
      AbsFld:=< exists(Labs){L:L in Fields|IsIsomorphic(L,Lrel)}
                select
                    Labs
                else (Degree(Lrel) eq 1 and Type(K) ne FldRat)
                    select
                        K
                    else
                        opt_abs(Lrel)
        : Lrel in RelFld >;

      //The algebra is isomorphic to the cartesian product of these fields
      Sum:=CartesianProduct(AbsFld);
      vprint EtaleAlg:"field decomposition:",Sum;

      //Store the isomorphisms between the relative and absolute fields

      RelToAbsMap:=[phi where phi:=Coercion(RelFld[i],AbsFld[i]):
        i in [1..r]];
      //We compute the image of the power basis of A wrt the relative bases
      //of the irreducible components. Inverting this matrix gives the map
      //from the direct sum of the relative fields to A.
      M:=Matrix([ &cat[Eltseq(L.1^i):L in RelFld]:i in [0..Degree(F)-1]])^(-1);

      //Therefore, the isomorphism from A to Sum can be done by first
      //taking a polynomial representation of en element of A, evaluating that
      //in the image of the generator of A in each of the relative fields
      //(this is by construction the generator of the relative field)
      //and mapping through the isomorphism  to the absolute field
      //
      //The other way around is also simple: map from the absolute field
      //to the relative ones, take the coefficient sequences of these elements
      //and concatenate them. Multiply this vector with M and we have a coordinate
      //vector wrt the power basis of A. We simply coerce it into A.
      iso:=map< A->Sum |
        a:-> <RelToAbsMap[i](Evaluate(a,RelFld[i].1)): i in [1..r]>,
        tp:-> A!Eltseq(
          Vector(&cat[Eltseq(tp[i]@@RelToAbsMap[i]): i in [1..r]]) * M)>;
      //store the map
      A`AbsoluteMap:=iso;
    elif ISA(Type(K), FldFin) then
      //irreducible components represented as a relative extension of K
      Fld:=[ext<K | Degree(f)> : f in fct];

      //The algebra is isomorphic to the cartesian product of these fields
      Sum:=CartesianProduct(Fld);
      vprint EtaleAlg:"field decomposition:",Sum;
      roots := [* Rep(Roots(fct[i], Fld[i]))[1] : i in [1..r] *];

      //We compute the image of the power basis of A wrt the relative bases
      //of the irreducible components. Inverting this matrix gives the map
      //from the direct sum of the relative fields to A.
      M:=Matrix([ &cat[Eltseq(rt^i): rt in roots] : i in [0..Degree(F)-1]])^(-1);

      //Therefore, the isomorphism from A to Sum can be done by
      //taking a polynomial representation of en element of A and evaluating that
      //in the image of the generator of A in each of the relative fields.
      //
      //The other way around is also simple: take the coefficient sequences
      //of the field elements and concatenate them. Multiply this vector with M
      //and we have a coordinate vector wrt the power basis of A.
      //We simply coerce it into A.
      iso:=map< A->Sum |
        a:-> <Evaluate(a, roots[i]): i in [1..r]>,
        tp:-> A!Eltseq(Vector(&cat[Eltseq(tp[i]): i in [1..r]]) * M) >;
      //store the map
      A`AbsoluteMap:=iso;
    else
      require false:
        "The given algebra must be over Q, an absolute number field, or a finite field";
    end if;
  end if;

  return Codomain(A`AbsoluteMap), A`AbsoluteMap;
end intrinsic;

/**
 ** SUnitGroup
 **
 ** Computes the S-Unit group of a semisimple algebra.
 **/

/* TO DO: this is as bad as pSelmerGroup was -- arghhh!!! */

intrinsic SUnitGroup(A::RngUPolRes,S::SetEnum:Raw:=false)->GrpAb,Map
  {Returns the S-Unit group of a semisimple algebra over a number field. 
  The set S should contain prime ideals related to the base field of A.}
  Field,iso:=AbsoluteAlgebra(A);
  r:=NumberOfComponents(Field);

  expvec:=<>;
  gens:=[A|];
  invs:=[];
  for i in [1..r] do
    OL:=IntegerRing(Field[i]);
    LS:=&join{Support(Type(P) eq RngIntElt select P*OL else OL!!P) :P in S};  
    grp,vecmp,bU:=SUnitGroup(Setseq(LS):Raw);
    Append(~invs,Invariants(grp));
    Append(~expvec,Matrix([vecmp(g):g in OrderedGenerators(grp)]));
    gens cat:=[<j eq i select u else Field[j]!1: j in [1..r]>@@iso:
                                                      u in Eltseq(bU)];
  end for;
  M:=DiagonalJoin(expvec);
  grp:=AbelianGroup(&cat invs);
  gens:=Vector(gens);
  function toVec(a)
    return Vector(Eltseq(a))*M;
  end function;
  function toA(a)
    return PowerProduct(gens,toVec(a));
  end function;
  
  if Raw then
    return grp,toA,toVec,gens;
  else
    return grp,toA;
  end if;
end intrinsic;

/**
 ** pSelmerGroup
 **
 ** Computes the p-SelmerGroup of A, i.e., the direct product of the
 ** pSelmerGroups of the direct summands of A. S should be a set of primes
 ** of the base field of A.
 **/

intrinsic pSelmerGroup(A::RngUPolRes,p::RngIntElt,S::SetEnum:Raw:=false)->
  GrpAb,Map
{Returns the p-Selmer group of a semi-simple algebra A over a field F,
for the set S of primes of F.  This combines the pSelmerGroup and map
for each field in the direct sum decomposition of A.}
  
  vprint EtaleAlg:"Computing",p,"-Selmer group of",A,"with respect to",S;
  
  //retrieve direct product rep of the algebra
  Field,iso:=AbsoluteAlgebra(A);
  r:=NumberOfComponents(Field);

  mp     := [**];
  vecmp  := [**];
  bU     := [**];
  expvec := [**];
  n      := [];
  
  for i := 1 to r do
    vprint EtaleAlg:" Computing Selmer group for",Field[i];
    OL:=IntegerRing(Field[i]);
    LS:=&join{Support(Type(P) eq RngIntElt select P*OL else OL!!P) :P in S};

    G, mp[i], vecmp[i], bU[i] := pSelmerGroup(p, LS : Raw);
    n[i]      := Ngens(G);
    expvec[i] := Matrix([(vecmp[i])(g) : g in OrderedGenerators(G)]);
  end for;

  // construct group and maps

  G := AbelianGroup([p : i in [1..&+n]]);

  function fromA(e)
    v:=iso(e);
    return &cat[Eltseq(mp[i](v[i])): i in [1..r]];
  end function;

  // map toA : use the maps from each component (very important!)

  // parse eltseq wrt G
  l := [0];
  for i := 1 to r do
    l[i+1] := l[i] + n[i];
  end for;

  function toA(x)
    y := Eltseq(x);
    a := < y[l[i]+1..l[i+1]] @@ mp[i] : i in [1..r] >;
    return a @@ iso;
  end function;

  if Raw then

    M := DiagonalJoin(< e : e in expvec>);
    V := RSpace(Integers(), Ncols(M));
    function toVec(a)
      return Vector(Eltseq(a)) * M;
    end function;

    // base elements as elements of A
    one  := < Field[i]!1 : i in [1..r] >;
    gens := [];
    for i := 1 to r do
      for u in Eltseq(bU[i]) do
        g := one;
        g[i] := u;
        Append(~gens, g);
      end for;
    end for;
    gens := [A| g @@ iso : g in gens];
    gens := Vector(gens);

    return G,
           map< A->G | a:->fromA(a), x:->toA(x) >,
           map< G->V | a:->toVec(a) >,
           gens;

  else // not Raw

    return G,
           map< A->G | a:->fromA(a), x:->toA(x) >;

  end if;
end intrinsic; 

/**
 ** LocalTwoSelmerMap
 **
 ** The map itself is easy: simply concatenate the LocalTwoSelmerMaps of all
 ** the primes extending P of all the field-summands of A. The tricky part comes
 ** in the inverse, where some chinese remaindering must be done. Presently,
 ** applications of this routine (notably LocalSelmerGroup(<EllIsogeny>,p))
 ** DEPEND on the map being simply the concatenation of the maps occurring
 ** in the returned SeqEnum (in the order in which they occur).
 **
 ** this is partly due to the fact that DirectSum([<abelian groups>]) does not
 ** return inclusion & projection maps.
 **/

function valm(p)
 fn:=function(a)
 if (a eq 0) then
  error "LocalTwoSelmerMap only defined on multiplicative group";
 else
//  a:=a*Denominator(FieldOfFractions(Order(p))!a)^2;
  v:=Valuation(a,p); return v; end if; end function;
return pmap<NumberField(Order(p))->Integers()|a:->fn(a)>; end function;

CRF:=recformat<i:RngIntElt,p:RngOrdIdl,map:Map,vmap:Map>;

// P may be RngOrdIdl or RngInt

intrinsic LocalTwoSelmerMap(A::RngUPolRes,P::Any)->Map,SeqEnum
  {Direct product of the LocalTwoSelmerMaps of the direct summands of
  the semisimple algebra A. The second returned value is for technical use
  only, and is a sequence of records. Each record contains fields i,p,map, and vmap: 
  here i is an index in the field decomposition of A, p is a prime extending P 
  to the i-th field, map is LocalTwoSelmerMap(p), and vmap is the corresponding
  valuation map on the field}
  
  locdat:=GetLocalData(A,P);
  if not(assigned(locdat`TwoSelmerMap)) then

    Field,iso:=AbsoluteAlgebra(A);
    r:=NumberOfComponents(Field);

    //we store the map components. These correspond to the field decomposition
    //of A tensored with the completion of the base field at P.
    TwoSelmerMapComponents:=
       &cat [ [ rec<CRF|i:=j,p:=p,map:=LocalTwoSelmerMap(p),vmap:=valm(p)> : 
           p in Support(Type(P) eq RngIntElt select P*IntegerRing(Field[j]) else
               IntegerRing(Field[j])!!P) ]: j in [1..r]];
    //The codomain is going to be the direct sum of the codomains of the
    //map components. However, MAGMA doesn't allow for automatic
    //construction of that. We do it by hand.
    
    grp:=AbelianGroup(&cat[Invariants(Codomain(tupple`map)):
       tupple in TwoSelmerMapComponents]);

    //One way, the map is easy. We take the representative in the field
    //decomposition, apply all map components (note that we have stored
    //the nr. of the field component of the ideal in tupple[1], so we know
    //what component to take of iso(a)) and concatenate the results
    //(and cast into the direct sum group)
    fn:=function(a)
	av:=iso(a);
	if exists{a:a in av|a eq 0} then
          error "ModSquaresMap only defined on multiplicative group";
	else
	  return grp!&cat[Eltseq(tupple`map(av[tupple`i])): 
	                        tupple in TwoSelmerMapComponents];
	end if;
      end function;
      
    //the inverse is quite a bit harder. We can take inverse images at
    //each of the primes, but we have to combine those by chinese remaindering
    //into a component. Finally we have to make sure that we compose the
    //element in A *multiplicatively*.
    
    fni:=function(b)
        b:=Eltseq(b);
	
	//we use that information of primes of the same field is adjacent
	//and that the information occurs in increasing order.
        refindex:=1;
	moduli:=[];
	elements:=[];
	av:=<>;
	n:=0;
        for tupple in TwoSelmerMapComponents do
	
	  //if the index of the field changes then we are finished
	  //with the present component. CRT and store it (and reset info) 
	  if tupple`i ne refindex then
	    assert tupple`i eq refindex+1;
	    Append(~av,CRT(elements,moduli));
	    refindex:=tupple`i;
	    moduli:=[];
	    elements:=[];
	  end if;
	  
	  //note that we allow ourselves some extra headroom to allow for
	  //the presence of a uniformiser. (val(4)+2 instead of val(4)+1).
	  Append(~moduli,tupple`p^(Valuation(Order(tupple`p)!4,tupple`p)+2));
	
	  GrpComponent:=Codomain(tupple`map);
	  
	  //advance indices to get the summand we should be dealing with
	  //(this has the effect of projecting on the direct summand of grp)
	  l:=n+Ngens(GrpComponent);
	  Append(~elements,Order(tupple`p)!
	     ((GrpComponent![b[k]:k in[n+1..l]])@@tupple`map));
	  n:=l;
        end for;
	
	//handle last component
	Append(~av,CRT(elements,moduli));
	
	//and compose element multiplicatively.
	return &*[<(i eq j) select
          av[i] else Field[j]!1 :j in [1..r]>@@iso: i in [1..r]];
      end function;
    locdat`TwoSelmerMap:=pmap<A->grp|a:->fn(a),b:->fni(b)>;
    locdat`TwoSelmerMapComponents:=TwoSelmerMapComponents;
    StoreLocalData(A,P,locdat);
  end if;
  return locdat`TwoSelmerMap,locdat`TwoSelmerMapComponents;
end intrinsic;

intrinsic RealExtensions(A::RngUPolRes,P::PlcNumElt)->SeqEnum
  {Find the maps of A into the real field, extending the given place}
  require IsInfinite(P) and IsReal(P) and NumberField(P) eq BaseRing(A):
    "Can only extend real places of the base field of the algebra";
  Aa,toAa:=AbsoluteAlgebra(A);
  exts:=[PowerStructure(Map)|];
  for i in [1..NumberOfComponents(Aa)] do
    for p in [p: p in InfinitePlaces(Aa[i])| IsReal(p) and Extends(p,P)] do
      RF:=Parent(Evaluate(Aa[i]!0,p));
      Append(~exts,map<A->RF| b:->Evaluate(toAa(b)[i],p)>);
    end for;
  end for;
  return exts;
end intrinsic;

intrinsic RealExtensions(A::RngUPolRes,P::Infty)->SeqEnum
  {Find the maps of A into the real field, extending the given place}
  require Type(BaseRing(A)) eq FldRat:
    "Can only extend real places of the base field of the algebra";
  Aa,toAa:=AbsoluteAlgebra(A);
  exts:=[PowerStructure(Map)|];
  for i in [1..NumberOfComponents(Aa)] do
    for p in [p: p in InfinitePlaces(Aa[i])| IsReal(p)] do
      RF:=Parent(Evaluate(Aa[i]!0,p));
      Append(~exts,map<A->RF| b:->Evaluate(toAa(b)[i],p)>);
    end for;
  end for;
  return exts;
end intrinsic;
  
