freeze;
//
//  Field Acrobatic, ammm, I mean Arithmetic
//
//  following used to be fields.m:
//


/******************************************************************************
 **
 **   Examples:
 **
 **/  

/*
     Q := Rationals();
     P := PolynomialRing(Q); x := P.1;
     k<i> := ext< Q | x^2+1 >;             // k = Q(i)
     K<w> := ext< k | x^2-2 >;             // K = Q(i,\sqrt(2))
     L<i_w> := ext< Q | x^4 - 2*x^2 + 9 >; // L = Q(i+\sqrt(2))

     // L and K are isomorphic.

     AutomorphismGroup(K);     // Gal(K:k) 
     AutomorphismGroup(K,k);   // Gal(K:k), the SAME as above
     AutomorphismGroup(L,k);   // Gal(L:k), isomorphic to above

     AutomorphismGroup(L);     // Gal(L,Q)
     AutomorphismGroup(L,Q);   // Gal(L,Q), the SAME as above
     AutomorphismGroup(K,Q);   // Gal(K,Q), isomorphic to above

*/


/******************************************************************************
 **
 **   Constructing the group of automorphisms of a field extension
 **
 **/  

intrinsic AutomorphismGroup( K::FldAlg, k::FldAlg ) -> GrpPerm, PowMapAut, Map
{The group of automorphisms of the field K fixing the subfield k. 
Returns three values: the group as a permutation group G, a container structure,
and a map sending elements of G to automorphisms of K}

     Ks := SimpleExtension(K);
     ks := SimpleExtension(k);

     require IsCoercible(K, ks.1) : 
            "The first argument must be an extension of the second argument";
  
     aut,           // Automorphism group of Ks as GrpPerm
     AUT,           // dito as a Set of maps
     map_aut_AUT    // transfer map from aut to AUT 
                    := AutomorphismGroup(Ks:Partial);

     gal,           // Galois group of Ks over ks as GrpPerm
     map_gal_aut    // transfer map from gal to aut 
                    := FixedGroup(Ks, ks:Partial);
                    
     map_gal_AUT := map_gal_aut*map_aut_AUT;
          
     // map := hom< gal -> Aut(K) | g :-> Coercion(K,Ks)*map_gal_AUT(g)*Coercion(Ks,K) >;
     // the following is the same but doesn't bother us with "Composition of thausands of maps"
     map := hom< gal -> Aut(K) | g :-> 
                    iso< K -> K | x :-> (Coercion(K,Ks)*map_gal_AUT(g   )*Coercion(Ks,K))(x),
                                  x :-> (Coercion(K,Ks)*map_gal_AUT(g^-1)*Coercion(Ks,K))(x) > >;

     return gal, Aut(K), map;
     
     
end intrinsic;

intrinsic AutomorphismGroup( K::FldRat, k::FldRat ) -> GrpPerm, PowMapAut, Map
{"} // "
  return AutomorphismGroup(K);
end intrinsic;


intrinsic AutomorphismGroup( K::FldAlg, k::FldRat ) -> GrpPerm, PowMapAut, Map
{"} // "
     Ks := SimpleExtension(K);

     gal,           // Automorphism group of Ks as GrpPerm
     AUT,           // dito as a Set of maps
     map_gal_AUT    // transfer map from gal to AUT 
                    := AutomorphismGroup(Ks:Partial);

          
     // map := hom< gal -> Aut(K) | g :-> Coercion(K,Ks)*map_gal_AUT(g)*Coercion(Ks,K) >;
     // the following is the same but doesn't bother us with "Composition of thausands of maps"
     map := hom< gal -> Aut(K) | g :-> 
                    iso< K -> K | x :-> (Coercion(K,Ks)*map_gal_AUT(g   )*Coercion(Ks,K))(x),
                                  x :-> (Coercion(K,Ks)*map_gal_AUT(g^-1)*Coercion(Ks,K))(x) > >;

     return gal, Aut(K), map;

end intrinsic;


intrinsic AutomorphismGroup( K::FldCyc:Abelian := false, Partial) -> GrpPerm, PowMapAut, Map
{The group of automorphisms of the field K. 
Returns three values: the group as a permutation group G, a container structure,
and a map sending elements of G to automorphisms of K}

  g, mg := CyclotomicAutomorphismGroup(K);
  if Type(g) eq GrpPerm then
    return g, Aut(K), mg;
  end if;
  mG := CosetAction(g, sub<g|>);
  G := Codomain(mG);
  
  return G, Aut(K), Inverse(mG)*mg; 
end intrinsic;  

intrinsic AutomorphismGroup( K::FldAlg:Abelian := false, Partial := false ) -> GrpPerm, PowMapAut, Map
{"} // "
  if Partial then
    AddAttribute(Type(K), "Aut");
    if assigned K`Aut then
      return Explode(K`Aut);
    end if;
    a := Automorphisms(K);
    g, mg := GenericGroup(a[2..#a] : Id := hom<K->K|GeneratorsSequence(K)>,
                              Mult := function(a,b)
                                c := a*b;
                                c`IsHomomorphism := true;
                                return c;
                                end function);
    xg := CosetAction(g, sub<g|>);                            
    g := Image(xg);
    mg := Inverse(xg)*mg;
    K`Aut := <g, Codomain(mg), mg>;
    return Explode(K`Aut);
  end if;
  if BaseField(K) eq Rationals() then
    if Type(DefiningPolynomial(K)) eq SeqEnum then
      Ks := SimpleExtension(K);
      G, _, mG := InternalAutomorphismGroup(Ks: Abelian := Abelian);
      return G, Aut(K), map<G -> Aut(K) | x:-> 
                              map<K -> K | y :-> K!(mG(x)(Ks!y))>>;
    else
      return InternalAutomorphismGroup(K:Abelian := Abelian);
    end if;
  end if;
  return AutomorphismGroup( K, BaseField(K) ); 
  
end intrinsic;


intrinsic AutomorphismGroup( K::FldRat ) -> GrpPerm, PowMapAut, Map
{"} // "
  return Sym(1), Aut(K), map< Sym(1)->Aut(K) | x:->iso<K->K|> >; 
end intrinsic;


// TO DO: looks misplaced

intrinsic Automorphisms(C::FldCyc) -> []
  {The automorphisms of the cyclic field C}
  A, _, mA := AutomorphismGroup(C);
  return [a@mA : a in A];
end intrinsic;


// TO DO: idiotic algorithm selection

intrinsic IsNormal(K::FldAlg[FldAlg]) -> BoolElt
{ True iff K is a normal extension of its base field. }
  if IsAbsoluteField(BaseField(K)) then
    return #GaloisGroup(K) eq Degree(K);
  end if;
  return #Automorphisms(K) eq Degree(K);
end intrinsic;

