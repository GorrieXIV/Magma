freeze;

/////////////////////////////////////////////////////////////////////////
// subscheme.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42133 $
// $Date: 2013-02-17 00:52:42 +1100 (Sun, 17 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": variables_of_scheme,seq_of_k_subsets, remove_repetitions;
import "../fan/fan.m": construct_fan_from_rays;


declare attributes Sch:
  is_stratum,         // remembers if the scheme is a toric stratum of its ambient 
  face,               // if is_stratum, then remembers corresponding face of fan
  stratum_map,        // if the scheme has variables in the ideal,
                      // then remembers the embedding of the appropriate coordinate toric variety. 
  stratum_scheme,     // pullback of the scheme under toric_stratum_map
  binomial_map,       // if the scheme has binomials in the ideal, 
                      // then remembers the embedding/normalisation of the minimal toric variety, 
                      // containing the reduced subscheme.
  binomial_scheme,    // pullback of the scheme under binomial_map
  blow_up_map,        // map from Bl(S) to Ambient(S).  
  restr_to_torus,     // the restriction of S to the biggest torus 
                      // intersecting S;
  restr_to_torus_map; // map composing big_torus_embedding and stratum_map.

function is_in_toric(Z)
   X:=Ambient(Z);
   return ISA(Type(X), TorVar);
end function;

procedure require_is_in_toric(Z: text:="Argument should be a subscheme in Ambient of type TorVar.")
   if not is_in_toric(Z) then 
       error text;
   end if;
end procedure;

intrinsic Scheme(X::TorVar, C::TorCon) -> Sch
{Returns the toric stratum corresponding to C. C must be a face of fan of X.}
   require Ambient(C) cmpeq OneParameterSubgroupsLattice(X): "The cone (argument 2) must live in the 1-parameter subgrous lattice of argument 1.";
   require C in Fan(X): "The cone (argument 2) must be a cone in Fan of argument 1.";
   indices:=[Index(rays, r): r in MinimalRGenerators(C)] where rays is Rays(Fan(X));
   Z:=Scheme(X,[X.i : i in indices]);
   Z`is_stratum:=true;
   Z`face:=C;
   return Z;
end intrinsic;

intrinsic IsStratum(Z::Sch) -> BoolElt
{True iff Z is defined by vanishing of variables and is non-empty.}
   require_is_in_toric(Z);
   if not assigned Z`is_stratum then 
      if IsEmpty(Z) then 
         Z`is_stratum:=false;
      else  
         B:=GroebnerBasis(Z);
         Z`is_stratum:= B subset variables_of_scheme(Z);
      end if;
   end if;
   return Z`is_stratum;
end intrinsic;

intrinsic Face(Z::Sch) -> BoolElt
{If Z is a stratum, returns the corresponding cone in the fan.}
   require IsStratum(Z): "Argument must be a stratum.";
   if not assigned Z`face then 
       B:=GroebnerBasis(Z);
       variables:= variables_of_scheme(Z);
       indices:=[Index(variables,b) : b in B];
       F:=Fan(Ambient(Z));
       C:=Cone([rays[i] :  i in indices]) where rays is Rays(F);
       CC:=Face(F,C);
       Z`face:=CC;
   end if;
   return Z`face;
end intrinsic;

/*
intrinsic '@'(psi::TorMap,Z::Sch) -> Sch
{Closure of the image psi(Z)}
   require Z subset Domain(psi): "Argument is not in the domain of the map";
   
 
end intrinsic;
*/

intrinsic '@@'(Z::Sch, psi::TorMap) -> Sch
{Preimage of Z under psi}
   // THINK: if we ever allow maps between subschemes of toric varieties,
   // then we need to check if Z is a subset of Codomain(psi) -- this might be 
   // expensive, so an easy check if Codomain is an ambient, should be
   // preserved anyway! 
   require Ambient(Z) eq Codomain(psi):
      "Argument is not in the codomain of the map";
   if IsIdentity(psi) then 
      return Z;
   end if;
   gd:=GoodDescription(psi);
   R:=CoordinateRing(Domain(psi));

   if &and [IsRational(xi) : xi in gd] then
      gd:=[FieldOfFractions(R)| RationalFunction(xi) : xi in gd];
      equs:=[R | Numerator(Evaluate(equ,gd)) : equ in Equations(Z)];
   else
      equs:=[R | Numerator(RationalFunction(RationalRoundUp(psi*f))) : f in Equations(Z)];
   end if;

   if &or[IsInvertible(equ) : equ in equs] then 
       return EmptyScheme(Domain(psi));
   end if;
   if Dimension(Domain(psi)) eq 0 and IsField(BaseRing(Domain(psi))) then
       return Domain(psi);
   end if;
   return Scheme(Domain(psi), equs);
end intrinsic;

intrinsic Stratum(Z::Sch) -> Sch, TorMap
{Returns the pullback of scheme Z to minimal toric stratum containing Z, 
together with the map giving embedding of ambients.}
   if not assigned Z`stratum_map then
     require_is_in_toric(Z);
     // Find monomials in the ideal:
     monos:=[i : i in [1..#vars] | vars[i] in Ideal(Z)] where vars is variables_of_scheme(Z);
     if IsEmpty(monos) then
         psi:=ToricIdentityMap(Ambient(Z));
         ZZ:=Z;
     else 
        // find coordinate subvariety:
        _,psi:=CoordinateSubvariety(Ambient(Z),monos);
        // pullback Z to there:
        ZZ:=Z@@psi;
     end if;
     Z`stratum_scheme:=ZZ;
     Z`stratum_map:=psi;
   end if;
   return Z`stratum_scheme, Z`stratum_map;
end intrinsic;

intrinsic BinomialToricEmbedding(Z::Sch) -> Sch, TorMap
{Takes binomial equations in the ideal of Z and construct toric variety, which is the normalisation of the closure of subtorus described by those binomials. Returns the pullback of scheme Z and the normalisation map into the ambient of Z.}
   if not assigned Z`binomial_map then 
        require_is_in_toric(Z);
	binomials:=[equ : equ  in Equations(Z)| 
                                   #Terms(equ) eq 2];
	binomials:=[Terms(equ): equ in binomials | Seqset(Coefficients(equ)) eq {-1,1}];
        
	if IsEmpty(binomials) then
                Z`binomial_map:=ToricIdentityMap(Ambient(Z));
                Z`binomial_scheme:=Z;
        else 
                X:=Ambient(Z);
 	        binomials:=[MonomialToCoxMonomialsLattice(X,term[1]) - MonomialToCoxMonomialsLattice(X,term[2])
				: term in binomials];
                forms:=binomials@@Dual(RayLatticeMap(X));
                L2,phi2:=Quotient(forms);
                L3:=Dual(L2);
                phi3:=Dual(phi2);
                cones:=Cones(Fan(X))@@phi3;
	        new_fan:=Fan(cones : define_fan);
                Y:=ToricVariety(BaseRing(X), new_fan);
                psi:=ToricVarietyMap(Y,X, phi3);
                Z`binomial_scheme:=Z@@psi;
                Z`binomial_map:=psi;
	end if;
   end if;
   return Z`binomial_scheme, Z`binomial_map;
end intrinsic;

intrinsic Blowup(S::Sch) -> TorVar, TorMap
{If S is defined by a monomial ideal, then returns the Blow up of this ideal,
together with the map.}
   if not assigned S`blow_up_map then 
     X:=Ambient(S);
     require ISA(Type(X), TorVar) : 
         "Argument must be a subscheme of a toric variety.";
     require &and[IsMonomial(m) :  m in Equations(S)] : 
         "Argument must be a monomial subscheme.";
     if IsEmpty(Equations(S)) then 
         S`blow_up_map:=ToricIdentityMap(X);
     end if;
     P:=Polytope(
         [MonomialToCoxMonomialsLattice(X,m) : m in Equations(S)]) +
           PositiveQuadrant(Dual(RayLattice(X)));
     F:=Fan(X);
     cone_indices:=ConeIndices(F);
     B:=Basis(RayLattice(X));
     // THINK: Big cases might speed up if we give the result of this 
     //        explicitely.
     basis_cones:=[Dual(Cone(B[Setseq(c)])) : c in cone_indices];
     
     polyhedrons:=[Preimage(Dual(RayLatticeMap(X)), P+c) : c in basis_cones];
     cones_new:= &cat[ Cones(DualFan(P)) : P in polyhedrons];
     rays:=&join [Seqset(MinimalRGenerators(c)) : c in cones_new];
     Rs:=[R: R in Rays(F) | R in rays]
          cat Sort(Setseq(rays diff Seqset(Rays(F))));
     bool,bl_fan:=construct_fan_from_rays(Rs, cones_new:
              max_cones:=false, min_rays:=false, 
              extra_cones:=[], intersection_data:=[]);
     require bool: bl_fan;
     Bl:=ToricVariety(BaseRing(S), bl_fan);
     psi:=ToricVarietyMap(Bl,X);
     S`blow_up_map:=psi;
   end if;
   return Domain(S`blow_up_map), S`blow_up_map;
end intrinsic;

intrinsic NonQFactorialLocus(X::TorVar) -> Sch
{Returns the monomial reduced subscheme of X whose points are non Q-factorial
points of X.}
    require IsField(BaseRing(X)): "Base ring must be a field"; 
    if IsQFactorial(X) then
        return EmptySubscheme(X);
    end if;

    F:=Fan(X);
    NQFcones, indices_of_NQFcones := NonSimplicialCones(F);
    facets_of_NQFc:=[[ConeIndices(F,f) :f in Facets(C)] : C in NQFcones];
    R:=CoordinateRing(X);
    all_variables:={1..Length(X)};
    polynomials:=[ [R|  &*[R | R.i : i in indices_of_NQFcones[j] diff cone]: 
                              cone in facets_of_NQFc[j] ]
                              : j in [1..#facets_of_NQFc]];
    ideal:=&meet [Ideal(polys) : polys in polynomials];
    return Scheme(X, ideal);
end intrinsic;

intrinsic DimensionOfNonQFactorialLocus(X::TorVar) -> RngIntElt
{Dimension of the locus of non-Q-factorial points.}
    if IsQFactorial(X) then 
       return -1;
    end if;
    F:=Fan(X);
    NQFcones:= NonSimplicialCones(F);
    codim:=Min([Dimension(C) : C in NQFcones]);
    return Dimension(X) - codim;
end intrinsic;

intrinsic InternalDimensionForSchemesInToricVarieties(S::Sch) -> RngIntElt
{For internal use only --- gives the dimension of a subscheme taking into
account components contained in non-Q-factorial locus.}
    // saturate irrelevant components:
    X:=Ambient(S); 
    // 0-dimensional case is slightly tricky, because magma does not 
    // handle very well the schemes of dimension 0.
    if Length(X) eq 0 then
         if IsEmpty([e: e in Equations(S) | not IsZero(e)]) then 
             return 0;
         elif 1 in Ideal(S) then 
             return -1;
         else 
             return 0;
         end if;
    end if;
    I:=Saturation(Ideal(S), IrrelevantIdeal(X));
    expected_dimension:=Max(Dimension(I) - NumberOfGradings(S), -1);
    // deal with the easy cases first:
    // Q-factorial case:
    if IsQFactorial(X) then
        return expected_dimension;
    end if;
    // S is empty case:
    if CoordinateRing(X)!1 in I then
        return expected_dimension;
    end if;
    // Hypersurface case:
    if expected_dimension eq Dimension(X)-1 then 
        return expected_dimension;
    end if;
    // Chop off non-Qfactorial locus:
    sing:=NonQFactorialLocus(X);
    S_minus_sing:=Saturation(I, Ideal(sing));
    // Case when choping off did not change anything:
    if I eq S_minus_sing then 
        return expected_dimension;
    end if;
    _, indices:=NonSimplicialCones(Fan(X));
    // this the dimension of the main component
    // (away from non-Q-factorial locus).
    dims:=[Integers()|Dimension(S_minus_sing) - NumberOfGradings(S), -1];
    for ind in indices do
        Y, psi:=CoordinateSubvariety(X, Setseq(ind));
        Append(~dims, $$(S@@psi));
    end for;
    // can't simply return Max(dims), because, then it also returns 
    // the index of the maximal entry in the sequence: 
    dim:=Max(dims);
    return dim;
end intrinsic;

intrinsic RestrictionToSubtorus(Z::Sch) -> Sch, TorMap
{The restriction of Z to the biggest subtorus of the ambient containing Z.}
  if not assigned Z`restr_to_torus then 
      X:=Ambient(Z);
      ZZ,psi1:=Stratum(Z); 
      T,psi2:=BigTorus(Ambient(ZZ));
      psi3:=psi2*psi1;
      ZinT:=ZZ@@psi2;
      Z`restr_to_torus_map:=psi3;
      Z`restr_to_torus:=ZinT;
  end if;
  return Z`restr_to_torus, Z`restr_to_torus_map;
end intrinsic;

 
