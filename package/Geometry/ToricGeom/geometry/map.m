freeze;

/////////////////////////////////////////////////////////////////////////
// maps.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 41262 $
// $Date: 2012-12-02 01:25:19 +1100 (Sun, 02 Dec 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Implements maps between toric varieties.
/////////////////////////////////////////////////////////////////////////

//THINK: to do : IsDominant, IsBirational, Inverse, 
//IsIsomorphism (= IsRegular and  IsBirational and IsRegular(Inverse()).
//

import "../utilities/functions.m": variables_of_scheme, prod_sequences;


declare attributes TorVar:
    identity_map;   // The identity map on X

declare type TorMap;
declare attributes TorMap:
//essential attributes:
   domain,          // Domain of map
   codomain,        // Codomain of map
   is_zero_seq,     // sequence of booleans, which marks if pullback of variable is zero
   is_zero_cone,    // a cone in the fan of the variety, marking zero variables
   principals,      // basis of rational functions on torus
   pullback_of_principals,    // pullback of above
   is_description_good,       // false if the map does know its description, or knows it, 
                              // but doesn't know if it is good.
//optional attributes:
   description,     // sequence of m-valued sections describing the map
   graph,           // ideal in big ring, which gives the graph of the map 
   is_regular,      // true if the map knows it is regular, false if the map knows it is not regular.
   lattice_map,     // false if the map knows that it is not torus invariant 
                    // and the underlying lattice map if it is torus invariant.
   inverse,         // if the map is birational, set to true first. 
                    // If the inverse is known, then set to the inverse.
                    // if the map is not birational, then set to false. 
   indeter_locus;    // A sequence of subschemes of domain, where the map is not defined.
      

///////////////////////////////////////////////////////////////////////
// printing
// l is the level: it's a string that can take values like
// "Default", "Maximal", "Minimal", "Magma".


intrinsic Print(psi::TorMap, s::MonStgElt)
{}
    if assigned psi`is_regular then
        if psi`is_regular then 
            text:="A regular";
        else
            text:="A rational";
        end if; 
    else
        text:="A";
    end if;
    // THINK: improve printing?
    printf "%o map between toric varieties described by:\n",text;
    prefix := "    ";
    desc:=AnyDescription(psi);
    for i in [1..#desc] do
        printf "%o%o", prefix, desc[i];
        if i ne #desc then printf ",\n"; end if;
    end for;
end intrinsic;





///////////////////////////////////////////////////////////////////////
// functions 
///////////////////////////////////////////////////////////////////////



// If psi:X->Y, then returns the sequence S of Length(Y) booleans, 
// with S[i]=true iff pullback of Y.i via psi is 0.}
function WhichVariablesArePulledBackToZero(psi)
    return psi`is_zero_seq;
end function;

// Returns the basis of the function field of 
// minimal coordinate subvariety containing the image of psi.
//(psi :: TorMap) -> SeqEnum[FldFunRatMElt]
function DefiningRationalFunctions(psi)
    return psi`principals;
end function;


//Returns the pullbacks by psi of the DefiningRationalFunctions(psi).
//(psi :: TorMap) -> SeqEnum[FldFunRatMElt]
function PullbackOfDefiningRationalFunctions(psi)
    return psi`pullback_of_principals;
end function;

// True iff psi has assigned any coordinate description.
// (psi :: TorMap) -> BoolElt
function HasDescription(psi)
    return assigned psi`description;
end function;


//True iff psi has assigned any coordinate description and this description is known to be good.
//(psi :: TorMap) -> BoolElt
function HasGoodDescription(psi)
    return assigned psi`description and psi`is_description_good;
end function;




function default_is_zero_cone(Y, is_zero_seq)
    inds:=[Integers()| i : i in [1..#is_zero_seq]| is_zero_seq[i]];
    return Cone(Fan(Y) , inds : extend:=true);
end function;


// Returns true iff f is homogeneous and of degree zero with respect to the
// gradings on X
function is_degree_zero(X,f)
        if not IsHomogeneous(X,f) then
                return false;
        end if;
        if Type(f) eq RngMPolElt then
                deg1, deg2:=Multidegree(X,f);
                return &and[IsZero(d) : d in deg1 cat deg2];
        else
                deg_n1, deg_n2:=Multidegree(X,Numerator(f));
                deg_d1, deg_d2:=Multidegree(X,Denominator(f));
                return &and[IsZero(deg_n1[i] - deg_d1[i]) : i in [1..#deg_n1]]
                   and &and[IsZero(deg_n2[i] - deg_d2[i]) : i in [1..#deg_n2]];
        end if;
end function;


function IsZeroCone(psi)
    return psi`is_zero_cone;
end function;

///////////////////////////////////////////////////////////////////////
// creation
///////////////////////////////////////////////////////////////////////


function CreateToricVarietyMap(domain, codomain, principals, pullback_of_principals, is_zero_seq:
                                is_zero_cone:=default_is_zero_cone(codomain, is_zero_seq))
   psi:=New(TorMap);
   psi`domain:=domain;
   psi`codomain:=codomain;
   psi`principals:=principals;
   psi`pullback_of_principals := pullback_of_principals;
   psi`is_zero_seq :=is_zero_seq;
   psi`is_zero_cone:=is_zero_cone;
   psi`is_description_good := false;
   return psi;
end function;






intrinsic ToricVarietyMap(X::TorVar,Y::TorVar, S::SeqEnum[RngMRadElt]:
relevant:=false, homogeneous:=false) -> TorMap
{} 
   require #S eq Length(Y):"Image Sequence must have the same length as the codomain";
   XiX:=FamilyOfMultivaluedSections(CoordinateRing(X));
   require Universe(S) cmpeq XiX:
           "Polynomials in image sequence must be in the field of fractions of the coordinate ring of the ambient of the domain";
   is_zero_seq:=[Booleans()|IsZero(xi) : xi in S];
   require relevant or not IsEmpty(Scheme(Y, [CoordinateRing(Y)|Y.i : i in
                                 [1..Length(Y)] | is_zero_seq[i]])): 
              "Given sequence defines an irrelevant map.";
   rays:=Rays(Y);
   is_zero_cone:=default_is_zero_cone(Y,is_zero_seq);
   is_zero_seq:=[Booleans()|rays[i] in min_gens: 
                       i in [1..#is_zero_seq]] where min_gens:=MinimalRGenerators(is_zero_cone);
   
   principals:=BasisOfRationalFunctionField(Y: is_zero_seq:=is_zero_seq); 
   pullback_of_principals:=[XiX|  Evaluate(p,S): p in principals];
   require homogeneous or &and[IsRational(p): p in pullback_of_principals] : 
           "RHS does not satisfy the homogeneity condition
               (pull-back of rational functions (degree 0) must be rational).";
   pullback_of_principals:=[FieldOfFractions(CoordinateRing(X))| RationalFunction(xi) : xi in pullback_of_principals];
   require homogeneous or &and[IsHomogeneous(X,p) :
                                 p in pullback_of_principals] : 
           "RHS does not satisfy the homogeneity condition (pull-back of
                         rational functions(degree 0)  must be homogeneous).";
   require homogeneous or &and[is_degree_zero(X,p) :
                                 p in  pullback_of_principals] : 
           "RHS does not satisfy the homogeneity condition (pull-back of
                         rational functions (degree 0) must be of degree 0).";
   psi:=CreateToricVarietyMap(X, Y, principals, pullback_of_principals, 
                                      is_zero_seq: is_zero_cone:=is_zero_cone);
   psi`description:=S;
   return psi;
end intrinsic;


intrinsic ToricVarietyMap(X::TorVar,Y::TorVar, S::SeqEnum[RngMPolElt]) -> TorMap
{}
   require #S eq Length(Y): "Image Sequence must have the same length as the codomain";
   RX:=CoordinateRing(X);
   require Universe(S) cmpeq RX:
           "Polynomials in image sequence must be in the field of fractions of the coordinate ring of the ambient of the domain";
   XiX:=FamilyOfMultivaluedSections(RX);
   return ToricVarietyMap(X,Y, ChangeUniverse(S, XiX));
end intrinsic;

intrinsic ToricVarietyMap(X::TorVar,Y::TorVar, S::SeqEnum[FldFunRatMElt]) -> TorMap
{The map X -> Y with defining equations S.}
   require #S eq Length(Y): "Image Sequence must have the same length as the codomain";
   RX:=CoordinateRing(X);
   require Universe(S) cmpeq FieldOfFractions(RX):
           "Polynomials in image sequence must be in the field of fractions of the coordinate ring of the ambient of the domain";
   XiX:=FamilyOfMultivaluedSections(RX);
   return ToricVarietyMap(X,Y, ChangeUniverse(S, XiX));
end intrinsic;




intrinsic ToricVarietyMap(X::TorVar,Y::TorVar, phi::Map[TorLat, TorLat]) -> TorMap
{}
   amb1:=OneParameterSubgroupsLattice(X);
   amb2:=OneParameterSubgroupsLattice(Y);
   require amb1 cmpeq Domain(phi) : 
     "Argument 1 does not live in the domain of the map.";
   require amb2 cmpeq Codomain(phi) : 
     "Argument 2 does not live in the codomain of the map.";
    XiX:=FamilyOfMultivaluedSections(CoordinateRing(X));
   is_zero_seq:=[Booleans()|false : i in [1..Length(Y)]];
   principals:= BasisOfRationalFunctionField(Y);
   B:=Basis(MonomialLattice(Y));
   pullback_of_principals:=[FieldOfFractions(CoordinateRing(X))|
                            DefiningMonomial(Divisor(X,v)) 
                            : v in Dual(phi)(B)];
   psi:=CreateToricVarietyMap(X, Y, principals, 
                              pullback_of_principals, is_zero_seq :
                              is_zero_cone:=ZeroCone(amb2)); 
   psi`lattice_map := phi;
   return psi;
end intrinsic;






intrinsic ToricVarietyMap(X1::TorVar, X2 :: TorVar) -> TorMap
{Rational map between toric varieties X1 --> X2 determined by phi on big torus. Fans of X and Y must live in the domain and codomain of phi respectively. If phi is not specified, it is assumed to be identity (so Fans of X and Y must live in the same lattice)}
   amb:=OneParameterSubgroupsLattice(X1);
   require amb cmpeq OneParameterSubgroupsLattice(X2) : 
     "Fans of the arguments do not live in the same lattice.";
   psi:=ToricVarietyMap(X1,X2,IdentityMap(amb));
   psi2:=ToricVarietyMap(X2,X1,IdentityMap(amb));
   psi`inverse:=psi2;
   psi2`inverse:=psi;
   return psi;
end intrinsic;






intrinsic '*'(psi1::TorMap, psi2::TorMap) -> TorMap
{Composition of maps.}
   require Codomain(psi1) cmpeq Domain(psi2): 
     "Domain of argument 2 must be the codomain of agrument 1.";
   // special cases when one of the maps is Identity
   if IsIdentity(psi1) then 
      return psi2;
   elif IsIdentity(psi2) then 
      return psi1;
   end if;
   domain:= Domain(psi1);
   codomain:=Codomain(psi2);
   Xi1:=FamilyOfMultivaluedSections(CoordinateRing(domain));
   gd1:=GoodDescription(psi1);
   gd2:=GoodDescription(psi2);
   ev:=[Xi1|Evaluate(xi , gd1) : xi in gd2];
   psi:=ToricVarietyMap(domain, codomain, ev: 
              relevant:=true, homogeneous:=true);
   // if both maps are regular, then so is their composition
   // further more, the description is complete
   if assigned psi1`is_regular and psi1`is_regular and 
      assigned psi2`is_regular and psi2`is_regular  then 
      psi`is_description_good:=true;
      psi`is_regular:=true;
   end if;
// THINK: if both maps have inverses, add inverse to the composition
   if assigned psi1`lattice_map and assigned psi2`lattice_map then
      psi`lattice_map:=psi1`lattice_map *psi2`lattice_map;
   end if;
   return psi;
end intrinsic;


intrinsic ToricIdentityMap(X::TorVar) -> TorMap
{The identity map of X.}
   if not assigned X`identity_map then 
       psi:=ToricVarietyMap(X,X);
       psi`inverse:=psi;
       psi`is_regular:=true;
       X`identity_map:=psi;
       S:=variables_of_scheme(X);
       ChangeUniverse(~S, FamilyOfMultivaluedSections(X));
       psi`description:=S;
       psi`is_description_good:=true;
   end if;
   return X`identity_map; 
end intrinsic;






///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Recover and construct attributes
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic AnyDescription(psi::TorMap) -> SeqEnum
{If psi stores any description, returns this description. Otherwise calculates some description without bothering about quality.}
   
   if HasDescription(psi) then
      return psi`description;
   end if;

   X:=Domain(psi);
   Y:=Codomain(psi);
   RLYD:=Dual(RayLattice(Y));   
   BRLYD:=Basis(RLYD);
   is_zero_seq:=WhichVariablesArePulledBackToZero(psi);
   B1:=[MonomialToCoxMonomialsLattice(Y,f) : f in DefiningRationalFunctions(psi)];
   
   B2:=[BRLYD[i] : i in [1..Length(Y)] | is_zero_seq[i]];
   B:=B1 cat B2;
   B3:=[];
   for v in BRLYD do 
      if Rank(Matrix(B cat B3)) lt Rank(Matrix(Append(B cat B3,v))) then
           Include(~B3, v);
      end if;
   end for;

   phi:=hom<RLYD->RLYD | Matrix(B cat B3)>;

   I1:=PullbackOfDefiningRationalFunctions(psi);
   I2:=[FieldOfFractions(CoordinateRing(X))| 0 :  i in B2];
   I3:=[FieldOfFractions(CoordinateRing(X))| 1 :  i in B3];
   
   psi`description:=[FamilyOfMultivaluedSections(CoordinateRing(X))|
        prod_sequences(I1 cat I2 cat I3, Eltseq(b)) : b in BRLYD@@phi];
   psi`is_description_good:=false;   

   return psi`description;
end intrinsic;

intrinsic CompleteDescription(psi::TorMap) -> SeqEnum
{Good (or complete) description of psi.}
   return GoodDescription(psi);
end intrinsic

intrinsic GoodDescription(psi::TorMap) -> SeqEnum
{Good (or complete) description of psi.}
   descr:=AnyDescription(psi);
   if HasGoodDescription(psi) then 
       return descr;
   end if;
   is_zero_seq:=WhichVariablesArePulledBackToZero(psi);
   
   Y:=Codomain(psi);
   Xi:=FamilyOfMultivaluedSections(Domain(psi));
   descr:=[is_zero_seq[i] select Zero(Xi) else descr[i]: i in [1..#is_zero_seq]];


   NY:=OneParameterSubgroupsLattice(Y);
   RLY:=RayLattice(Y);
   RLYmap:=RayLatticeMap(Y);
   F:=Fan(Y);
   rays:=AllRays(F);
   C:=IsZeroCone(psi);
   NF, phi:=NormalFan(F,C);
   if IsIdentity(phi) then 
       translation:=[1..#Cones(F)];
   else 
       // THINK: Might be cheaper to operate on indices instead:
       translation:=[Index([ C subset CC and Image(phi,CC) eq c 
               : CC in Cones(F)], true) : c in Cones(NF)];
   end if;
             
   factors, exponents:=Exponents(descr);
   psi`description:=descr;

   RLphi:= Expand(RLYmap*phi);
   for i in [1..#factors] do 
      expon:=RLY![e[i] : e in exponents ];
      v:=RLphi(expon);
      bool, k:=IsInSupport(v,NF);
      if bool then
         inds:=ConeIndices(Fan(Y))[translation[k]];
         C:=Cone([Basis(RLY,j) : j in inds]);
         if not expon in C then
              w:=Eltseq(expon - Preimage( v, RLphi, C));
              psi`description:=[Xi|psi`description[j]/(Power(factors[i],w[j]))  
                                : j in [1..#w]];
         end if;
      end if;
   end for;
   psi`is_description_good:=true;
   return AnyDescription(psi);
end intrinsic;




intrinsic  MonomialToCoxMonomialsLattice(X::TorVar,f::RngMPolElt) -> TorLatElt
{}
   require Parent(f) cmpeq CoordinateRing(X):
            "Argument 2 is not in the Cox Ring of argument 1.";
   return Dual(RayLattice(X))!Exponents(f);
end intrinsic;


intrinsic  MonomialToCoxMonomialsLattice(X::TorVar,f::FldFunRatMElt) ->
TorLatElt
{Given a monomial on X returns the element in the Cox Monomials Lattice (dual to Ray Lattice) corresponding to f.}
   require Parent(f) cmpeq FieldOfFractions(CoordinateRing(X)):  
            "Argument 2 is not in the Cox Ring of argument 1.";
   f1:=Numerator(f);
   f2:=Denominator(f);
   return Dual(RayLattice(X))!Exponents(f1) -  Dual(RayLattice(X))!Exponents(f2);
end intrinsic;



intrinsic BasisOfDegree0CoxMonomials(X::TorVar : is_zero_seq:=[false: i in [1..Length(X)]]) -> SeqEnum[TorLatElt]
{Returns a basis of the rational function field of X expressed in terms of lattice points of Cox monomials lattice.}
  RL:=RayLattice(X);
  RLmap:=RayLatticeMap(X);

  zero_variables:=RLmap([Basis(RL,i) : i in [1..Length(X)] | is_zero_seq[i]]);

  quo_in_N, q:=Quotient(ConeWithInequalities(LinearConeGenerators(zero_variables)));
  emb:=KernelEmbedding(q);
  sub_in_mono_lattice:=Domain(emb);
  return Dual(RLmap)(emb(Basis(sub_in_mono_lattice)));
end intrinsic;


intrinsic BasisOfRationalFunctionField(X::TorVar : is_zero_seq:=[false: i in [1..Length(X)]]) -> SeqEnum[FldFunRatMElt]
{A basis of the rational function field of X expressed in terms of rational
monomials of Cox Ring.}
  F:=FieldOfFractions(CoordinateRing(X));
  return [F| DefiningMonomial(Divisor(X,v)):
         v in BasisOfDegree0CoxMonomials(X: is_zero_seq:=is_zero_seq)];
end intrinsic;

intrinsic UnderlyingToriMap(psi::TorMap) -> TorMap
{The map of the big tori of domain and codomain. The image of psi must not be contained in any toric stratum.}
  require not &or WhichVariablesArePulledBackToZero(psi): 
      "The image of Argument is contained in a toric stratum.";
  // THINK: store the result!
  // THINK: do not calculate the composition, but extract from the defining data of maps!
  T1, emb:=BigTorus(Domain(psi));
  T2, _, proj:=BigTorus(Codomain(psi));
  return emb*psi*proj;
end intrinsic;













///////////////////////////////////////////////////////////////////////
// map attributes
///////////////////////////////////////////////////////////////////////

intrinsic Domain(psi::TorMap) -> TorVar
{The domain of psi.}
    return psi`domain;
end intrinsic;

intrinsic Codomain(psi::TorMap) -> TorVar
{The codomain of psi.}
    return psi`codomain;
end intrinsic;





intrinsic IndeterminacyLocus(psi::TorMap) -> SeqEnum[Sch]
{Returns a sequence of schemes, whose union is the indeterminacy locus of psi.}
    if not assigned psi`indeter_locus then 
        descr:=GoodDescription(psi);
        dens:=&join[{p[1] : p in Factorisation(Denominator(xi))} : xi in descr];
        irrel:=[Scheme(Codomain(psi), i) : i in IrrelevantComponents(Codomain(psi))];
        pullbacks:=[PowerStructure(Sch)|i@@psi : i in irrel];
        psi`indeter_locus:=pullbacks cat [PowerStructure(Sch)|Scheme(Domain(psi),f): f in dens];
    end if;
    return psi`indeter_locus;
end intrinsic;





intrinsic IsRegular(psi::TorMap) -> BoolElt
{Returns true iff psi is a regular map.}
    if not assigned psi`is_regular then 
        // THINK: if psi is torus invariant it should be cheaper to check on fans.
        psi`is_regular:=&and[IsEmpty(Z) : Z in IndeterminacyLocus(psi)];
    end if;
    return psi`is_regular;
end intrinsic;



// THINK: calculate inverse if exists!
intrinsic Inverse(psi::TorMap) -> TorMap
{Inverse of psi, provided it is known.}
    require assigned psi`inverse: "Inverse of the argument is not known"; 
    return psi`inverse;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// map properties
///////////////////////////////////////////////////////////////////////


intrinsic IsIdentity(psi::TorMap) -> BoolElt
{true if psi is equal to identity map of some toric variety.}
    return Domain(psi) cmpeq Codomain(psi) and 
          psi eq ToricIdentityMap(Domain(psi));
end intrinsic;

intrinsic IsTorusInvariant(psi::TorMap)-> BoolElt, Map[TorLat,TorLat]
{True iff psi is described by monomials (without coefficients). Then also returns the underlying map of lattices. If any of the variables is pulled back to 0, then returns false.}

   if assigned psi`lattice_map then
      if ISA(Type(psi`lattice_map), Map) then
         return true, psi`lattice_map;
      end if;
      return false, _;
   end if;

   X:=Domain(psi);
   Y:=Codomain(psi);
   NX:=OneParameterSubgroupsLattice(X);
   NY:=OneParameterSubgroupsLattice(Y);

   if Dimension(Y) eq 0 then
      psi`lattice_map:=ZeroMap(OneParameterSubgroupsLattice(X), 
                               OneParameterSubgroupsLattice(Y));
      return true,  psi`lattice_map;
   end if;

   if &or WhichVariablesArePulledBackToZero(psi) then
       psi`lattice_map:=false;
       return false, _;
   end if;
   


   pullbacks_of_principals:=PullbackOfDefiningRationalFunctions(psi);
   
   

   if not &and[IsMonomial(f):  f in pullbacks_of_principals] then 
       psi`lattice_map:=false;
       return false, _;
   end if;    


   principals:=DefiningRationalFunctions(psi);
   RLMY:=RayLatticeMap(Y);
   principals_in_MY:=[MonomialToCoxMonomialsLattice(Y,f)@@Dual(RLMY) 
                                       : f in principals];
   RLMX:=RayLatticeMap(X);
   pullbacks_in_MX:=[MonomialToCoxMonomialsLattice(X,f)@@Dual(RLMX) 
                                       : f in pullbacks_of_principals];
   MtrxY:=Matrix(principals_in_MY)^-1;
   MtrxX:=Matrix(pullbacks_in_MX);
   psi`lattice_map:=hom<NX -> NY | Transpose(MtrxY*MtrxX)>;
   return true, psi`lattice_map;

end intrinsic;

/*
intrinsic Graph(psi::TorVarMap) -> RngMPol
{Returns the ideal for computing the images of varieties under psi, together with maps of rings.}
   descr:=GoodDescription(psi);
   irrat:=&cat[Factorisation(IrrationalPart(xi)) : xi in descr];
   factors:=[PolynomialRing(Universe(irrat))|];
   exponents:=[Integers()|];

   for p in irrat do
      i:=Index(factors, p[1]);
      if IsZero(i) then
         Append(~factors,p[1]);
         Append(~exponents, Denominator(p[2]));
      else
         exponents[i]:=LCM(exponents[i], Denominator(p[2]));
      end if;
   end for;



end intrinsic;
*/


///////////////////////////////////////////////////////////////////////
// map application
///////////////////////////////////////////////////////////////////////


/*
// THINK: improve, where the result is; add requirements. Suspending for now.
// THINK: psi @ P or P @ psi?
intrinsic '@'(psi::TorMap, P::Pt) -> Pt
{Image psi(P).}
   descr:=GoodDescription(psi);
   evalu:=[Evaluate(xi, ChangeUniverse(P, CoordinateRing(Codomain(psi)))) 
                                                        : xi in descr];
   return evalu;
end intrinsic;
*/

intrinsic '*'(psi::TorMap, f::RngMPolElt) -> RngMPolElt
{}
   cox2:=CoordinateRing(Codomain(psi));
   require f in cox2: "Polynomial must be in the Cox ring of codomain of psi.";
   return Evaluate(f, GoodDescription(psi));
end intrinsic;


intrinsic '*'(psi::TorMap, f::FldFunRatMElt) -> FldFunRatMElt
{}
   cox2:=CoordinateRing(Codomain(psi));
   n:=Numerator(f);
   d:=Denominator(f);   
   require n in cox2: "Function must be in the Cox ring of codomain of map.";
   psi_times_d:=psi*d;
   require not IsZero(psi_times_d): "Argument pulls back to 1/0."; 
   return (psi*n)/(psi_times_d);
end intrinsic;

intrinsic '*'(psi::TorMap, f::RngMRadElt) -> FldFunRatMElt
{Pulls f back by map psi. f must be in the Cox ring of codomain of psi.}
   cox2:=CoordinateRing(Codomain(psi));
   n:=Numerator(f);
   d:=Denominator(f);   
   require n in FamilyOfMultivaluedSections(cox2): "Function must be in the Cox ring of codomain of map.";
   psi_times_d:=Evaluate(d, GoodDescription(psi));
   require not IsZero(psi_times_d): "Argument pulls back to 1/0."; 
   return Evaluate(n, GoodDescription(psi))/(psi_times_d);
end intrinsic;



intrinsic Pullback(psi::TorMap, D::DivTorElt)-> DivTorElt
{D must be Q-Cartier. If psi is torus-invariant, then returns the pull-back of D by psi. Otherwise return a torus-invariant divisor, which is linearly equivalent to the pull-back of D. psi should be regular in codim 1, or otherwise, there will be component, which has unpredictable multiplicity.}
  require Codomain(psi) cmpeq Variety(D) : "Argument 2 must be defined on codomain of Argument 1.";
  require IsQCartier(D) : "Argument 2 is not Q-Cartier.";
  X:=Domain(psi);
  bool, phi:=IsTorusInvariant(psi);
  if bool then
      D1:=Divisor(X, [D*phi(r) : r in AllRays(Fan(X))]);
  else
      bool:=IsCartier(D);
      if bool then 
        q:=1;
      else
        YCWMap:=CartierToWeilMap(Codomain(psi));
        q:=Denominator(Weil(D)@@YCWMap);
      end if;
      DD:= LinearlyEquivalentDivisorWithNoSupportOn(q*D, 
                           [Codomain(psi).i : i in [1..Length(Codomain(psi))] | 
                            WhichVariablesArePulledBackToZero(psi)[i]]);
      fDD:=DefiningMonomial(DD);
      fD1:=RationalFunction(RationalPart(psi*fDD));
      D1:=(1/q) *Divisor(X, fD1);
  end if;
  return D1; 
end intrinsic;



intrinsic 'eq'(psi1::TorMap, psi2::TorMap)->BoolElt
{Equality test for maps between Toric Varieties.}
      X:=Domain(psi1);
      Y:=Codomain(psi1);
      require X cmpeq Domain(psi2) and Y cmpeq Codomain(psi2): "Maps must be between the same varieties.";
      if not  WhichVariablesArePulledBackToZero(psi1) eq  WhichVariablesArePulledBackToZero(psi2) then
          return false; 
      end if;
      basis1:=DefiningRationalFunctions(psi1);
      basis2:=DefiningRationalFunctions(psi2);
      pullbacks1:=PullbackOfDefiningRationalFunctions(psi1);
      pullbacks2:=PullbackOfDefiningRationalFunctions(psi2);

      if basis1 eq basis2 then 
          return pullbacks1 eq pullbacks2;
      end if;

      RLMY:=RayLatticeMap(Y);
      Q,pi:=Quotient(IsZeroCone(psi1));
      phi:=Dual(RLMY*pi);
      basis1_in_MY_reduced:=[Dual(Q)|MonomialToCoxMonomialsLattice(Y,f)@@phi 
                                       : f in basis1];

      basis2_in_MY_reduced:=[Dual(Q)|MonomialToCoxMonomialsLattice(Y,f)@@phi 
                                       : f in basis2];

      Mtrx:=RowSequence(Matrix(basis1_in_MY_reduced)*(Matrix(basis2_in_MY_reduced))^-1);

      pullbacks21:=[&*[pullbacks2[i]^M[i] : i in [1..#M]] : M in Mtrx];

      return pullbacks21 eq pullbacks1;
end intrinsic;

/*
intrinsic ()->
{}




end intrinsic;
*/






