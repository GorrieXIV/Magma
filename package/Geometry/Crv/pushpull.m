freeze;

/*****************************************************************
pushpull.m

Date: 14 Feb 2003

Author: Nils Bruin

Pullback and pushforward routines for morphisms between curves.

Given a map phi:D->C between curves over compatible base rings,
it implements

Pullback(phi,X) and Pushforward(phi,Y)

for X,Y functions, places, and divisors on C resp. D

and

Pullback(phi,omega)

for omega a differential on C.

It also implements Degree and RamificationDivisor

WARNING:

Presently, Pushforward does not work for places in the support of the base
locus of phi.

Pushing forward a divisor involves pushing forward the "infinite places" of
the codomain of phi. Therefore, if one wants to use pushforward of
divisors, one should make sure that phi is defined at the "infinite places".
If the infinite places are represented by non-singular loci on the model,
then Extend(phi) will do the trick. Otherwise, change the model of the
codomain such that the places at infinity miss the base locus of phi.

Mike Harrison 14/12/2004

Began work of conversion to new function field type: changed Pullback(map)
and toRelativeMap and Pushforward, Pullback for functions.

Will change the pushforward map to construct the field extension as
a finite affine algebra over the lower field. This has several
advantages (particularly for non-plane curves)
 - it can handle finite inseparable maps fine.
 - there is no need to use multiple norms for non-simple relative extensions
   (if the relative algebraic function field extension was built that way)
   or to avoid this by flattening to a simple extension [this isn't an
   important point].
 - this should be a prototype for using the new function fields on their own
   to decsribe generically finite maps. No algebriac function field is needed
   so this can be generalised to higher dimensional cases. [ However, see the
   note below!]

Slight pain - was planning to use only the new function fields for the
  pushforward and pullback maps: that's one of the main reasons they
  are there! However, currently the arithmetic is much slower than for
  the algebraic function fields, so will revert back to those for the
  moment for the lower relative function field for the relative
  pushforward map.
  
MCH 3/1/05 - finished changes except for functions for differentials
              on curves (as opposed to on function fields).
	     Now done!

******************************************************************/

import "../Sch/funcoord.m": NonEmptyPatchIndex;

declare attributes MapSch: RCtoKD, RDtoKDrel,degree;

/****************************************************
 * Some auxiliary intrinsics
 ****************************************************/

forward toRelativeMap, AlFFPullback;

function AffNorm(relmap,f)
 // Computes the norm of f (in KD) for the function field inclusion
 //  KC -> KD corresponding to the relative map
  
   return Determinant( RepresentationMatrix(relmap(Numerator(f))) )/
	   Determinant( RepresentationMatrix(relmap(Denominator(f))) );
	  
end function;

function AffTrace(relmap,f)
 // Computes the trace of f (in KD) for the function field inclusion
 //  KC -> KD corresponding to the relative map

   return Trace( RepresentationMatrix(
	   relmap(Numerator(f))/relmap(Denominator(f))) );

end function;

function MapTrace(phi,f)
 // Useful internal function for getting trace of f by phi map
 
      F,mp := AlgorithmicFunctionField(FunctionField(Codomain(phi)));
      return AffTrace(toRelativeMap(phi),f) @@ mp;
end function;

/*********************************************
This one's more elegant, using function fields.
However, it seems quite a bit slower than the option below.

intrinsic Degree(phi::MapSch)->RngIntElt
  {Degree of a non-constant morphism between curves}
  require IsCurve(Domain(phi)) and IsCurve(Codomain(phi)):
    "Only implemented for maps between curves";
  i:=InternalIsogenyDegree(phi);
  if i ge 0 then phi`degree:=i; return i; end if;
  if not(assigned(phi`degree)) then
    C:=Codomain(phi);
    x:=SeparatingElement(FunctionField(C));
    D:=GCD(Divisor(x),Divisor(Parent(x)!1));
    d:=Integers()!(Degree(Pullback(phi,D))/Degree(D));
    phi`degree:=d;
  end if;
  return phi`degree;
end intrinsic;
**********************************************/

intrinsic Degree(phi::MapSch)->RngIntElt
  {Degree of a non-constant morphism between curves}
  require IsCurve(Domain(phi)) and IsCurve(Codomain(phi)):
    "Only implemented for maps between curves";
  require IsProjective(Domain(phi)) and IsProjective(Codomain(phi)):
    "Only implemented for maps between projective domain and codomain";
  if Type(Domain(phi)) eq CrvEll and Type(Codomain(phi)) eq CrvEll then
   i:=InternalIsogenyDegree(phi); else i:=-1; end if;
  if i ge 0 then phi`degree:=i; return i; end if;
  if #Components(phi) gt 1 then  // added Mar 08, SRD
    phi`degree := &*[Degree(m) : m in Components(phi)];
    return phi`degree; end if;
  if not(assigned(phi`degree)) then
    C:=Codomain(phi);
    x:=SeparatingElement(AlgorithmicFunctionField(FunctionField(C)));
    D:=GCD(Divisor(x),Divisor(x^0));
    PBD:=AlFFPullback(phi,D);
    d:=Integers()!(Degree(PBD)/Degree(D));
    phi`degree:=d;
  end if;
  return phi`degree;
end intrinsic;

intrinsic RamificationDivisor(phi::MapSch[Crv,Crv])->DivCrvElt
  {Ramification divisor of phi, i.e., the places on the domain of phi
   where phi is ramified}
  require HasFunctionField(Codomain(phi)) and HasFunctionField(Domain(phi)) :
    "Only implemented for maps between integral curves";
  KC,mp:=AlgorithmicFunctionField(FunctionField(Codomain(phi)));
  omega:=Differential(SeparatingElement(KC) @@ mp);
  return Divisor(Pullback(phi,omega)) - Pullback(phi,Divisor(omega));
end intrinsic;

/****************************************************
 * Access and computation functions for induced maps
 * between function fields.
 ****************************************************/

function RestrictionToFunctionFieldPatch(phi)

    D:=Domain(phi);
    C:=Codomain(phi);

    assert HasFunctionField(C);
    assert HasFunctionField(D);
    Di := NonEmptyPatchIndex(D);
    Ci := NonEmptyPatchIndex(C);
    // these are both non-zero as a function fields exist!! 
    
    return RestrictionToPatch(phi,Di,Ci);
end function;

function PullbackMap(phi)
  if not(assigned phi`RCtoKD) then
    D:=Domain(phi);
    C:=Codomain(phi);
    // assert IsCurve(C) and IsCurve(D) and IsProjective(C) and IsProjective(D); 
    assert BaseRing(C) eq BaseRing(D);
    assert HasFunctionField(C) and HasFunctionField(D);

    KC:=FunctionField(C);
    KD:=FunctionField(D);
    phi_aff := RestrictionToFunctionFieldPatch(ProjectiveClosure(phi));

    //PRCa := Integers(FunctionField(Ambient(C)));    
    PRCa := CoordinateRing(Ambient(Codomain(phi_aff)));
    CatoKD:=hom< PRCa->KD| [KD| eqn : eqn in DefiningEquations(phi_aff)] : Check:=false>;
    seq := [(CatoKD(Numerator(elt)))/(CatoKD(Denominator(elt))) 
                 where elt is KC.i : i in [1..Rank(Integers(KC))]];
    phi`RCtoKD:=hom<KC->KD | seq>;
  end if;
  return phi`RCtoKD;
end function;

function toRelativeMap(phi)
  if not(assigned phi`RDtoKDrel) then
    D:=Domain(phi);
    C:=Codomain(phi);
    //assert IsCurve(C) and IsCurve(D) and IsProjective(C) and IsProjective(D);
    assert BaseRing(C) eq BaseRing(D);
    assert HasFunctionField(C) and HasFunctionField(D);
      
    KC:=FunctionField(C);
    KCA,kmap := AlgorithmicFunctionField(KC);
              // temporarily(?!) reduce to working with the alg fn fld
	      // for speed of arithmetic in generating
    KD:=FunctionField(D);

    phi_aff := RestrictionToFunctionFieldPatch(ProjectiveClosure(phi));

    // Following Nils, we could embed using generic points and pullbacks.
    //  Here, for new function fields, we will embed directly!
    
    // We build KD as a finite algebra over KC (called KDaff)
    
    PRD := CoordinateRing(Ambient(Domain(phi_aff)));
    /* mch - Integers(FunctionField(Ambient(D))) is not the same as
       the above if the function field patch of D isn't the 1st!    */
    fns := [FieldOfFractions(PRD) | f : f in DefiningEquations(phi_aff)];
    fs := [PRD|Numerator(f) : f in fns];
    gs := [PRD|Denominator(f) : f in fns];
      // phi_aff given by [f1/g1,f2/g2,..] where f1.. in fs, g1.. in gs
    
    KDaffX := PolynomialRing(KCA,Rank(PRD));
    PRDtoKDaffX := hom<PRD->KDaffX | [KDaffX.i : i in [1..Rank(PRD)]] >;
    Irels := ideal<KDaffX| [PRDtoKDaffX(f) : f in Basis(DefiningIdeal(Domain(phi_aff)))] cat
	 [PRDtoKDaffX(fs[i])-kmap((KC.i))*PRDtoKDaffX(gs[i]) : i in [1..#fs]] >;
    // "remove the points where phi_aff is undefined"
    Irels := ColonIdeal(Irels, PRDtoKDaffX(&*[g : g in gs]));
    KDaff := quo<KDaffX | Irels>;
    
    error if not IsField(KDaff), "Cannot work with constant map";
    
    // Finally, make homomorphism from CoordRing(Da) to KDaff
    //  whose extension to KD gives a KC-isomorphism
    seq := [(KDaff!PRDtoKDaffX(Numerator(elt)))/
               (KDaff!PRDtoKDaffX(Denominator(elt))) 
		   where elt is KD.i : i in [1..Rank(PRD)]];
    phi`RDtoKDrel := 
	hom<IntegerRing(KD) -> KDaff | seq>; 

  end if;
  return phi`RDtoKDrel;
end function;

/****************************************************
 * Pull & push for function field elements
 ****************************************************/

intrinsic Pullback(phi::MapSch[Crv, Crv],f::FldFunFracSchElt)->FldFunFracSchElt
  {The pullback of a function by a finite map between curves}
  require HasFunctionField(Domain(phi)) and HasFunctionField(Codomain(phi)) :
    "Domain and codomain of argument 1 must be integral curves";
  require BaseRing(Domain(phi)) eq BaseRing(Codomain(phi)) : 
			"Domain and codomain must have the same base ring";
  require f in FunctionField(Codomain(phi)):
    "Argument 2 must be an element of the function field of the codomain";
  return psi(f) where psi is PullbackMap(phi);
end intrinsic;

intrinsic Pushforward(phi::MapSch[Crv, Crv],f::FldFunFracSchElt)->FldFunFracSchElt
  {The push-forward (effectively a norm) of a function by a finite map
  between curves}
  require HasFunctionField(Domain(phi)) and HasFunctionField(Codomain(phi)) :
    "Domain and codomain of argument 1 must be integral curves";
  require BaseRing(Domain(phi)) eq BaseRing(Codomain(phi)) : 
			"Domain and codomain must have the same base ring";
  require f in FunctionField(Domain(phi)):
    "Argument 2 must be an element of the function field of the domain";
  // complication as we're still working with the alg function field
  //  rather than the new function field of the codomain
  //  FOR SPEED REASONS!!
     F,mp := AlgorithmicFunctionField(FunctionField(Codomain(phi)));
  return AffNorm(toRelativeMap(phi),f) @@ mp;
end intrinsic;

/****************************************************
 * Pullback for differentials
 ****************************************************/

intrinsic Pullback(phi::MapSch[Crv, Crv],omega::DiffCrvElt)->DiffCrvElt
  {The pullback of a differential by a finite map between curves}
  C := Codomain(phi);
  require HasFunctionField(C) and HasFunctionField(Domain(phi)) :
	  "Domain and Codomain of argument 1 must have function fields";
  require BaseRing(C) eq BaseRing(Domain(phi)) :
	"Domain and Codomain of argument 1 must have equal base rings";
  require FunctionField(Curve(omega)) eq FunctionField(C): 
    "Argument 2 must be on the codomain of argument 1";
  F,mc := AlgorithmicFunctionField(FunctionField(C));
  z:=mci(SeparatingElement(F)) where mci is Inverse(mc);
  return Pullback(phi,omega/Differential(z))*
          Differential(Pullback(phi,z));
end intrinsic;

/****************************************************
 * Pull & push for curve places
 ****************************************************/

intrinsic Pullback(phi::MapSch[Crv, Crv],Plc::PlcCrvElt)->DivCrvElt
  {The pullback of a place by a finite map between curves}
  C := Codomain(phi);
  D := Domain(phi);
  require HasFunctionField(C) and HasFunctionField(D):
       "Only implemented for maps between integral projective curves";
  require BaseRing(C) eq BaseRing(D) : 
	"Domain and Codomain of argument 1 must have the same base ring";
  require FunctionField(Curve(Plc)) eq FunctionField(C):
    "Argument 2 must be on the codomain of argument 1";
  f,g:=TwoGenerators(Plc);
  fpb:=Pullback(phi,f);
  gpb:=Pullback(phi,g);
  KD,m := AlgorithmicFunctionField(FunctionField(D));
  Ofin:=MaximalOrderFinite(KD);
  Oinf:=MaximalOrderInfinite(KD);
  gens := [m(fpb),m(gpb)];  
  Di:= Divisor(ideal<Ofin|gens>,ideal<Oinf|gens>);
  return CurveDivisor(D,LCM(Di,DivisorGroup(KD)!1));   
end intrinsic;

/***************************************
Don't do it like this until relative function fields are optimised further

function PlcToRel(phi,P)
  f,g:=TwoGenerators(P);
  print "f,g:",f,g;
  frel:=toRelativeMap(phi)(f);
  grel:=toRelativeMap(phi)(g);
  print "frel,grel:",frel,grel;
  KDrel:=Parent(frel);
  Ofin:=MaximalOrderFinite(KDrel);
  print "Ofin:",Ofin:Magma;
  I:=ideal<Ofin|[frel,grel]>;
  print "I (raw):",I;
  I:=I meet Ofin;
  print "I meet Ofin:",I;
  if IsPrime(I) then
    print "That one's OK";
    return Place(I);
  else
    print "Going for Oinf now";
    Oinf:=MaximalOrderInfinite(KDrel);
    print "Oinf:",Oinf;
    I:=ideal<Oinf|[frel,grel]>meet Oinf;
    assert IsPrime(I);
    print "Take this one then";
    return Place(I);
  end if;
end function;

function RelNorm(D)
  Ifin,Iinf:=Ideals(D);
  return Divisor(Norm(Ifin),Norm(Iinf));
end function;

****************************************/

function special_pushforward(phi,P)
/* When phi(Cluster(P)) is empty, so the main method below fails,
   use the following: get the unique place over (Norm(f),Norm(g))
   where f,g are the two generators of P */

   relmap := toRelativeMap(phi);
   f,g := TwoGenerators(P);
   Nf := AffNorm(relmap,f);
   Ng := AffNorm(relmap,g);
   D := GCD( Numerator(Divisor(Nf)), Numerator(Divisor(Ng)) );
   cands := Support(D);
   assert #cands gt 0;
   if #cands gt 1 then
    _,Fmp := AlgorithmicFunctionField(FunctionField(Codomain(phi)));
    sel:={PFP:PFP in cands| (Valuation(Pullback(phi,Fmp(a)),P) ge 1)
	and (Valuation(Pullback(phi,Fmp(b)),P) ge 1) where
		a,b := TwoGenerators(PFP)};
    assert #sel eq 1;
    PFP:=Rep(sel);
   else
    PFP := cands[1];
   end if;
   return CurvePlace(Codomain(phi),PFP);
end function;   

intrinsic Pushforward(phi::MapSch[Crv, Crv],P::PlcCrvElt)->DivCrvElt
  {The push-forward (image in the intersection theory sense) of a place
  by a finite map between curves}
  /*{Presently only implemented if the image of P is disjoint from
  the singular locus of the codomain of phi and for places with a supporting
  scheme that is disjoint from the base locus of the map.}*/
  require HasFunctionField(Domain(phi)) and HasFunctionField(Codomain(phi)) :
	      "Domain and codomain of argument 1 must have function fields";
  require BaseRing(Domain(phi)) eq BaseRing(Codomain(phi)) : 
	    "Domain and codomain of argument 1 must have equal base rings";
  require FunctionField(Curve(P)) eq FunctionField(Domain(phi)) : 
		"Argument 2 must be on the domain";
  Z:=Cluster(P);
  PFZ:=phi(Z);
  if IsEmpty(PFZ) then
    PFP := special_pushforward(phi,P);
  else
    cands:=Support(Divisor(DivisorGroup(Codomain(phi)),Ideal(PFZ)));
    sel:={PFP:PFP in cands| Valuation(Pullback(phi,PFP),P) ge 1};
    assert #sel eq 1;
    PFP:=Rep(sel);
  end if;
  return (Integers()!(Degree(P)/Degree(PFP)))*PFP;
end intrinsic;

/****************************************************
 * Pull & push for function field divisors
 ****************************************************/
 
function AlFFPullback(phi, D)
  C := Codomain(phi);
  Dom := Domain(phi);
  assert IsCurve(C) and IsCurve(Dom) and
          HasFunctionField(C) and HasFunctionField(Dom);
       
  KC,mc:= AlgorithmicFunctionField(FunctionField(C));
  assert FunctionField(D) eq KC;
  //KCf:=RationalExtensionRepresentation(KC);
  I:=Ideals(D); //we only use the finite ideal
  genI:=Generators(I); //only generators of the finite ideal
  //Dpr is the divisor generated by the generators of I, in *BOTH*
  //the finite and the infinite order. Dpr equals D at the
  //finite places.
  Dpr:=Divisor(ideal<MaximalOrderFinite(KC)|genI>,
               ideal<MaximalOrderInfinite(KC)|genI>);
  //So D-Dpr is only supported at infinity.
  DminDpr:=D-Dpr;
  //we pull back Dpr per place:
  
  plcInf:=InfinitePlaces(KC);
  PBDminDpr:=&+[Valuation(DminDpr,p)*
	FunctionFieldDivisor(Pullback(phi,CurvePlace(C, p))):p in plcInf];
  
  KD,md:=AlgorithmicFunctionField(FunctionField(Dom));
  //KDf:=RationalExtensionRepresentation(KD);
  
  PBgenI:=[md(Pullback(phi,mci(f))):f in genI] where mci is Inverse(mc);
  PBDpr:=Divisor(ideal<MaximalOrderFinite(KD)|PBgenI>,
                                  ideal<MaximalOrderInfinite(KD)|PBgenI>);
  //The pullback  of D now is just PBDminDpr+PBDpr
  return PBDminDpr+PBDpr;
end function;

function AlFFPushforward(phi, D)
  C := Codomain(phi);
  Dom := Domain(phi);
  assert (IsCurve(C) and IsCurve(Dom) and HasFunctionField(C) and
      HasFunctionField(Dom));
  KD,md:=AlgorithmicFunctionField(FunctionField(Dom));
  assert FunctionField(D) eq KD;
  //KDf:=RationalExtensionRepresentation(KD);
  I:=Ideals(D); //only the finite ideal
  genI:=Generators(I);
  Ofin:=MaximalOrderFinite(KD);
  Oinf:=MaximalOrderInfinite(KD);
  Dpr:=Divisor(ideal<Ofin|genI>,ideal<Oinf|genI>);
  DminDpr:=D-Dpr;
  
  plcInf:=InfinitePlaces(KD);
  PFDminDpr:=&+[Valuation(DminDpr,p)*
	FunctionFieldDivisor(Pushforward(phi,CurvePlace(Dom,p))):p in plcInf];

  KC,mc:=AlgorithmicFunctionField(FunctionField(C));
  //KCf:=RationalExtensionRepresentation(KC);
    
  PFgenI:=[mc(Pushforward(phi,mdi(f))):f in genI] where mdi is Inverse(md);
  PFDpr:=Divisor(ideal<MaximalOrderFinite(KC)|PFgenI>,
                            ideal<MaximalOrderInfinite(KC)|PFgenI>);
  return PFDminDpr+PFDpr;
end function;


/****************************************************
 * Pull & push for curve divisors
 ****************************************************/

intrinsic Pullback(phi::MapSch[Crv, Crv],D::DivCrvElt)->DivCrvElt
  {The pullback of a divisor by a finite map between curves}
  require HasFunctionField(Domain(phi)) and HasFunctionField(Codomain(phi)) :
    "Domain and codomain of argument 1 must have function fields";
  require BaseRing(Domain(phi)) cmpeq BaseRing(Codomain(phi)) :
    "Domain and codomain of argument 1 must have equal base rings";
  require FunctionField(Curve(D)) cmpeq FunctionField(Codomain(phi)) :
    "The divisor must be on the codomain of the map";
  return CurveDivisor(Domain(phi),AlFFPullback(phi,FunctionFieldDivisor(D)));
end intrinsic;

intrinsic Pushforward(phi::MapSch[Crv, Crv],D::DivCrvElt)->DivCrvElt
  {The push-forward (image in the intersection theory sense) of a divisor
  by a finite map between curves}
  /*{Pushforward presently has problems if so-called infinite places of the domain
  land inside the singular locus of the codomain or if the representation of the
  map is not defined at the supporting scheme of some of the infinite places.}*/
  require HasFunctionField(Domain(phi)) and HasFunctionField(Codomain(phi)) :
    "Domain and codomain of argument 1 must have function fields";
  require BaseRing(Domain(phi)) cmpeq BaseRing(Codomain(phi)) :
    "Domain and codomain of argument 1 must have equal base rings";
  require FunctionField(Curve(D)) cmpeq FunctionField(Domain(phi)) :
    "Argument 2 must be on codomain of argument 1";
  return CurveDivisor(Codomain(phi),AlFFPushforward(phi,FunctionFieldDivisor(D)));
end intrinsic;
