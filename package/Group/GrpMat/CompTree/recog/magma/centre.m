/******************************************************************************
 *
 *    centre.m  Composition Tree Centre Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Eamonn O'Brien and Henrik B‰‰rnhielm
 *    Dev start : 2008-05-21
 *
 *    Version   : $Revision:: 3098                                           $:
 *    Date      : $Date:: 2015-04-16 03:42:31 +1000 (Thu, 16 Apr 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: centre.m 3098 2015-04-15 17:42:31Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "../../GrpMat/util/chevalley-order.m" : ClassicalCentreOrder;

// Error object in exceptions
CentreError := recformat<
    Description : MonStgElt, 
    Error : Any>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

/* construct elements of Sylow p-subgroup of centre of quasi-simple group */

SylowSubgroupCentre := function (G, p: OrderLimit := 0, NmrTries := 20)
   S := [ Generic (G) | ]; W := [];
   P := RandomProcessWithWords (G);
   repeat
      g, w := Random (P);
      flag, h, ppower, rem := PrimePowerOrderElement(g, p);
      if flag and IsCentral (G, h) then 
         // assert Order (h) mod p eq 0;
         if not (h in S) then 
            Append (~S, h); 
            wh := w^rem; Append (~W, wh); 
         end if;
         if OrderLimit ne 0 then 
            Z := sub <Generic (G) | S>; 
            if #Z ge OrderLimit then return S, W; end if;
         end if;
      end if;
      NmrTries -:= 1;
   until NmrTries eq 0;
   return S, W; 
end function;

/* use Monte Carlo algorithm to construct centre of 
   known order of quasi-simple group; if we know that we have 
   constructed the centre, then we also return true, else false */

EstimateCentre := function (G, order: NmrTries := 100)
   B := PrimeBasis (order);
   gens := [ Generic (G) | ]; words := [];
   Z := sub <Generic (G) | >;
   for p in B do 
      x, y := Valuation (order, p);
      S, W := SylowSubgroupCentre (G, p: OrderLimit := order div y,
	  NmrTries := NmrTries);
      gens cat:= S; words cat:= W;
      Z := sub <Generic (G) | gens>;
      if #Z ge order then return Z, words, true; end if;
   end for;
   return Z, words, #Z ge order;
end function;

// Find a generator for a cyclic group
function CyclicGenerator(G)
    // prime -> <prime deg, element, slp>
    gens := AssociativeArray();

    W := WordGroup(G);
    for i in [1 .. NumberOfGenerators(G)] do
	order := FactoredOrder(G.i);
	o := &* [p[1]^p[2] : p in order];
	
	for p in order do
	    flag, gen := IsDefined(gens, p);
	    if not flag or p[2] gt gen[1] then
		gens[p] := <p[2], G.i^(o div p[1]^p[2]),
		    W.i^(o div p[1]^p[2])>;
	    end if;
	end for;
    end for;

    return &* [gens[p][2] : p in Keys(gens)],
	&* [gens[p][3] : p in Keys(gens)];
end function;

function C9Centre(G : NmrTries := 100)
    // A C9 group can only have a centre in a matrix representation
    if Category(G) eq GrpMat then
	if forall{g : g in Generators(G) | Determinant(g) eq 1} then 
	    order := GCD(Degree(G), #CoefficientRing(G) - 1);
	else
	    order := #CoefficientRing(G) - 1;
	end if;

	// First find the centre
	Z, slps := EstimateCentre(G, order : NmrTries := NmrTries);

	// Then obtain a single centre generator
	if IsTrivial(Z) then
	    return sub<Generic(G) | >, _;
	else
	    a, slp := CyclicGenerator(Z);
	    return sub<Generic(Z) | a>, Evaluate(slp, slps);
	end if;
    else
	return sub<Generic(G) | >, _; 
    end if;
end function;

/* return generator for centre of C9-group;
   we assume only that G is absolutely irreducible */

CentreOfC9Group := function (G: NmrTries := 20)
   d := Degree (G); q := #BaseRing (G);

   if forall{g : g in Generators (G) | Determinant (g) eq 1} then 
      order := Gcd (d, q - 1);
   else
      order := q - 1;
   end if;

   B := PrimeBasis (order);
   gen := Identity (G); word := Identity (WordGroup (G));
   for p in B do 
      x, y := Valuation (order, p);
      S, W := SylowSubgroupCentre (G, p: OrderLimit := order div y,
                                         NmrTries := NmrTries);
      orders := [Order (s): s in S];
      m, index := Maximum (orders);
      gen *:= S[index]; word *:= W[index];
      if Order (gen) ge order then return gen, word, true; end if;
   end for;
   return gen, word, Order (gen) ge order;
end function;

function CentreOfClassicalGroup(G)
   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   
   flag, getOrder := IsDefined(ClassicalCentreOrder, ClassicalType(G));
   if flag then
       order := getOrder(d, q);
   else
       error Error(rec<CentreError |
	   Description := "Group is not classical in natural representation", 
	   Error := G>);
   end if;

   flag, e := IsDivisibleBy(q - 1, order);
   assert flag;

   alpha := PrimitiveElement(F);
   Z := sub<Generic(G) | ScalarMatrix(d, alpha^e)>;
   assert #Z eq order;
   return Z;
end function;
