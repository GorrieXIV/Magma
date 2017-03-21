freeze;

//$Id:: derived.m 1605 2008-12-15 09:05:48Z jbaa004                        $:

import "basics.m" : InitialiseGroup;
import "closure.m" : RandomSubProduct;

function MyDerivedGroupMonteCarlo(G : NumberGenerators := 10, 
    MaxGenerators := Maximum (Ngens (G), 100), 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G))) 

    R := Randomiser;
    W := WordGroup (R);

    U := UserGenerators (G);
    if #U ne Ngens (W) then 
       U := [G.i : i in [1..Ngens (G)]];
    end if;
    
    if NumberOfGenerators (W) ne #U then 
	error "W must have the same rank as number of generators of G";
    end if;

    // Get initial generators
    gens := [Generic (G) | (U[i], U[j]) : i in [1 .. #U],
	j in [1 .. #U] | j gt i];
    slps := [(W.i, W.j) : i in [1 .. NumberOfGenerators(W)],
	j in [1 .. NumberOfGenerators(W)] | j gt i];

    if #gens gt 0 then
	// Add random conjugates to get probable generating set
	for i in [1 .. Maximum (NumberGenerators, #gens * 2 + 10)] do
	    g, w := Random(Randomiser);
	    Append(~gens, gens[i]^g);
	    Append(~slps, slps[i]^w);
	end for;
    end if;

    if #gens gt MaxGenerators then
       Gens := [Generic (G) | ]; Slps := [];
       for i in [1..MaxGenerators] do 
          Gens[i], Slps[i] := RandomSubProduct (gens, slps);
       end for;
       gens := Gens; slps := Slps;
    end if;
   
    // Remove redundant generators
    D := sub<Generic (G) | {@ g : g in gens | not IsIdentity(g) @}>;
    derivedSLPs := [slps[Index(gens, g)] : g in UserGenerators(D)];

    return D, derivedSLPs;
end function;

intrinsic DerivedGroupMonteCarlo(G :: GrpMat : 
    NumberGenerators := 10, 
    MaxGenerators := Maximum (Ngens (G), 100), 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G))) 
    -> GrpMat, []
    {Return the derived group of G, and a list of SLPs of its
    generators in the generators of G. The SLPs are elements of the
    word group of the random process. The algorithm is Monte Carlo and 
    may return a proper subgroup of the derived group. We construct
    at least NumberGenerators and at most MaxGenerators for the derived group.}

    return MyDerivedGroupMonteCarlo(G : MaxGenerators := MaxGenerators, 
	NumberGenerators := NumberGenerators,
	Randomiser := Randomiser);
end intrinsic;

intrinsic DerivedGroupMonteCarlo(G :: GrpPerm : 
    NumberGenerators := 10, 
    MaxGenerators := Maximum (Ngens (G), 100), 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G))) 
    -> GrpPerm, []
    {Return the derived group of G, and a list of SLPs of its
    generators in the generators of G. The SLPs are elements of the
    word group of the random process. The algorithm is Monte Carlo and 
    may return a proper subgroup of the derived group. We construct
    at least NumberGenerators and at most MaxGenerators for the derived group.}

    return MyDerivedGroupMonteCarlo(G :
	NumberGenerators := NumberGenerators, MaxGenerators := MaxGenerators, 
	Randomiser := Randomiser);
end intrinsic;

/* construct normal closure gens^G */

MyNormalClosure := function (G, gens: NumberOfElements := 10)
   d := Degree (G);

   if Type (G) eq GrpMat then 
      F := BaseRing (G);
      L := GL (d, F);
   elif Type (G) eq GrpPerm then
      L := Sym (d);
   else
      L := G;
   end if;

   N := sub <L | gens>;
   E := [NormalSubgroupRandomElement (G, N): i in [1..2 * NumberOfElements]];
   N := sub <L | gens, E>;
   P := RandomProcess (N);
   gens := [Random (P): i in [1..NumberOfElements div 2]];
   return sub <L | gens>, P;
end function;

/* derived subgroup of G */

MyDerivedSubgroup := function (G: NumberOfElements := 10)

   gens := [G.i : i in [1..Ngens (G)]];
   gens := {(g, h): g in gens, h in gens};

   N, P := MyNormalClosure (G, gens: NumberOfElements:= NumberOfElements);
   return N, P;
end function;

/* normal generating set for derived group of G */

MyDerivedSubgroupWithWords := function (G: NumberOfElements := 10) 

   d := Degree (G);
   F := BaseRing (G);
   P := GL (d, F);
   gens := []; words := [];
   U := UserGenerators (G);
   S := G`SLPGroup;
   n := #U;
   Limit := Minimum (2 * n, n + 10);
   nmr := 0;
   repeat
      nmr +:= 1;
      x, w := RandomWord (G);
      for i in [1..#U] do 
         c := (P!U[i], x);
         if not (c in gens) and c ne Id (G) then 
            Append (~gens, c);
            Append (~words, (S.i, w));
         end if;
      end for;
   until nmr ge NumberOfElements or #gens ge Limit;

   D := sub <GL (d, F) | gens>;
   InitialiseGroup (D);
   D`UserGenerators := gens;
   D`UserWords := words;
   assert Ngens (D) eq #gens;
   return D;
end function;

function IsMetabelian(G) 
    /* One-sided Monte-Carlo algorithm that determines if G is metabelian.
    A negative answer is always correct.
    Error probability is at most 3/4 for every G. */
    local elements, commutators, derivedGroup;
    
    // Create commutators of all generators, since their normal closure is
    // the derived group
    elements := {(G.i, G.j) : i in [1 .. NumberOfGenerators(G)],
	j in [1 .. NumberOfGenerators(G)] | j gt i};

    // The normal closure of this is the derived group
    derivedGroup := sub<G | elements>;

    // Get random element of the derived grop
    commutators := [NormalSubgroupRandomElement(G, derivedGroup),
	NormalSubgroupRandomElement(G, derivedGroup)];
    if IsIdentity((commutators[1], commutators[2])) then
	return true;
    else
	return false;
    end if;
end function;
