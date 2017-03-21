freeze;

import "parallel.m": ParallelRandomElement;
import "misc.m": IsFixed;

/* estimate the orbit size */
EstimateOrbitSize := function (nmr, NHITS)
   LB := 2 * nmr^2 / (1.96 + Sqrt (4 * NHITS - 1))^2;
   UB := 2 * nmr^2 / (-1.96 + Sqrt (4 * NHITS - 1))^2;
   vprint AutomorphismGroup, 2: "Estimates of orbit size are ",
       Floor (LB), Floor (UB), Floor (nmr^2 div (2 * NHITS));
   return Floor (LB), Floor (UB), Floor (nmr^2 div (2 * NHITS));
end function;

/* 95% confidence interval between LB and UB;
   "The estimation of Animal abundance" by G.A.F. Seber p. 188
   is source of lower and upper bounds; NHITS must be 15 or greater */
BirthdayParadox := function (U, A, NHITS: MAXSIZE := 10^4)
   if (Type (A) eq GrpMat and Ngens (A) eq 0) or
      (Type (A) eq SeqEnum and #A eq 0) then
      return 1, 1, 1;
   end if;

   NmrSteps := 100;
   R := RandomProcess (A: Scramble := NmrSteps);
   DIV := 10000;

   Images := {@ @};
   position := [];
   nmr := 0;
   nhits := 0;
   repeat
      nmr +:= 1;
      a := Random (R);
      image := U^a;
      index := Position (Images, image);
      if index ne 0 then
	 nhits +:= position[index];
         position[index] +:= 1;
         if nhits ge NHITS then
            return EstimateOrbitSize (nmr, NHITS);
         end if;
      else
         Include (~Images, image);
         position[#Images] := 1;
      end if;
      if nmr mod DIV eq 0 then
         vprint AutomorphismGroup, 2: "Generated ", nmr, " random elements ";
      end if;
   until nmr gt MAXSIZE;

   vprint AutomorphismGroup: "Number of orbit coincidences found is ", nhits;
   return 0, 0, 0;
end function;

intrinsic EstimateOrbit (G :: GrpMat, U :: ModTupFld: MaxSize := 10^4,
            NumberCoincidences := 15) -> RngIntElt, RngIntElt, RngIntElt
{estimate size of orbit of subspace U under G by constructing at most MaxSize
 elements of orbit and counting at most NumberCoincidences coincidences;
 return lower bound, upper bound, and estimate of size; if no estimate
 can be made, the function returns 0}

   return BirthdayParadox (U, G, NumberCoincidences: MAXSIZE := MaxSize);

end intrinsic;

intrinsic EstimateOrbit (G :: GrpMat, v :: ModTupFldElt: MaxSize := 10^4,
            NumberCoincidences := 15) -> RngIntElt, RngIntElt, RngIntElt
{estimate size of orbit of vector v under G by constructing at most MaxSize
 elements of orbit and counting at most NumberCoincidences coincidences;
 return lower bound, upper bound, and estimate of size; if no estimate
 can be made, the function returns 0}

   return BirthdayParadox (v, G, NumberCoincidences: MAXSIZE := MaxSize);

end intrinsic;

intrinsic ApproximateStabiliser (G :: Grp, A :: GrpMat, U :
   ImageGenerators := [], MaxSize := 10^4, NumberCoincidences := 15,
   OrderCheck := false)
  -> GrpMat, GrpMat, RngIntElt, RngIntElt, RngIntElt
{A is image of representation of G and A acts on U, a subspace or vector;
 we assume either a 1-1 correspondence between generators of G and those of A,
 or between generators of G and those elements of A supplied as ImageGenerators;
 find elements of G whose image in A fixes U and estimate size
 of the orbit of U under A; construct at most MaxSize orbit elements
 or until we find NumberCoincidences repetitions; if OrderCheck
 is true, report the order of the subgroup S of A which we find which
 stabilises U; return preimage of S in G, and S}

   error if (Type (A) ne GrpMat),
        "Must supply matrix group as second argument";

   error if (Type (U) ne ModTupFld) and (Type (U) ne ModTupFldElt),
        "U must be vector or subspace";

   if #ImageGenerators gt 0 then A`UserGenerators := ImageGenerators; end if;
   error if #Generators (G) ne #UserGenerators (A),
        "Both groups must have the same number of user-generators";

   P := Generic (G);

   fixed := {i: i in [1..Ngens (A)] | U eq U^A.i};
   if #fixed eq Ngens (A) then
      return G, A, 1, 1, 1;
   else
      d := Degree (A); F := BaseRing (A); gl := GL(d, F);
      Auts := {G.i : i in fixed};
      H := sub < gl | [A.i : i in fixed]>;
   end if;

   nhits := NumberCoincidences;
   NHITS := NumberCoincidences;

   DIV := 10000;
   nmr := 0;

   Images := {@ U @};
   GWords := {@ G.1^0 @};
   Words := {@ A.1^0 @};
   id := Identity (A);
   MatOrder := [];
   repeat
      nmr +:= 1;
      a, g := ParallelRandomElement (A, G);
      image := U^a;
      if image in Images then
         index := Position (Images, image);
         word := a *  Words[index]^-1;
          aut := g * GWords[index]^-1;
         assert U^word eq U;
         vprint AutomorphismGroup, 2:
         "Order of stabilising automorphism found is ", Order (aut);
         Include (~Auts, aut);
         H := sub < gl | H, word>;

         nhits -:= 1;
         if nhits eq 0 then
            lb, ub, os := EstimateOrbitSize (nmr, NHITS);
            Auts := sub <P | Auts>;
            return Auts, H, lb, ub, os;
         end if;

         if OrderCheck then
            "Order of H is ", #H;
            Append (~MatOrder, #H);
            if IsFixed (MatOrder) then
               lb, ub, os := EstimateOrbitSize (nmr, NHITS - nhits + 1);
               Auts := sub <P | Auts>;
               return Auts, H, lb, ub, os;
            end if;
         end if;
      else
         Include (~Words, a);
         Include (~GWords, g);
         Include (~Images, image);
      end if;

      if nhits eq 0 then
          lb, ub, os := EstimateOrbitSize (nmr, NHITS);
          Auts := sub <P | Auts>;
          return Auts, H, lb, ub, os;
      end if;

      if nmr mod DIV eq 0 then
         vprint AutomorphismGroup, 2: "Processed", nmr, "random elements";
      end if;

   until nmr gt MaxSize;

   vprint AutomorphismGroup:"Built up an orbit of size ", #Images;
   return sub <P | Auts>, H, 0, 0, 0;

end intrinsic;
