freeze;

import "present.m": ConstructPresentation;
import "congruence.m": PAFFC, PFFC, IsValidInput, SetMapTypes, MyCongruenceImage; 
import "general.m": IsKnownFinite, IsKnownInfinite, HasKnownIsomorphicCopy;
import "finite.m": IsFiniteMatrixGroup;
import "attributes.m": RF;
import "algebra.m": IsomorphismAlgebraAlgorithm;

/* positive characteristic only;
   H is congruence image of G; is H isomorphic to G? */

PositiveIsIsomorphism := function (G, H, images: OrderLimit := 10^15,
   Short := 30, Small := 10^6, Presentation := "CT");

   if IsTrivial (H) then return false, []; end if;
   if Ngens (H) lt Ngens (G) then return false, []; end if;

   gens, Rels := ConstructPresentation (G, H, images: OrderLimit := OrderLimit,
      Short := Short, Small := Small, Presentation := Presentation);

   if gens ne [G.i: i in [1..Ngens (G)]] then 
      error "*** GIVE UP HERE"; 
      // return false, _; 
   end if;

   for i in [1..#Rels] do
      vprint Infinite: "Evaluate relator ...", i;
      g := Evaluate (Rels[i], gens);
      if not IsIdentity (g) then return false, _; end if;
   end for;

   return true, Rels;
end function;

/* search for isomorphic copy of G, defined over field of positive char */

PositiveIsom := function (G: StartDegree := 1, Algebra := false,
   EndDegree := Maximum (20, StartDegree), Short := 30, ImageOrder := 1, 
   OrderLimit := 10^15, Small := 10^6, Presentation := "CT");

   K := BaseRing (G);
   p := Characteristic (K);

   ext := Maximum (StartDegree, 1);

   F := Type (K) eq FldFun select BaseRing (BaseRing (K)) else BaseRing (K);
   f := Degree (F);

   CongruenceFunction := Type (K) eq FldFun select PAFFC else PFFC;

   soln := -1; 
   repeat 
      vprint Infinite: "Construct congruence image";
      H, tau, images, soln := CongruenceFunction (G: EndDegree := EndDegree,
                                   ExtDegree := ext, start := soln);
      if H cmpeq false then return false, _, _, _; end if;

      ext := BaseRing (Parent (soln));
      // vprint Infinite: "Soln is ", soln;

      CT := CompositionTree (H);
      order := CompositionTreeOrder (H); 
      vprint Infinite: "Order of latest image is ", order;

      if order gt ImageOrder then 
         ImageOrder := order;
         if (Algebra) and ISA (Type(K), FldFunRat) then
            vprint Infinite: "** Use Algebra Algorithm to construct isom copy";
            found := IsomorphismAlgebraAlgorithm (G, H, images); 
            Rels := [];
         else 
            found, Rels := PositiveIsIsomorphism (G, H, images: Short := Short, 
            OrderLimit := OrderLimit, Small := Small, Presentation := Presentation);
         end if;
      else 
         found := false;
      end if;
      if found then return true, H, tau, Rels; end if;
   until (Degree (ext) div f gt EndDegree); 

   return false, _, _, _;
end function;

/* G defined over positive char (rational) function field;
   estimate order of G by constructing congruence images
   over extensions of coefficient field; repeat until largest 
   image order appears NmrTries times */

EstimateOrder := function (G: Modp := true, NmrTries:= 3, Limit := 20)
   p := Characteristic (BaseRing (G));
   O := []; ext := 1; deg := []; F := [];
   repeat 
      I := CongruenceImage (G: ExtDegree := ext);
      Append (~O, LMGOrder (I));
      Append (~deg, ext);
      Append (~F, #BaseRing (I));
      ext +:= 1; if Modp and ext mod p eq 0 then ext +:= 1; end if;
      max, index := Maximum (O);
   until #[x : x in O | x eq max] eq NmrTries or #O gt Limit;

   index := [i : i in [1..#O] | O[i] eq max];
   f := Minimum ([F[i]: i in index]);
   index := [i : i in index | F[i] eq f];
   index := Minimum (index);
   vprint Infinite: "Orders, extension, and field size for images ", O, deg, F;
   vprint Infinite: "Choose degree F ", deg[index], F[index];
   return #O le Limit, deg[index], max;
end function;

intrinsic IsomorphicCopy (G:: GrpMat: Verify := false,
   StartDegree := 1, EndDegree := Maximum (20, StartDegree), Algebra := false, 
   Presentation := "CT", OrderLimit := 10^15, Small := 10^6, Short := 30)
   -> BoolElt, GrpMat, HomGrp
{ construct isomorphic copy of G over finite field; if one is constructed,
  then return true, isomorphic copy H, and isomorphism from G to H,
  else return false;
  Verify: verify that G is finite;
  StartDegree, EndDegree: limit on degrees of field extensions;
  Algebra: if G defined over function field of positive characteristic, 
           then use the algebra based algorithm; 
  Presentation: one of "CT", "PC", "FP";
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   if not IsValidInput (G) then 
      error "IsomorphicCopy: incorrect input";
   end if;

   if IsKnownInfinite (G) then 
      error "IsomorphicCopy: Input is not finite"; 
   end if;

   /* possible that isomorphic copy is not over finite field;
      this could be improved by computing new congruence image
      over finite field */
   if HasKnownIsomorphicCopy (G) then 
      H := G`Congruence`Image; 
      if ISA (Type (BaseRing (H)), FldFin) eq true then 
         tau := G`Congruence`Map;
         return true, H, tau;
      end if;
   end if;

   if IsTrivial (G) then
      I, tau := CongruenceImage (G);
      return true, I, tau;
   end if;

   K := BaseRing (G);
   p := Characteristic (K); 
   if Verify and not IsKnownFinite (G) then 
      if ISA (Type(K), FldRat) or ISA (Type (K), RngInt) then
         flag := InternalIsFinite (G);
      else 
         flag, H, tau, Rels, N := IsFiniteMatrixGroup (G: 
            Kernel := true, Short := Short, Small := Small, 
            Algebra := Algebra, Presentation := Presentation);
         if IsKnownFinite (G) then 
            /* if G is defined over function field, we use algebra algorithm 
               to decide finiteness; we may discover an isomorphism */
            if ISA (Type(K), FldFunRat) and assigned G`Congruence`Isomorphism then
               return true, H, tau;
            elif (p eq 0 or IsTrivial (N)) then 
               return true, H, tau;
            end if;
         end if;
      end if;
      if not flag then error "IsomorphicCopy: Input is not finite"; end if;
   end if;

   if p eq 0 then 
      H, tau, images := MyCongruenceImage (G: Selberg := true);
      G`Congruence`Finite := true;
      G`Congruence`Isomorphism := true;
      return true, H, tau;
   else 
      Modp := Algebra or ISA (Type (K), FldFun);
      flag, StartDegree, guess := EstimateOrder (G: Modp := Modp, 
                                     NmrTries := 3, Limit := 20);
      vprint Infinite: "Estimate order: ", guess;
      if not flag and not IsFinite (G) then 
         error "IsomorphicCopy: Input is not finite"; 
      end if;
      found, H, tau, Rels := PositiveIsom (G: StartDegree := StartDegree,
         Algebra := Algebra, EndDegree := EndDegree, Short := Short, 
         ImageOrder := guess - 1, OrderLimit := OrderLimit, 
         Small := Small, Presentation := Presentation);
      if found then 
         if assigned H`Order then G`Order := H`Order; end if;
         G`Congruence := rec<RF | Map := tau, Relations := Rels, 
                                   Finite := true, Image := H>;
         SetMapTypes (G, false, true, true);
         return true, H, tau;
      end if;
   end if;
   error "IsomorphicCopy: Failed to construct isomorphic copy"; 
end intrinsic;
