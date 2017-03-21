freeze;

// import "../Smash/random.m": RandomElement;
import "../Smash/misc.m": ReverseBubbleSort, EliminateRepetitions;
import "jordan.m": JordanBlocks;
import "stabiliser.m": SpaceStabiliser;

SeedLength := 10; NumberMultiplications := 100;

/* generate some elements having orders which
   are not powers of the characteristic */

procedure pDashLocalElements (G, NmrTries, ~Orders, ~Elts)

   Orders := [];
   Elts := [];

   p := Characteristic (BaseRing (G));

   P := RandomProcess (G);
   for i in [1..NmrTries] do 
      x := Random (P);
      o := ProjectiveOrder (x);
      if not IsPowerOf (o, p) and not (o in Orders) then 
         Append (~Elts, x);
         Append (~Orders, o);
      end if;
   end for;

   ReverseBubbleSort (~Orders, ~Elts);
   EliminateRepetitions (~Elts, ~Orders);

end procedure;

/* given g of projective order p <> characteristic of F, 
   find a subgroup H of G which normalises a p-subgroup of G */

pDash := function (G, g, Nmr, NmrTries) 

   F := BaseRing (G);
   p := Characteristic (F);

   o := ProjectiveOrder (g);

   if not IsPrime (o) or Gcd (p, o) ne 1 then 
     vprint Tensor: "Element has order ", o;
     return false, false;
   end if;

   if IsScalar (g) then 
     vprint Tensor: "Element is scalar ";
     return G, false;
   end if;

   d := Degree (G);

   V := VectorSpace (F, d);

   Spaces, Degrees := JordanBlocks (g);
   vprint Tensor: "The number of Jordan blocks is ", #Spaces;

   X := Set (Degrees);
   vprint Tensor: "Distinct degrees in Jordan form are ", X;
   
   /* are all the eigen values present in the field? */
   LargeField := X ne {1};

   H := G;

   if #X gt 1 then 
      for x in X do
         Sum := &+[Spaces[i] : i in [1..#Spaces] | Degrees[i] eq x];
         H, fixed := SpaceStabiliser (H, Sum, Nmr, NmrTries);
      end for;
   end if; 

   for x in X do
      T := {Spaces[i] : i in [1..#Spaces] | Degrees[i] eq x};
      H, fixed := SpaceStabiliser (H, T, Nmr, NmrTries);
   end for;
      
   P := GL (Degree (G), BaseRing (G));
   H := sub <P | H, g>;

   return H, LargeField;

end function;

/* write H and g currently defined over GF (q) over larger field GF(q^n) */

EmbedLargerField := function (H, g, n) 
  
   F := BaseRing (H);
   ExtF := ext <F | n>;
   Large := GL (Degree (H), ExtF);
   return sub <Large | {Eltseq (g) : g in Generators (H)}>, Large!Eltseq (g);

end function;

/* the larger field of H is an extension of a base field and 
   we write H over the base field */
 
RestrictSmallerField := function (H, n)

//   F := GroundField (BaseRing (H));
// a bug in GroundField -- hence next 3 lines 
   F := BaseRing (H);
   n := Round (Root (#F, n));
   F := GF (n);

   Small := GL (Degree (H), F);
   return sub <Small | {Eltseq (g) : g in Generators (H)}>;

end function;

/* compute subgroup H which is p-local; in particular <g>^H is an 
   elementary abelian p-group; g has order p^k, projective order p */

pDashSubgroup := function (G, parent, gg, Nmr, NmrTries) 

   g := gg;

   H, LargeField := pDash (G, g, Nmr, NmrTries); 
   P := GL (Degree (G), BaseRing (G));
   H := sub < P | H, parent>;

   if LargeField then 

      q := #BaseRing (G);

      /* degree of extension */
      n := Order (q, Order (g));

      H, g := EmbedLargerField (H, g, n);

      H, LargeField := pDash (H, g, Nmr, NmrTries); 

      if LargeField then error "** ERROR in pDashSubgroup **"; end if; 

      H := RestrictSmallerField (H, n);

   end if;

   return H;

end function;

/* parent is element of order o; generate g, an element of prime order 
   p from parent; construct p-local subgroup for this prime and 
   store it in Subs */

procedure pDashLocals (G, RF, ~Subs, parent, o, Nmr, NmrTries, List, ~Settled)

   local p;

   D := Set (PrimeBasis (o)); 
   d := Degree (G);

   Settled := false;

   /* don't consider p-local subgroups here */
   Exclude (~D, Characteristic (BaseRing (G)));

   for p in D do

      g := parent^(o div p);
      if IsScalar (g) then continue; end if;
      vprint Tensor: "\nConsider element of projective order ", p;

      /* compute local subgroup containing g */
      vprintf Tensor: "\nLook for local subgroup for prime %o\n", p;
      H := pDashSubgroup (G, parent, g, Nmr, NmrTries);
      r := rec <RF | H := H, pLocal := false, pLocalElement := g>;
      Append (~Subs, r);
         
   end for;

end procedure;
