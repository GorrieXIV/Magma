freeze;

import "canonical.m": PGroupStabiliser;
import "unipotent.m": ShadowPGroupStabiliser;
import "autos.m": IsIdentityMap, SpecialMatrixToAutomorphism, ExtendToFactor,
                   ExtendToSubgroup;
import "autos.m": ExtractMatrixGroup, ExtractMatrices, ActionOnFactor;
import "misc.m": DefiningParameters, SubmoduleToSubspace,
                 SubspaceToSubgroup, OrderGL, BasisCharSubgroup;
import "parameters.m": MembershipTest, AutRF, NHITS, ProbablyTrivial, SMALL,
         RF, SMALLORBIT, LARGE, MAXORBITSIZE, ORBITLIMIT, MultiplicatorChop;
import "finger.m": Fingerprint;
import "approximate.m": BirthdayParadox, ApproximateStabiliser;
import "aut.m": SetupMaps, SmallGeneratingSet, KernelPGL;

/* does some subset of the generating set of G generate G? */
SubsetGenerates := function (G, Auts)
   n := Ngens (G);
   S := [G.i : i in [1..n]];
   for i in [1..n - 1] do
      T := Subsets ({1..n}, i);
      if exists (s) {s : s in T | sub <G | [S[x] : x in s]> eq G} then
         return [Auts[x] : x in s];
      end if;
   end for;

   return Auts;
end function;

/* set up hom from free group W to automorphism group */
function SchreierVectorToAutGroup (P, maps)
   gens := Isetseq (PCGenerators (P));
   A := AutomorphismGroup (P, gens, [ gens @ alpha : alpha in maps ]);
   W := FreeGroup (#maps);
   return hom < W -> A | [A.i: i in [1..Ngens (A)]] : Check := false >, W, A;
end function;

AllGeneratorsFix := function (P, Auts, U, pt, N, Lift, alphainv)
   Autos := Auts`Autos;

   /* do all generators fix pt? */
   i := 1;
   while i le #Autos do
      /* compute the image of a point */
      im := pt^(Autos[i]`extension);
      if Lift then im := PGroupStabiliser (N, im); end if;
      if im ne pt then return false, _; end if;
      i +:= 1;
   end while;

   maps := [Autos[i]`map : i in [1..#Autos]];
   /* do we lift element to point stabiliser? */
   if Lift eq false then return true, maps; end if;

   Sgl := [];
   pAutos := Auts`pAutos;
   for i in [1..#maps] do
      map := maps[i];
      im,_,_,_,beta := ShadowPGroupStabiliser (P, pAutos, N,
                                               U^(Autos[i]`extension));
      assert im eq pt;
      map := map * beta * alphainv;
      if not IsIdentityMap (map) then
         Append (~Sgl, map);
      end if;
   end for;

   return true, Sgl;
end function;

/* orbit and stabiliser of pt under action of non-p automorphisms;
   if Lift is true, we compute orbits of blocks under p-group;
   if BirthdayTrivial is true, then BirthdayParadox suggests
   the orbit has length 1 and we test this first */
CFOrbitStabiliser := function (U, top, bottom, P, Auts, alpha, pt, Lift:
                               BirthdayTrivial := false);
   Autos := Auts`Autos;

   O := {@ pt @};

   /* trivial case */
   if #Autos eq 0 then
      vprint AutomorphismGroup: "Non-p-group acting is trivial";
      return [], O;
   end if;

   /* generators for p-group */
   if Lift then
      pAutos := Auts`pAutos;
      N := ExtractMatrices (pAutos);
      // alphainv := PowHom (alpha, -1);
      alphainv := alpha^-1;
   else
      N := []; alphainv := [];
   end if;

   /* do all automorphisms fix pt? */
   if BirthdayTrivial then
      fix, Sgl := AllGeneratorsFix (P, Auts, U, pt, N, Lift, alphainv);
      vprint AutomorphismGroup, 2: "All non-p generators fix pt?", fix;
      if fix then return Sgl, O; end if;
   end if;

   maps := [Autos[i]`map: i in [1..#Autos]];
   gamma, W := SchreierVectorToAutGroup (P, maps);
   Sgl := [];

   /* set up T as group of matrices representing non-p action
      on Frattini quotient; the elaborate definition of theta
      by use of pos is forced because magma evaluates order
      of T if we use the more natural definition */

   gl := ActionOnFactor (P, P, FrattiniSubgroup (P), Auts`Autos);
   p, d := DefiningParameters (P);
   T := sub <GL (d, p) | gl>;
   gensT := [GL (d, p)! T.i :  i in [1..Ngens (T)]];
   pos := [Position (gensT, gl[i]): i in [1..#gl]];
   theta := hom <W -> T | [T.i : i in pos]>;

   S := sub < T | >;

   vprint AutomorphismGroup, 2: "Number of non-p-group generators is ", #Autos;

   DIV := 1000;

   TraceVector := [[]];
   k := 1;
   /* construct the orbit and stabiliser */
   while k le #O do

      pt := O[k];

      for i in [1..#Autos] do

         /* compute the image of a point */
         im := pt^(Autos[i]`extension);
         if Lift then im := PGroupStabiliser (N, im); end if;

         /* find position */
         j := Position (O, im);

         /* add new element to orbit or stabiliser */
         if j eq 0 then
            Include (~O, im);
            vector := Append (TraceVector[k], i);
            Append (~TraceVector, vector);
         else
            r := [-x : x in TraceVector[j]];
            Reverse (~r);
            vector := TraceVector[k] cat [i] cat r;
            word := W!vector;
            /* a redundant generator? */
            if MembershipTest then
               mat := theta (word);
               if not mat in S then
                  S := sub <T | S, mat>;
                  if pClass (P) eq 2 then
                     map := SpecialMatrixToAutomorphism (P, mat);
                  else
                     map := gamma (word);
                  end if;
                  redundant := false;
               else
                  redundant := true;
               end if;
            else
               map := gamma (word);
               redundant := IsIdentityMap (map);
            end if;
            if not redundant then
               /* do we lift element to point stabiliser? */
               if Lift then
                  auto := [rec <RF | map := map>];
                  ExtendToFactor (P, top, bottom, ~auto);
                  auto := auto[1];
                  im,_,_,_,beta := ShadowPGroupStabiliser
                                   (P, pAutos, N, U^(auto`extension));
                  assert im eq O[1];
                  map := map * beta * alphainv;
               end if;
               // EOB -- MFN's bug in Jan05 caused by this map
               // being identity but matrix mat above was not
               // if not IsIdentityMap (map) then
                  Append (~Sgl, map);
               // end if;
            end if;
         end if;
         if #O mod DIV eq 0 then
            vprint AutomorphismGroup: "Length of block orbit is ", #O;
         end if;
      end for;

     if MembershipTest and #S * #O eq #T then break; else k +:= 1; end if;

   end while;

   error if MembershipTest and #O * #S ne #T,
   "Error: in CFOrbitStabiliser: #O = ", #O, " #S = ", #S, " #T = ", #T;

   /* can we take a subset of this generating set Sgl? */
   if #O gt 1 and MembershipTest then
      vprint AutomorphismGroup, 2: "Attempt to get smaller generating set";
      vprint AutomorphismGroup, 2: "Initial generating size is ", #Sgl;
      Sgl := SubsetGenerates (S, Sgl);
      vprint AutomorphismGroup, 2: "Final generating size is ", #Sgl;
   end if;

   return Sgl, O;
end function;

/* top/bottom is a characteristic section of P;
   U is a subspace of this section; determine its
   orbit and stabiliser under Auts */
CFProcessOrbit := function (top, bottom, P, Auts, U: BirthdayTrivial := false)
   Trivial := BirthdayTrivial;

   A := Auts`pAutos;
   N := ExtractMatrices (A);

   UC, trans, Y, B, alpha, length := ShadowPGroupStabiliser (P, A, N, U);
   assert U^trans eq UC;
   vprint AutomorphismGroup: "Length of p-orbit is ", length;

   Lift := length gt 1;
   C, O := CFOrbitStabiliser (U, top, bottom, P, Auts, alpha, UC, Lift:
                              BirthdayTrivial := Trivial);
   vprint AutomorphismGroup: "Non-p orbit length is ", #O;

   B := [rec <RF | map := map, type := "p-automorphism">: map in B];
   // p, d := DefiningParameters (P);
   // B := [rec < RF | map := hom <P -> P | [<P.j, (alpha (P.j))>:
   //                                       j in [1..d]]>>: alpha in B];
   C := [rec <RF | map := map, type := "general">: map in C];

   OrbitLength := length * #O;
   vprint AutomorphismGroup, 2:
       "Existing automorphism group order is ", Auts`Order;
   vprint AutomorphismGroup: "Orbit length is ", OrbitLength;

   assert Auts`Order mod OrbitLength eq 0;

   Stab := rec<AutRF | Autos := C,
                       pAutos := B,
                       Order := Auts`Order div OrbitLength>;
   vprint AutomorphismGroup, 2: "Order of stabiliser is ", Stab`Order;

   return Stab, OrbitLength, #O;
end function;

/* choose diamond in U; Labels record diamonds already selected;
   Exclude records those which are currently under consideration.

DR May 2011: ChooseDiamond moved to C-level (InternalChooseDiamon).

ChooseDiamond := function (Labels, Exclude)
	for i in [2..#Labels] do
		for j in [1..#Labels[i] - 1] do
			if IsDefined (Labels[i], j + 1) and
				IsDefined (Labels[i - 1], j) and
				IsDefined (Labels[i], j) eq false
				and not (<i, j> in Exclude) then
				return i, j;
			end if;
		end for;
	end for;

	return false, false;
end function;*/


/* A acts on Vspace, construct subspace lattice of Vspace
   and record intersections and sums with Uspace */
ConstructLattice := function (Vspace, Uspace, A)
   M := GModule (A);
   CS, CF := CompositionSeries (M);
   r := #CS;
   V := [SubmoduleToSubspace (M, CS[i]): i in [r..1 by -1]] cat
                 [sub <Vspace | >];
   U := [];
   Labels := [];
   for i in [1..r + 1] do
      temp := sub <Vspace | Uspace, V[i]>;
      U[i] := [Vspace];
      Labels[i] := [];
      for j in [1..i] do
         U[i][j] := temp meet V[j];
         if j eq i or Dimension (U[i][j]) eq 0 then
            Labels[i][j] := true;
         end if;
      end for;
   end for;

   return U, Labels;
end function;

/* set up action on diamond specified by i and j;
   if orbit of resulting point is known to be of size 1, and so
   stabiliser is trivially known, return true, else false */
SetupActionOnDiamond := function (P, Auts, M, Mspace, U, Labels, i, j)
   top := U[i - 1][j];
   bottom := U[i][j + 1];
   space, phi := quo < top | bottom >;
   pt := phi (U[i][j]);

/*
   "dimension of space is ", Dimension (space);
   "dimension of pt is ", Dimension (pt);

   dim := Dimension (space);
   if Dimension (pt) in [dim div 2 + 1 .. dim - 1] then
      pt := DualSpace (pt);
      "SWITCH TO DUAL -- now pt has dimension ", Dimension (pt);
   end if;
*/

   if pt eq space or Dimension (pt) eq 0 then
      Labels[i][j] := true;
      return true, Auts, Labels, pt, _, _;
   end if;

   Top := SubspaceToSubgroup (P, Mspace, top, 0 : Subgroup := M);
   Bottom := SubspaceToSubgroup (P, Mspace, bottom, 0 : Subgroup := M);

   ExtendToFactor (P, Top, Bottom, ~Auts`Autos);
   ExtendToFactor (P, Top, Bottom, ~Auts`pAutos);

   return false, Auts, Labels, pt, Top, Bottom;
end function;

/* examine diamond specificed by i and j; estimate orbit under
   Auts of restriction of U[i][j] to this diamond;
   Birthday determines how much work we do in BirthdayParadox
   to estimate the length of the orbit of U[i][j];
   P is p-covering group; M is multiplicator;
   Mspace is vector space corresponding to M */
ExamineDiamond := function (P, Auts, M, Mspace, U, Labels, i, j: Birthday := 0)
   trivial, Auts, Labels, pt, Top, Bottom:=
      SetupActionOnDiamond (P, Auts, M, Mspace, U, Labels, i, j);

   if trivial then
      return Auts, Labels, 1, 1, 1, pt, _, _;
   end if;

   MA := ExtractMatrixGroup (Auts`Autos);
/*
if #Labels eq 6 then
  print Auts`Autos[1]`extension:Magma;
  print "Before BP:",pt:Magma;
  print MA:Magma;
  print Birthday;
end if;
*/
   LB, UB, Size := BirthdayParadox (pt, MA, NHITS: MAXSIZE := Birthday);
/*
if #Labels eq 6 then
  print "After BP:",LB,UB,Size;
end if;
*/

   /* return Size as 1 only if we are certain that the orbit
      has length 1; here we obtained length 1 from BirthdayParadox
      and so we cannot be certain, hence we return ProbablyTrivial */

   if Size eq 1 then Size := ProbablyTrivial; end if;

   return Auts, Labels, LB, UB, Size, pt, Top, Bottom;
end function;

/* select diamond to process;
   P is p-covering group; M is multiplicator;
   Mspace is vector space corresponding to M */
SelectFactor := function (P, Auts, M, Mspace, U, Labels)
   finished := false;
   list := []; Orb := [];
   list_set := {car<IntegerRing(), IntegerRing()> | }; Long := {car<IntegerRing(), IntegerRing()> | };
   first_long := false;
   while not finished do
      i, j := InternalChooseDiamond(Labels, list_set join Long);
      if i cmpeq false then
         finished := true;
      else
         Auts, Labels, LB, UB, Size, pt := ExamineDiamond
                (P, Auts, M, Mspace, U, Labels, i, j: Birthday := SMALL);
         if Size eq 0 then
            Include(~Long, <i,j>);
            if first_long cmpeq false then first_long := <i,j>; end if;
         elif Size eq 1 then
            Labels[i][j] := true;
         elif Size gt 1 then
            vprint AutomorphismGroup, 2: "Estimate of orbit size is ", Size;
            if Size eq ProbablyTrivial then Size := 1; end if;
            Append (~Orb, Size);
            Append (~list, <i, j>);
            Include (~list_set, <i,j>);
            if Size lt ORBITLIMIT then finished := true; end if;
         end if;
      end if;
   end while;

   if #Orb gt 0 then
      vprint AutomorphismGroup, 2: "Short orbit diamonds are ", list;
      vprint AutomorphismGroup, 2: "Estimated orbit lengths for these diamonds are ", Orb;
      min, index := Minimum (Orb);
      return list[index], Labels, false, min;
   elif #Long gt 0 then
      vprint AutomorphismGroup, 2: "Must choose hard case";
      vprint AutomorphismGroup, 2: "Long orbit diamonds are ", Long;
      return first_long, Labels, true, 0;
   else
      return false, Labels, false, _;
   end if;
end function;

/* verify that automorphisms stabilise U[i][j] */
VerifyStabiliser := function (P, M, Mspace, Top,  U, i, j, Auts)
   ExtendToFactor (P, Top, sub<Top|>, ~Auts`Autos);
   s := SubspaceToSubgroup (P, Mspace, U[i][j], 0 : Subgroup := M);

   MAPS := [Auts`Autos[k]`map: k in [1..#Auts`Autos]];
   if #MAPS gt 0 then
      assert {alpha (s) eq s: alpha in MAPS} eq {true};
      i, j; "Really fix? true";
   end if;

   MAPS := [Auts`pAutos[k]`map: k in [1..#Auts`pAutos]];
   if #MAPS gt 0 then
      assert {alpha (s) eq s: alpha in MAPS} eq {true};
      "p-autos really fix? true";
   end if;

   return true;
end function;

/* it is potentially difficult to determine stabiliser of pt;
   if Magma is true, we attempt to compute the stabiliser
   of pt directly using intrinsic function;
   if MonteCarlo is true, we use a Monte-Carlo algorithm to
   approximate the stabiliser of pt */
HardCase := function (P, Auts, pt: Magma := true, MonteCarlo := false)
   /* kernels of homs from matrix groups to matrix groups
      cannot be evaluated in Magma; hence do not use
      this routine except for class 2 */
   if pClass (P) gt 2 then return false, Auts; end if;

   /* can Magma explicitly compute with this subgroup of GL(d, p)? */
   IsSmallEnough := function (p, d, Order)
      if p eq 2 and d lt 12 then
         return true;
      elif p eq 3 and d lt 10 then
         return true;
      elif p lt 7 and d lt 8 then
         return true;
      elif p lt 19 and d lt 6 then
         return true;
      elif d lt 5 then
         return true;
      elif Order lt Isqrt (OrderGL (d, p)) then
         return true;
      else
         return false;
      end if;
   end function;

   SetupStab := function (P, Auts, Stab, d, p: Small := true)
      if Small then
         Stab := SmallGeneratingSet (sub < GL (d, p) | Stab >);
      end if;
      vprint AutomorphismGroup, 2:
          "Number of generators of stabiliser is now ", Ngens (Stab);
      Autos := [rec <RF | map := SpecialMatrixToAutomorphism (P, Stab.i),
                       type := "general">: i in [1..Ngens (Stab)]];
      Auts`Autos := Autos; Auts`pAutos := []; Auts`Order := #Stab;
      vprint AutomorphismGroup, 2:"Order of aut group is now ", Auts`Order;
      return Auts;
   end function;

   p, d := DefiningParameters (P);

   /* can we compute the stabiliser directly using Magma? */

   /*
   if Magma and Auts`Order ne OrderGL (d, p) then
      "HERE WE GO BACK TO GL";
      gl := GL (d, p);
      Auts := SetupMaps (P, [gl.i:  i in [1..Ngens (gl)]], [], OrderGL (d,p));
      // Auts := SetupStab (P, Auts, Stab, d, p: Small := false);
   end if;
   */

   /* updated to allow general class 2 computation: February 2007 */
   if Magma then
      vprint AutomorphismGroup:
          "Attempt to compute using intrinsic stabiliser function";
      Small := ActionOnFactor (P, P, FrattiniSubgroup (P), Auts`Autos);
      Small cat:= ActionOnFactor (P, P, FrattiniSubgroup (P), Auts`pAutos);
      T := sub <GL (d, p) | Small>;
      RandomSchreier (T);
      Verify (T);
      gens := ExtractMatrices (Auts`Autos cat Auts`pAutos);
      assert #Small eq #gens;
      MA := sub <GL (Nrows (gens[1]), p) | gens>;
      RandomSchreier (MA);
      Verify (MA);
//      theta := hom <T -> MA | gens>;
      index := [Position (Small, T.i): i in [1..Ngens (T)]];
      theta := hom <T -> MA | [gens[i]: i in index]>;
      Stab := Stabiliser (MA, pt);
      K := Kernel (theta);
      kernel := [GL(d, p)!K.i : i in [1..Ngens (K)]];
      Stab := [GL(d, p)!(Stab.i @@ theta) : i in [1..Ngens (Stab)]] cat kernel;
      return true, SetupStab (P, Auts, Stab, d, p);
   end if;

   /* use Monte-Carlo algorithm to approximate? */
   if MonteCarlo then
      Small := ActionOnFactor (P, P, FrattiniSubgroup (P), Auts`Autos);
      MA, gens := ExtractMatrixGroup (Auts`Autos);
      SmallMA := sub <GL(d, p) | [Small[i] : i in gens]>;
      Stab, large, LB, UB, Size :=
        ApproximateStabiliser (SmallMA, MA, pt: MaxSize := MAXORBITSIZE,
                   NumberCoincidences := NHITS, OrderCheck := true);
      Stab join:= {Small[i] : i in [1..#Small] | not (i in gens)};
      return true, SetupStab (P, Auts, Stab, d, p);
   end if;

   return false, Auts;
end function;

/* G is p-group; P is p-covering group of H; M is multiplicator;
   Auts describe automorphisms of H, extended to act on P;
   U is allowable subgroup whose quotient by P is G; determine
   stabiliser of U under action of Auts

   Sep 2013: added Isom parameter to address crash reported by
   David Howden; if we find new char subgroups in computing aut gps,
   then we return to class 2 and start again since new char groups
   usually lead to major reductions in cost;
   this cannot be done for calls from isomorphism testing
   and generating p-groups */
OrbitStabiliser := function (P, M, U, G, H, Auts, Chars: Verify := false, Isom := false)
   /* trivial case */
   if #U eq 1 or U eq M then return Auts, _, _; end if;

   Mspace := BasisCharSubgroup (M, M);
   Uspace := BasisCharSubgroup (M, U);

   /* determine stabiliser of Uspace under action of Auts
      in a single computation */

   SimpleCase := function (P, M, Mspace, Uspace, Auts: Verify := false)

      vprint AutomorphismGroup:
          "Call CFProcessOrbit with MultiplicatorChop false";
      Top := M;
      Bottom := sub < M | >;
      Auts, length := CFProcessOrbit (Top, Bottom, P, Auts, Uspace);
      if Verify eq true then
         flag := VerifyStabiliser (P, M, Mspace, Top, [[Mspace]], 1, 1, Auts);
         assert flag eq true;
      end if;
      vprint AutomorphismGroup, 2: "Orbit has length ", length;
      return Auts, _, _;
   end function;

   vprintf AutomorphismGroup:
       "M has rank %o, U has rank %o\n", NPCgens (M), NPCgens (U);

   ExtendToSubgroup (P, M, ~Auts`Autos);
   ExtendToSubgroup (P, M, ~Auts`pAutos);

   MA, index := ExtractMatrixGroup (Auts`Autos cat Auts`pAutos);
   if #index eq 0 then return Auts, 1, _; end if;

   /* simple case */
   if #Auts`Autos eq 0 or MultiplicatorChop eq false then
      return SimpleCase (P, M, Mspace, Uspace, Auts: Verify := false);
   end if;

   Ugroup := U;
   U, Labels := ConstructLattice (Mspace, Uspace, MA);

   finished := false;
   while not finished do
      index, Labels, Hard, Size := SelectFactor (P, Auts, M, Mspace, U, Labels);
      vprint AutomorphismGroup, 2: "Index for chosen diamond is ", index;
      if index cmpeq false then break; end if;

      ListOrbit := true;
      if Hard then
         Break, NewChars, Subgroup := Fingerprint (G, Chars, Auts`Order);
         if Break and not Isom then
            return false, NewChars, Subgroup;
         else
            vprint AutomorphismGroup:
                "No useful result from Fingerprint -- work harder";
            i := index[1]; j := index[2];
            Auts, Labels, LB, UB, Size, pt, Top, Bottom :=
            ExamineDiamond (P, Auts, M, Mspace, U, Labels, i, j: Birthday := 0);
            ORDER := Auts`Order;
            succeed, Auts := HardCase (P, Auts, pt);
            if succeed then
               Size := ORDER div Auts`Order;
               nonp := Size;
               ListOrbit := false;
            else
               Auts, Labels, LB, UB, Size, pt, Top, Bottom :=
                   ExamineDiamond (P, Auts, M, Mspace, U, Labels, i, j:
                                   Birthday := LARGE);
               vprint AutomorphismGroup: "Estimate of size of orbit is ", Size;
            // error "Failure in OrbitStabiliser: orbit too large, will not compute stabiliser";
            end if;
         end if;
      else
         i := index[1]; j := index[2];
         trivial, Auts, Labels, pt, Top, Bottom :=
            SetupActionOnDiamond (P, Auts, M, Mspace, U, Labels, i, j);
      end if; /* if Hard */

      /* if no progress, list the orbit */
      if ListOrbit then
         vprint AutomorphismGroup, 2:
             "Space has dimension ", NPCgens (Top) - NPCgens (Bottom);
         vprint AutomorphismGroup: "Pt has dimension ", Dimension (pt);
         if Dimension (pt) gt 0 then
            vprint AutomorphismGroup: "Call CFProcessOrbit";
            Auts, Size, nonp := CFProcessOrbit (Top, Bottom, P, Auts, pt:
                                            BirthdayTrivial := Size eq 1);
         end if;
      end if;

      /* check the result */
      if Verify then
         flag := VerifyStabiliser (P, M, Mspace, Top,  U, i, j, Auts);
      end if;

      Labels[i][j] := true;
      vprint AutomorphismGroup, 2: "Length of ", i, j, " orbit is ", Size;

      /* trivial stabiliser? */
      if #Auts`Autos + #Auts`pAutos eq 0 then
         return Auts, _, _;
      end if;

      /* if only p-automorphisms exist, write down stabiliser
         of Uspace in one call to PGroupStabiliser */

      if #Auts`Autos eq 0 then
         vprint AutomorphismGroup:
              "Only p-group survives -- now finish in 1 call ";
         ExtendToSubgroup (P, M, ~Auts`pAutos);
         return SimpleCase (P, M, Mspace, Uspace, Auts: Verify := false);
      end if;

      /* recursively chop up p-multiplicator? */
      if nonp gt SMALLORBIT then
         return $$ (P, M, Ugroup, G, H, Auts, Chars: Verify := false);
      end if;

   end while;

   return Auts, _, _;
end function;
