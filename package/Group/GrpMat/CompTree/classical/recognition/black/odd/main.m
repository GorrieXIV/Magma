freeze;

import "base-omega.m": MyClassicalBaseCases, MakeConjugate;
import "glue.m": ConstructInvolution, SX4ForGlue, OrthogonalGlue;
import "split.m": MyDerivedCentraliser, Step1;
import "rest-omega.m": SplitOmegaPlus8Centraliser;
import "split.m": GlueCentraliser, SmallestFaithful, MatrixBlocks;
import "base-omega.m": FixGens;
import "SX63.m": MySolveSX63, MyO78q3;
import "../../basics.m": MagmaStandardCopy;
import "../../../../recog/magma/centre.m":EstimateCentre;
import "base.m": MySolveSLRep;

declare verbose ClassicalRecognition, 1;

// do the list of matrices E satisfy standard presentation
// determined by d, q and type?
TestPresentation := function (E, d, q, type)
   if type eq "A" then
      type := "SL";
   elif type eq "2A" then
      type := "SU";
   elif type eq "C" then
      type := "Sp";
   elif type eq "D" then
      type := "Omega+";
   elif type eq "2D" then
      type := "Omega-";
   else
      type := "Omega";
   end if;

   Q, R := ClassicalStandardPresentation (type, d, q);
   Z := Evaluate (R, E);
   return #Set (Z), Z;
end function;

SetupStandardGenerators := function (E1, E2, W1, W2, glue, wglue, 
    n, f, q, type, FinalCall)

   // Orthogonal Generators
   if type eq "D" then
       c := E2[8] *  glue * E1[8];
      wc := W2[8] * wglue * W1[8];
       E := [E1[i] : i in [1..7]] cat [c];
       W := [W1[i] : i in [1..7]] cat [wc];
      return E, W;
   end if;

   if type eq "2D" then
       c := E1[5] *  glue * E2[8];
      wc := W1[5] * wglue * W2[8];
       t := ((n - f) div 2) - 1;
       E := [E1[i] : i in [1..3]] cat [E2[4],  c];
       W := [W1[i] : i in [1..3]] cat [W2[4], wc];
      return E, W;
   end if;

   if type eq "B" then
       c := E1[4] *  glue * E2[8];
      wc := W1[4] * wglue * W2[8];
       E := [E1[i] : i in [1..3]] cat  [c] cat [E2[4]];
       W := [W1[i] : i in [1..3]] cat [wc] cat [W2[4]];
      return E, W;
   end if;

   // non-orthogonal generators
   wc := W2[2] * wglue * W1[2];
    c := E2[2] *  glue * E1[2];

   if type eq "A" then
      E := [E1[1],  c, E1[3], E1[4]];
      W := [W1[1], wc, W1[3], W1[4]];
      return E, W;
   end if;
   
   if type eq "C" then
      if FinalCall then
         E := [E1[1],  c, E1[3], E1[4], E1[5], E1[6]^( c^((n div 2) - 2))];
         W := [W1[1], wc, W1[3], W1[4], W1[5], W1[6]^(wc^((n div 2) - 2))];
      else
	 E := [E1[1],  c, E1[3], E1[4], E1[5], E1[6]];
	 W := [W1[1], wc, W1[3], W1[4], W1[5], W1[6]];
      end if;
      return E, W;
   end if;
   
   if type eq "2A" then
      if IsEven (n) then
         if FinalCall then
            E := [E1[1],  c, E1[3], E1[4], E1[5], E1[6]^( c^((n div 2) - 2)), 
                  E1[7]^( c^((n div 2) - 2))];
            W := [W1[1], wc, W1[3], W1[4], W1[5], W1[6]^(wc^((n div 2) - 2)), 
                  W1[7]^(wc^((n div 2) - 2))];
         else
            E := [E1[1],  c, E1[3], E1[4], E1[5], E1[6], E1[7]];
            W := [W1[1], wc, W1[3], W1[4], W1[5], W1[6], W1[7]];
         end if;
      else
         if FinalCall then
            r1 := (n - 3) div 2;
            r2 := (n - 5) div 2;
            E := [E2[1]^ c^-r1,  c, E2[3]^ c^-r1, E2[4]^ c^-r1,  
                   glue^ c^-(r1 - 1), E2[6], E2[7]];
            W := [W2[1]^wc^-r1, wc, W2[3]^wc^-r1, W2[4]^wc^-r1, 
                  wglue^wc^-(r1 - 1), W2[6], W2[7]];
         else
            if n ge 5 then
               E := [E2[1],  c, E2[3], E2[4],  glue, E2[6], E2[7]];
               W := [W2[1], wc, W2[3], W2[4], wglue, W2[6], W2[7]];
            else
               E := [E2[1],  c, E2[3], E2[4], E2[5], E2[6], E2[7]];
               W := [W2[1], wc, W2[3], W2[4], W2[5], W2[6], W2[7]];
            end if;
         end if;
      end if;
      return E, W;
   end if;
end function;

// for Sp(d, q) we need generators which satisfy relations precisely 
FixForScalars := function (G, type, d, q, E, W)
   Q, R := ClassicalStandardPresentation ("Sp", d, q);
   S := Set (Evaluate (R, E));
   GG := sub<Generic (Parent (Rep (E))) | E>;
   if #S eq 1 then return true, E, W; end if;

   Z, WZ := EstimateCentre (GG, 2);
   S := [x : x in S]; 
   P := [S : i in [1..#E]];
   C := CartesianProduct (P);

   if d eq 4 then
      WW := [W[i]: i in [1,2,3,4,6]];
   else 
      WW := W;
   end if;
   j := 0; 
   for c in C do 
      j +:= 1;
      M := [E[i] * c[i]: i in [1..#E]];
       if #Set (Evaluate (R, M)) eq 1 then 
          // j;  [Order (x): x in c];
          w := []; 
          for i in [1..#E] do 
             if Order (c[i]) ne 1 then 
                fix := WZ[1]; fix := Evaluate (fix, WW);
                w[i] := W[i] * fix; 
             else 
                w[i] := W[i];
             end if;
          end for;
          // assert Evaluate (w, [G.i: i in [1..Ngens (G)]]) eq M;
          return true, M, w;
       end if;
   end for;
   return false, _, _;
end function;

// main algorithm: 
// G is isomorphic to classical group of degree n and supplied type over F
// InputDegree records the degree of the root group supplied to ClassicalSolve 

MyClassicalSolve := function (G, F, n, InputDegree, type: Check := true, 
   Verify := false, Limit := 20)

   p := Characteristic (F);
   if type eq "2A" then
      E := GF(p, Degree (F) div 2);
      q := #E;
   else
      q := #F;
   end if;
   
   IsMatrixGroup := Type (G) eq GrpMat;
   IsOrthogonal := type in ["D", "2D", "B"];
   FinalCall := n eq InputDegree;

   // recognition code does not work for central extensions of type Omega
   if type eq "B" and n eq 7 and q gt 3 then 
      ZG := EstimateCentre (G, 2);
      if #ZG ne 1 then
         vprint ClassicalRecognition: "Group has non-trivial centre, not Omega";
         return false, _;
      end if;
   end if;
   
   if IsOrthogonal and q mod 4 eq 3 then
      if type eq "B" then
         DegreeForBaseCases := 7;
      else
         DegreeForBaseCases := 8;
      end if;
   elif IsOrthogonal and q mod 4 eq 1 and not (q in {5, 9}) then
      DegreeForBaseCases := 8;
   elif IsOrthogonal and (q in {5, 9}) then
      DegreeForBaseCases := 6;
   else
      if type in {"A", "2A", "C"} and q eq 3 then 
         DegreeForBaseCases := 6;
      else 
         DegreeForBaseCases := 4;
      end if;
   end if;
   // solve base case
   if n le DegreeForBaseCases then
      E, W := MyClassicalBaseCases (G, F, n, type: Final := FinalCall);
      return E, W;
   end if;

   found, X, Y, WX, WY, G1, G2, typeX, typeY, f, rem, g, C, 
        Cwords := Step1 (G, type, n, q: Check := Check);
   if not found then return false,_,_,_,_,_,_,_,_,_,_,_,_,_; end if; 

   vprint ClassicalRecognition: "Split f rem is ", f, rem;

   E1, W1 := $$ (G1, F, f, InputDegree, type);
   if Verify then 
      vprint ClassicalRecognition: "Type 1 is ", LieType (G1, Characteristic (F));
      // "Type 1 is ", LMGCompositionFactors (G1);
      // "G1 CORRECT? ", f, TestPresentation (E1, f, q, type) eq 1; 
   end if;

   // if G is orthogonal then G2 must be of +type
   if type in ["D", "2D", "B"] then
      E2, W2 := $$ (G2, F, rem, InputDegree, "D"); 
   else
      E2, W2 := $$ (G2, F, rem, InputDegree, type);
   end if;

   if Verify then 
      ct := type in ["D", "2D", "B"] select "D" else type; 
      vprint ClassicalRecognition: "Type 2 is ", LieType (G2, Characteristic (F));
      // "Type 2 is ", LMGCompositionFactors (G2);
   end if;

   // we must ensure that delta and delta' are conjugate  
/* 
   if IsMatrixGroup and type eq "D" and f eq 4 then
      E1, W1 := MakeConjugate (E1, W1, F);
   end if;
*/

   vprint ClassicalRecognition: "Now set up standard generators for two factors back in G";
   E1 := Evaluate (W1, UserGenerators (X));
   E2 := Evaluate (W2, UserGenerators (Y));
   W1 := Evaluate (W1, WX); 
   W2 := Evaluate (W2, WY); 
   
   // fix required for Sp(f, q) generators
   if type eq "C" then 
      flag, E1, W1 := FixForScalars (G, type, f, q, E1, W1);
      assert flag;
   end if;

   // I is the involution whose centraliser contains the glue element 
   // u and v are the involutions from E1 and E2 respectively whose product = I 
   // Base1 and Base2 are copies of SL2 in involution centraliser used to line up base 
   vprint ClassicalRecognition: "Set up involution for SX4 ";
   I, wI, Base1, WBase1, Base2, WBase2, u, wu, v, wv := 
      ConstructInvolution (E1, W1, E2, W2, f, F, type);
   assert Order (I) eq 2;

   vprint ClassicalRecognition: "Now set up CI ";
   // contruct centraliser CI of I, and extract factor Z isomorphic to 
   // SX(4, q) from CI containing glue element 
   NmrTries := 0;
   repeat
      NmrTries +:= 1;
      DI, DIwords, CI, CIwords := MyDerivedCentraliser (G, I, wI);
      if type eq "D" and q mod 4 eq 1 and n eq 8 then
         foundfactors, Z, WZ := SplitOmegaPlus8Centraliser (G, F, DI, DIwords: 
                     Glueing := true, u := u, v := v);
         trem := 8; W := Z; WW := WZ;
         assert IsCentral (Z, u) eq false;
         assert IsCentral (Z, v) eq false;
      else
         // if G = SX(8, q) then DI has two SX(4, q) factors, 
         // and we must choose the correct one 
         // if q = 3 mod 4, same concern applies to SX(16, q) 
         repeat 
            foundfactors, Z, W, WZ, WW, typeZ, typeW, ff, trem := 
               GlueCentraliser (DI, DIwords, type, n, q);
            if (n eq 8 and type in {"A", "2A", "C"}) or 
               (n eq 16 and q mod 4 eq 3 and type in {"D"}) then 
               good := not IsCentral (Z, u) and not IsCentral (Z, v); 
            else 
               good := true;
            end if;
         until good;
      end if;
   until foundfactors or NmrTries gt Limit;
   if NmrTries gt Limit then error "MyClassicalSolve: Failed to construct Z"; end if;

   // ensure Z is chosen correctly 
   if (not IsOrthogonal and n eq 8 and 
      forall{x : x in UserGenerators (Z) | x * Base1[2] eq Base1[2] * x})
      or (not IsOrthogonal and n ne 8 and trem eq 4) then
      Z := W; WZ := WW; 
   end if;

   // W is the Omega+4 factor 
   if IsOrthogonal and (n ge 7 and q mod 4 eq 1)
      then Z := W; WZ := WW; 
   end if;

   // set up Z for finding the glue element
   // add u, v or two copies of SL(2, q) to existing generators of Z
   if IsOrthogonal and q mod 4 eq 1 then
      U := UserGenerators (Z) cat [u, v];
      Z := sub<Generic (Z) | Z, u, v>;
      WZ := WZ cat [wu, wv];
      Z`UserGenerators := U;
   elif IsOrthogonal and q mod 4 eq 3 then
      Index := [];
      Base12 := Base1 cat Base2;
      Base12 := [Generic (Z)!x : x in Base12];
      WBase12 := WBase1 cat WBase2;
      for i in [1..Ngens (Z)] do
         if not (UserGenerators (Z)[i] in Base12) then
            Append (~Index, i);
         end if;
      end for;
      Z := sub<Generic (Z) | [Z.i : i in Index] cat Base12>;
      WZ := [WZ[i] : i in Index] cat WBase12;
      Z, WZ := FixGens (G, WZ);
   else
      Index := [];
      Base12 := Base1 cat Base2;
      Base12 := [Generic (Z)!x : x in Base12];
      WBase12 := WBase1 cat WBase2;
      for i in [1..Ngens (Z)] do
         if not (UserGenerators (Z)[i] in Base12) then
            Append (~Index, i);
         end if;
      end for;
      Z := sub<Generic (G) | [Z.i : i in Index] cat Base12>;
      WZ := [WZ[i] : i in Index] cat WBase12;
      // assert  Evaluate (WZ, UserGenerators (G)) eq [Z.i: i in [1..Ngens (Z)]];
   end if;

   vprint ClassicalRecognition: "Now call glue";
   ttt := Cputime ();
   if not (IsOrthogonal) or (IsOrthogonal and q mod 4 eq 1) then
      glue, wglue := SX4ForGlue (Z, WZ, F, n, type, FinalCall, 
                        IsMatrixGroup, IsOrthogonal);
   else
      wglue := OrthogonalGlue (Z, WZ, F, type);
   end if;
   vprint ClassicalRecognition, 1 : "Total time to here ", Cputime (ttt);

   vprint ClassicalRecognition: "Now evaluate glue in input group ...";
   glue := Evaluate (wglue, UserGenerators (Z));
   wglue := Evaluate (wglue, WZ);

   vprint ClassicalRecognition: "Now evaluate standard generators in input group ...";
   E, W := SetupStandardGenerators (E1, E2, W1, W2, glue, wglue, n, f, q, type, FinalCall);
   return E, W;
end function;

// a characteristic independent base case?
IsBaseCase := function (type, d, q)
    if type eq "SL" and d in {2, 3} then
       return true;
    elif type eq "SL" and IsEven (q) and d in {4, 5} then
       return true;
    elif type eq "Sp" and d in {2, 4} then
       return true;
    elif type eq "Sp" and d in {6} and IsEven (q) and q gt 2 then
       return true;
    elif type eq "SU" and d in {2, 3, 4} then
       return true;
    elif type eq "SU" and d in {5, 7} and IsEven (q) and q gt 2 then
       return true;
    // elif type in {"Omega+", "Omega-"} and d in {4, 6, 8} 
    elif type in {"Omega-"} and (d eq 10) and IsEven (q) and q gt 2 then
       return true;
    elif type in {"Omega+", "Omega-"} and (d in {4, 6} or
       (d eq 8 and not (q in {5, 9}))) then 
       return true;
    elif type in {"Omega"} and (d in {7} and not q in {5, 9}) then
       return true;
    else 
       return false;
    end if;
end function;

intrinsic Internal_ClassicalSolve (G :: Grp, type :: MonStgElt, d :: RngIntElt, q :: RngIntElt) -> BoolElt, [], []
{G is isomorphic to a classical group of specificied <type> in 
    dimension d, with defining field F; 
the string <type> is one of SL, Sp, SU, Omega, Omega+, Omega-; 
return maps to and from the standard copy, maps rewriting maps, 
standard generators of G and their SLPs in the defining generators of G}

   require Type (G) in {GrpMat, GrpPerm}: "Group must be matrix or permutation group"; 
   require IsPrimePower (q): "Field size is not valid";
   require d ge 2: "Dimension must be at least 2";
   require type in ["SL", "Sp", "SU", "Omega", "Omega+", "Omega-"]: 
      "Type is not valid";

   F := GF (q);
   orig := type;
   if type eq "SL" then
      type := "A"; rank := d - 1;
   elif type eq "SU" then
      type := "2A"; rank := d - 1;
   elif type eq "Sp" then
      type := "C"; rank := d div 2; 
   elif type eq "Omega+" then
      type := "D"; rank := d div 2;
   elif type eq "Omega-" then
      type := "2D"; rank := d div 2;
   elif type eq "Omega" then  
      type := "B"; rank := d div 2;
   end if;

   // special cases for q = 3 
   Fext := type eq "2A" select ext<F | 2> else F;
   if type in {"C", "2A"} and d in {5, 6} and #F eq 3 then
      E, W := MySolveSX63 (G, d, type: FinalCall := true);
   elif type in {"B", "D", "2D"} and d in {7, 8} and #F eq 3 then 
      vprint ClassicalRecognition, 1 : "Special code Omega 7/8 q = 3";
      E, W := MyO78q3 (G, type);
   elif type eq "A" and d gt 2 and #F in {2, 3} then 
       E, W := MySolveSLRep (G, d, #F);
   elif IsBaseCase (orig, d, q) then
      vprint ClassicalRecognition, 1 : "Call base case function";
      E, W := MyClassicalBaseCases (G, Fext, d, type: Final := true);
   else
       if q eq 2 then error "ClassicalSolve: Code does not apply for q = 2"; end if;
       vprint ClassicalRecognition: "*** Use black copy code";
       if Type (G) eq GrpMat then 
          vprint ClassicalRecognition, 1 : "Input to black code: degree = ", Degree (G), "irred? ", IsIrreducible (G);
       end if;
       if IsOdd(#F) then 
	   vprint ClassicalRecognition, 1 : "*** Call odd black code";
           E, W := MyClassicalSolve (G, Fext, d, d, type);
       elif IsEven (#F) then 
           vprint ClassicalRecognition, 1 : "*** Call even black code";
           E, W := Internal_ClassicalSolveEven (G, orig, d, #F);
       end if;
   end if;

   if Type (E) eq BoolElt then return false, _, _;  else 
   return true, E, W; end if;
end intrinsic;
