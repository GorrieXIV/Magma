freeze;

/* implementation of Neumann & Praeger non-constructive recognition
   algorithm for SL(2, q) = Sp (2, q) in its natural 
   representation by Michael Downward and Eamonn O'Brien; 
   now includes SU(2, q) and code of Peter Brooksbank 
   to recognize (S)O^+-(2, q); latest version July 2007 */

import "classical.m": InfoRecog;

/*
input: subgroup <G> of GL(2,q)
output:
   <flag> = true if <G> preserves unique symmetric bilinear form
   <form> = symmetric form preserved by <G>
*/
SymmetricForm2 := function (G) 
     M := GModule (G);
     N := Dual (M);
     F := BaseRing (G);
     mat := KMatrixSpace (F, 2, 2);
     Ghom := sub < mat | Basis (AHom (M, N)) >;
     sym := sub < mat | [ [1,0,0,0], [0,1,1,0], [0,0,0,1] ] >; 
     Gsym := Ghom meet sym;
     if Dimension (Gsym) eq 1 then 
        mat := MatrixAlgebra (BaseRing (G), 2)!Gsym.1;
        return Rank (mat) eq 2, mat; 
     else 
         InfoRecog (2, "<G> does not preserve a unique symmetric form");
         if #F in {3, 5} and #G in {1, 2} then 
            return true, MatrixAlgebra (F, 2)![0,1,1,0];
         end if;
         return false, _;
     end if;
end function;

/*
input: any matrix group <G> and symmetric form <bil> preserved by <G>
output:
   <flag> = true if <G> preserves a quadratic form with associated bilinear form <bil>
   <form> = the quadratic form preserved, given in its usual form
*/
QuadraticFormOfBilinearForm := function (G, bil)

     d := Nrows (bil);

     if Characteristic (BaseRing (G)) eq 2 then
        X := Zero (KMatrixSpace (BaseRing (G), d, d * Ngens (G)));
        W := Zero (KMatrixSpace (BaseRing (G), 1, d * Ngens (G)));
        for i in [1..Ngens (G)] do
           g := G.i;
           for s in [1..d] do
           // modify column (i, s) of X
              for t in [1..d] do
                 if s eq t then
                    X[t][(i-1)*d+t] := g[t][t]^2 - 1;
                 else
                    X[t][(i-1)*d+s] := g[s][t]^2;
                 end if;
              end for;
              // modify entry (i, s) of W
              W[1][(i-1)*d+s] := &+[ g[s][t] * g[s][u] * bil[t][u] : 
                                  t in [1..d], u in [1..d] | u gt t];
           end for;
        end for;

        // test for a solution to the linear system
        flag, diag, ker := IsConsistent (X, W);
        if not flag then
            InfoRecog (2, "<G> preserves no quadratic form");
           return false, _;
        end if;
        diag := diag[1];

     else
	diag := [ bil[i][i]/2 : i in [1..Nrows (bil)] ]; 
     end if; 

     // insert diagonal entries
     form := Zero (MatrixAlgebra (BaseRing (G), d));
     for s in [1..d] do
        form[s][s] := diag[s];
        for t in [s+1..d] do
	   form[s][t] := bil[s][t];
        end for;
     end for;
     
return true, form;
end function;

/*
input: subgroup <G> of GL (2, q)
output:
   <flag> = true if <G> preserves a unique quadratic form 
   <form> = the quadratic form preserved
    <bil> = the associated bilinear form
   <type> = the type of <form>  ... "orthogonalplus" or "orthogonalminus"
*/
OrthogonalForm2 := function (G) 
     flag, bil := SymmetricForm2 (G);
     if not flag then
        return false, _, _, _; 
     end if;
     flag, form := QuadraticFormOfBilinearForm (G, bil);
     if not flag then
        return false, _, _, _;
     end if;
     // next determine the type
     pol := Polynomial ([ form[1][1], form[1][2], form[2][2] ]);
     if #Roots (pol) eq 0 then
        type := "orthogonalminus";
     else
        type := "orthogonalplus";
     end if;
return true, form, bil, type;
end function;

/*
input: <G>
output:
   <flag> = true if <G> preserves a quadratic form and contains <Omega>
   <type> = "orthogonalplus" or "orthogonalminus"
   <proper> = true if <G> contains <Omega> as proper subgroup 
   <q_form> = the quadratic form preserved
   <b_form> = the bilinear form preserved
*/
RecognizeOmega2 := function (G : NumberOfElements := 20)

    if IsTrivial (G) then return false, _, _, _, _; end if;

    F := BaseRing (G);
    q := #F;
    MA := MatrixAlgebra (F, 2);

    if q eq 5 then
       RandomSchreier (G);
       Verify (G);
       o := #G;
       if o eq 2 then  // <Omega> is the only exceptional case
          return true, "orthogonalplus", false, MA![0,1,-1,0], MA![0,1,-1,0];
       end if;
    end if; 

    // q = 4  ... no problems

    if q eq 3 then
       RandomSchreier (G);
       Verify (G);
       o := #G;
       if o eq 4 then
          if IsCyclic (G) then  // <G> = SOMinus (2, 3)
              return true, "orthogonalminus", true, 
                           MA![0,1,-1,0], MA![0,1,-1,0];
          else // <G> = GOPlus (2, 3)
              return true, "orthogonalplus", true, _, _;
          end if;
       end if;
       if o eq 2 then
          if forall { g : g in G | IsScalar (g) } then  
              return true, "orthogonalminus", false, _, _;
              // this group is also SOPlus (2, 3)
          else
             return false, _, _, _;
          end if;
       end if;
    end if;

    if q eq 2 then
       RandomSchreier (G);
       Verify (G);
       o := #G;
       if o eq 2 then  // only nontrivial problem group is GOPlus (2, 2)
          return true, "orthogonalplus", true, _, _;
       end if;
    end if;

    // general case

    flag, form, bil, type := OrthogonalForm2 (G);
    if flag eq false then return false, _, _, _, _; end if;

    // now <G> preserves quadratic <form>
    // check that <G> contains Omega
    if type eq "orthogonalplus" then
    // if type eq 1 then 
       required := (q - 1) div Gcd (2, q - 1);
    else 
       required := (q + 1) div Gcd (2, q + 1);
    end if;

    flag, x := RandomElementOfOrder (G, required: MaxTries := NumberOfElements);
    if flag eq false then return false, _, _, _, _; end if;

    // check spinor norm
    proper := exists { i : i in [1..Ngens (G)] | SpinorNorm (G.i, bil) eq 1 };

    // name := type eq 1 select "orthogonalplus" else "orthogonalminus"; 
    return true, type, proper, form, bil;

end function;

/*
input: <G>
output:
   <flag> = true if <G> preserves a quadratic form and contains <SO>
   <type> = "orthogonalplus" or "orthogonalminus"
   <proper> = true if <G> contains <SO> as proper subgroup 
   <q_form> = the quadratic form preserved
   <b_form> = the bilinear form preserved
*/
RecognizeSO2 := function (G: NumberOfElements := 20) 

    if IsTrivial (G) then return false, _, _, _, _; end if;

    F := BaseRing (G);
    q := #F;
    MA := MatrixAlgebra (F, 2);

    // first deal with special cases
    // these are similar to, but easier than, special cases in RecognizeOmega2

    if q eq 2 then
       o := #G;
       if o eq 2 then  // only nontrivial problem group is GOPlus (2, 2)
          return true, "orthogonalplus", false, _, _;
       end if;
    end if;

    if q eq 3 then
       o := #G;
       if o eq 4 then
          if IsCyclic (G) then  // <G> = SOMinus (2, 3)
              return true, "orthogonalminus", false, 
                           MA![0,1,-1,0], MA![0,1,-1,0];
          else // <G> = GOPlus (2, 3)
              return true, "orthogonalplus", true, _, _;
          end if;
       end if;
       if o eq 2 then
          if forall { g : g in G | IsScalar (g) } then  
              return true, "orthogonalplus", false, _, _;
          else
             return false, _, _, _;
          end if;
       end if;
    end if;

    // general case

    if (q mod 2 eq 0) then  // SO = GO, which is nonabelian
 
        if IsAbelian (G) then 
            return false, _, _, _, _; 
        else
            flag, name, proper, form, bil := RecognizeOmega2 (G);
            if flag then
                return true, name, true, form, bil;
            else
                return false, _, _, _, _;
            end if;
        end if;

    end if;

    // if <q> is odd follow a similar path to RecognizeOmega2

    flag, form, bil, type := OrthogonalForm2 (G);
    if flag eq false then return false, _, _, _, _; end if;

    if type eq 1 then
        required := q - 1;
    else 
        required := q + 1;
    end if;

    flag, x := RandomElementOfOrder (G, required: MaxTries := NumberOfElements);
    if flag eq false then return false, _, _, _, _; end if;

    // this catches desired cyclic and dihedral groups

    name := type eq 1 select "orthogonalplus" else "orthogonalminus"; 
    return true, name, not IsAbelian (G), form, bil;

end function;
 
// construct orbit of v under G; we want to know 
// if orbit length > 60
VectorOrbit := function (G, v)
   O := {@ v @};
   k := 1;
   while k le #O do
      for i in [1..Ngens (G)] do
         Include (~O, O[k]^G.i);
      end for;
      if #O gt 60 then return false; end if; 
      k +:= 1;
   end while;
   return O;
end function;

IdentifyGModuloZ := function (G)
   V := VectorSpace (BaseRing (G), 2);
   v := sub < V | V.1 >;
   O := VectorOrbit (G, v);
   if Type (O) ne BoolElt then
      L := [[Position (O, O[i]^G.j):  i in [1..#O]]: j in [1..Ngens (G)]];
      H := sub < Sym (#O) | L >;
      if #H eq 12 or #H eq 24 or #H eq 60 then
         if IdentifyGroup (H) eq <60, 5> then return "A5"; end if; // A5
         if IdentifyGroup (H) eq <24, 12> then return "S4"; end if; // S4
         if IdentifyGroup (H) eq <12, 3> then return "A4"; end if; // A4
      end if;
   end if;
   return false;
end function;

MyIsSemiLinear := function (G, x)
   if IsIrreducible (CharacteristicPolynomial (x)) then
      x1 := x^2;
      if forall{i : i in [1..Ngens (G)] | IsId ( (x1, x1^G.i))} then
         return true;
      end if;
   end if;
   return false;
end function;

MyIsImprimitive := function (G, x)
   if #Eigenvalues (x) eq 2 then
      S := {};
      for l in Eigenvalues (x) do
         Include (~S, Eigenspace (x, l[1]));
      end for;
      if forall {i : i in [1..Ngens (G)] | S^G.i eq S} then return true; end if;
   end if;
   return false;
end function;

MyFindRandomh := function (G : NumberOfElements := 100)
   InfoRecog (2, "Warning: considering random elements");
   P := RandomProcess (G); 
   nmr := NumberOfElements;
   repeat
     h := Random (P);
     if not IsCentral (G, h^2) then return h; end if;
     if nmr eq 0 then 
        InfoRecog (1, "Unable to find suitable random element"); 
        return false; 
     end if; // G/Z probably has exponent 2
     nmr -:= 1;
   until false;
end function;

MyFindh := function (G : NumberOfElements := 100)
   if forall (h){G.i : i in [1..Ngens (G)] | IsCentral (G, G.i^2)} then
      if forall {(G.i, G.j) : i in [1..Ngens (G)], j in [1..Ngens (G)] | 
                 IsCentral (G, (G.i, G.j))} then
         return false; // G/Z has exponent 2
      else
         if forall (h) {(G.i, G.j) : i in [1..Ngens (G)], j in [1..Ngens (G)] | IsCentral (G, (G.i, G.j)^2)} then
            return MyFindRandomh (G : NumberOfElements := NumberOfElements);
         end if;
      end if;
   end if;
   return h;
end function;

RecogniseDegree2 := function (G, Case: NumberOfElements := 100)

   // input must be matrix group of dimension 2
   if Type (G) ne GrpMat or Dimension(G) ne 2 then
      InfoRecog (1, "Error: Input must be matrix group of degree 2"); 
      return false; 
   end if; 

   if IsTrivial (G) then return false; end if;

   if Case eq "linear" and assigned G`recognize`isLinearGroup then 
      return G`recognize`isLinearGroup; 
   end if;
   if Case eq "symplectic" and assigned G`recognize`isSymplecticGroup then 
      return G`recognize`isSymplecticGroup; 
   end if;
   if Case eq "unitary" and assigned G`recognize`isUnitaryGroup then 
      return G`recognize`isUnitaryGroup; 
   end if;
   if Case eq "orthogonalplus" 
      and assigned G`recognize`isOrthogonalPlusGroup then 
      return G`recognize`isOrthogonalPlusGroup; 
   end if;
   if Case eq "orthogonalminus" 
      and assigned G`recognize`isOrthogonalMinusGroup then 
      return G`recognize`isOrthogonalMinusGroup; 
   end if;

   if Case in ["orthogonalplus", "orthogonalminus", "unknown"] then 
      flag, type, proper := RecognizeOmega2 (G);

      if flag eq true then 
         if type eq "orthogonalplus" then 
            G`recognize`isOrthogonalPlusGroup := true; 
            return Case in ["orthogonalplus", "unknown"];
         else 
            G`recognize`isOrthogonalMinusGroup := true; 
            return Case in ["orthogonalminus", "unknown"];
         end if;
      else 
         G`recognize`isOrthogonalPlusGroup := false; 
         G`recognize`isOrthogonalMinusGroup := false; 
      end if; 
   end if;

   if Case in ["orthogonalplus", "orthogonalminus"] then
      return false;
   end if;

   if not IsAbsolutelyIrreducible (G) then 
      G`recognize`isLinearGroup := false;
      G`recognize`isUnitaryGroup := false;
      G`recognize`isSymplecticGroup := false;
      return false;
   end if;

   F := BaseRing (G);
      
   /* can G be rewritten modulo scalars over subfield? */
   small, H := IsOverSmallerField (G : Scalars := true); 
   if small then 
      K := BaseRing (H);
      /* is K a subfield not equal to GF(q) */
      if #F ne #K^2 then 
         InfoRecog (1, "Group is written modulo scalars over inappropriate subfield");
         G`recognize`isLinearGroup := false;
         G`recognize`isUnitaryGroup := false;
         G`recognize`isSymplecticGroup := false;
         return false; 
      end if;
   else
      H := G;
      K := F;
   end if;

   // small enough to check directly; avoids problems with later checks 
   if #K le 5 then 
      P := SL (2, K); RandomSchreier (P); RandomSchreier (H);
      Verify (P); Verify (H);
      if P subset H then
         if K eq F then 
            InfoRecog (1, "SL is contained in G (checked directly)"); 
            G`recognize`isLinearGroup := true;
            G`recognize`isSymplecticGroup := true;
            G`recognize`isUnitaryGroup := false;
         else 
            InfoRecog (1, "SU is contained in G (checked directly)"); 
            G`recognize`isLinearGroup := false;
            G`recognize`isSymplecticGroup := false;
            G`recognize`isUnitaryGroup := true;
         end if;
         return true;
      else
         InfoRecog (1, "G does not contain classical group (checked directly)"); 
         G`recognize`isLinearGroup := false;
         G`recognize`isSymplecticGroup := false;
         G`recognize`isUnitaryGroup := false;
         return false;
      end if;
   end if;

   if IsAbelian (H) then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Group is abelian"); return false; 
   end if; // abelian

   if not IsIrreducible (H) then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Group is reducible"); return false; 
   end if; // reducible

   // find h such that h^2 is non-central
   // if we cannot such h, conclude H/Z probably has exponent 2
   h := MyFindh (H : NumberOfElements := NumberOfElements);
   if Type (h) eq BoolElt then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Central quotient probably has exponent 2"); 
      return false; 
   end if; 

   if MyIsSemiLinear (H, h) cmpeq true then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Group is semilinear"); return false; 
   end if; // is conjugate to subgroup of GammaL

   x := h^2;
   
   if MyIsImprimitive (H, x) then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Group is imprimitive"); return false; 
   end if; // imprimitive

   // is H/Z isomorphic to A4, S4, A5?
   a := IdentifyGModuloZ (H);
   if Type (a) ne BoolElt then 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := false;
      InfoRecog (1, "Group modulo its centre is isomorphic to " cat a); 
      return false; 
   end if;

   // everything else goes through okay
   InfoRecog (1, "Group has passed all of the tests");

   if K eq F then 
      G`recognize`isLinearGroup := true;
      G`recognize`isSymplecticGroup := true;
      G`recognize`isUnitaryGroup := false;
   else 
      G`recognize`isLinearGroup := false;
      G`recognize`isSymplecticGroup := false;
      G`recognize`isUnitaryGroup := true;
   end if;

   return true;
end function;
