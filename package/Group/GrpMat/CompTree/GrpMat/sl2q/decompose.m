freeze;

import "../Smash/functions.m": 
SetTensorProductFlag, TensorProductFlag, SetTensorBasis, SetTensorFactors;

import "../Tensor/is-tensor.m": ConstructTensorFactors, TensorDimensions;
import "../Tensor/find-point.m": GeneralFindPoint;

/* evaluate scalar multiple lambda of g */

ScalarMultiple := function (g, lambda)
   P := Parent (g);
   F := BaseRing (P);
   d := Degree (P);
   return MatrixAlgebra (F, d) ! lambda * g;
end function;

ScaleMatrix := function (g)
   det := Determinant (g);
   m := Nrows (g);
   flag, lambda := IsPower (det, m);
   if flag eq false then return false; end if;
   return ScalarMultiple (g, lambda^-1);
end function;

ScaleFactor := function (G)
   K := BaseRing (G);
   m := Degree (G);
   new := [Identity (GL (m, K))];
   U := UserGenerators (G);
   scale := false;
   for i in [1..#U] do
      det := Determinant (U[i]);
      if det gt 1 then scale := true; end if;
      flag, lambda := IsPower (det, m);
      // error if flag eq false, "Error in ScaledTensorFactors";
      if flag eq false then return false; end if;
      new[i] := ScalarMultiple (U[i], lambda^-1);
   end for;
   if scale then
      S := sub <GL (m, K) | new>; S`UserGenerators := new; return S, true;
   else
      return G, false;
   end if;
end function;

/* return tensor factors which have determinant 1 */

ScaledTensorFactors := function (G, b)
   K := BaseRing (G);
   U := UserGenerators (G);
   x, y := AreProportional ([U[i]^b[1]: i in [1..#U]], b[2]);

   m := Nrows (y[1][1]);
   gens := [y[i][1]: i in [1..#y]];  
   First := sub <GL (m, K) | [y[i][1]: i in [1..#y]]>;  
   First`UserGenerators := gens;

   n := Nrows (y[1][2]);
   gens := [y[i][2]: i in [1..#y]];  
   Second := sub <GL (n, K) | [y[i][2]: i in [1..#y]]>;
   Second`UserGenerators := gens;
      
   return ScaleFactor (First), ScaleFactor (Second), First, Second;

end function;

/* given sequence E of elements of finite field, construct certain
   arithmetic progressions; if MaxAP is true, give up as soon as 
   we find one of length #E */

FindAPs := function (E, deg, p: MaxAP := false)

   if #E le 1 then return []; end if;
   AP := [];
   for first in [1..#E] do 
      x := E[first];
      for index in [1..#E] do 
         if index eq first then continue; end if;
         y := E[index];
         d := y - x;
         list := [x, y];
         if deg mod #list eq 0 then
            Append (~AP, list);
         end if;
         for i in [3..#E] do 
	    if MaxAP eq false and #list ge p then break i; end if;
            term := list[i - 1] + d;
            if term in E and not (term in list) then 
               list[i] := term;
	       if deg mod i eq 0 then 
                  Append (~AP, list);
	       end if;	   
            else 
               break i; 
            end if;
         end for;
         if MaxAP and #list eq #E then return [list]; end if;
      end for;
   end for;

   return SetToSequence (Set (AP));

end function;

/* construct space determined by g and arithmetic progression a
   of its eigenvalues, and send space to FindPoint */

ProcessSequence := function (G, g, a) 
   Z := Integers ();
   F := BaseRing (G);
   w := PrimitiveElement (F);
   ev := [w^(Z!x) : x in a];   
   Space := &+[Eigenspace (g, e): e in ev];
   CB := "unknown"; Status := false;
   GeneralFindPoint (G, ~Space, Dimension (Space), ~Status, ~CB);
   return Status, CB;
end function;
 
procedure StoreDetails (G, Result)
   CB := Result[1];
   SetTensorProductFlag (G, true);
   SetTensorBasis (G, CB);
   U, W := ConstructTensorFactors (G, Result);
   SetTensorFactors (G, [U, W]);
end procedure;

/* G is a tensor product of symmetric powers of SL(2, q)
   twisted under action of Frobenius maps;
   decompose one symmetric power */

DecomposeTensor := function (G)

   d := Degree (G);
   if d eq 2 then return false, _; end if;
    
   F := BaseRing (G);
   p := Characteristic (F);
   e := Degree (F);

   if (IsOdd (p) and ((e eq 2 and d in {(p - 1)^2, p * (p - 1)}) or 
                (d eq p^e))) or (p eq 2 and e eq 2 and d eq 4) then 
      vprint sl2q: "Need special version of DecomposeTensor for these cases";
      if d mod p eq 0 then   
         factors := [[p, d div p]]; 
      elif d mod (p - 1) eq 0 then 
         factors := [[p - 1, d div (p - 1)]]; 
      end if;
      flag := IsTensor (G: Factors := factors);
      if flag cmpeq true then 
         u, w := TensorDimensions (G);
         Result := <TensorBasis (G), u>;
         return true, Result; 
      else 
         return false, _;
      end if;
   end if;

   q := #F;

   NmrTries := 100;
   required := p eq 2 select (q - 1) else (q - 1) div 2;
   flag, g := RandomElementOfOrder (G, required: 
                 MaxTries:= NmrTries,  Central := true);
   if flag cmpeq false then 
      vprint sl2q: "Failed to find element of order ", required;
      return false, false; 
   end if;

   Lambda := Eigenvalues (g);
   vprint sl2q: "Number of eigenvalues is ", #Lambda;
   original := #Lambda;

   Lambda := [x : x in Lambda | x[2] eq 1];

   vprint sl2q: "Number of eigenvalues of multiplicity 1 = ", #Lambda;
   if #Lambda le 1 then 
      vprint sl2q: "Too few eigenvalues left"; 
      return false, false; 
   end if;

   /* are there multiplicities in eigenvalues? */
   multiplicity := #Lambda lt original;

   E := [Log (x[1]): x in Lambda];  
   Z := Integers ();
   Zq := quo <Z | q - 1>;
   E := [Zq ! x : x in E];

   nmr := 0;

   /* largest prime dividing d */
   lp := Maximum (PrimeBasis (d));

   /* minimum length of AP if multiplicity among EVs */
   least := (p + 1) div 2;

   /* construct arithmetic progressions of length ell,
      where ell is at most p and ell is a multiple of lp;
      if multiplicity-free then ell is proper divisor of d;
      if not, then ell >= least */ 

   for first in [1..#E] do 
      x := E[first];
      for index in [1..#E] do 
         if index eq first then continue; end if;
         y := E[index];
         step := y - x;
         a := [x, y];
	 if d mod #a eq 0 then 
            if (multiplicity and #a ge least) or
               (not multiplicity and #a mod lp eq 0) then 
               flag, Result := ProcessSequence (G, g, a);
               nmr +:= 1;
               if flag then 
                  StoreDetails (G, Result);
                  vprint sl2q:"Arithmetic progression is ", a;
                  vprint sl2q:"Number of calls to FindPoint is", nmr; 
                  return true, Result; 
               end if;
            end if;
         end if; 

	 /* construct APs of length at most p; if the length 
            of the AP properly divides the degree of G, 
            then send space to FindPoint */
         for i in [3..p] do 
            term := a[i - 1] + step;
	    if not (term in E) then break i; end if;
	    if (term in a) then break i; end if;
            a[i] := term;
            if #a gt d div 2 then break i; end if;
	    if d mod #a eq 0 then 
               if (multiplicity and #a ge least) or
                  (not multiplicity and #a mod lp eq 0) then 
                  flag, Result := ProcessSequence (G, g, a);
                  nmr +:= 1;
                  if flag then 
                     vprint sl2q:"Arithmetic progression is ", a;
	             vprint sl2q:"Number of calls to FindPoint is", nmr; 
                     StoreDetails (G, Result);
                     return true, Result; 
                  end if;
               end if;
	    end if;	   
         end for;
      end for;
   end for;

   return false, false;

end function;
