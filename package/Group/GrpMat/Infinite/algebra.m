freeze;

import "attributes.m": RF;
import "general.m": MatrixGenerators; 
import "congruence.m": SetMapTypes, MyCongruenceImage;
import "finite.m": IsFiniteMatrixGroup;
import "virtual.m": ModuleViaNullSpace;

/* G is congruence image defined over F of function field group H;
   generating sets S and T, closed under inverses, 
   are in one-to-one correspondence; 
   construct a basis for the F-enveloping algebra of G, 
   and construct corresponding shadow elements of H */

EnvelopingAlgebraBasis := function (G, S, H, T: Verify := false)

   F := BaseRing (G);
   n := Degree (G);
   MA := KMatrixSpace (F, n, n);

   d := Degree (H);
   K := BaseRing (H);
   MB := KMatrixSpace (K, d, d);

   A := [MA | ]; B := [MB | ];
   A[1] := Id (G); B[1] := Id (H);

   V := VectorSpace(F, n^2);
   X := sub <V | [Vector(x): x in A]>;

   i := 0;
   while i lt #A do 
      //"* i", i; "* #S", #S;
      i +:= 1;
      for j in [1..#S] do 
         x := A[i] * S[j];
	 Include (~X, Vector(x), ~new);
	 if not new then continue; end if;
         Append (~A, x);
         y := B[i] * T[j];
         Append (~B, y);
         if Dimension (X) mod 20 eq 0 then 
            vprint Infinite: "Dimension of enveloping algebra is now ...", Dimension (X);
         end if;
      end for;
   end while;

   if Verify then 
      for j in [1 .. #A] do
	  r := Rank(Matrix([A[i]: i in [1..j]]));
	  assert r eq j;
      end for;
   end if;

   vprint Infinite: "Dimension of enveloping algebra is ", Dimension (X);

   return A, B;
end function;

/* G is admissible representation defined over F for function field group H 
   with generating sets S and T in one-to-one correspondence; 

   we know a basis A for enveloping algebra of G and the corresponding 
   elements B of H; does enveloping algebra for H have same dimension 
   as that for G? if not, return false and element in kernel, else true;

   if in positive characteristic, then evaluate trace of coefficients
   wrt GroundField and also scale by mu, degree of extension */ 

IsAlgebraBasis := function (V, A, S, B, T: mu := 1,
                            EvaluateTrace := false, Field := [])

   for i in [1..#A] do
      for j in [1..#S] do 
         g := A[i] * S[j];
         c := Coordinates (V, g);
         if EvaluateTrace eq true then 
            c := [Trace (c[k], Field): k in [1..#c]]; 
         end if;
//         h := &+[c[i] * B[i]: i in [1..#c]];
//         h := c[1] * B[1]; for k in [2..#c] do h +:= c[k] * B[k]; end for;
         h := c[1] * B[1];
	 for k in [2..#c] do
	    AddScaledMatrix(~h, c[k], B[k]);
	 end for;
         value := mu * B[i] * T[j]; 
         if h ne value then return false, h - value; end if;
       end for;
   end for;
   return true, _; 
end function;

/* compute exponent e of unipotent matrices in GL(n, F) where F has
   char p > 0; e satisfies the inequality p^(e - 1) < n <= p^e */

ExponentUnipotent := function (n, p)
   flag, e := IsPowerOf (n, p);
   if flag then return e; else return Ilog (p, n) + 1; end if;
end function;

/* H is subgroup of GL(n, K) where K is function field
   defined over field F of positive characteristic; 
   attempt to decide if H is finite; 

   Isomorphism: search for isomorphic copy;

   PowerLimit: compute power of generators only if < PowerLimit;

   if H is known to be completely reducible or nilpotent, then
   call function with appropriate optional flag set to true, 
   since we can reach a decision more readily;

   return true if H is finite, false if H is infinite */

PositiveCharFF := function (H: CompletelyReducible := false, 
   PowerLimit := 100, Nilpotent := false, Isomorphism := false)

   K := BaseRing (H);
   F := CoefficientRing (K);
   p := Characteristic (F);
   assert p gt 0;

   n := Degree (H);

   /* if H is nilpotent, then we may replace H by H^(p^e),
      where p^e is exponent of unipotent elements */
   e := ExponentUnipotent (n, p);
   power := p^e;
   if power gt PowerLimit then Nilpotent := false; end if;

   if (not Isomorphism) and Nilpotent then
      vprint Infinite: "Replace generators by unipotent exponent power", power; 
      H := sub <GL(n, K) | [H.i^power: i in [1..Ngens (H)]]>;
      if IsTrivial (H) then return true; end if;
      // if G is finite, H is now completely reducible 
      CompletelyReducible := true;
   end if;

   G, tau, S := MyCongruenceImage (H: Algebra := true);
   T := MatrixGenerators (H);
   S := MatrixGenerators (S);

   A, B := EnvelopingAlgebraBasis (G, S, H, T);

   E := BaseRing (G); 
   VA := KMatrixSpaceWithBasis (A);

   /* is the kernel of congruence map trivial?
      if not, construct submodule and take projections;
      recursively investigate these to decide finiteness */

   InvestigateKernel := function (H, T, B: 
      CompletelyReducible := false, Nilpotent := false)

      K := BaseRing (H);
      F := CoefficientRing (K);

      /* we know a basis A for enveloping algebra of G and the 
         corresponding elements B of H; does enveloping algebra 
         for H have same dimension as that for G? */

      mu := Degree (E) div Degree (F);
      basis, J := IsAlgebraBasis (VA, A, S, B, T: mu := mu, Field := F,
         EvaluateTrace := CompletelyReducible select false else true);
      vprint Infinite: "Basis?", basis;
      if basis then return true, basis; end if;

      /* we have found element in kernel of congruence map */

      /* if group is completely reducible or nilpotent 
         and kernel is non-trivial, then group is infinite */

      if CompletelyReducible or Nilpotent then return false, _; end if;

      vprint Infinite: "Investigate kernel of congruence homomorphism";
      N := ModuleViaNullSpace (T, J);
      vprint Infinite: "Dimension of submodule found is ", Dimension (N);
      if Dimension (N) eq 0 then return false, _; end if;
   
      n := Degree (H);
      V := VectorSpace (K, n);
      CB := ExtendBasis (Basis (N), V);
      CB := [Eltseq (x): x in CB];
      CB := GL(n, K) ! CB;

      /* rewrite H wrt basis exhibiting submodule */
      H := sub<GL(n, K) | [CB * H.i * CB^-1: i in [1..Ngens (H)]]>;
      T := [CB * T[i] * CB^-1: i in [1..#T]];
      B := [CB * B[i] * CB^-1: i in [1..#B]];

      a := Dimension (N);
      /* process first block */
      H1 := sub<GL(a, K) | [ExtractBlock (H.i, 1, 1, a, a): 
                           i in [1..Ngens (H)]]>; 
      T1 := [ExtractBlock (T[i], 1, 1, a, a): i in [1..#T]];
      B1 := [ExtractBlock (B[i], 1, 1, a, a): i in [1..#B]];
      vprint Infinite: "Dimension of first block of H is", Degree (H1);
      first := $$ (H1, T1, B1); 
      vprint Infinite: "Result of first block call of degree ", Degree (H1), ":", first;
      if first eq false then return false, _; end if;
         
      /* process second block */
      H2 := sub<GL(n - a, K) | 
              [ExtractBlock (H.i, a+1, a+1, n-a, n-a): i in [1..Ngens (H)]]>; 
      vprint Infinite: "Dimension of second block of H is", Degree (H2);
      T2 := [ExtractBlock (T[i], a+1, a+1, n-a, n-a): i in [1..#T]];
      B2 := [ExtractBlock (B[i], a+1, a+1, n-a, n-a): i in [1..#B]];
      second := $$ (H2, T2, B2);
      vprint Infinite: "Result of second block call of degree ", Degree (H2), ":", second;
      if second eq false then return false, _; end if;
      // assert first eq true and second eq true;
      return true, basis;
   end function;

   finite, isom := InvestigateKernel (H, T, B: Nilpotent := Nilpotent,
           CompletelyReducible := CompletelyReducible); 
   H`Congruence`Finite := finite;

   /* if nilpotent, we considered powers of generators of input group only */
   if finite and isom and (Nilpotent eq false) then 
      H`Congruence`Isomorphism := true; 
   end if;

   return finite, G, tau;
end function;

/* positive char only */

IsomorphismAlgebraAlgorithm := function (H, G, S: CompletelyReducible := false)

   T := MatrixGenerators (H);
   S := MatrixGenerators (S);

   A, B := EnvelopingAlgebraBasis (G, S, H, T);

   VA := KMatrixSpaceWithBasis (A);

   K := BaseRing (H);
   F := CoefficientRing (K);
   assert Characteristic (F) gt 0;

   /* we know a basis A for enveloping algebra of G and the 
      corresponding elements B of H; does enveloping algebra 
      for H have same dimension as that for G? if so, we have
      an isomorphism */

   E := BaseRing (G); 
   mu := Degree (E) div Degree (F);
   basis, J := IsAlgebraBasis (VA, A, S, B, T: mu := mu, Field := F,
         EvaluateTrace := CompletelyReducible select false else true);
   vprint Infinite: "Basis?", basis;
   return basis;
end function;

/* H is a subgroup of GL(n, K) where K is a function field
   and F is its coefficient field; if H is finite, return true,
   else return false;

   Isomorphism: search for isomorphic copy;

   if we can decide the order of a subgroup of GL(n, F), 
   then we can also decide the order of H;

   if H is completely reducible or nilpotent, then call this 
   function with appropriate optional parameter set to true, 
   since we can reach a decision more readily */

FunctionFieldAlgebraAlgorithm := function (H : CompletelyReducible := false, 
      Isomorphism := false, Magma := true, Nilpotent := false) 
   K := BaseRing (H);

   if not ISA (Type(K), FldFunRat) then error "Incorrect input"; end if;

   F := CoefficientRing (K);

   if Characteristic (F) gt 0 then 
      return PositiveCharFF (H: Nilpotent := Nilpotent, 
      Isomorphism := Isomorphism, CompletelyReducible := CompletelyReducible);
   end if; 

   G, tau, S := MyCongruenceImage (H: Prime := 0, Selberg := false);

   H`Congruence := rec<RF | Map := tau, Image := G>;
   SetMapTypes (H, false, true, false);

   T := MatrixGenerators (H);
   S := MatrixGenerators (S);

   /* if congruence map has a kernel, then H is not finite */
   if #Set(S) ne #Set(T) then return false, _, _; end if;

   /* if G is not finite, then H is not finite */
   flag := IsFiniteMatrixGroup (G: Magma := Magma, OrderTest := false);
   if not flag then return false, _, _; end if; 

   A, B := EnvelopingAlgebraBasis (G, S, H, T);

   V := KMatrixSpaceWithBasis (A);
  
   /* we know a basis A for enveloping algebra of G and the corresponding 
      elements B of H; does enveloping algebra for H have same dimension 
      as that for G? if not, then H is not finite */

   finite := IsAlgebraBasis (V, A, S, B, T);

   H`Congruence`Finite := finite;
   if finite then 
      H`Congruence`Isomorphism := true; return true, G, tau;
   else 
      return false, _, _; 
   end if;
end function;
