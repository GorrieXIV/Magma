freeze;

// import "../Smash/random.m": RandomElement;
import "groebner.m": FindNonNegativeSolution;

/*  following three functions are not currently used */

CopiesOf := function (P, u)

   Copies := {};
   lu := #u; 
   for i in [1..#P] do 
      v := P[i];
      Include (~Copies, [u[v[j]] : j in [1..lu]]);
   end for;
   
   return Copies;

end function;

SolveEquations := function (A, v)

   flag, s := IsConsistent (A, v); 

   if flag then 
      flag := forall {s[i] : i in [1..Degree (s)] | s[i] ge 0}; 
   else 
      s := false;
   end if;

   return flag, s;

end function;

SumOfWeights := function (a, b)

   return &+[a[i] * b[i] : i in [1..#a]];

end function;

/* find tensor product of polynomials f and g */

PolynomialTensorProduct := function(f, g)

   return CharacteristicPolynomial(
        TensorProduct(CompanionMatrix (f), CompanionMatrix (g)));

end function;

/* take some power of g, an element of (projective) order n 
   to obtain an element of (projective) order at most Limit */

PowerOfSmallOrder := function (g, n, Limit)

   if n eq 1 or IsPrime (n) then return g; end if;

   f := Factorisation (n);
   powers := [f[i][1]^f[i][2] : i in [1..#f]];
   powers := [x : x in powers | x le Limit];

   if #powers gt 0 then 
      power := Random (powers);
      newg := g^(n div power);
   else
      newg := g^(n div f[1][1]);
   end if;

   return newg;
   
end function;

/* use the inherent symmetry of a left-hand factor to write 
   down permutations to reduce the number of possible solutions */
   
ApplySymmetry := function (F, n, PolyBasis) 

   q := #F;
   factor := Gcd (q - 1, n);

   if factor eq 1 then return []; end if;

   omega := PrimitiveElement (F);
   lambda := omega^((q - 1) div factor);

   PR := Parent (PolyBasis[1]);
   f := PR.1 - lambda;

   Image := [Position (PolyBasis, PolynomialTensorProduct (PolyBasis[i], f)):
                        i in [1..#PolyBasis]];
   Image cat:= [#PolyBasis + 1];

   p := SymmetricGroup (#PolyBasis + 1) ! Image;
   Perms := [Eltseq (p^i) : i in [Order(p) - 1..1 by - 1]];

   return Perms;

end function;

/* P is the list of permutations, u is one possible left-hand side; 
   if some image of u under an element of P occurs later in an 
   ordering, we don't need to process u */
   
ProcessVector := function (P, u, lenu)
   
   i := 1; 
   repeat 
      v := P[i];
      Im := [u[v[j]] : j in [1..lenu]];
      if Im gt u then return false; end if;
      i +:= 1;
   until i gt #P;

   return true;

end function;

/* given sequence of polynomials, some product of which is f,
   find which exponents occur in f */

ExponentsOfFactors := function (R, f)

   fac := Factorisation (f);

   exponents := [0 : i in [1..#R]];

   for i in [1..#fac] do
      factor := fac[i];
      j := Position (R, factor[1]);
      exponents[j] := factor[2];
   end for;

   return exponents;

end function;

/* setup the basis matrices and write them over the integers */

SetupMatrices := function (Table)

   n := #Table[1];
   m := #Table[1][1];

   R := RMatrixSpace (Integers (), n, m);

   M := [];
   for i in [1..#Table] do
      x := Table[i];
      y := &cat[x[j] : j in [1..#x]];
      M[i] := R!y;
   end for;

   return M;

end function;

/* Perms is list of possible permutations which can be 
   used to reduce number of possible left-hand sides; 
   M is the set of matrices; t is the right-hand side;
   Degrees is list of degrees of the factors;
   DimU is the degree of the u factor; 
   build up left-hand side and solve system */

FindFactorisation := function (Perms, M, t, Degrees, DimU, NonNegativeSolution)

   tot := 0;

   n := #M;
   lenm := n + 1;
   m := [0 : i in [1..n + 1]];
   x := 0;

   Outstanding := false; /* can we settle the question for this element? */

   LIMIT := 10^5; // max number of solns to consider 
   repeat 
      index := 1;
      m[index] +:= 1;
      x +:= Degrees[index];

      while (index le n and x gt DimU) do
         x -:= m[index] * Degrees[index];
         m[index] := 0;
         index +:= 1;
         m[index] +:= 1;
         if index le n then 
            x +:= Degrees[index];
         end if;
      end while;

      if x eq DimU then 
         if #Perms eq 0 or ProcessVector (Perms, m, lenm) then 
            A := &+[m[i] * M[i] : i in [1..n]];
            tot +:= 1; 
            flag, s, K := IsConsistent (A, t); 

            if flag then 
               vprintf Tensor: "A solution over Z was found after testing %o\
 vectors of correct weight\n", tot;
               vprintf Tensor: "Kernel has dimension %o\n", Dimension (K);
               Resolved := true;
               if exists {i : i in [1..Degree (s)] | s[i] lt 0} then
                  if Dimension (K) gt 0 then 
                     if NonNegativeSolution then 
                        /* we should test if some translate of this solution 
                          is non-negative; this may be very expensive */
                        vprint Tensor: "Now try for a solution over N";
                        NonNegative, s := FindNonNegativeSolution (A, t);
                     else 
                        Resolved := false;
                        /* record one possible solution over Z */
                        NonNegative := false;
                        zm := m; zs := s;
                     end if; /* if NonNegativeSolution */
                  else 
                     vprint Tensor: "Solution is unique";
                     NonNegative := false;
                  end if; /* Dimension (K) gt 0 */
               else
                  vprint Tensor: "Our existing solution is over N ";
                  NonNegative := true;
               end if; /* if exists */

               if not Resolved then Outstanding := true; end if;

               if NonNegative then 
                  vprint Tensor: "A solution over N found after testing", tot,  
                        "vectors of correct weight";
                  vprint Tensor: "m = ", m, "s = ", s;
                  return true, m, s, true;
               end if;

            end if; /* if flag */

         end if; /* if ProcessVector */

      end if; /* if x eq DimU */

   until (index gt n) or (tot gt LIMIT);
   // until (index gt n); 
   
   if tot gt LIMIT then Outstanding := true; end if;

   if Outstanding then 
      vprint Tensor: "*** Existence of non-negative solution for some u unresolved ***"; 
      return true, zm, zs, false; 
   end if;

   vprint Tensor: "Number of vectors of correct weight tested is ", tot;

   return false, false, false, true;

end function;

/* compute factors of x^n - theta */

ListFactors := function (F, n, theta)

   local x;

   A<x> := PolynomialRing (F);

   P := x^n - theta;

   R := Factorisation (P);
   Reverse (~R);

   PolyBasis := [R[i][1] : i in [1..#R]];
   Degrees := [Degree (R[i][1]) : i in [1..#R]];

   return PolyBasis, Degrees;

end function;

/* compute tensor product of each element of PolyBasis1 with 2
   and record what combination of elements of PolyBasis
   is equal to this product */   

ComputeTensorTable := function (PolyBasis, PolyBasis1, PolyBasis2)

   T := [];
   for i in [1..#PolyBasis1] do
      T[i] := [];
      for j in [1..#PolyBasis2] do
         tp := PolynomialTensorProduct (PolyBasis1[i], PolyBasis2[j]);
         T[i][j] := ExponentsOfFactors (PolyBasis, tp);
      end for;
   end for;

   return T;

end function;

/* f is the characteristic polynomial of an element of order n;
   does it have a tensor factorisation with a factor of degree dimU? */

DecideFactorisation := function (F, f, n, phi, n0, PolyBasis,
                                 dimU, t, NonNegativeSolution)

   /* run over theta where theta is an element of F^* / (F^*)^n  
      and F^* is the multiplicative group of the field */

   x := PrimitiveElement (F);
   E := [x^i : i in [0..n0 - 1]];

   Outstanding := false;
   for theta in E do

      PolyBasis1, Degrees1 := ListFactors (F, n, theta);
      PolyBasis2, Degrees2 := ListFactors (F, n, phi * theta^-1);
      Table := ComputeTensorTable (PolyBasis, PolyBasis1, PolyBasis2);
      M := SetupMatrices (Table);

      Perms := ApplySymmetry (F, n, PolyBasis1);
      found, u, v, Resolved := FindFactorisation (Perms, M, t, 
				      Degrees1, dimU, NonNegativeSolution);
      vprintf Tensor: "u = %o  v = %o\n", u, v;
      if found and Resolved then return found, u, v, Resolved; end if;
      if not Resolved then Outstanding := true; end if; 

   end for;

   return false, false, false, not Outstanding;

end function;

/* try to tensor factorise the characteristic polynomials
   of N random elements of G; Outstanding records if the 
   possible factorisation over the natural nuumbers
   is not conclusively decided */

procedure FactorisePolynomials (G, N, ~List, ~Outstanding, NonNegativeSolution)

   MaxOrder := 40;
   MaxNmrFactors := 24;
 
   F := BaseRing (G);
   q := #F;

   /* examine tensor factorisation of characteristic polynomial */
   Tested := {@ @};
   NmrElts := 0;

   Outstanding := false;

   P := RandomProcess (G);
   repeat
      NmrElts +:= 1;
      g := Random (P);
      n, phi := ProjectiveOrder (g);
    
      /* if the order of g is too large, replace g by some power */
      if n gt MaxOrder then 
         g := PowerOfSmallOrder (g, n, MaxOrder);
         n, phi := ProjectiveOrder (g);
      end if;

      if n gt MaxOrder then continue; end if;

      f := CharacteristicPolynomial (g);

      if not (f in Tested) then
         Include (~Tested, f);
         n0 := Gcd (n, q - 1);

         /* get factors of x^n - phi and express f as a product 
            of its irreducible factors */

         PolyBasis, Degrees := ListFactors (F, n, phi);

         if #Degrees gt MaxNmrFactors then 
             vprint Tensor: "*** Too Many Factors ***"; 
             continue; 
         end if;

         vprintf Tensor: "\nProjective order of element is %o\n", n;

         t := ExponentsOfFactors (PolyBasis, f);
         t := RSpace (Integers (), #t) ! t;

         for pair in List do
            vprintf Tensor: "Processing dimension factorisation %o\n", pair;
            /* do we find tensor product factorisation? */
            found, u, v, Resolved := DecideFactorisation (F, f, n, phi, n0, 
				   PolyBasis, pair[1], t, NonNegativeSolution);

            vprintf Tensor: "Resolved is %o\n", Resolved;

            if (not found) and Resolved then Exclude (~List, pair); end if;

            if not Resolved then Outstanding := true; end if;
         end for;
      end if;
   until #List eq 0 or NmrElts ge N;
end procedure;
