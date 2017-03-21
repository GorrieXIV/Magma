freeze;

import "functions.m": TensorProductFlag;
import "functions.m": SetTensorInducedBasis;
import "functions.m": SetTensorInducedPermutations;
import "functions.m": SetTensorInducedFactors;
import "functions.m": SetTensorInducedFlag;
import "functions.m": SetGenerators;
import "random.m": RandomElement;
import "tensor.m": KroneckerFactors;
import "smash.m": SmashModule;

forward MultipleTensorProductDecomposition;
forward SwapFactors;

/* matrices generate a matrix group G over a finite field.
   and <S> is a subgroup which acts absolutely irreducibly.
   Test to see if G is tensor-induced.
   If the underlying module for <S> can be decomposed as a
   tensor product of spaces all of the same dimension, and if 
   these tensor factors are permuted non-trivially 
   by the action of G, then the function returns true.
   If no such decomposition is found the function returns false.
   The function uses random elements to try and find the tensor
   decomposition. Thus a negative answer is NOT conclusive.  */

procedure UndoTensorProductFlags (module)

   delete module`TensorProductFlag, module`TensorBasis, module`TensorFactors;

end procedure;
  
SymmetricTensorProductDecomposition := function (module, S) 

  vprintf Smash: "\nTesting to see if the group is tensor-induced\n";
  numTries := 20;  

  d, F := BasicParameters (module);
  matrices := GroupGenerators (module);
  A := MatrixAlgebra (F, d);
  ngens := #matrices;

  Smodule := GModule (Set(S));
  SetGenerators (Smodule, Set (S));

  divisors := Divisors (d);
  poss := [];
  for dd in divisors do
    if dd ne 1 and dd ne d then
      isp, n := IsPowerOf (d, dd);
      if isp then
        Append (~poss, [dd, n]);
      end if;
    end if;
  end for;

  if poss eq [] then 
    vprint Smash: "Dimension is not a proper power";
    return false; 
  end if;

  for pair in poss do

     vprintf Smash: "Trying pair %o in SymmetricTensorProductDecomposition\n", pair;

     dd := pair[1]; n := pair[2];
     flag, tenpow := MultipleTensorProductDecomposition 
                       (Smodule, dd, n, numTries);
     if flag eq false then continue; end if;

     /* it has found a (potentially trivial) decomposition */
     basis := tenpow[1];

     /* for consistency with outcome of IsTensorInduced */
     basis := basis^-1;

     invbasis := basis^-1;

     /* permutations of factors induced by generators */
     permaction := [];
     k := 1;
     permutes := true;
     while permutes and k le ngens do
        // g := basis * (A!matrices[k]) * invbasis;
        /* for consistency with outcome of IsTensorInduced */
        g := invbasis * (A!matrices[k]) * basis;
        pi_g := Sym (n)!1;
        i := 1;
        while permutes and i lt n do
          j := i;
          flag, factors := KroneckerFactors (g, dd^(n - i), dd, F);
          if flag eq false then
            repeat
              j +:= 1; 
              if j le n then
                pi_ij := SwapFactors (1, j + 1 - i, dd, n + 1 - i, F);  
                flag, factors := KroneckerFactors (g * pi_ij, dd^(n - i), dd, F);
                if flag eq true then
                   pi_g := Sym (n)!(i, j) * pi_g;
                end if;
              end if;
            until j gt n or flag eq true;
          end if;
          if flag eq false then
             permutes := false;
          else
            g := factors[1];
            i +:= 1;
          end if;
        end while;

        if permutes then 
          vprintf Smash: "%o-th generator acts as permutation %o on factors\n", k, pi_g;
          Append (~permaction, pi_g); 
          k +:= 1;
        else
          vprint Smash: k, "-th generator does not permute factors";
        end if; 

     end while;

     /* is action trivial? */
     if forall {x : x in permaction | IsIdentity (x)} then
        continue;
     end if; 

     vprint Smash: "Found a tensor-induced decomposition";
     vprintf Smash: "Module is %o-th power of a %o-dimensional module\n", n, dd;

     if permutes then 
        SetTensorInducedFlag (module, true);
        SetTensorInducedBasis (module, basis);
        SetTensorInducedFactors (module, tenpow[2]);
        SetTensorInducedPermutations (module, permaction);
        return true;
     end if; 

  end for;

  return false;

end function;

/* This procedure uses random elements to try and decompose the 
   module as a tensor product of n spaces of dimension d.

   The method is iterative; at each stage of a successful 
   decomposition a space W of dimension a power of d is written 
   as tensor product of two such spaces W1, W2 of lower dimension.
   This is done using a randomly generated element of an appropriate
   order as input for a call of the function SmashModule.
   At most numTries random elements are tried at each stage.

   Basis is either set to false if unsuccessful, or to a matrix 
   over the appropriate algebra, describing the basis of the 
   module which gives rise to the decomposition.  */

MultipleTensorProductDecomposition := function (module, d, n, numTries) 
  
  vprintf Smash: "Trying to decompose as a %o-th tensor power of a \
%o-dimensional module\n", n, d;

  if d^n ne Dimension (module) then return false, _; end if;

  if IsAbsolutelyIrreducible (module) eq false then
     return false, _;
  end if;

  dd, F := BasicParameters (module);
  q := #F;

  A := MatrixAlgebra (F, dd);
  GLprimes := {Characteristic (F)};
  for i in [1..d] do 
    if q ne 2 or i ne 1 then  // exclude q^i - 1 = 1
      GLprimes := GLprimes join SequenceToSet (PrimeBasis (q^i - 1)); 
    end if;
  end for;

  attempt := 1;
  while attempt le numTries do
    vprintf Smash: "In MultipleTensorProductDecomposition loop, attempt %o of %o\n", 
         attempt, numTries;
    h := RandomElement (module);

    po := ProjectiveOrder (h);
    if po ne 1 then
      poprimes := SequenceToSet (PrimeBasis (po));
    else
      poprimes := {};
    end if;

    for r in poprimes do
      if r in GLprimes eq false then
        vprintf Smash: "Projective order %o of element incompatible with %o\
-fold tensor power of V (%o, %o)\n", po, n, d, q;
        vprint Smash: "GLprimes = ", GLprimes;
        vprint Smash: "poprimes = ", poprimes;
        return false, _;
      end if;
    end for;
        
    for r in poprimes do
      hh := h^(po div r);
      SS := [hh];
      UndoTensorProductFlags (module);
      SmashModule (module, ~SS, "PartialSmash");
      if TensorProductFlag (module) cmpeq true then 
        basis := TensorBasis (module);
        module1 := TensorFactors (module)[1];
        module2 := TensorFactors (module)[2];
        dim1 := Dimension (module1);
        dim2 := Dimension (module2);
 
        isp, nn := IsPowerOf (dim1, d);

        if isp then
          if nn ne 1 then
            flag, tenpow1 := $$ (module1, d, nn, numTries);
            if flag eq false then return false, _; end if;
          else
            tenpow1 := [* Identity (GL (dim1, F)), [module1] *];
          end if;
          nn := n - nn;
          if nn ne 1 then
            flag, tenpow2 := $$ (module2, d, nn, numTries);
            if flag eq false then return false, _; end if;
          else
            tenpow2 := [* Identity (GL (dim2, F)), [module2] *];
          end if;
          P := TensorProduct (tenpow1[1], tenpow2[1]);
          factors := tenpow1[2] cat tenpow2[2];
          return true, [* A!(P * basis), factors *];
        end if;
      end if;
    end for;
    attempt +:= 1;
  end while;

  vprintf Smash: "Failed to decompose as a %o-th tensor power of a \
%o-dimensional module\n", n, d;

  return false, _;

end function;

/* set pi_ij to be a d = dd^n by d matrix over F (in a matrix algebra)
   that swaps the i-th and j-th factors in the tensor product of n
   dd-dimensional spaces. We assume that i < j. */

SwapFactors := function (i, j, dd, n, F) 

   d := dd^n;
   Al := MatrixAlgebra (F, d);
   pi_ij := [];
   for k in [1..d^2] do
     pi_ij[k] := 0;
   end for;

   Mb := dd^i;
   Mc := dd^j;
   A := dd^(i - 1) - 1;
   B := dd^(j - i - 1) - 1;
   C := dd^(n - j) - 1;
   Mr := dd^(i - 1);
   Ms := dd^(j - 1);

   for a in [0..A] do
     for b in [0..B] do
       for c in [0..C] do
         for r in [0..dd - 1] do
           for s in [0..dd - 1] do
             k := a + Mr * r + Mb * b + Ms * s + Mc * c + 1;
             l := a + Mr * s + Mb * b + Ms * r + Mc * c + 1;
             pi_ij[d * (k - 1) + l] := 1;
             pi_ij[d * (l - 1) + k] := 1;
           end for;
         end for;
       end for;
     end for;
   end for;    
   return Al!pi_ij;

end function;

/* action of g on tensor factors */

SymmetricTensorAction := function (G, g)
   basis := TensorInducedBasis(G);
   if basis cmpeq "unknown" then
      error "Group not known to be tensor induced";
   end if;
   permutes := true;
   invbasis := basis^-1;
   // g := basis * g * invbasis;
   /* for consistency with outcome of IsTensorInduced */
   g := invbasis * g * basis;

   P := TensorInducedPermutations (G);
   n := Maximum ([Degree (Parent (x)): x in P]);
   d := Degree(G);
   dd := Iroot (d, n);

   pi_g := Sym (n)!1;
   i := 1;
   F := BaseRing(G);
   while permutes and i lt n do
      j := i;
      flag, factors := KroneckerFactors (g, dd^(n - i), dd, F);
      if flag eq false then
         repeat
            j +:= 1; 
            if j le n then
               pi_ij := SwapFactors (1, j + 1 - i, dd, n + 1 - i, F);  
               flag, factors := KroneckerFactors (g * pi_ij, dd^(n - i), dd, F);
               if flag eq true then
                  pi_g := Sym (n)!(i, j) * pi_g;
               end if;
             end if;
         until j gt n or flag eq true;
      end if;
      if flag eq false then
         permutes := false;
      else
         g := factors[1];
         i +:= 1;
      end if;
   end while;
   if permutes then 
      vprintf Smash: "Element acts as permutation %o on factors\n", pi_g;
   else
      vprint Smash: "Element does not permute factors";
   end if; 

   return pi_g;

end function;
