freeze;

import "sl2.m": SL2Basis;

import "../Smash/functions.m":TensorProductFlag;

import "../Tensor/is-tensor.m": TensorDimensions;

import "decompose.m": DecomposeTensor, ScaledTensorFactors,
ScalarMultiple, ScaleMatrix, ScaleFactor;

import "issympower.m": IsSymmetricPower, PreimageOfElement;

import "ldu.m": SL2ElementToSLP;

/* given g as element of G, a (projective) repn of SL(2, q), 
   construct its preimage in natural repn of SL(2, q) */

LargeToSmall := function (G, g)
  
   Basis := SL2Basis (G);
   if Type (Basis) eq BoolElt then
      error "First apply RecogniseSL2";
   end if;
   gens := Basis[1]; words := Basis[2]; dim2cb := Basis[3]; cb := Basis[4];

   K := BaseRing (G);
   if IsTensor (G) cmpeq true then 
      CB := TensorBasis (G);
      // order changed to reflect change in IsTensor
      // u, w := TensorDimensions (G);
      w, u := TensorDimensions (G);

      flag, facs := IsProportional (g^CB, u);
      // old before change to IsTensor 
      // if flag then h := GL(u, K) ! facs[1]; else return false; end if;
      if flag then h := GL(u, K) ! facs[2]; else return false; end if;
      det := Determinant (h);
      flag, lambda := IsPower (det, u);
      if flag eq false then return false; end if;
      h := GL (u, K) ! ScalarMultiple (h, lambda^-1);
      // old before change to IsTensor 
      // P := TensorFactors (G)[1];
      P := TensorFactors (G)[2];
      P := ScaleFactor (P);
   else 
      h := g;
      P := G;
   end if;

   flag, n := PreimageOfElement (P, cb * h * cb^-1, cb);
   if flag eq false or Determinant (n) ne 1 then return false; end if;

   return dim2cb * n * dim2cb^-1;
end function;

/* h element of H = SL(2, q); G (projective) representation of H;
   return image of h in G */
   
SmallToLarge := function (G, h)

   w := SL2ElementToSLP (G, h);
   if Type (w) eq BoolElt then return false; end if;
   if not assigned G`SLPGroup then
      W := Parent (w);
      G`SLPGroup := W;
      G`SLPGroupHom := hom <W -> G | UserGenerators (G)>;
   end if;
   g := G`SLPGroupHom (w); 
   return g;
end function;
