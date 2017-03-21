freeze;

/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************

                     MODABVAR: Modular Abelian Varieties in MAGMA

                              William A. Stein

   FILE: inner_twists.m
   DESC: Inner twists of spaces of modular symbols associated to newforms.

    Modifications by Jordi Quer (April, 2006) to the function InnerTwistCharacters:
    -   The bound 15+N div 4 has been replaced by 15+N div 2, because using the former
        too many twists were detected (for example, for level 28 and quadratic character,
        and for level 52 and characters of orders 4 and 12).
    -   The output when IsTrivial(eps) and (N eq SquarefreeFactorization(N)) should NOT contain any
        CM twist.

 ***************************************************************************/

import "modabvar.m":
   Verbose;

import "misc.m":
   IsSquareFree,
   idxG0;

import "rings.m":
   CC, QQ, Qbar;

import "../ModSym/arith.m":
   GetModulus;

forward
   Aplists_Embedded_In_CC,
   CC_Sequence_AlmostEqual,
   Compute_Inner_Twists_Over_K,
   InnerTwistCharacters,
   IsInnerTwist,
   MapsFromModularSymbolsTypeFieldToCC,
   TwistIsOverK;

function Compute_Inner_Twists_Over_K(M, K, proof)
   assert Type(M) eq ModSym;

   eps := DirichletCharacter(M);
   one := Parent(eps)!1;

   if K cmpeq QQ or (IsTrivial(DirichletCharacter(M)) and IsSquareFree(Level(M))) then
      return [one],[one];
   end if;

   if Type(K) eq FldNum then
      L := MaximalAbelianSubfield(K);
      N := Norm(Conductor(L));
      if GCD(N,Level(M)) eq 1 then   // since inner twist characters have conductor dividing level.
         return [one],[one];
      end if;
   end if;

   twists, cm := InnerTwistCharacters(M, proof);  // these are all of them.
   twists_K := [x : x in twists | TwistIsOverK(x,K)];
   cm_K := [x : x in cm | TwistIsOverK(x,K)];
   // Now which are defined over K?  Don't worry -- function calling us
   //  will base extend to Qbar if there are twists.

//      printf "WARNING: %o nontrivial inner twists ignored.\n",#twists_K-1;
//      return [one],[one];

   if #twists_K gt 0 then
      return twists_K, cm_K;
   end if;
   return [one],[one];
end function;

function TwistIsOverK(chi, K)  // not yet written -- see above requirement.
   return true;
end function;


function MapsFromModularSymbolsTypeFieldToCC(K)
   case Type(K):
      when FldRat, RngInt:
         return [hom<K -> CC | x :-> CC!x>];
      when FldCyc:
         s := CyclotomicOrder(K);
         return [hom<K -> CC | Exp(n*2*Pi(CC)*CC.1/s)> : n in [1..s] | GCD(n,s) eq 1];
      when RngUPolRes, FldNum:
         f := GetModulus(K);
         R := Parent(f);
         L := BaseRing(R);
         // inductively compute embeddings of base ring to CC using above.
         X := MapsFromModularSymbolsTypeFieldToCC(L);
         // Define maps from R to poly ring over CC.
         RC := PolynomialRing(CC);
         Y := [ hom<R -> RC | f :-> RC![phi(x) : x in Eltseq(f)]> : phi in X ];
         // For each element of Y, there are deg(f) maps from K to CC.
         Z := [];
         for phi in Y do
            for root in [x[1] : x in Roots(phi(f))] do
               psi := hom<K -> CC | x :->  Evaluate(phi(R!Eltseq(x)),root)>;
               Append(~Z,psi);
            end for;
         end for;
         return Z;
      else
         assert false;
   end case;
end function;


function Aplists_Embedded_In_CC(M, P)
   assert Type(M) eq ModSym;
   assert Type(P) eq SeqEnum;

   // 1. Get eigenvalue sequences as extensions of polynomial ring.
   S := SystemOfEigenvalues(M, P[#P]+1);
   // Throw away the elements of S corresponding to primes not in P.
   T := [];
   p := 2;
   for s in S do
      if p in P then
         Append(~T, s);
      end if;
      p := NextPrime(p);
   end for;

   // 2. Embeddings in C.
   PHI := MapsFromModularSymbolsTypeFieldToCC(Parent(T[1]));
   T := [[phi(x) : x in T] : phi in PHI];
   return T;
end function;

function CC_Sequence_AlmostEqual(v, w, prec)
   assert #v eq #w;
   for i in [1..#v] do
      if Abs(v[i] - w[i]) gt prec then
         return false;
      end if;
   end for;
   return true;
end function;

function IsInnerTwist(chi, aplists, P)
   assert Type(chi) eq GrpDrchElt;
   assert Type(aplists) eq SeqEnum;
   assert Type(P) eq SeqEnum;

   twist := [(CC!Evaluate(chi,P[i]))*aplists[1][i] : i in [1..#P]];
   for j in [1..#aplists] do
       aplist := aplists[j];
       if CC_Sequence_AlmostEqual(twist, aplist, 10^(-5)) then
          return true, j eq 1;
       end if;
   end for;
   return false, false;
end function;

function InnerTwistCharacters(M, proof)
   assert Type(M) eq ModSym;

   eps := DirichletCharacter(M);
   one := Parent(eps)!1;
   N := Modulus(eps);
   if IsTrivial(eps) and (N eq SquarefreeFactorization(N)) then
//      return [one], [one];
      return [one], [];
   end if;
   k := Weight(M);

   if proof then
      bound := Ceiling(k/12*idxG0(N^2));
   else
//      bound := 15 + N div 4;
      bound := 15 + N div 2;
   end if;
   Verbose("InnerTwistCharacters",
       Sprintf("Using possibly unproved (but probably OK) bound of %o in verifying "*
          "that inner twists are really inner twists.",bound),"");

   if IsEven(Conductor(eps)) then
      NN := LCM(8, Modulus(eps));
      if NN ne N then
         eps := Extend(eps, NN);
      end if;
   end if;
   N := Modulus(eps);

   quadratic_characters := [x : x in Elements(Parent(eps)) | Order(x) le 2];

   s := Order(eps);
   if IsOdd(s) then
      sqrt_eps := Sqrt(eps);
   end if;

   P := [p : p in [2..bound] | IsPrime(p) and N mod p ne 0];
   //   P := [p : p in [2..bound] | IsPrime(p)];
   aplists := Aplists_Embedded_In_CC(M, P);

   ans := [];
   ans_cm := [];
   for gamma in [a : a in [1..s] | GCD(a,s) eq 1] do
      for psi in quadratic_characters do
         if IsEven(s) then   // in this case gamma is necessarily odd,
                             // so gamma-1 is even, so sqrt(eps^(gamma-1)) is easy.
            chi := psi*eps^((gamma-1) div 2);
         else
            chi := psi*sqrt_eps^(gamma-1);
         end if;
         t, cm := IsInnerTwist(chi, aplists, P);
         if t then
            Append(~ans, chi);
         end if;
         if cm and not IsTrivial(chi) then
            Append(~ans_cm, chi);
         end if;
      end for;
   end for;

   return ans, ans_cm;
end function;
