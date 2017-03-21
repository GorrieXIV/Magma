freeze;

forward MySL2ElementToWord;

declare verbose sl2q, 1;

import "../Smash/functions.m": TensorProductFlag;
import "../Tensor/is-tensor.m": TensorDimensions;
import "black-sl2.m": RecogniseBlackBoxSL2, BlackBoxElementToSLP; 
import "natural.m": ConstructSL2Basis;
import "decompose.m": DecomposeTensor, ScaledTensorFactors, 
                      ScaleFactor, ScalarMultiple, ScaleMatrix;
import "issympower.m": IsSymmetricPower, PreimageOfElement;
import "ldu.m": SL2ElementToSLP;
import "large-to-small.m": LargeToSmall, SmallToLarge;

/* set up hom from B -> G where U is the list of images of
   generators of B; do it in this way to  ensure that it
   does not force membership testing in G */

MyHom := function (G, B, U)
   d := Degree (G);
   if Type (G) eq GrpMat then 
      F := BaseRing (G);
      P := GL (d, F);
   elif Type (G) eq GrpPerm then 
      P := Sym (d);
   end if;
   gens := [P ! G.i : i in [1..Ngens (G)]];
   pos := [Position (gens, U[i]) : i in [1..#U]];
   return hom <B -> G | [G.i : i in pos]>;

end function;

HasCorrectShape := function (X, i, j)
   return (X[1][1] eq 1) and (X[2][2] eq 1) and
          (X[j][i] eq 0) and (X[i][j] ne 0);
end function;

/* upper triangular, lower triangular and diagonal matrices required */
  
IsSL2Basis := function (gens)

   if Nrows (Rep (gens)) ne 2 then 
      return false, _, _, _;
   end if;

   if forall{x : x in gens | Determinant (x) ne 1} then 
      return false, _, _, _;
   end if;

   if #gens ne 3 then return false, _, _, _; end if;

   if not exists (DM) {x : x in gens | IsDiagonal (x)} then 
      return false, _, _, _;
   end if;

   if not exists (LM) {x : x in gens | HasCorrectShape (x, 2, 1)} then 
      return false, _, _, _;
   end if;

   if not exists (UM) {x : x in gens | HasCorrectShape (x, 1, 2)} then 
      return false, _, _, _;
   end if;

   return true, DM, LM, UM;
end function;

SL2Basis := function (G)
   if assigned G`SL2Basis then return G`SL2Basis; else return false; end if;
end function;

procedure SetSL2Basis (G, Basis)
   G`SL2Basis := Basis; 
end procedure;

/* recognise SL(2, q) */
MyRecogniseSL2 := function (H: Verify := true) 

   if Degree (H) eq 2 then 
      if Verify then 
         flag := IsLinearGroup (H) and IsProbablyPerfect (H);
      else 
         flag := true; 
      end if;
      if flag then 
         flag := ConstructSL2Basis (H);
         if flag then 
            return true;
         else
            return false;
         end if;
      else
         return false;
      end if;
   end if;

   flag, CB := DecomposeTensor (H);
   if flag eq true then 
      First, Second := ScaledTensorFactors (H, CB);
      if Type (First) eq BoolElt then return false; end if;
   else 
      H`TensorProductFlag := false;
      Second := H;
   end if;

   if Degree (Second) eq 2 then 
      // N := First;
      N := Second;
      cb := Identity (N);
      gens := UserGenerators (N);
   else 
      flag, cb, gens := IsSymmetricPower (Second);
      if not flag and assigned First then 
         flag, cb, gens := IsSymmetricPower (First);
      end if;
      if not flag then return false; end if;
      K := BaseRing (H);
      N := sub <GL (2, K) | gens>;
      N`UserGenerators := gens;
   end if;

   if assigned H`SLPGroup then 
      N`SLPGroup := H`SLPGroup; 
      N`SLPGroupHom := MyHom (N, N`SLPGroup, gens);
   end if;

   flag := ConstructSL2Basis (N);
   if flag eq false then return false; end if;

   /* add into B the change-of-basis matrix for the symmetric power */
   B := SL2Basis (N);
   SetSL2Basis (H, <B[1], B[2], B[3], cb>);

   return true;
end function;

MainRecogniseSL2 := function (G, Fdef) 
   q := #Fdef;

   if Type (G) eq GrpMat then 
      F := BaseRing (G);
      d := Degree (G);
      p := Characteristic (F);
      f := Factorization (q);
      e := f[1][2];

      Blackbox := q in {2, 3} or (p ne f[1][1]) or (IsOdd (p) and 
               ((e eq 2 and d in {(p - 1)^2, p * (p - 1)}) or (d eq p^e))); 

      M := GModule (G);

      Blackbox := Blackbox or (not IsAbsolutelyIrreducible (M)); 

      if not Blackbox and #F gt q then 
         flag := IsOverSmallerField (G : Scalars := true); 
         if flag eq true then 
            // "Input group must be over minimal field modulo scalars";
            Blackbox := true;
         end if;
      end if;
   else 
      Blackbox := true;
   end if;

   W, delta := WordGroup (G);
   G`SLPGroup := W;
   G`SLPGroupHom := delta;

   /* special cases */
   if (Blackbox) then 
      vprintf sl2q: "RecogniseSL2: Call BlackBox code\n";
      return RecogniseBlackBoxSL2 (G, q);
   end if;

   flag := IsStandardGF (F);
   if not flag then
      error "Group is not defined over standard copy of field -- use
Embed to create isomorphic copy over standard field";
   end if;

   /* otherwise use the more efficient defining characteristic algorithm */
   P := GL(d, p^e);
   if #F lt q then 
      vprintf sl2q:"To apply RecogniseSL2 to G, first embed G in GL(%o, %o^%o)\n", d, p, e;
      // EOB April 27, 2011 -- error here to work with user generators 
      // since W and delta are on generators 
      // U := [P!u: u in UserGenerators (G)];
      U := [P!u: u in [G.i: i in [1..Ngens (G)]]];
      M := sub <P| U>;
      M`UserGenerators := U;
      M`SLPGroup := G`SLPGroup;
      M`SLPGroupHom := delta;
      new := true;
   else
      M := G;
      // March 2013 -- added 4 lines 
      if assigned G`UserGenerators then 
         RecordU := G`UserGenerators;
         delete M`UserGenerators; 
      end if;
      new := false;
   end if;

   flag := MyRecogniseSL2 (M);
   if not flag then return false, _, _, _, _; end if;

   /* may need to record data from M */
   if new then 
      G`SL2Basis := M`SL2Basis;
      if TensorProductFlag (M) cmpeq true then 
         CB := TensorBasis (M);
         facs := TensorFactors (M);
         G`TensorProductFlag := true; 
         G`TensorBasis := CB;
         G`TensorFactors := facs;
      end if;
   else 
      // March 2013 -- added next line
      if assigned RecordU then G`UserGenerators := RecordU; end if;
   end if;

   H := SL(2, Fdef);
   gl := GL(Degree (G), F);
   forw := hom<gl -> H | x :-> LargeToSmall (M, P ! x)>;
   back := hom<H -> gl | x :-> SmallToLarge (M, x)>;
  
   Embed(CoefficientRing(gl), CoefficientRing(P));

   word := hom<gl -> W | x :-> MySL2ElementToWord (M, P ! x)>;
   return true, forw, back, word, delta;
end function;

intrinsic RecogniseSL2 (G::GrpMat, F :: FldFin : Verify := true) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, F),
 construct homomorphisms between G and (P)SL(2, F);
 return homomorphism from G to (P)SL(2, F), homomorphism
 from (P)SL(2, F) to G, the map from G to
 its word group and the map from the word group to G.
}
   if Verify then 
      v, q1 := SL2Characteristic (G: Verify := false);
      good := (#F eq 4 and q1 eq 5) or (#F eq 5 and q1 eq 4) or (#F eq q1);
      if not good then return false, _, _, _, _; end if;
   end if;
   return MainRecogniseSL2 (G, F);
end intrinsic;

intrinsic RecogniseSL2 (G::GrpPerm, F :: FldFin : Verify := true) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, F),
 construct homomorphisms between G and (P)SL(2, F);
 return homomorphism from G to (P)SL(2, F), homomorphism
 from (P)SL(2, F) to G, the map from G to
 its word group and the map from the word group to G.
}
   if Verify then 
      v, q1 := SL2Characteristic (G: Verify := false);
      good := (#F eq 4 and q1 eq 5) or (#F eq 5 and q1 eq 4) or (#F eq q1);
      if not good then return false, _, _, _, _; end if;
   end if;
   return MainRecogniseSL2 (G, F);
end intrinsic;

intrinsic RecogniseSL2 (G::GrpMat, q ::RngIntElt : Verify := true) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to
 its word group and the map from the word group to G.
}
   if Verify then 
      v, q1 := SL2Characteristic (G: Verify := false);
      good := (q eq 4 and q1 eq 5) or (q eq 5 and q1 eq 4) or (q eq q1);
      if not good then return false, _, _, _, _; end if;
   end if;
   return RecogniseSL2(G, GF(q));
end intrinsic;

intrinsic RecogniseSL2 (G::GrpPerm, q ::RngIntElt : Verify := true) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to
 its word group and the map from the word group to G.
}
   if Verify then 
      v, q1 := SL2Characteristic (G: Verify := false);
      good := (q eq 4 and q1 eq 5) or (q eq 5 and q1 eq 4) or (q eq q1);
      if not good then return false, _, _, _, _; end if;
   end if;
   return RecogniseSL2(G, GF(q));
end intrinsic;

intrinsic RecogniseSL2 (G::GrpMat) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to its word group, 
  and the map from the word group to G.
}
   /* field size subject to assumption G is (P)SL(2) */
   k, q := SL2Characteristic (G: Verify := false);
   if k eq 0 or q eq 0 then 
      "Failed to identify field size, input is probably not (P)SL(2)"; 
      return false, _, _, _, _;
   else
      vprint sl2q:"Defining field has size ", q;
   end if;
   return RecogniseSL2(G, q);
end intrinsic;

intrinsic RecogniseSL2 (G::GrpPerm) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to its word group, 
  and the map from the word group to G.
}
   /* field size subject to assumption G is (P)SL(2) */
   k, q := SL2Characteristic (G: Verify := false);
   if k eq 0 or q eq 0 then 
      "Failed to identify field size, input is probably not (P)SL(2)"; 
      return false, _, _, _, _;
   else
      vprint sl2q:"Defining field has size ", q;
   end if;
   return RecogniseSL2(G, q);
end intrinsic;

intrinsic RecognizeSL2 (G::GrpMat, q ::RngIntElt) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to
 its word group and the map from the word group to G.
}
   return RecogniseSL2 (G, q);
end intrinsic;

intrinsic RecognizeSL2 (G::GrpPerm, q ::RngIntElt) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to
 its word group and the map from the word group to G.
}
   return RecogniseSL2 (G, q);
end intrinsic;

intrinsic RecognizeSL2 (G::GrpMat) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to its word group, 
  and the map from the word group to G.
}
   // field size subject to assumption G is (P)SL(2) 
   k, q := SL2Characteristic (G: Verify := false);
   if k eq 0 or q eq 0 then 
      "Failed to identify field size, input is probably not (P)SL(2)"; 
      return false, _, _, _, _;
   else
      vprint sl2q:"Defining field has size ", q;
   end if;
   return RecogniseSL2(G, q);
end intrinsic;

intrinsic RecognizeSL2 (G::GrpPerm) -> BoolElt, Map, Map, Map, Map 
{if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 construct homomorphisms between G and (P)SL(2, q);
 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, the map from G to its word group, 
  and the map from the word group to G.
}
   // field size subject to assumption G is (P)SL(2) 
   k, q := SL2Characteristic (G: Verify := false);
   if k eq 0 or q eq 0 then 
      "Failed to identify field size, input is probably not (P)SL(2)"; 
      return false, _, _, _, _;
   else
      vprint sl2q:"Defining field has size ", q;
   end if;
   return RecogniseSL2(G, q);
end intrinsic;

/* write g as SLP in user-generators of G */

MySL2ElementToWord := function (G, g) 

   Basis := SL2Basis (G);

   if Type (Basis) eq BoolElt then 
      error "First apply RecogniseSL2"; 
   end if;
   dim2cb := Basis[3]; cb := Basis[4];

   K := BaseRing (Parent (cb));
   parent := GL(Degree (G), K);
   g := parent ! g;

   if TensorProductFlag (G) cmpeq true then 
      CB := TensorBasis (G);
      // u, w := TensorDimensions (G);
      w, u := TensorDimensions (G);
      flag, facs := IsProportional (g^CB, u);
      // if flag then h := GL(u, K) ! facs[1]; else return false; end if;
      if flag then h := GL(u, K) ! facs[2]; else return false; end if;
      det := Determinant (h);
      flag, lambda := IsPower (det, u);
      if not flag then return false; end if;
      h := GL (u, K) ! ScalarMultiple (h, lambda^-1);
      // P := TensorFactors (G)[1];
      P := TensorFactors (G)[2];
      P := ScaleFactor (P);
   else 
      h := g;
      P := G;
   end if;

   flag, n := PreimageOfElement (P, cb * h * cb^-1, cb);
   if flag eq false or Determinant (n) ne 1 then return false; end if;

   w := SL2ElementToSLP (G, dim2cb * n * dim2cb^-1);
   if Type (w) eq BoolElt then return false; end if;
   W := Parent (w);

   if not assigned G`SLPGroup then 
      G`SLPGroup := W; 
      G`SLPGroupHom := hom <W -> G | UserGenerators (G)>;
   end if;

   if IsScalar (g * parent ! G`SLPGroupHom (w)^-1) eq false then
      return false; 
   end if;
   return w;
end function;

intrinsic SL2ElementToWord (G:: GrpMat, g:: Mtrx) -> BoolElt, GrpSLPElt
{if g is element of G which has been constructively recognised to have
 central quotient isomorphic to PSL(2, q), then return true and element of 
 word group of G which evaluates to g, else false}

   if assigned G`SL2OracleData then 
      flag, w := BlackBoxElementToSLP (G, g);
   elif assigned G`SL2Basis then  
      w := MySL2ElementToWord (G, g);
   else   /* field of size 2 or 3 */
      phi := InverseWordMap (G);
      if g in G then w := g @ phi; end if; 
   end if;
   if assigned w and Type (w) eq GrpSLPElt then 
      return true, w;
   else
      return false, _;
   end if;
end intrinsic;

intrinsic SL2ElementToWord (G:: GrpPerm, g:: GrpPermElt) -> BoolElt, GrpSLPElt
{if g is element of G which has been constructively recognised to have
 central quotient isomorphic to PSL(2, q), then return true and element of 
 word group of G which evaluates to g, else false}

   if assigned G`SL2OracleData then 
      flag, w := BlackBoxElementToSLP (G, g);
   elif assigned G`SL2Basis then  
      w := MySL2ElementToWord (G, g);
   else /* field of size 2 or 3 */
      phi := InverseWordMap (G);
      if g in G then w := g @ phi; end if; 
   end if;
   if assigned w and Type (w) eq GrpSLPElt then 
      return true, w;
   else
      return false, _;
   end if;
end intrinsic;
