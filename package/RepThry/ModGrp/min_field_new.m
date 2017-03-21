freeze;

declare verbose SmallerField, 1;

forward MainSmallerField, ScalarList; 

QualityLimit := 5;

/* construct random F-linear combination of group algebra M;
   P is group or random process for the group */

AlgebraRandomElement := function (AA, F, P: Length := 4)
   RanElt := function (F);
      repeat x := Random (F); until x ne 0;
      return x;
   end function;
   B := [AA ! Random (P): i in [1..Length]];
   L := [RanElt (F): i in [1..#B]];
   return &+[L[i] * B[i]: i in [1..#B]];
end function;

Spin := function (G, v)

/* construct a linearly independent basis consisting of 
   images of v under G; this is the so-called Spin algorithm */ 

   return SpinOrbit (v, [G.i: i in [1..Ngens (G)]]);
 
end function;

InSmallerField := function (gens, F)
   return forall{g : g in gens | forall{x : x in Eltseq (g) | x in F}};
end function;

/* decide if G can be written over F = GF (p^d) */

LowerFieldTest := function(M, d : NumberRandom := 20) 

   vprint SmallerField: "Test SmallerField for degree ", d;
   K := BaseRing (M);
   n := Dimension(M);

   p := Characteristic (K);
   F := GF (p, d);

   MA := MatrixAlgebra (K, n);
   G := Group(M);
   AG := ActionGroup(M);
   P := RandomProcess (AG: Scramble := QualityLimit);
   SF := PolynomialRing (F);
   nmr := 0; 
   repeat 
      x := AlgebraRandomElement (MA, F, P: Length := 4 + 2 * nmr);
      cp := CharacteristicPolynomial (x);
      coeffs := Coefficients (cp);
      if forall {x : x in coeffs | x in F} then
         facs := Factorisation (SF!cp);
         degs := [<Degree (f[1]), f[2]>: f in facs];
         nmr +:= 1;
         found := <1,1> in degs; 
      else
         vprint SmallerField: "Coefficients of characteristic polynomial not over smaller field";
         return false, _; 
      end if;
   until found or nmr gt NumberRandom;

   if not found then 
      error "Should find an element with eigenspace of dimension 1"; 
   end if;

   vprint SmallerField: "Number of tries to find element with eigenspace of rank 1 = ", nmr;
   // vprint SmallerField: "Time to get good random element is ", Cputime (t);

   pos := Position (degs, <1,1>);
   fac := facs[pos];
   R := Roots (fac[1]);
   r := R[1][1];
   E := Eigenspace (x, r);
   vprint SmallerField: "Now spin eigenspace to construct basis";
   S := Spin (AG, E.1);
   S;
   A := MA!&cat[Eltseq (s): s in S];
   Am1 := A^-1;
   Q := ActionGenerators(M);
   gens := [A * Q[i] * Am1: i in [1..#Q] ];
   if InSmallerField (gens, F) then
      N := GModule(G, gens);
      return true, N;
   else
      return false, _;
   end if;
end function;

/* can G be written (modulo Scalars) over one of the subfields whose
   degree is listed in divse? if so, rewrite G */

procedure ProcessSubfields (~G, ~divse: Scalars := true)

   if divse eq {} then return; end if;

   repeat 
      d := Maximum (divse);
      if Scalars then 
         flag, tmp := ModScalarsTest (G, d);
      else 
         flag, tmp := LowerFieldTest (G, d);
      end if;
      if flag eq false then 
         divse diff:= Set (Divisors (d));
      else 
         G := tmp;
         divse := divse meet Set (Exclude (Divisors (d), d));
         $$ (~G, ~divse: Scalars := Scalars); 
         return;
      end if;
   until #divse eq 0;
         
end procedure;

MainSmallerField := function (G, divse: Scalars := true)
   K := BaseRing (G);
   H := G;
   ProcessSubfields (~H, ~divse: Scalars := Scalars);
   F := BaseRing (H);
   if #F ne #K then 
      G`SmallerField := BaseRing (H); 
      G`SmallerFieldChangeOfBasis := H`SmallerFieldChangeOfBasis;  
      return true, H;
   end if;
   if assigned G`SmallerFieldChangeOfBasis then
      delete G`SmallerFieldChangeOfBasis;
   end if;
   return false, _;
end function;

intrinsic IsOverSmallerField (G::GrpMat: Scalars := false) -> BoolElt, GrpMat 
{Does G have an equivalent representation (modulo scalars if Scalars is true) 
 over a subfield? If so, return true and equivalent representation.} 
/* 
   if Type (SmallerField (G)) eq FldFin then 
      return true, SmallerFieldImage (G); 
   end if;
*/
//   require IsAbsolutelyIrreducible (G): "Group must be absolutely irreducible";
   K := BaseRing (G);
   e := Degree (K);
   n := Degree (G);
   divse := Set (Exclude (Divisors (e), e));
   G`SmallerFieldChangeOfBasis := Identity (GL (n, K));  
   return MainSmallerField (G, divse: Scalars := Scalars);

end intrinsic;

intrinsic IsOverSmallerField (G :: GrpMat, k :: RngIntElt : 
                              Scalars := false) -> BoolElt, GrpMat 
{Does G have an equivalent representation (modulo scalars if Scalars 
 is true) over a subfield of degree k?  
 If so, return true and equivalent representation.} 

/* 
   F := SmallerField (G)); 
   if Type (F) eq FldFin and #F eq Characteristic (F)^k then 
      return true, SmallerFieldImage (G); 
   end if;
*/

   K := BaseRing (G);
   e := Degree (K);
   if not k in [1..e - 1] or e mod k ne 0 then return false, _; end if;

// require IsAbsolutelyIrreducible (G): "Group must be absolutely irreducible";
   n := Degree (G);
   G`SmallerFieldChangeOfBasis := Identity (GL (n, K));  
   return MainSmallerField (G, {k}: Scalars := Scalars);

end intrinsic;

intrinsic SmallerFieldBasis (G::GrpMat) -> GrpMatElt 
{Return change of basis matrix for G so that G (possibly mod scalars)
 can be written over a smaller field}

   if assigned G`SmallerFieldChangeOfBasis then 
      return G`SmallerFieldChangeOfBasis;
   else 
      return "unknown";
   end if; 
end intrinsic;

intrinsic SmallerField (G::GrpMat) -> FldFin  
{Return smaller field over which G (possibly mod scalars) can be written} 
   if assigned G`SmallerField then 
      return G`SmallerField;
   else 
      return "unknown";
   end if;
end intrinsic;

intrinsic SmallerFieldImage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt 
{G can be rewritten (possibly mod scalars) over smaller field;
 return image of g in group defined over smaller field} 

   CB := SmallerFieldBasis (G);
   if Type (CB) ne GrpMatElt then 
      error "No smaller field change of basis known"; 
   end if;
   F := SmallerField (G);
   d := Degree (G);
   K := BaseRing (G);
   CB := GL (d, K) ! Eltseq (CB);
   g := g^CB;
   E := Eltseq (g);
   v := VectorSpace (K, d^2) ! E;
   depth := Depth (v);
   if depth eq 0 then error "Matrix is zero"; end if;
   alpha := v[depth];
   S := ScalarMatrix (d, alpha^-1);
   // assert IsScalar (g * GL(d, K) ! h^-1);
   return GL(d, F) ! (g * S), alpha; 
end intrinsic;
