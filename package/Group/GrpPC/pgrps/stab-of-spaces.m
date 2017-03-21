freeze;
declare verbose Stabiliser, 1;

// Alg := "Matrix"; // find primitive element by random search of matrices
Alg := "Field"; // find primitive element of finite field using intrinsic

/* implementation of algorithms to determine Jacobson
   radical and unit group of matrix algebra;

   also much-revised implementation of algorithm of
   Schwingel to compute stabiliser in GL (d, q)
   of sequence of subspaces of GF(q)^d;

   this implementation developed by Brooksbank & O'Brien;
   last revision May 2007 */

IdentityMatrix := function (F, d)
   return Identity (MatrixAlgebra (F, d));
end function;

/* matrix blocks for composition factor which does not
   act absolutely irreducibly */
SmallOverLargerField := function (block, d, F)
   one := One (F);
   zero := Zero (F);
   root := PrimitiveElement (F);
   m1block := -1 * block;
   zblock := 0 * block;

   n := Nrows (block);
   r := d div n;
   // "n is ", n;

   id := IdentityMatrix (F, d);
   gens := [];
   mat := id;
   InsertBlock (~mat, block, 1, 1);
   Append (~gens, mat);
   if n eq 1 or n eq d then return gens; end if;

   if #F eq 2 then
      mat := id;
      InsertBlock (~mat, zblock, 1, 1);
      InsertBlock (~mat, block, 1, (r - 1) * n + 1);
      for i in [2 .. r] do
         InsertBlock (~mat, block, (i - 1) * n + 1, (i - 2) * n + 1);
         InsertBlock (~mat, zblock, (i - 1) * n + 1, (i - 1) * n + 1);
      end for;
      Append (~gens, mat);
      mat := id;
      InsertBlock (~mat, block, 1, n + 1);
      Append (~gens, mat);
   else
      mat := id;
      InsertBlock (~mat, m1block, 1, 1);
      InsertBlock (~mat, block, 1, (r - 1) * n + 1);
      for i in [2 .. r] do
         InsertBlock (~mat, m1block, (i - 1) * n + 1, (i - 2) * n + 1);
         InsertBlock (~mat, zblock, (i - 1) * n + 1, (i - 1) * n + 1);
      end for;
      Append (~gens, mat);
   end if;

   gens := SequenceToSet (gens);
   return SetToSequence (gens);
end function;

ConstructBlockGenerators := function (M)
   F := BaseRing (M);
   d := Dimension (M);
   E := EndomorphismAlgebra (M);
   assert Ngens (E) eq 1;

   if Alg eq "Field" then
      t := Cputime ();
      m :=  MinimalPolynomial (E.1);
      Q := ext <F | m>;
      h := hom <Q -> E | x :-> Evaluate(PolynomialRing(F)!Eltseq(x, F), E.1)>;
      theta := PrimitiveElement (Q);
      alpha := h(theta);
   else
      t := Cputime ();
      /* find a primitive element for E */
      ord := #E - 1;
      if Order (E.1) eq ord then
         alpha := E.1;
      else
         repeat
            alpha := Random (E);
         until Determinant (alpha) ne 0 and Order (alpha) eq ord;
      end if;
      "total time for matrix computation is ", Cputime (t);
   end if;

   /* determine basis so that alpha has identical
      blocks along its diagonal */

   J, CB, facs := PrimaryRationalForm (alpha);
   e := Degree (facs[1][1]);
   m := Dimension (M) div e;
   if m gt 1 then
      block := ExtractBlock (J, 1, 1, e, e);
   else
      block := J;
   end if;
   size := OrderGL (m, (#F)^e);
   gens := SmallOverLargerField (block, d, F);
   return [CB^-1 * g * CB : g in gens], size;
end function;

MatricesToAlgebraElement := function (M)
   if #M eq 0 then return []; end if;
   return Matrix ([Vector (m): m in M]);
end function;

VectorsToMatrix := function (N)
   if Type (N) eq ModTupFld then N := Basis (N); end if;
   return Matrix (N);
end function;

VectorsToMatrices := function (N, d)
   if Type (N) eq ModTupFld then N := Basis (N); end if;
   if #N eq 0 then return []; end if;
   return [Matrix (d, d, N[i]) : i in [1..#N]];
end function;

/* INPUT - dims = list of dimensions of blocks
         - d = dimension of matrices
   OUTPUT - init = list of integers s.t. i-th block starts at
                  position ( init[i]+1, init[i]+1 )
          - blocks = list of integers containing the positions
                    of the block entries in vector of length d^2 */
BlockInfo := function (dims, d)
   // determine positions in row vector of block entries
   b := #dims;          // number of blocks
   blocks := [];       // positions of block entries in vector
   init := [ 0 ];      // i-th block starts at position init[i]+1
   start := 0;
   for i in [1 .. b] do
      for j in [1 .. dims[i]] do
         blocks cat:= [start+1 .. start+dims[i]];
         start +:= d;
      end for;
      start +:= dims[i];
      if i gt 1 then
         init[i] := init[i-1] + dims[i-1];
      end if;
   end for;
   return <init, blocks>;
end function;

/* determine all isomorphic blocks and insert them in 'mat'

  INPUT - mat = dxd matrix containing 1 nontrivial block
        - block = the nontrivial block of 'mat' (nxn matrix)
        - n = dimension of 'block'
        - iso = list containing positions of isomorphic blocks and the
                actual isomorphisms
                [ b_1, b_2, iso_2, b_3, iso_3, ..., b_t, iso_t ]
                => M_1^iso_i = M_i
        - init = i-th block starts at position init[i]+1

  OUTPUT - matrix 'mat' containing isomorphisc blocks according to 'iso' */
procedure IsoBlocks (~mat, block, n, iso, init)
   c := #iso;
   for i in [2 .. c-1 by 2] do
      B := iso[i + 1]^1 * block * (iso[i+1]^-1);  // isomorphic block
      s := init[iso[i]];                     // block starts at position s+1
      InsertBlock (~mat, B, s + 1, s + 1);
   end for;
end procedure;

/* determines gens satisfying isomorphism conditions given by 'iso'
  and adds them to 'mats'

  INPUT - gens = list of matrices already determined
        - iso = [ b_1, b_2, iso_2, b_3, iso_3, ..., b_t, iso_t ]
                b_i-th block ( i = 2, ..., t ) is isomorphic to
                b_1-st block via isomorphism iso_i, i.e.,
                M_1^iso_i = M_i
        - init = i-th block starts at position ( init[i]+1, init[i]+1 )
        - d = dimension of matrices
        - F = field
        - n = dimension of block being dealt with
        - r = block being dealt with starts at position ( r+1, r+1 ) */
procedure IsoGenerators (~gens, iso, init, d, F, r, sub)
   id := IdentityMatrix (F, d);
   for i in [1..#sub] do
      mat := id;
      n := Nrows (sub[i]);
      InsertBlock (~mat, sub[i], r + 1, r + 1);
      // insert isomorphic blocks & append generator to 'gens'
      IsoBlocks (~mat, sub[i], n, iso, init);
      Append (~gens, mat);
   end for;
end procedure;

/* generators for GL (n, F) */
GLGenerators := function (n, F)
   if Type (F) eq RngIntElt then F := GF (F); end if;

   if #F gt 2 or n gt 1 then
      G := GL (n, F);
      return [G.i: i in [1..Ngens (G)]];
   else
      gens := [IdentityMatrix (F, n)];
   end if;
   return gens;
end function;

/* add to 'gens' generators for a subgroup of GL(n,F) in block
    starting at position ( r+1, r+1 )
   this subgroup is generated by sub;

  INPUT - gens = list of dxd generating matrices already determined
        - d = dimension of matrices
        - F = field
        - r = block starts at position ( r+1, r+1 )
        - sub = generators for subgroup  of appropriate GL block */
procedure BlockGenerators (~gens, d, F, r, sub)
   id := IdentityMatrix (F, d);
   for i in [1..#sub] do
      mat := id;
      InsertBlock (~mat, sub[i], r + 1, r + 1);
      Append (~gens, mat);
   end for;
end procedure;

/* INPUT - dims = list containing dimensions of the blocks
         - isom - isom[i] = [a] => a-th block forms single iso class
                  isom[i] = [ a, b, [iso_b], c, [iso_c], ... ]
                  => i-th block is isomorphic to a-th block and
                     isomorphism is iso_i, i.e.,
                     M_a^iso_i = M_i
         - F = field
         - d = dimension of stabilising matrices
         - init = i-th block starts at position init[i]+1
   OUTPUT - a list 'gens' of vectors which as dxd matrices are in
            block form and generate the general linear groups in
            the blocks satisfying the isomorphism conditions */
GLBlockGenerators := function (dims, isom, CF, F, d, init: Matrices := [])
   Supplied := Matrices;
   supplied := #Supplied eq 0 select false else true;

   li := #isom;
   gens := [];
   size := 1;
   for i in [1 .. li] do
      c := #isom[i];                // length of i-th isomorphism info
      n := dims[ isom[i][1] ];      // dimension of block
      r := init[ isom[i][1] ];      // block starts at position r+1
      index := isom[i][1];
      if IsAbsolutelyIrreducible (CF[index]) then
         if supplied eq false then
            sub := GLGenerators (n, F);
         else
            sub := Supplied[i];
         end if;
         size *:= OrderGL (n, #F);
      else
         sub, temp := ConstructBlockGenerators (CF[index]);
         size *:= temp;
      end if;
      if c eq 1 then
         BlockGenerators (~gens, d, F, r, sub);
      else
         IsoGenerators (~gens, isom[i], init, d, F, r, sub);
      end if;
   end for;
   return MatricesToAlgebraElement (gens), size;
end function;

/* INPUT - blockSol = list of vectors which as dxd matrices generate
                     the linear groups in the blocks satisfying
                     isomorphism conditions
        - sys = list of vectors representing the system of linear
                equations whose solution is the non-p-part (in block
                form) of the algebra normalising the lattice
        - F = field
        - d = dimension of the parent vector space

   OUTPUT - a list 'blockPart' containing dxd matrices generating
           the non p-part of the subgroup of GL(d,F) normalising
           the lattice */
BlockPartGenerators := function (blockSol, sys, blocks, F, d)
   h := d^2;
   nh := h + 1;
   z := Zero (F);
   one := One (F);
   zero := [z: i in [1..nh]];   // zero vector
   blockPart := [];

   Vnh := VectorSpace (F, nh);
   sys := Basis (sys);
   sys := [Eltseq (s) cat [0]: s in sys];

   for i in [1..Nrows (blockSol)] do
      b := blockSol[i];

      // substitute block entries of generator 'b' in the system
      newsys := sys;

      for j in blocks do
         eqn := zero;
         eqn[j] := one;
         eqn[nh] := b[j];
         Append (~newsys, eqn);
      end for;

      vprint Stabiliser: "Number of equations in newsys is ", #newsys;
      N := sub <Vnh | newsys>;
      B := BasisMatrix (N);
      c := Nrows (B);

      vprint Stabiliser: "Dimensions of newsys is ", c;

      // determine one solution for the non-homogeneous system obtained
      if c gt h then
         vprint Stabiliser: "There is no solution for equations";
         return false;
      else
         v := Vector (Transpose (ExtractBlock (B, [1..c], [nh])));
         newsys := ExtractBlock (B, 1, 1, c, h);
         flag, s := IsConsistent (Transpose (newsys), v);
         if flag eq true then
            Append (~blockPart, s);
         else
            vprint Stabiliser: "System is not consistent";
            return false;
         end if;
      end if;
   end for;

   blockPart := VectorsToMatrices (blockPart, d);

   return blockPart;
end function;

/* INPUT - solution = list of solutions for system of linear equations
                   after changing basis to block form
      - dims = list containing dimensions of blocks
      - isom = list containing isomorphism information for blocks
      - F = field
      - d = dimension of matrices and parent vector space

   OUTPUT - pPart = list of dxd invertible matrices generating the
                    p-part of the stabiliser
       - blockPart = list of dxd invertible matrices generating
                     the non-p-part of the stabiliser
       - size = order of the subgroup of GL(d,F) generated by the
                matrices in 'pPart' and 'blockPart'

   if Jacobson is true then use intrinsic Jacobson radical function,
   otherwise compute as in Brooksbank & O'Brien paper */
UnitsGenerators := function (A, solution, dims, isom, CF:
                             Matrices := [], Jacobson := false)
   d := Degree (A);
   F := BaseRing (A);
   Supplied := Matrices;

   /* get some information on the blocks
      - init = i-th block starts at row and column init[i]+1
      - blocks = list containing the positions in a vector of length d^2
              of the block entries in the corresponding dxd matrix */

   info := BlockInfo (dims, d);    //   = [ init, blocks ]
   char := Characteristic (F);

   sys := NullspaceOfTranspose (solution);

   // p-part
   if not Jacobson then
      index := info[2];
      MA := KMatrixSpace (F, #index, d^2);
      Z := Zero (MA);
      for i in [1..#index] do Z[i][index[i]] := 1; end for;
      newsys := VerticalJoin (BasisMatrix (sys), Z);
      pPart := NullspaceOfTranspose (newsys);
      pPart := [Matrix (d, d, p): p in Basis (pPart)];
   else
      // "Using inbuilt Jacobson";
      pPart := JacobsonRadical (A);
      pPart := [pPart.i : i in [1..Ngens (pPart)]];
   end if;

   if #pPart gt 0 then
      e := Degree (F); w := PrimitiveElement (F);
      W := [w^i : i in [0..e - 1]];
      pPart := &cat[[x * W[i + 1]: i in [0..e - 1]]: x in pPart];
      // go over to group elements by inserting 1's in the diagonal
      MA := MatrixAlgebra (F, d);
      id := Identity (MA);
      pPart := [MA!pPart[i] + id : i in [1..#pPart]];
   end if;

   size := char^#pPart;

   // determine non-p-part generators as group elements
   blockSol, temp := GLBlockGenerators (dims, isom, CF, F, d, info[1]:
                                        Matrices := Supplied);
   blockPart := BlockPartGenerators (blockSol, sys, info[2], F, d);
   if Type (blockPart) eq BoolElt then
      return false, _, _;
   elif blockPart cmpeq [] then
      temp := 1;
   end if;
   size *:= temp;

   // remove trivial generators
   pPart := [m : m in pPart | IsIdentity (m) eq false];
   blockPart := [m : m in blockPart | IsIdentity (m) eq false];

   // check trivial case
   if pPart eq [] and blockPart eq [] then
      blockPart := [IdentityMatrix (F, d)];
   end if;

   return pPart, blockPart, size;
end function;

/* system of linear equations specified by spaces U, namely U * X = U */
EquationsForStabiliser := function (U)
   P := Parent (U);
   d := Ncols (P.1);

   F := BaseRing (P);
   zero := Zero (F);
   zeroeqn := [zero : i in [1..d^2]];

   dimU := Nrows (U);
   heads := [Depth (U[i]): i in [1..dimU]];

   sys := [];
   for i in [1..dimU] do

      // determine equations for U[i] * X = (y_1, ..., y_d ) in U
      for col in [1..d] do
         eqn := zeroeqn;

         // equation for y_col = U[1][col]*y_heads[1] + ...
         //                           + U[dimU][col]*y_heads[dimU]
         for row in [1 .. dimU] do
            for c in [1 .. d] do
               eqn[(c - 1) * d + heads[row]] := U[row][col] * U[i][c];
            end for;
         end for;
         for c in [1 .. d] do
            eqn[(c - 1) * d + col] -:= U[i][c];
         end for;
         if eqn ne zeroeqn then Append (~sys, eqn); end if;
      end for;
   end for;

   return sys;
end function;

/* construct algebra specified by spaces */
SpacesAlgebra := function (Spaces)
   P := Rep (Spaces);
   d := Degree (P);
   F := BaseRing (P);
   U := [* BasisMatrix (s): s in Spaces *];
   X := &cat[EquationsForStabiliser (u): u in U];
   KA := KMatrixSpace (F, #X, d^2);
   T := KA!&cat (X);
   N := NullspaceOfTranspose (T);
   MA := MatrixAlgebra (F, d);
   return sub <MA | VectorsToMatrices (N, d)>;
end function;

/* determine isomorphisms among modules */
DetermineIsomorphisms := function (S)
   assert #S gt 0;

   Different := [S[1]];
   Combined := [ [*1*] ];

   for i in [2..#S] do
      j := 0; new := true;
      repeat
         j +:= 1;
         flag, map := (IsIsomorphic (S[i], Different[j]));
         new := flag eq false;
      until (new eq false) or (j ge #Different);
      if new then
         Append (~Different, S[i]);
         Append (~Combined, [* i *]);
      else
         Append (~Combined[j], i);
         Append (~Combined[j], map);
      end if;
   end for;

   return Combined;
end function;

/* CF are composition factors for module;
   is there a (necessarily 1-dimensional) composition factor where
   action matrices are all simultaneously 0?
   if so, the algebra has no invertible elements */
HasNoUnits := function (CF)
   for i in [1..#CF] do
      if Dimension (CF[i]) eq 1 then
         A := ActionGenerators (CF[i]);
         if Set (A) eq {0} then return true; end if;
      end if;
   end for;
   return false;
end function;

MyUnitGroup := function (A : Jacobson := false)
   M := RModule (A);

   CS, CF, CB := CompositionSeries (M);

   /* criterion for absence of units */
   nounits := HasNoUnits (CF);
   if nounits then return false, _, _, _; end if;

   dims := [Dimension (CF[i]): i in [1..#CF]];
   isom := DetermineIsomorphisms (CF);
   vprint Stabiliser: "Distinct isomorphism types are ", isom;
   vprint Stabiliser: "Dimensions of these are ", dims;

   J := CB^-1;
   gens := Basis (A);
   solution := [CB * b * J : b in gens];
   solution := Matrix ([Vector (s): s in solution]);

   if exists {x : x in CF | IsAbsolutelyIrreducible (x) eq false} then
      vprint Stabiliser: "Not absolutely irreducible";
   end if;

   pPart, blockPart, order := UnitsGenerators (A, solution, dims, isom, CF:
                                               Jacobson := Jacobson);
   if Type (pPart) eq BoolElt then
      error "Problem: algebra has no units";
      return false, _, _, _;
   end if;

   vprint Stabiliser: "Order of stabiliser of sequence is ", order;

   d := Degree (A);
   F := BaseRing (A);
   if Jacobson then
      P := [GL(d, F) ! p : p in pPart];
   else
      P := [GL(d, F) ! (J * b * CB) : b in pPart];
   end if;
   B := [GL(d, F) ! (J * b * CB) : b in blockPart];

   return B, P, order;
end function;

intrinsic UnitGroup (A:: AlgMat) -> BoolElt, GrpMat, RngIntElt
{If matrix algebra defined over a finite field has invertible matrices,
then return true, the group of such matrices and its order, else return false}

   d := Degree (A);
   F := BaseRing (A);
   require IsFinite (F): "Base field for algebra must be finite";

   B, P, order := MyUnitGroup (A);
   if Type (B) eq BoolElt then return false, _, _; end if;
   G := sub<GL(d, F) | B, P>;
//   G`Order := order;
   return true, G, order;

end intrinsic;

/* construct the stabiliser in GL(d, p) for a sequence of subspaces */

MyStabiliserOfSpaces := function (Spaces: Verify := false,
            Jacobson := true,  Matrices := [], Previous := [])
   if #Spaces eq 0 then return [], [], _; end if;

   Supplied := Matrices; Input := Previous;

   P := Rep (Spaces);
   d := Degree (P);
   F := BaseRing (P);

   Spaces := {x : x in Spaces | Dimension (x) in [1..d - 1]};

   if #Spaces eq 0 then
      S := GL (d, F);
      return [S.i : i in [1..Ngens (S)]], [], OrderGL (d, #F);
   end if;

   A := SpacesAlgebra (Spaces);

   if #Input eq 0 then
      M := RModule (A);
      CS, CF, CB := CompositionSeries (M);
      dims := [Dimension (CF[i]): i in [1..#CF]];
      isom := DetermineIsomorphisms (CF);
      vprint Stabiliser: "Distinct isomorphism types are ", isom;
      vprint Stabiliser: "Dimensions of these are ", dims;
   else
      CF := Input[1]; CB := Input[2]; dims := Input[3]; isom := Input[4];
   end if;

   cb := CB^-1;
   gens := Generators (A);
   solution := [CB * b * cb : b in gens];
   solution := Matrix ([Vector (s): s in solution]);

   if exists {x : x in CF | IsAbsolutelyIrreducible (x) eq false} then
      vprint Stabiliser: "Not Absolutely irreducible";
   end if;

   pPart, blockPart, order :=
      UnitsGenerators (A, solution, dims, isom, CF:
          Matrices := Supplied, Jacobson := Jacobson);
   vprint Stabiliser: "Order of stabiliser of sequence is ", order;

   if Jacobson then
      P := [GL(d, F) ! p : p in pPart];
   else
      P := [GL(d, F) ! (cb * b * CB) : b in pPart];
   end if;

   B := [GL(d, F) ! (cb * b * CB) : b in blockPart];

   if Verify then
      G := GL(d, F);
      stab := sub <G | B cat P>;
      vprint Stabiliser: "Computed stabiliser has order ", #stab;
      Spaces := SetToSequence (Spaces);
      S := Stabiliser (G, Spaces[1]);
      for i in [2..#Spaces] do
         S := Stabiliser (S, Spaces[i]);
      end for;
      #S;
      assert #S eq #stab;
   end if;

   return B, P, order;
end function;

intrinsic StabiliserOfSpaces (Spaces:: SeqEnum) -> GrpMat, SeqEnum
{Subgroup of GL(d, q) which fixes sequence of subspaces of natural vector
 space; also return generators for largest unipotent subgroup of stabiliser}

   require #Spaces gt 0: "Sequence must be non-empty";
   P := Rep (Spaces);
   d := Degree (P);
   F := BaseRing (P);
   require IsFinite (F): "Base field for spaces must be finite";
   B, P, order := MyStabiliserOfSpaces (Spaces);
   H := sub <GL(d, F) | B, P>;
   H`Order := order;
   return H, P;

end intrinsic;

intrinsic JacobsonRadicalOverFiniteField (A:: AlgMat) -> AlgMat
{Jacobson radical for matrix algebra defined over finite
 field, using algorithm of Brooksbank and O'Brien}

   d := Degree (A);
   F := BaseRing (A);
   require IsFinite (F): "Base field for algebra must be finite";
   PA := MatrixAlgebra (F, d);

   function return_ideal(L)
      // return sub<PA | L>;
      return ideal<A | L>;
   end function;

   /* if number of generators is 1, then nilpotent part
      of generator generators Jacobson radical */
   if Ngens (A) eq 1 then
      s, n := JordanDecomposition (A.1);
      return return_ideal(n);
   end if;

   if Dimension (A) in [0, d^2] then return return_ideal([]); end if;
   gens := Basis (A);

   M := RModule (A);
   CS, CF, CB := CompositionSeries (M);
   cb := CB^-1;

   dims := [Dimension (CF[i]): i in [1..#CF]];

   solution := [CB * b * cb : b in gens];
   solution := Matrix ([Vector (s): s in solution]);
   info := BlockInfo (dims, d);
   sys := NullspaceOfTranspose (solution);

   index := info[2];
   MA := KMatrixSpace (F, #index, d^2);
   Z := Zero (MA);
   for i in [1..#index] do Z[i][index[i]] := 1; end for;

   newsys := VerticalJoin (BasisMatrix (sys), Z);
   P := NullspaceOfTranspose (newsys);
   P := [Matrix (d, d, p): p in Basis (P)];
   P := [cb * b * CB : b in P];

   return return_ideal(P);

end intrinsic;
