freeze;

//$Id:: forms.m 1605 2008-12-15 09:05:48Z jbaa004                          $:

// Convert quadratic form to an upper triangular matrix
function NormaliseQuadForm(form)
    n := NumberOfRows(form);
    assert NumberOfColumns(form) eq n;
    newForm := ZeroMatrix(CoefficientRing(form), n, n);
    
    for i in [1 .. n] do
	for j in [i .. n] do
	    if not i eq j then
		newForm[i][j] := form[i][j] + form[j][i];
	    else
		newForm[i][j] := form[i][j];
	    end if;
	end for;
    end for;
    
    return newForm;
end function;

MyTransformForm := function (form, d, q, type)
   return TransformForm (form, type: field := GF (q));
end function;

Mbar := function (mat, p, e)
  assert Characteristic(CoefficientRing(mat)) eq p;
   return FrobeniusImage(mat, e);
end function;

Vbar := function (vec, p, e)
  assert Characteristic(CoefficientRing(vec)) eq p;
   return FrobeniusImage(vec, e);
end function;

/*
<basis> spans V, <sbasis> spans subspace W, <form> is a bilinear form;
return basis for the orthogonal complement of W in V
*/
OrthogonalComplement := function (basis, sbasis, form, bt)
   F := BaseRing (Parent (form));
   p := Characteristic (F);
   e := Degree (F) div 2;
   mat := [];
   if Type (basis) eq ModTupFld then basis := Basis (basis); end if;
   if Type (sbasis) eq ModTupFld then sbasis := Basis (sbasis); end if;
   for v in basis do
      a := [];
      for w in sbasis do
         if (bt eq 1) then
            Append (~a, InnerProduct (v * form, w));
         else
            Append (~a, InnerProduct (v * form, Vbar (w, p, e)));
         end if;
      end for;
      Append (~mat, a);
   end for; 
   mat := RMatrixSpace (F, #mat, #mat[1])!&cat (mat);
   N := Nullspace (mat);
   B := [Eltseq (b): b in Basis (N)];
   return [&+[b[i] * basis[i]: i in [1..#b]]: b in B];
end function;

/* 
<form> is a bilinear form, <bas> is the basis of a subspace;
return restriction of <form> to subspace relative to basis
*/
RestrictForm := function (form, bas, bt) 
   d := #bas;
   F := BaseRing (form);
   k := Degree (F);
   if (bt eq -1) and (k mod 2 eq 1) then
      error "Odd degree extension not possible for unitary form";
   end if;
   p := Characteristic (F);
   res := MatrixAlgebra (F, d)!0;
   for i in [1..d] do
      for j in [1..d] do
         if (bt eq 1) then
            res[i][j] := InnerProduct (bas[i] * form, bas[j]);
         else
            res[i][j] := InnerProduct (bas[i] * form, Vbar (bas[j], p, k div 2));
         end if;
      end for;
   end for;
return res;
end function;

/* 
<form> is a symmetric matrix;
return type of orthogonal space corresponding to <form>
*/
IdentifyOrthogonalType := function (form)
   d := Nrows (form);
   F := BaseRing (Parent (form));
   q := #F;
   if (d mod 2 eq 1) then
      C := TransformForm (form, "orthogonalcircle");
      return 0, C;
   end if;
   type := SymmetricBilinearFormType (form);
   C := TransformForm (form, type);
   if type eq "orthogonalplus" then
      return 1, C;
   else
      return -1, C;
   end if;
end function;

/*
Input bilinear form <M> (possibly degenerate)
Output the group preserving <M>
*/
GroupPreservingForm := function (M, bt: Simple := true) 
   F := BaseRing (M);
   l := Degree (F);
   p := Characteristic (F);
   r := Rank (M);
   n := Nrows (M);
   if Rank (M) eq 0 then return GL (n, F); end if;
   MA := MatrixAlgebra (F, n);
   V := VectorSpace (F, n);
   Vbas := Basis (V);
   R := Nullspace (M);
   Rbas := Basis (R);
   C := Complement (V, R);
   Cbas := Basis (C);
   conj1 := Matrix (Cbas cat Rbas);
   M1 := conj1 * M * Transpose (conj1);
   M1nd := ExtractBlock (M1, 1, 1, r, r);

   // determine the type of <M1nd>
   if (bt eq -1) then
      if (l mod 2 eq 1) then
         error "odd degree extension not possible for unitary form";
      end if;
      e := l div 2;
      if Mbar (M1nd, p, e) ne Transpose (M1nd) then
         error "not an hermitian form";
      end if;
      type := "unitary";
      U := GU (r, F);
   else
      if (M1nd eq -Transpose (M1nd)) then
         type := "symplectic";
         U := Sp (r, F);
      elif (M1nd eq Transpose (M1nd)) then
	 if (r eq 1) then
            U := sub < GL (1, F) | -Identity (GL (1, F)) >;
         else
            sgn := IdentifyOrthogonalType (M1nd);
            if (sgn eq 0) then
               type := "orthogonal";
               if Simple eq true then 
               U := Omega (r, F);
               else 
               U := GO (r, F);
               end if;
            elif (sgn eq 1) then
               type := "orthogonalplus";
               U := GOPlus (r, F);
            elif (sgn eq -1) then
               type := "orthogonalminus";
               U := GOMinus (r, F);
            else
               error "neither an orthogonal nor symplectic form";
            end if;
         end if;
      end if;
   end if;

   if (r gt 1) then
      conj2 := TransformForm (M1nd, type);
      conj2 := GL (r, F)!conj2;
      clgens := Generators (U^(conj2^-1));
   else
      clgens := Generators (U);
   end if;
   if (r eq n) then
      gens := clgens;
   else
      glgens := Generators (GL (n-r, F));
      gens := [];
      for x in clgens do
         X := Identity (MA);
         InsertBlock (~X, x, 1, 1);
         Append (~gens, X);
      end for;
      for x in glgens do
         X := Identity (MA);
         InsertBlock (~X, x, r+1, r+1);
         Append (~gens, X);
      end for;
      X := Identity (MA);
      X[1][r+1] := 1;
      Append (~gens, X);
   end if;
   gp := sub < GL (n, F) | [ conj1^-1 * X * conj1 : X in gens ] >;
   return gp;
end function;

function SubPerp(V, U :
    InnerProd := func<x, y | (x, y)>)
    /* Return orthogonal complement of U in V w.r.t. to InnerProd, which should
    be a function taking two arguments of type ModTupFldElt and returning an
    element of CoefficientRing(V).

    By default, the inner product of V is used. */
    local field, F, elt_perp, sub_perp;
    
    field := CoefficientRing(V);
    F := VectorSpace(field, 1);
    
    elt_perp := func<v | hom<V -> F | [<x, elt<F | InnerProd(x, v)>> :
    x in Basis(V)]>>;
    sub_perp := func<W | &meet[Kernel(elt_perp(W.i)) :
    i in [1 .. Dimension(W)]]>;

    return sub_perp(U);
end function;
