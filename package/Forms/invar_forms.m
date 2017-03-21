freeze;
/*****************************************************
  Intrinsics to find the spaces of 
  
  1) symmetric and alternating bilinear forms
  2) sesquilinear forms 
  3) quadratic forms
  
  which are invariant or semi-invariant under the action of
  a finite group G acting on a G-module over a finite field.

  November 2012 Don Taylor

  $Id: invar_forms.m 45908 2014-01-21 06:20:02Z don $

  Intrinsics defined in this file:
  
    InvariantBilinearForms
    InvariantFormBases
    InvariantQuadraticForms
    InvariantSesquilinearForms
    SemiInvariantBilinearForms
    SemiInvariantQuadraticForms
    SemiInvariantSesquilinearForms
    SemilinearDual
    TwistedDual
    TwistedSemilinearDual
*/

declare verbose Forms, 3;

/*****************************************************
   Dual modules
   ------------
   
   Dual(M), the "usual" dual of a G-module (obtained by acting by the
   inverse transpose of each generator of G) is defined in the C kernel.
*/

intrinsic SemilinearDual( M :: ModGrp, mu::Map ) -> ModGrp
{ The semilinear dual of the G-module M with respect to the 
  field automorphism mu }
  G := Group(M);
  return GModule(sub< Generic(G) | 
     [ ConjugateTranspose(G.i^-1,mu) : i in [1..Ngens(G)] ] >);
end intrinsic;

intrinsic TwistedDual( M :: ModGrp, lambda::Map ) -> ModGrp
{ The twisted dual of the G-module M with respect to the linear character lambda }
  G := Group(M);
  return GModule(sub< Generic(G) | 
     [ ScalarMatrix(Dimension(M),lambda(G.i))*Transpose(G.i^-1) : i in [1..Ngens(G)] ] >);
end intrinsic;

intrinsic TwistedSemilinearDual( M :: ModGrp, lambda::Map, mu::Map ) -> ModGrp
{ The twisted semilinear dual of the G-module M with respect to the 
  linear character lambda and the field automorphism mu}
  G := Group(M);
  return GModule(sub< Generic(G) | 
     [ ScalarMatrix(Dimension(M),lambda(G.i))*ConjugateTranspose(G.i^-1,mu) : i in [1..Ngens(G)] ] >);
end intrinsic;


/*****************************************************
   Absolutely invariant forms
   --------------------------
   
   The function sym_space is used only when the characteristic
   of the field is 2.  The return value is a basis for the
   space of alternating (or symmetric, if full is true) matrices.
*/
sym_space := function(F,L,n : full := false)
  S := [L|];
  for i := 1 to n do
    for j := i+1 to n do
      mat := ZeroMatrix(F,n,n);
      mat[i,j] := 1; mat[j,i] := 1;
      Append(~S,mat);
    end for;
    if full then
      mat := ZeroMatrix(F,n,n);
      mat[i,i] := 1;
      Append(~S,mat);
    end if;
  end for;
  return sub<L|S>;
end function;

sym_alt := function(E,F,n)
  L := KMatrixSpace(F,n,n);
  B := Basis(E);
  if Characteristic(F) eq 2 then
    sym := Basis(sym_space(F,L,n : full) meet sub< L | B >);
    alt := Basis(sym_space(F,L,n) meet sub< L | B >);
  else
    S := sub< E | { bb + Transpose(bb) : b in B | true where bb is L!b } >;
    A := sub< E | { bb - Transpose(bb) : b in B | true where bb is L!b } >;
    sym := Basis(S);
    alt := Basis(A);
  end if;
  MA := MatrixAlgebra(F,n);
  ChangeUniverse(~sym,MA);
  ChangeUniverse(~alt,MA);

  return sym, alt;
end function;

intrinsic InvariantBilinearForms( G::GrpMat ) -> SeqEnum[AlgMatElt], SeqEnum[AlgMatElt]
{ Bases for the symmetric and alternating forms preserved by the matrix group G }
  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  n := Degree(G);
  M := GModule(G);
  E := AHom(M,Dual(M));
  if Dimension(E) gt 0 then
    sym, alt := sym_alt(E,F,n);
  else
    sym := [MatrixAlgebra(F,n)|];
    alt := sym;
  end if;
  return sym, alt;
end intrinsic;


expand := func< E,F,L,mat | L!&cat[ Eltseq(a,E) : a in Eltseq(mat)] >;

herm_space := function(E,F,n)   // used only when the characteristic of F is 2
  L := KMatrixSpace(E,n,2*n);
  xi := PrimitiveElement(F);
  q := #E;
  S := [L|];
  for i := 1 to n do
    mat := ZeroMatrix(F,n,n);
    mat[i,i] := 1;
    Append(~S,expand(E,F,L,mat));
    for j := i+1 to n do
      mat := ZeroMatrix(F,n,n);
      mat[i,j] := 1; mat[j,i] := 1;
      Append(~S,expand(E,F,L,mat));
      mat := ZeroMatrix(F,n,n);
      mat[i,j] := xi; mat[j,i] := xi^q;
      Append(~S,expand(E,F,L,mat));
    end for;
  end for;
  return sub<L|S>;
end function;

// There is an intrinsic InvariantHermitianForms(G::GrpMat) in
// Lattice/Lat/iterate.m but in that case G must be defined over
// an imaginary quadratic field.
intrinsic InvariantSesquilinearForms( G::GrpMat ) -> SeqEnum[AlgMatElt]
{ A basis for the space of hermitian forms preserved by the matrix group G }
  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  flag, q := IsSquare(#F);
  require flag : "the field order must be a square";
  F0 := GF(q);
  n := Degree(G);
  MA := MatrixAlgebra(F,n);

  contract := func< mat | MA![F![a[i],a[i+1]] : i in [1..2*n*n by 2]]
    where a is Eltseq(mat) >;

  M := GModule(G);
  mu := hom< F -> F | x :-> x^q >;
  D := SemilinearDual( M, mu );
  E := AHom(M, D);
  if Dimension(E) gt 0 then
    B := Basis(E);
    Q := KMatrixSpace(F0,n,2*n);
    if Characteristic(F) eq 2 then
      U := herm_space(F0,F,n) meet sub< Q | [ expand(F0,F,Q,b) : b in B] >;
    else
      xi := PrimitiveElement(F);
      W := [ b + ConjugateTranspose(b,mu) : b in B ] cat 
           [ (xi - mu(xi))*(b - ConjugateTranspose(b,mu)) : b in B ];
      U := sub< Q | [ expand(F0,F,Q,b) : b in W] >;
    end if;
    herm := [contract(u) : u in Basis(U)];
  else
    herm := [MA|];
  end if;
  return herm;
end intrinsic;

// The following function assumes the characteristic *is not* 2
symToQuad := function(B)
  Q := B;
  for i := 1 to Nrows(B) do
    Q[i,i] := B[i,i]/2;
    for j := 1 to i-1 do
      Q[i,j] := 0;
    end for;
  end for;
  return Q;
end function;

// The following function assumes the characteristic *is* 2
quad_from_alt := function(alt,F,n,G,scalars)
  quad := [MatrixAlgebra(F,n)|];
  for J in alt do
    gen_seq := [];
    rho := [];
    // construct the form with 0 diagonal which polarises to J
    Q0 := UpperTriangularMatrix([J[i,j] : j in [i..n], i in [1..n]]);
//      assert forall{ i : i in [1..n] | Q0[i,i] eq 0 };
    for k := 1 to Ngens(G) do
      A := G.k;
      Q := A*Q0*Transpose(A);
      Append(~rho,Matrix(F,1,n,[Q[i,i] : i in [1..n]]));
      a := (Type(scalars) eq SeqEnum) select scalars[k] else scalars;
      A2 := Matrix(F,n,n,[x^2 : x in Eltseq(A)])+ScalarMatrix(F,n,a);
      Append(~gen_seq, Transpose(A2));
    end for;
    V := VectorSpace(F,#rho * n);
    big_vec := V!HorizontalJoin(rho);
    big_mat := HorizontalJoin(gen_seq);
    flag, v, K := IsConsistent(big_mat,big_vec);
    if flag then
      for i := 1 to n do Q0[i,i] := v[i]; end for;
      Append(~quad,Q0);
      // the set of quadratic forms which polarise to J is an affine space
      if Dimension(K) gt 0 then
        for b in Basis(K) do
          Q1 := Q0;
          for i := 1 to n do Q1[i,i] := v[i]+b[i]; end for;
          Append(~quad,Q1);
        end for;
      end if;
    end if;
  end for;
  return quad;
end function;

intrinsic InvariantQuadraticForms( G::GrpMat ) -> SeqEnum[AlgMatElt]
{ A basis for the space of quadratic forms preserved by the matrix group G }
  
  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  n := Degree(G);
  sym, alt := InvariantBilinearForms(G);
  return (Characteristic(F) eq 2) 
    select quad_from_alt(alt,F,n,G,F!1)
      else [MatrixAlgebra(F,n)| symToQuad(form) : form in sym];
end intrinsic;


intrinsic InvariantFormBases( G::GrpMat ) -> SeqEnum[AlgMatElt], SeqEnum[AlgMatElt], SeqEnum[AlgMatElt], SeqEnum[AlgMatElt]
{ Bases for the spaces of symmetric, alternating, hermitian and quadratic
  forms preserved by the matrix group G }
  sym, alt := InvariantBilinearForms(G);
  herm := InvariantSesquilinearForms(G);
  quad := InvariantQuadraticForms(G);
  return sym, alt, herm, quad;
end intrinsic;

/*****************************************************
   Semi-invariant forms
   --------------------
   
   If G is a matrix group defined over a field F, then for each 
   homomorphism lambda : G -> F*, the semi-invariant symmetric and
   alternating forms are defined by matrices J such that
   g*J*Transpose(g) eq lambda(g)*J.
   
   If F is a field of order q^2 and if mu(x) = x^q, the semi-invariant
   hermitian forms are defined by hermitian matrices J such that
   g*J*mu(Transpose(g)) eq lambda(g)*J.
   
   There is some overlap with the preceding intrinsics because the forms
   associated with the trivial homomorphism are absolutely invariant.
*/

// If G is a matrix group and F is a field, find all homomorphisms
// from G to the multiplicative group of F.
F_homs := function( G, F )
  A, f := quo< G | DerivedGroup(G) >;
  B, g := AbelianGroup(A);
  L, h := AbelianGroup(GL(1,F));
  return [ hom< G -> F | x :-> (x@f@g@theta@@h)[1][1] > : theta in Homomorphisms(B,L) ];
end function;

/*
  The following function is a minor modification of the function with the
  same name in Group/GrpMat/Forms/form.m.  In this version the function 
  succeeds if the derived group is irreducible but not necessarily absolutely 
  irreducible.  It should only be called if G is known to be absolutely 
  irreducible.
*/
ApproximateDerivedGroup := function(G : NUM_TRIES := 20)
  P := RandomProcess(G : Scramble:=Max(50,Ngens(G)) );

  H := sub< G | (Random(P),Random(P)), (Random(P),Random(P)), (Random(P),Random(P)) : Check := false>;
  oldl := Dimension(G);
  tries := 0;
  vprint Forms, 2 : "Looking for approximate derived group";
  repeat
    l := #CompositionSeries(GModule(H));
    if l eq 1 and IsAbsolutelyIrreducible(H) then return true, H; end if;
    if l lt oldl then
      oldl := l;
      tries := 0;
    end if;
    H := sub< G | H, (Random(P),Random(P)) : Check := false>;
    tries +:= 1;
  until tries ge Max(NUM_TRIES,Ngens(G));
  vprint Forms, 2 : tries, "tries";

  if IsIrreducible(H) then return true, H; end if;
  vprint Forms, 2 : "Approximate derived group not found";
  return false, _;

end function;


// The following function returns *true* if it fails to find a unique 
// invariant bilinear form for the derived group of G.
quickCheck := function(G)
  vprint Forms, 2 : "In quickCheck";
  found, H := ApproximateDerivedGroup(G);
  if found then
    sym, alt := InvariantBilinearForms(H);
    F := BaseRing(G);
    if #sym + #alt eq 0 then 
      return false, [car<Parent([F|]),Parent(sym),Parent(alt)>|]; 
    end if;
    if Characteristic(F) eq 2 then
      if #sym ne 1 or #alt ne 1 then return true, _; end if;
    else
      if #sym + #alt ne 1 then return true, _ ; end if;
    end if;
    vprint Forms, 2 : "Computing the scalar multipliers";
    J := (#sym eq 1) select sym[1] else alt[1];
    n := Nrows(J);
    scalars := [F|];
    for i := 1 to Ngens(G) do
      A := G.i;
      JA := A*J*Transpose(A);
      // make sure that JA is a scalar multiple of J; this will always
      // be the case if H is normal in G but may fail in general.
      assert exists(j,k){ <j,k> : j,k in [1..n] | JA[j,k] ne 0 };
      if J[j,k] eq 0 then return true, _; end if;
      mult := JA[j,k]/J[j,k];
      if JA ne mult*J then return true, _; end if;
      Append(~scalars,mult);
    end for;
    return false, [<scalars,sym,alt>];
  end if;
  return true, _;

end function;

// The following function returns *true* if it fails to find a unique 
// invariant sesquilinear form for the derived group of G.
quickCheckHerm := function(G,F0,mu)
  vprint Forms, 2 : "In quickCheckHerm";
  found, H := ApproximateDerivedGroup(G);
  if found then
    herm := InvariantSesquilinearForms(H);
    vprint Forms, 2 : #herm, "invariant forms for the approximate derived group";
    if #herm eq 0 then return false, [car<Parent([F0|]),Parent(herm)>|]; end if;
    if #herm ne 1 then return true, _; end if;
    vprint Forms, 2 : "Computing the scalar multipliers";
    J := herm[1];
    n := Nrows(J);
    scalars := [F0|];
    for i := 1 to Ngens(G) do
      A := G.i;
      JA := A*J*ConjugateTranspose(A,mu);
      assert exists(j,k){ <j,k> : j,k in [1..n] | JA[j,k] ne 0 };
      if J[j,k] eq 0 then return true, _; end if;
      mult := JA[j,k]/J[j,k];
      if JA ne mult*J then return true, _; end if;
      Append(~scalars,mult);
    end for;
    return false, [<scalars,herm>];
  end if;
  return true, _;

end function;

intrinsic SemiInvariantBilinearForms( G::GrpMat ) -> SeqEnum
{ A sequence of triples <scalars, S, A> where scalars is a sequence of field
  elements, one for each generator of the matrix group G and S and A are bases 
  for the symmetric and alternating forms preserved by G (up to multiplication 
  by scalars) }
  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  if IsAbsolutelyIrreducible(G) then
    failed, retval := quickCheck(G);
  else
    failed := true;
  end if;
  if failed then
    n := Degree(G);
    L := KMatrixSpace(F,n,n);
    M := GModule(G);
    MA := MatrixAlgebra(F,n);
    retval := [car< Parent([F|]), Parent([MA|]), Parent([MA|]) > |];
    for lambda in F_homs(G,F) do
      E := AHom(M,TwistedDual(M,lambda));
      if Dimension(E) gt 0 then
        sym, alt := sym_alt(E,F,n);
        scalars := [ lambda(G.i) : i in [1..Ngens(G)] ];
        Append(~retval,<scalars,sym,alt>);
      end if;
    end for;
  end if;
  return retval;
end intrinsic;

intrinsic SemiInvariantSesquilinearForms( G::GrpMat ) -> SeqEnum
{ A sequence of pairs <scalars, H> where scalars is a sequence of field 
  elements, one for each generator of the matrix group G and H is a basis for 
  the space of hermitian forms preserved by G (up to multiplication by scalars)
}

  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  flag, q := IsSquare(#F);
  require flag : "the field order must be a square";

  F0 := GF(q);
  mu := hom< F -> F | x :-> x^q >;
  if IsAbsolutelyIrreducible(G) then
    failed, retval := quickCheckHerm(G,F0,mu);
  else
    failed := true;
  end if;
  if failed then

    n := Degree(G);
    M := GModule(G);
    MA := MatrixAlgebra(F,n);

    contract := func< mat | MA![F![a[i],a[i+1]] : i in [1..2*n*n by 2]]
      where a is Eltseq(mat) >;

    retval := [ car< Parent([F|]), Parent([MA|]) > | ];

    for lambda in F_homs(G,F0) do
      D := TwistedSemilinearDual( M, lambda, mu );
      E := AHom(M, D);
      if Dimension(E) gt 0 then
        B := Basis(E);
        Q := KMatrixSpace(F0,n,2*n);
        if Characteristic(F) eq 2 then
          U := herm_space(F0,F,n) meet sub< Q | [ expand(F0,F,Q,b) : b in B] >;
        else
          xi := PrimitiveElement(F);
          W := [ b + ConjugateTranspose(b,mu) : b in B ] cat 
               [ (xi - mu(xi))*(b - ConjugateTranspose(b,mu)) : b in B ];
          U := sub< Q | [ expand(F0,F,Q,b) : b in W] >;
        end if;
        scalars := [ lambda(G.i) : i in [1..Ngens(G)] ];
        Append(~retval,<scalars,[contract(u) : u in Basis(U)]>);
      end if;
    end for;
  end if;
  return retval;
end intrinsic;

intrinsic SemiInvariantQuadraticForms( G::GrpMat ) -> SeqEnum
{ A sequence of pairs <scalars, Q> where scalars is a sequence of field 
  elements, one for each generator of the matrix group G and Q is a basis for 
  the quadratic forms preserved by G (up to multiplication by scalars) }
  
  F := BaseRing(G);
  require IsFinite(F) : "the field must be finite";
  n := Degree(G);
  MA := MatrixAlgebra(F,n);
  retval := [ car< Parent([F|]), Parent([MA|]) > | ];

  ch_sym_alt := SemiInvariantBilinearForms(G);
  if Characteristic(F) eq 2 then
    for t in ch_sym_alt do
      scalars := t[1];
      quad := quad_from_alt(t[3],F,n,G,scalars);
      if #quad gt 0 then
        Append(~retval,<scalars,quad>);
      end if;
    end for;
  else
    for t in ch_sym_alt do
      if #t[2] gt 0 then
        Append(~retval, < t[1], [MA| symToQuad(form) : form in t[2]] > );
      end if;
    end for;
  end if;
  return retval;

end intrinsic;


