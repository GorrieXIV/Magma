freeze;

/*
    Construct normalizer of extra-special group in GL(n,q).
    Written by Derek Holt
*/

PermutationMatrix := function(perm,F)
  //Why is this not an internal function!!!
  //perm permutation, F = field.
  local ps, d, V, W;
  ps := ElementToSequence(perm);
  d := #ps;
  V := RMatrixSpace(F,d,d);
  W := VectorSpace(F,d);
  return V![ W.(ps[i]) : i in [1..d] ];
end function;

PermInducingAut := function(R,phi)
//Given automorphism phi of regular permutation group R, and an automorphism
//phi of R, return unique permutation fixing 1, normalising R and
//inducing phi on R
  local d;
  d := Degree(R);
  perm :=[1];
  for i in [2..d] do
    isc,g := IsConjugate(R,1,i);
    perm[i] := 1^(phi(g));
  end for;
  return Sym(d)!perm;
end function;

MakeDeterminantOne := function(mat)
//If possible multiply matrix mat by scalar matrix to make determinant 1
 local d, K, det, isp, r;
 d := Nrows(mat); K := BaseRing(mat);
 det := Determinant(mat);
 if det eq K!1 then return mat; end if;
 isp,r := IsPower(det^-1,d);
 if isp then return mat * ScalarMatrix(K,d,r);
 else return mat;
 end if;
end function;

NormaliserOfExtraSpecialGroup:= function(r,q :
        general:=false, normaliser:=false, unitary:=false, orthogonal:=false )
/* Construct complete normaliser of extraspecial group as subgroup of
 * GL(r,q). r must be a prime power p^n with p | q-1.
 * Extraspecial group has order p^(2n+1) and exponent p for p odd,
 * and is of + type - central product of dihedrals - for p=2.
 *
 * If general is false then intersection with SL(r,q) is returned
 * normaliser only applies when unitary or orthogonal set, and
 * returns full normaliser fixing form mod scalars
 *
 * orthogonal option returns intersection with OmegaPlus(d,q) when d = 2^r
 * (this is always same as intersection with SOPlus and GOPlus).
 */
  local fac, p, n, gl, z, w, esg, d, M, mat, insl, slm1, slm2, slm3, exp, rno,
        dp, R, phi, cmat, north;
  if r le 2 then error
     "Degree must be at least 3 in NormaliserOfExtraSpecialGroup";
  end if;
  if normaliser then general:= true; end if;
  insl := true;
  fac := Factorisation(r);
  if #fac ne 1 then error
     "First argument must be a prime power in NormaliserOfExtraSpecialGroup";
  end if;
  p := fac[1][1]; n := fac[1][2];
  if (q-1) mod p ne 0 then error
     "Divisibility condition not satisfied in NormaliserOfExtraSpecialGroup";
  end if;
  if unitary then
    qfac:=Factorisation(q); pp:=qfac[1][1]; ee:=qfac[1][2]; rq:=pp^(ee div 2);
    if ee mod 2 ne 0 or (rq-1) mod p eq 0 then
      error "Inappropriate field for unitary option";
    end if;
  end if;
  if orthogonal and p ne 2 then
    error "orthogonal option only applicable for even degrees";
  end if;
  z := PrimitiveElement(GF(q));  w := z^((q-1) div p);
    // w is a primitive p-th root of 1
  gl := GL(r,q);
  // first make generators of extraspecial group
  esg := [gl|];

  //diagonal generators:
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      for k in [0..p-1] do
        for l in [1..p^i] do Append(~d,w^k); end for;
      end for;
    end for;
    Append(~esg, DiagonalMatrix(GF(q),d));
  end for;

  //permutation matrix generators
  M := func< r,p | r mod p eq 0 select p else r mod p >;
    
  dp := []; // we will collect the permutations for use later.
  for i in [0..n-1] do
    perm := [];
    for j in [1..p^(n-1-i)] do
      for l in [1..p^(i+1)] do
         perm[(j-1)*p^(i+1) + l] := (j-1)*p^(i+1) + M(l+p^i,p^(i+1));
      end for;
    end for;
    Append(~dp,perm);
    Append(~esg, PermutationMatrix(perm,GF(q)) );
  end for;

  //esg now generates extraspecial group of order p^(2n+1).

  //Now normaliser gens.
  esn := [gl|];
  //First diagonals.
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      exp := 0;
      for k in [0..p-1] do
        exp +:= k;
        for l in [1..p^i] do Append(~d,w^exp); end for;
      end for;
    end for;
    
    slm1 := MakeDeterminantOne(DiagonalMatrix(GF(q),d));
    if Determinant(slm1) ne w^0 then
      if r ne 3 then error "Bug A"; end if;
      insl := false;
    end if;
    if Determinant(slm1) eq w^0 or general then
      Append(~esn, slm1);
    end if;
  end for;

  slm2:=[];
  first := true;
  for i in [0..n-1] do
    mat := MatrixAlgebra(GF(q),p^(i+1))!0;
    rno := 0;
    for k in [0..p-1] do
      for j in [1..p^i] do
         rno +:= 1;
         for l in [0..p-1] do
           mat[rno][j+l*p^i] := w^(k*l);
         end for;
      end for;
    end for;
    mat := DirectSum([mat : j in [1..p^(n-1-i)]]);
    if p eq 2 and q mod 8 in {1,7} then
      //2 is a square mod p - make determinant 1 and also make orthogonal
      r2 := Root(GF(q)!2,2);
      mat *:= r2^-1;
    else //in orthogonal case we need a consistent multiplier.
      if first then
        det := Determinant(mat);
        if det eq GF(q)!1 then
          isp:=true; rt:=GF(q)!1;
        else isp,rt := IsPower(det^-1,r);
        end if;
      end if;
      if isp then mat *:= rt; end if;
    end if;
    slm2[i+1] := mat;
    //slm2[i+1] := MakeDeterminantOne(mat);
    if r eq 3 and not insl then Append(~esn,slm1^-1*slm2[i+1]*slm1); end if;
    if Determinant(slm2[i+1]) ne w^0 then
      if r ne 4 then error "Bug B"; end if;
      if insl then
        insl := false;
        if general then
          Append(~esn, slm2[i+1]);
        end if;
      else
        Append(~esn, slm2[i]^-1*slm2[i+1]);
      end if;
    elif orthogonal and r gt 4 and q mod 8 in {3,5} then
      if not first then
        Append(~esn, slm2[i]^-1*slm2[i+1]);
      elif normaliser then
        north := slm2[i+1];
      end if;
    else Append(~esn, slm2[i+1]);
    end if;
    first := false;
  end for;

  //Finally some permutation matrices that normalise it.
  R := sub< Sym(r) | dp >;
  for i in [2..n] do
    phi := hom< R->R | [R.1*R.i] cat [R.j : j in [2..n]] >;
    slm3 :=
        MakeDeterminantOne(PermutationMatrix(PermInducingAut(R,phi),GF(q)));
    if Determinant(slm3) eq w^0 or general then
      Append(~esn,slm3);
    end if;
    if  insl and Determinant(slm3) ne w^0 then
      // q  = 3 or 7 mod 8
      if r ne 4 then error "Bug C"; end if;
      Append(~esn, slm3^-1*slm2[1]*slm3);
      Append(~esn, slm3^-1*slm2[2]*slm3);
    end if;
    if not insl then
      // q = 5 mod 8
      Append(~esn, MakeDeterminantOne(slm2[1]*slm3));
    end if; 

  end for;

  G := sub< gl | esg cat esn >;

  if orthogonal then
    scal := r eq 4 select true else false;
    //r = 4 handled separately
    isit, form := SymmetricBilinearForm(G:Scalars:=scal);
    cmat := TransformForm(form,"orthogonalplus");
    if r gt 4 and normaliser and q mod 8 in {3,5} then
      Append(~esn,north);
    end if;
  elif unitary then
    isit, form := UnitaryForm(G);
    cmat := TransformForm(form,"unitary");
  end if;

  //Better adjoin a generating scalar!
  if unitary and not normaliser then
    zz:=z^(rq-1);
    if general then
      Append(~esn, ScalarMatrix(GF(q), r, zz) );
    else
      Append(~esn, ScalarMatrix(GF(q), r, zz^((rq+1) div GCD(rq+1,r))) );
    end if;
  elif normaliser or not orthogonal then
    if general then
      Append(~esn, ScalarMatrix(GF(q), r, z) );
    else
      Append(~esn, ScalarMatrix(GF(q), r, z^((q-1) div GCD(q-1,r))) );
    end if;
  end if;

  G := sub< gl | esg cat esn >;
  if unitary or orthogonal then
    G := G^cmat;
    if orthogonal and r eq 4 and not normaliser then
      G := G meet OmegaPlus(r,q);
    end if;
  end if;

  return G;
  //in orthogonal case: p=3,5 mod 8, c=4 (go,so), p=1,7 mod 8, c=8

end function;

NormaliserOfSymplecticGroup:= function(r,q :
                 general:=false, normaliser:=false,  unitary:=false)
/* Construct complete normaliser of extraspecial group as subgroup of
 * GL(r,q). r must be a prime power p^n with p | q-1.
 * Extraspecial group has order p^(2n+1) and exponent p.
 *
 * If general is false then intersection with SL(r,q) is returned
 *
 * The unitary option is only intended to be called when q is a square and
 * sqrt(q) = 3 mod 4.
 *
 * normaliser only applies when orthogonal set, and
 * returns full normaliser fixing form mod scalars
 */
  local fac, p, n, gl, z, w, w4, esg, d, M, mat, exp, rno, dp, R, phi,
        insl, slmk, slmk2, slm, got;

  if r le 2 then error
     "Degree must be at least 3 in NormaliserOfSymplecticGroup";
  end if;
  if normaliser then general:= true; end if;
  fac := Factorisation(r);
  if #fac ne 1 then error
     "First argument must be a prime power in NormaliserOfSymplecticGroup";
  end if;
  p := fac[1][1]; n := fac[1][2];
  if p ne 2 then error "Prime must be 2 in NormaliserOfSymplecticGroup";
  end if;
  if (q-1) mod 4 ne 0 then error
     "Divisibility condition not satisfied in  NormaliserOfSymplecticGroup";
  end if;
  if unitary then
    qfac:=Factorisation(q); pp:=qfac[1][1]; ee:=qfac[1][2]; rq:=pp^(ee div 2);
    if ee mod 2 ne 0 or rq mod 4 eq 1 then
      error "Inappropriate field for unitary option";
    end if;
  end if;
  z := PrimitiveElement(GF(q));  w := z^((q-1) div p);
    // since p=2, w = -1
  gl := GL(r,q);
  // first make generators of extraspecial group
  esg := [gl|];

  insl := true;
  //diagonal generators:
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      for k in [0..p-1] do
        for l in [1..p^i] do Append(~d,w^k); end for;
      end for;
    end for;
    Append(~esg, DiagonalMatrix(GF(q),d));
  end for;

  //permutation matrix generators
  M := func< r,p | r mod p eq 0 select p else r mod p >;
    
  dp := []; // we will collect the permutations for use later.
  for i in [0..n-1] do
    perm := [];
    for j in [1..p^(n-1-i)] do
      for l in [1..p^(i+1)] do
         perm[(j-1)*p^(i+1) + l] := (j-1)*p^(i+1) + M(l+p^i,p^(i+1));
      end for;
    end for;
    Append(~dp,perm);
    Append(~esg, PermutationMatrix(perm,GF(q)) );
  end for;
  //We also take a scalar of order 4, although this seems to be there anyway!
  w4 := z^((q-1) div 4);
  Append(~esg, DiagonalMatrix(GF(q),[w4: i in [1..r]]));

  //esg now generates symplectic group of order p^(2n+2).

  //Now normaliser gens.
  esn := [gl|];
  //diagonals different for symplectic
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      exp := 0;
      for k in [0..p-1] do
        exp +:= k;
        for l in [1..p^i] do Append(~d,w4^exp); end for;
      end for;
    end for;
    //determinant is w4^(d/2) = 1 for d>4, -1 for d=4
    //slm := MakeDeterminantOne(DiagonalMatrix(GF(q),d));
    slm := DiagonalMatrix(GF(q),d);
    if Determinant(slm) ne w^0 then
      if r ne 4 then error "Bug B"; end if;
      if insl then
        insl := false;
        if general then
          Append(~esn, slm);
        end if;
        slmk := slm;
      else Append(~esn, slmk^-1*slm);
      end if;
    else Append(~esn, slm);
    end if;
  end for;

  got := false;
  if unitary then //multiply by scal to preserve unitary form
    scal := Root(GF(q)!2,rq+1)^-1;
  else scal := GF(q)!1;
  end if;
  for i in [0..n-1] do
    mat := MatrixAlgebra(GF(q),p^(i+1))!0;
    rno := 0;
    for k in [0..p-1] do
      for j in [1..p^i] do
         rno +:= 1;
         for l in [0..p-1] do
           mat[rno][j+l*p^i] := w^(k*l) * scal;
         end for;
      end for;
    end for;
    mat := DirectSum([mat : j in [1..p^(n-1-i)]]);
    //if scal=1, then determinant is (-2)^(d/2).
    //note -2 is a square iff q = 1 or 3 mod 8 (but 3 does not occur here).
    if unitary then //make determinant one while preserving form.
        det := Determinant(mat);
        isp,rt := IsPower(det^-1,r*(rq-1));
        assert isp or r eq 4;
        if isp then mat *:= ScalarMatrix(GF(q^2),r,rt^(rq-1)); end if;
      slm := mat;
    else
      slm := MakeDeterminantOne(mat);
    end if;
    if Determinant(slm) ne  w^0 then
      if r ne 4 then error "Bug C"; end if;
      if not got then
        got := true;
        slmk2 := slm;
        if general then
          Append(~esn, slm);
        end if;
      else Append(~esn, slmk2^-1*slm);
      end if;
    else Append(~esn, slm);
    end if;
  end for;

  //Finally some permutation matrices that normalise it.
  R := sub< Sym(r) | dp >;
  for i in [2..n] do
    phi := hom< R->R | [R.1*R.i] cat [R.j : j in [2..n]] >;
    mat := PermutationMatrix(PermInducingAut(R,phi),GF(q));
    if r eq 4 and not unitary then
      slm := MakeDeterminantOne(mat);
    else slm := mat;
    end if; 
    if Determinant(slm) ne  w^0 then
      if r ne 4 then error "Bug D"; end if;
      Append(~esn, slmk^-1*slm);
    else Append(~esn, slm);
    end if;
  end for;

  G := sub< gl | esg cat esn >;
  if unitary then
    isit, form := UnitaryForm(G);
    cmat := TransformForm(form,"unitary");
  end if;

  //Better adjoin a generating scalar!
  if unitary and not normaliser then
    zz:=z^(rq-1);
    if general then
      Append(~esn, ScalarMatrix(GF(q), r, zz) );
    else
      Append(~esn, ScalarMatrix(GF(q), r, zz^((rq+1) div GCD(rq+1,r))) );
    end if;
  else
    if general then
      Append(~esn, ScalarMatrix(GF(q), r, z) );
    else
      Append(~esn, ScalarMatrix(GF(q), r, z^((q-1) div GCD(q-1,r))) );
    end if;
  end if;

  G := sub< gl | esg cat esn >;
  if unitary then
    G := G^cmat;
  end if;
  return G;

end function;

NormaliserOfExtraSpecialGroupMinus := function(r,q: symplectic:=false,
                                        general:=false, normaliser:=false)
/* Construct complete normaliser of minus-type extraspecial group as subgroup
 * of GL(r,q), where r = 2^n.
 *
 * If general is false then intersection with SL(r,q) is returned
 * normaliser should only be set when symplectic is true, and means
 * return full normaliser fixing symplectic form mod scalars
 *
 */
  local fac, p, n, gl, w, a, b, esg, d, M, mat, exp, rno, dp, R, phi,
        mat1, mat2, slm, insl, slmk, nsmat, iss;
  fac := Factorisation(r);
  if #fac ne 1 or fac[1][1] ne 2 or q mod 2 ne 1 then error
   "First argument must be a power of 2 in NormaliserOfExtraSpecialGroupMinus";
  end if;
  if normaliser then general:=true; end if;
  n := fac[1][2];

  function MakeSymplectic(mat,form)
    local c,d,K,r;
      d := Nrows(mat); K:=BaseRing(mat);
      formt := mat*form*Transpose(mat);
      c := formt[1][2];
      if IsSquare(c) then
        r := Root(c,2);
        return true, mat*ScalarMatrix(K,d,r^-1);
      else return false, mat;
      end if;
  end function;

  if symplectic then
    form := DirectSum([Matrix(GF(q),2,2,[0,1,-1,0]) : i in [1..r div 2]]);
    //the symplectic form preserved by derived subgroup of group
  end if;

  insl := true;
  gl := GL(r,q);
  w := GF(q)!(-1);
  // first make generators of extraspecial group
  // need two squares summing to -1.
  a:= 0;
  for i in [1..q-1] do
     bool, b:= IsSquare(GF(q)!(-1 - i^2));
     if bool then
         a:= GF(q)!i;
         break;
     end if;
  end for;

  esg := [gl|];
  mat := GL(2,q)![a,b,b,-a]; //Det(mat) = 1
  Append(~esg,DirectSum([mat : j in [1..2^(n-1)]]));

  //diagonal generators (n >= 1):
  for i in [1..n-1] do
    d := [];
    for j in [1..2^(n-1-i)] do
      for k in [0..1] do
        for l in [1..2^i] do Append(~d,w^k); end for;
      end for;
    end for;
    Append(~esg, DiagonalMatrix(GF(q),d));
  end for;

  //permutation matrix generators
  M := func< r,p | r mod p eq 0 select p else r mod p >;
    
  dp := []; // we will collect the permutations for use later.
  for i in [0..n-1] do
    perm := [];
    for j in [1..2^(n-1-i)] do
      for l in [1..2^(i+1)] do
         perm[(j-1)*2^(i+1) + l] := (j-1)*2^(i+1) + M(l+2^i,2^(i+1));
      end for;
    end for;
    Append(~dp,perm);
    if i eq 0 then
      Append(~esg, PermutationMatrix(perm,GF(q)) *
                     DiagonalMatrix(GF(q),&cat[[1,-1] : i in [1..2^(n-1)]]) );
      //determinant = 1
    else
      Append(~esg, PermutationMatrix(perm,GF(q)) );
    end if;
  end for;

  //esg now generates extraspecial group of order p^(2n+1).

  //Now normaliser gens.
  iss := true;
  esn := [gl|];
  //first those for first component.
  mat1 := GL(2,q)![1,1,-1,1]; //Det(mat1) = 2
  slm := MakeDeterminantOne(DirectSum([mat1 : j in [1..2^(n-1)]]));
  if Determinant(slm) ne w^0 then
    if r gt 4 then error "Bug A"; end if;
    insl := false;
    slmk := slm;
  end if;
  if symplectic then
    isit, slm := MakeSymplectic(slm,form);
    if isit or normaliser then
      Append(~esn, slm);
    else
      iss:=false; nsmat:=slm; //could have Det(nsmat) = -1
    end if;
  elif Determinant(slm) eq w^0 or general then
    Append(~esn, slm);
  end if;
  mat2 := GL(2,q)![1+a+b,1-a+b,-1-a+b,1-a-b]; //Det(mat2) = 4
  slm := MakeDeterminantOne(DirectSum([mat2 : j in [1..2^(n-1)]]));
  if Determinant(slm) ne w^0 then error "Bug B"; end if;
  if symplectic then
    isit, slm := MakeSymplectic(slm,form);
    assert isit;
    Append(~esn, slm);
  else Append(~esn, slm);
  end if;

  for i in [1..n-1] do
    mat := MatrixAlgebra(GF(q),2^(i+1))!0;
    rno := 0;
    for k in [0..1] do
      for j in [1..2^i] do
         rno +:= 1;
         for l in [0..1] do
           mat[rno][j+l*2^i] := w^(k*l);
         end for;
      end for;
    end for;
    // determinant mat = 4 when i=1
    slm := MakeDeterminantOne(DirectSum([mat : j in [1..2^(n-1-i)]]));
    if Determinant(slm) ne w^0 then
      slm := slmk^-1*slm;
    end if;
    if symplectic then
      isit, slm := MakeSymplectic(slm,form);
      if isit or normaliser then
        Append(~esn, slm);
      elif iss then
        iss:=false; nsmat:=slm;
      else
        //this only happens when Determinant(nsmat) = 1
        isit, slmn := MakeSymplectic(nsmat^-1*slm,form);
        assert isit;
        Append(~esn, slmn);
      end if;
    else Append(~esn, slm);
    end if;
  end for;

  if n gt 1 then
    //One to mix up the first and second Q8 and D8
    mat := MatrixAlgebra(GF(q),4)![1,0,1,0,0,1,0,1,0,1,0,-1,-1,0,1,0];
    //Det(mat)=4
    slm := MakeDeterminantOne(DirectSum([mat : j in [1..2^(n-2)]]));
    if Determinant(slm) ne w^0 then
      slm := slmk^-1*slm;
    end if;
    if symplectic then
      isit, slm := MakeSymplectic(slm,form);
      if isit or normaliser then
        Append(~esn, slm);
      elif iss then
        iss:=false; nsmat:=slm;
      else
        //this only happens when Determinant(nsmat) = 1
        isit, slmn := MakeSymplectic(nsmat^-1*slm,form);
        assert isit;
        Append(~esn, slmn);
      end if;
    else Append(~esn, slm);
    end if;

    //Finally some permutation matrices that normalise it.
    R := sub< Sym(r) | dp >;
    for i in [3..n] do
      phi := hom< R->R | [R.1, R.2*R.i] cat [R.j : j in [3..n]] >;
      slm := MakeDeterminantOne(
              PermutationMatrix(PermInducingAut(R,phi),GF(q)) );
      if Determinant(slm) ne w^0 then error "Bug C"; end if;
      if symplectic then
        isit, slm := MakeSymplectic(slm,form);
        if isit then
          Append(~esn, slm);
        elif iss then
          iss:=false; nsmat:=slm;
        else
          //this only happens when Determinant(nsmat) = 1
          isit, slmn := MakeSymplectic(nsmat^-1*slm,form);
          assert isit;
          Append(~esn, slmn);
        end if;
      else Append(~esn, slm);
      end if;
    end for;
  end if;

  //Better adjoin a generating scalar in SL!
  if normaliser or not symplectic then
    z := PrimitiveElement(GF(q));
    if general then
      Append(~esn, ScalarMatrix(GF(q), r, z) );
    else
      Append(~esn, ScalarMatrix(GF(q), r, z^((q-1) div GCD(q-1,r))) );
    end if;
  end if;

  G := sub< gl | esg cat esn >;
  if symplectic then
    //isit, form := SymplecticForm(G : Scalars:=true);
    G := G^TransformForm(form,"symplectic");
  end if;
  return G;

end function;
