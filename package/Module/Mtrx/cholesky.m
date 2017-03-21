freeze;

intrinsic Cholesky(M::Mtrx) -> Mtrx
  {Computes a Cholesky decomposition of M}
  M := PseudoCholeskyForm(M:Swap := false);
  return PseudoCholeskyFormToCholesky(M);
end intrinsic;

intrinsic PseudoCholeskyFormToCholesky(M::Mtrx:Error := true) -> Mtrx
  {Transforms a pseudo Cholesky form of M into a Cholesky decomposition.}
  n := Ncols(M);
  C := M;
  for i in [1..n] do
    if C[i][i] lt 0 then 
      if Error then
        error "Matrix is not positive definite or not enough precision";
      else
        C[i][i] := 0;
      end if;
    end if;
    C[i][i] := SquareRoot(C[i][i]);
    for j in [i+1..n] do
      C[j][i] := 0;
      C[i][j] *:= C[i][i];
    end for;
  end for;
  return C;
end intrinsic;

intrinsic PseudoCholeskyForm(M::Mtrx:Swap := false, Error := true) -> Mtrx, Mtrx, GrpPermElt
  {Computes a pseudo Cholesky decomposition of M.}

  n := Nrows(M);
  T := IdentityMatrix(Integers(), n);
  P := Sym(n).0;
  Q := M;
  Z := Integers();
  for i:= 1 to n do
    // find maximum:
    if Swap then
      _, p := Maximum([Q[j][j] : j in [i..n]]);
      p := p+i-1;
      if p lt n then
        mp := Maximum([Q[j][j] : j in [p+1..n]]);
      end if;
      if p ne i then
        P:= Sym(n)!(p,i)*P;
        for j := i to n do
          a := Q[j][i];
          Q[j][i] := Q[j][p];
          Q[j][p] := a;
        end for;
        for j := i to n do
          a := Q[i][j];
          Q[i][j] := Q[p][j];
          Q[p][j] := a;
        end for;

        SwapRows(~T, i, p);
      end if;

      assert IsSymmetric(Submatrix(Q, i, i, n-i, n-i));
    end if;

    for j := i+1 to n do
      Q[j][i] := Q[i][j];
      if Q[i][i] eq 0 then
        if Error then
          error "Error: Matrix was not positive definite or insufficient precision";
        else
          return false, _, _;
        end if;
      end if;
      Q[i][j] := Q[i][j] / Q[i][i];
    end for;
    for k := i+1 to n do
      for l := k to n do
        Q[k][l] := Q[k][l] - Q[k][i] * Q[i][l];


        Q[l][k] := Q[k][l]; // to keep it symmetric!!
      end for;
    end for;

  end for;
  return Q, T, P;
end intrinsic;

