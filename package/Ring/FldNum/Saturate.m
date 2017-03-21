freeze;

//import "../RingExt/extras.m" : RingExtSaturation;


// These are broken in cases when the rows are not independent (MW Nov 2015)
// > K<s37>:=QuadraticField(37);
// > Saturation(Matrix([[K|0,0,0]])); // bug with row/column accounting - fixed with 
// addition of zero handling
// > Saturation(Matrix([[K|1,1,1],[1,1,1]])); // infinite loop

intrinsic Saturation(M::PMat) -> .
  {The saturation wrt to the number field of the module.}
  R := MaximalOrder(CoefficientRing(M));
  N := Matrix(FieldOfFractions(R), Matrix(M));
  O := 1*R;
  O := O^-1;

  return Saturation(CoefficientIdeals(M), N, [O : i in [1..Ncols(N)]]);
end intrinsic;


intrinsic Saturation(M::Mtrx[RngOrd]) -> .
  {"} // "
  R := MaximalOrder(CoefficientRing(M));
  M := Matrix(FieldOfFractions(R), M);
  O := 1*R;
  O := O^-1;

  return Saturation([O : i in [1..Nrows(M)]], M, [O : i in [1..Ncols(M)]]);
end intrinsic;


intrinsic Saturation(M::Mtrx[FldAlg]) -> .
  {"} // "
  R := MaximalOrder(CoefficientRing(M));
  O := 1*R;
  O := O^-1;

  return Saturation([O : i in [1..Nrows(M)]], M, [O : i in [1..Ncols(M)]]);
end intrinsic;

intrinsic Saturation(A::[RngOrdFracIdl], M::Mtrx, B::[RngOrdFracIdl]) -> .
  {"} // "
  //return RingExtSaturation(A, M, B);

  if IsZero(M) then
      return Matrix(CoefficientRing(M), 0, Ncols(M), []);
  end if;

  B := [x^-1 : x in B];
  A_orig := A;
  M_orig := M;

  R := CoefficientRing(M);
  T1 := IdentityMatrix(R, Nrows(M));
  T2 := IdentityMatrix(R, Ncols(M));
  R := MaximalOrder(R);

  function IsDiagonal(X)
    C := CoefficientRing(X);
    one := C!1;
    zero := C!0;
    return SequenceToMultiset(Eltseq(X))
      eq {* zero^^(Ncols(X) *Nrows(X) - Nrows(X)), one^^Nrows(X)*};
  end function;

  while not IsDiagonal(M) do
    P := PseudoMatrix(A, M);
    H, T := HermiteForm(P);
    A := CoefficientIdeals(H);
    M := Matrix(H);
    T1 := T*T1;

    P := PseudoMatrix(B, Transpose(M));
//    H, T := HermiteForm(P);
    H := HermiteForm(P);
    B := CoefficientIdeals(H);
    M := Transpose(Matrix(H));
//    T2 := T2*T^-1;
  end while;

  mult := [A[i]*B[Position(Eltseq(M[i]), 1)] : i in [1..#A]];
//  B := [x^-1 : x in B];
  

//  return M, A, B, T1, T2;

  FOF:=FieldOfFractions(R); // MW, Nov 9 2015
  m := PseudoMatrix([1*R : x in mult | not IsOne(x)],
		    Matrix(FOF,[Eltseq(T1[i]*M_orig) :
                                i in [1..Nrows(T1)] | not IsOne(mult[i]) ]));
  return VerticalJoin(PseudoMatrix(A_orig, M_orig), m),
         PseudoMatrix([1*R : x in mult | not IsOne(x)],
	              Matrix(FOF,[Eltseq(T1[i]) :
                                  i in [1..Nrows(T1)]|not IsOne(mult[i])]));
end intrinsic;
