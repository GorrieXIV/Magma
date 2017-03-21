freeze;

/**************************************************************

  Helper functions to compute (I-A)^(-1) efficiently for a
  p-adic matrix A (see comments in IminAinvB function).
        Mike Harrison 01/2004
  
**************************************************************/

function WorkVal(n)

    // returns the number of matrix multiplications (+2) involved
    // in a call  GeometricSeries(A,n)
    
    if n eq 1 then return 2; end if;
    bits := Intseq(n,2);
    return (2*#bits + #[1:i in bits | i eq 1] -2);
    
end function;

function GeometricSeries(A,n)

    // returns 1+A+A^2+...+A^n by a binary powering method

    sum := Parent(A)!1; // sum = 1 !   
    if n eq 1 then 
        return sum + A;
    end if;
    bits := Intseq(n,2);
    powA := A;
    bfirst := true;
    for i := #bits-1 to 1 by -1 do
        if bits[i] eq 0 then
            sum := sum + (bfirst select powA else sum*powA);
            powA := powA^2;
        else
            tmp := powA^2;
            sum := sum + tmp + (bfirst select powA else sum*powA);
            powA := A*tmp;
            delete tmp;
        end if;
        bfirst := false;
    end for;
    return sum+powA;
    
end function;

function AdjointMethod(A,R)

    d := NumberOfRows(A)-2;
    tr := Trace(A);
    M := A - ScalarMatrix(d+2,tr);
    for r in [1..d] do
        M := A*M;
	tr := Trace(M) div (r+1);
        M := M - ScalarMatrix(d+2,tr);
    end for;
    det := (RowSubmatrix(A,1)*ColumnSubmatrix(M,1))[1,1];
    M := (1 div det) * M;
    return Matrix(R,M);
    
end function;

function IminAinv(A,prec,val,Rbig)

    maxpow := Ceiling(prec/val) - 1;
    N := NumberOfRows(A);
    if WorkVal(maxpow) le N then
        M := GeometricSeries(A,maxpow);
    else
        R := Parent(A[1,1]);
        M := ((Precision(R) ge u) select A else
                Matrix(ChangePrecision(Rbig,u),A)) where u is
                  prec+Valuation(Factorial(N-1),2);
        M := AdjointMethod(Parent(M)!1 - M,R);
    end if;
    return M;

end function;

function IminAinvB(A,prec,b,Rbig)

    // A is an N*N matrix and b a col vector of length N, both with
    // entries in an UnramifiedQuotientRing, R (2-adic), of precision
    // p and degree n. prec <= p.
    // Function returns B1, an R-sequence of length N s.t.
    // vec(B1) = (I-A)^(-1).b mod 2^prec.
    // The main point is that the function will usually be called when
    // all entries of A are divisible by 2^large, large ~ n, and prec
    // will be no more than a small(ish) multiple of n, so we don't
    // necessarily want to compute (I-A)^(-1) by general inversion.
    
    val := Min([Valuation(a): a in Eltseq(A)]);
    if val ge prec then return Eltseq(b); end if;
    return Eltseq(IminAinv(A,prec,val,Rbig)*b);
    
end function;
