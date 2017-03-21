freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//        Related to action on upper half plane                   //
//                                                                //
////////////////////////////////////////////////////////////////////


// the following takes as input the elements of some
// matrix, given as a sequence, and finds the fixed points.
// this may also be used when the matrix is not in a
// congruence subgroup, as in FindArc below.

function fixedpoints(seq,H)
    a,b,c,d := Explode(seq);
    if (a eq d) and (b eq 0) and (c eq 0) then
       return [H];
    end if;

    P := PolynomialAlgebra(Parent(a));
    x := P.1;
    f := c*x^2 + (d-a)*x - b;

  if Type(Parent(a)) eq FldRe then
    rts := Roots(f, ComplexField(Parent(a)));
    return [H!r[1] : r in rts | IsCoercible(H, r[1])];
  end if;

    if Type(a) in {RngIntElt,RngQuadElt} then
       g := Gcd([c,b,d-a]);
       if g gt 1 then
	  C := Integers()!(c/g);
	  B := Integers()!(b/g);
	  A := Integers()!((d-a)/g);
	  f := C*x^2 + A*x - B;
       end if;
    end if;    
    if c eq 0 then
       return [H!Infinity()];
    elif b eq 0
       then return [H!0];
    end if;

    assert IsCoercible(Rationals(),Discriminant(f));
    // "First argument must be a matrix with
    // rational determinant and trace.";

    // replace f with a polynomial with integer discriminant
    fact := Factorization(f);
    disc := Rationals()!Discriminant(f);
    
    if fact[1][2] eq 2 then
       factor := fact[1][1];
       coefs := Coefficients(factor);
       return [H|-coefs[1]/coefs[2]];
    end if;
    
    if #fact eq 2 then       
       factor1 := fact[1][1];
       factor2 := fact[2][1];
       coefs1 := Coefficients(factor1);
       coefs2 := Coefficients(factor2);
       return [H|-coefs1[1]/coefs1[2],-coefs2[1]/coefs2[2]];
    end if;
    print f;
    // denom := Denominator(disc);
    // de1,de2 := SquarefreeFactorization(denom);
    // de3 := de1*de2;
    // f := de3*f;
    // a,b,c,d := Explode([a*de3,b*de3,c*de3,d*de3]);
    A := Coefficient(f,2);
    B := Coefficient(f,1);
    C := Coefficient(f,0);
    // next line could be rewritten in terms of
    // previously computed terms.
    dK,s := SquarefreeFactorization(Integers()!Discriminant(f));
    L := ScalarField(H);
    if dK ne 1 then
//	if not (L cmpeq Rationals()) then
//	    require dK lt 0: "Argument 1 must come from a
//	    unit in a quaternion algebra";
//	end if;
	PL := PolynomialRing(L);
	t := PL.1;
	LK := NumberField(t^2-dK);
	// warning: there are two possible conjugates,
	// but we only want the one in the upper half plane.
	// we assume that the subsequent corecing into H function
	// always returns the positive imaginary valued point.
	x := LK![-B/2/A,s/2/A];
	if dK gt 0 then
	   y := LK![-B/2/A,-s/2/A];
	   return [H!x,H!y];
	else
	   return [H!x];
	end if;
     else
	x1 := L!((a-d + s)/2/c);
	x2 := L!((a-d - s)/2/c);
	return [H!x1, H!x2];
    end if;
end function;

intrinsic FixedPoints(g::GrpPSL2Elt, H::SpcHyp : Precision := 0) -> SeqEnum // SpcHypElt
    {returns the fixed points of the action of g on the upperhalf
    plane H.  This is either a sequence of at most 2 points, which are
    in the closure of H (under the complex topology) or a sequence
    containing H, in the case of g being the identity}

    if assigned Parent(g)`IsShimuraGroup then
      seq := Eltseq(Matrix(g : Precision := Precision));
    else
      seq := Eltseq(g`Element);
      if Precision ne 0 then
        ChangeUniverse(seq, RealField(Precision));
      end if;
    end if;
    return fixedpoints(seq,H);
end intrinsic;


intrinsic FixedArc(g::GrpPSL2Elt,H::SpcHyp) -> SeqEnum
   {if the first argument g is an involution, this returns the end points
    of an arc fixed by g, such that the mid point of the arc is fixed by g}    
    m := Matrix(g);
    require m[1,1] + m[2,2] eq 0 : "matrix must have order 2";
    // we use the fact that in the situation we are considering,
    // the fixed point of the matrix is at the top of the fixed arc.
    // we assume that the matrix has positive determinant.
    point := ExactValue(FixedPoints(g,H)[1]);
    K := Parent(point);
    seq := Eltseq(point);
    // make the entries of seq integers:
    if seq[1] eq 0 then
       denom := Denominator(seq[2]);
    else
       denom := LCM([Denominator(s) : s in seq]);
    end if;
    seq1 := [Integers()|seq[1]*denom,seq[2]*denom];
    // we assume that K is an imaginary quadratic field
    // i.e., d is negative:
    d := Rationals()!((K![0,1])^2);
    PolRing := PolynomialRing(Rationals()); x := PolRing.1;
    M := NumberField(x^2 + d);
    return [H|(M!seq1)/denom,(M![seq1[1],-seq1[2]])/denom];
end intrinsic;



