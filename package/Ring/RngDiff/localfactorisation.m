freeze;

// This file is based on M.van Hoeij. - Formal solutions and factorization
// of differential operators with power series coefficients, 1997.

// June 2009.
// This file contains routines relating to the factorisation of differential
// operators over a Laurent series ring, without allowing 
// finding factors over finite extensions of the Laurent series ring.


// June 2009 Improvements for the future.
// ** Try and do the lifting and other stuff without
// Truncation, but with truncation as map to a 
// polynomial ring or some quotient ring. In this way everything can be
// done for finite precision Laurent series rings.
// ** It may also be worthwile to consider the structures for p-adics for
// changing the series rings implementations.
// ** Add restrictions on constant rings like it being a number field, or
// a field that allows places on it.
// A.W.

// Maxima verbose declarations in this file
declare verbose LocalFactorisation, 3;


////////////////////////////////////////////////////////////////////
//                                                                //
//                         General functions                      //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Appears in Factorisation.
function LossInPrecisionInFactorisation(L)
  // Input: a differential operator over a Laurent series ring, 
  //        whose derivation is NOT the standard one.
  // Output : true iff moving forward and backward to a monic standard operator
  //          with standard derivation t*d/dt
  //          does not cause any loss in precision.
  R := Parent(L);
  F := BaseRing(R);
  assert IsDifferentialLaurentSeriesRing(F);
  assert Characteristic(F) eq 0;
  relprecF := RelativePrecision(F);
  assert relprecF lt Infinity();
  lcoef := LeadingCoefficient(L);
  relprecderivF := RelativePrecisionOfDerivation(F);
  relprecF := RelativePrecision(F);
  // Precision loss for changing derivation to the standard D=t*d/dt.
  // Assume the realtive precision of the coefficients be at most that of
  // the ring F, as that is how F may add orders with. The following is 
  // broader than may be necessary.
  if (relprecderivF lt relprecF) then
    return true;
      // This can weakened by the requirement that g, D(g), D^2(g), ...,
      // D^(deg-1)(g) have relative precisions < those of 
      // of all the coefficients whose valuation is finite.
      // Here g = (t/f), when L has derivation f*d/dt.
      //
  // Precision loss for making monic.
  elif RelativePrecision(lcoef) lt Infinity() then 
    relprecscoefs := {RelativePrecision(v): v in Eltseq(L)};
    relprecscoefs := {v : v in relprecscoefs | v lt Infinity()};
    if IsEmpty(relprecscoefs) then 
      maxrelprec := Infinity();
    else
      maxrelprec := Maximum(relprecscoefs);
    end if;
    if RelativePrecision(lcoef) lt Minimum(maxrelprec,relprecF) then
      return true;
    end if;
  end if;
  return false;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                        Truncate functions                      //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in InitialLeftFactor and CoprimeLifting.
function TruncateEntriesMatrix(Mat)
  // Input: A matrix Mat over a (differential) series ring.
  // Output:  Mat without the order terms.
  B:=BaseRing(Mat);
  assert IsDifferentialSeriesRing(B) or ISA(Type(B),RngSer);
  trunccoeffs:= func<v | [B|Truncate(v[i]): i in [1 .. Ncols(Mat)]]>;
  return Matrix([trunccoeffs(Mat[i]) : i in [1..Nrows(Mat)]]);
end function;

// ok
// Used in InitialLeftFactor and CoprimeLifting.
function TruncateEntriesVector(V)
  // Input: A vector V over a (differential) series ring.
  // Output:  V without the order terms
  B:=BaseRing(V);
  assert IsDifferentialSeriesRing(B) or ISA(Type(B),RngSer);
  return Vector(B,[Truncate(V[i]) : i in [1..Ncols(V)]]);
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//              Functions for solving matrix equations            //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in InitialLeftFactor and CoprimeLifting.
function TransferToSystemOverRngSerPow(M,V,prec,v)
  // Input: A matrix M and vector V over a (Differential) Laurent series ring
  //        C((t)), and an integer v.
  // Output: The matrix t^(-v)*M and t^(-v)*V.
  //         The new matrix and vector are defined
  //         over a power series ring C[[t]] with fixed precision prec.
  F:=BaseRing(M);
  assert ISA(Type(F), RngSerLaur) or IsDifferentialLaurentSeriesRing(F);
  if IsDifferentialLaurentSeriesRing(F) then 
    fld := ConstantRing(F);
  else
    fld := BaseRing(F);
  end if;  
  // assert that v is such that the coercion is valid.
  minvals := [ExtendedReals()|Minimum([Valuation(e) : e in Eltseq(V)])];
  for row in RowSequence(M) do
    minval := Minimum([Valuation(e) : e in row]);
    Append(~minvals, minval);
  end for;
  minval := Minimum(minvals);
  assert minval-v ge 0;
  // Coercion into a power series ring.
  P:=PowerSeriesRing(fld, prec);
  mat := ChangeRing((F.1)^(-v)*M,P);
  vector:= ChangeRing((F.1)^(-v)*V,P);
  return mat, vector;
end function;

// ok
// Used in the next function.
function RelativePrecisionForMatrix(Mat)
  // Input: A matrix Mat. Its coefficients are elements
  //        of a power series ring.
  // Output: The minimum relative precision of the entries in Mat that
  //         are not order terms.  
  P := BaseRing(Mat);
  assert ISA(Type(P), RngSerPow);
  bl, minrows := IsCoercible(Integers(), Precision(P));
  assert bl;
  for row in RowSequence(Mat) do
    // An order term has relative precision 0, and no other terms do.
    posrow := [Integers()| RelativePrecision(m) : 
                 m in row | RelativePrecision(m) gt 0];
    if #posrow ge 1 then
      minrows := Minimum(minrows, Minimum(posrow));
    end if;
  end for;
  return minrows;
end function;

// ok
// Based on code by Allan Steel. 
// Used in the next code.
function SystemOverBaseRing(Mat,V)
  // Input: A matrix Mat and a vector V. Their coefficients are elements
  //        of a power series ring or number field over C.
  // Output: M and v over C coordinatewise such that S*Mat=V has a 
  //        solution vector S in C iff it is one for X*M=v.
  R := BaseRing(Mat);
  typeR := Type(R);
  assert ISA(typeR, RngSerPow) or ISA(typeR, FldNum);
  n:=Ncols(Mat);
  assert #Eltseq(V) eq n;
  if ISA(typeR, RngSerPow) then
    bl, prec := IsCoercible(Integers(),Minimum([RelativePrecisionForMatrix(Mat),
                               RelativePrecisionForMatrix(Matrix(V)),
		               Precision(R)]));
    assert bl;
    // The following will be used for row of a matrix or a vector.
    // For instance, Mat[i,1] is written as a horizontal sequence on the 
    // basis [1,R.1,...,(R.1)^(prec-1)]. 
    // Mat [i,2] is written as a horizontal sequence on the 
    // basis [1,R.1,...,(R.1)^(prec-1)] and then cat-ted to the first, etc.
    coeffs := func<v |[Coefficient(v[i], j): j in [0..prec - 1], i in [1..n]]>;
  else
    coeffs := func<v | &cat([Eltseq(v[i]):  i in [1 .. n]])>;
  end if;
    // If Mat is an mxn matrix, then M becomes an m*(n*prec) matrix.
  M := Matrix([coeffs(Mat[i]): i in [1..Nrows(Mat)]]);
  v := Matrix([coeffs(V)]);
  return M, Vector(v);
end function;

// ok
// Based on code by Allan Steel.
// Used in the next code.
function HasSolutionOverBaseRing(Mat,V)
  // Input: A matrix Mat and a vector V. Their coefficients are elements
  //        of a power series ring or number field over C.
  // Output: bl, S, space. bl is true iff S*Mat=V has a solution vector S
  //         having entries in C. 
  R := BaseRing(Mat);
  assert ISA(Type(R), RngSerPow) or ISA(Type(R), FldNum);
  M, v := SystemOverBaseRing(Mat,V);
  hassolution, S, N := IsConsistent(M,v);
  if hassolution then
    return true, Vector(S), N;
  else
    return false, Vector(BaseRing(M),[]), VectorSpace(BaseRing(M),0);
  end if;
end function;

// ok
// Used in InitialLeftVector and CoprimeLifting.
function HasUniqueSolutionOverBaseRing(Mat,V)
  // Input: A matrix Mat and a vector V. Their coefficients are elements
  //        of a power series ring or number field over C.
  // Output: bl, S. bl is true iff S*Mat=V has a unique solution vector S
  //         having entries in C. 
  R := BaseRing(Mat);
  assert ISA(Type(R), RngSerPow) or ISA(Type(R), FldNum);
  hassolution, vecS, N := HasSolutionOverBaseRing(Mat,V);
  if not hassolution then
    return false, vecS;
  elif Dimension(N) gt 0 then
    return false, vecS;
  else
    return true, vecS;
  end if;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//               Slope Valuation over Laurent Series              //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Can be done by using newton polygon as in Valuation(L,s,pl) as well.
intrinsic SlopeValuation(L::RngDiffOpElt, s::RngElt) -> FldRatElt
  {The valuation of L, with respect to the rational slope s.
   The derivation of L must be t*d/dt, where t is the generator of the 
   differential Laurent series ring of the basering of L.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsDifferentialLaurentSeriesRing(F):
    "The operators must be defined over a differential Laurent series ring.";  
    // We need to make sure that the derivation is the correct one,
    // So locally of the form t*d/dt, for the local parameter t.
  require Characteristic(F) eq 0:
    "The base ring of the operator must have characteristic 0.";
  require HasProjectiveDerivation(R):
    "The derivation of L is not of the correct form.";
  bl, s := IsCoercible(Rationals(), s);
  require bl:
    "The second argument is not coercible as a rational number.";  
  num:=Numerator(s);
  den:=Denominator(s);
  assert (GCD(num,den) eq 1) and (den gt 0);
  if IsWeaklyZero(L) then
    valscoeffsL := [];
  else   
    seqL:=Eltseq(TruncateCoefficients(L));
    valscoeffsL:=[<Valuation(seqL[j]),j-1> : j in [1..Degree(L)+1]];
      // The coefficient 0 has valuation infinity. Take it out.
    valscoeffsL:=[v : v in valscoeffsL | IsCoercible(Integers(),v[1])];
  end if;  
  if IsEmpty(valscoeffsL) then
    return Infinity();
  else 
    min, position:= Minimum([v[1]*den-v[2]*num: v in valscoeffsL]);
    return Rationals()!min;
  end if;
end intrinsic

// ok
// Used in InitialLeftFactor and CoprimeLifting.
function MinOfValsOfCoefs(L) 
  // Input: L, a differential operator ring over a series ring. 
  // Output: The mimimum of the valuations of the coefficients of L.
  assert ISA(RngDiffOpElt, Type(L));
  F:=BaseRing(Parent(L));
  assert IsDifferentialSeriesRing(F);
  return ExtendedReals()!(Minimum([Valuation(v) : v in Eltseq(L)]));
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//             Initial Factorisation - before lifting             //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// This implementation uses the fact that we have a finite precision ring
// via truncation.
function InitialLeftFactor(L,B,s) 
  // Input: Differential operators L<>0 and B over a differential Laurent
  //        series ring F, whose derivation
  //        is t*d/dt, where t is thw local parameter in the BaseRing F
  //        of L (= BaseRing of B).
  // Output: The differential operator A, such that
  //        L=A*B up to the first order precision w.r.t. the
  //        SlopeValuation v_s(t^iD^j)=i*denominator(s)-j*numerator(s) of s.
  //        The coeffients of A are truncated.
  // Assumptions: 
  //        * the monomials in B have SlopeValuation -p*num*den,
  //          where p*den is the order of B.
  //        * the slope s is a rational.
  R:=Parent(L);
  assert ISA(RngDiffOp, Type(R));
  F:=BaseRing(R);
  assert Characteristic(F) eq 0;
  assert IsDifferentialLaurentSeriesRing(F); 
  assert HasProjectiveDerivation(R);
  assert not HasZeroDerivation(R); 
  bl, relprecF := IsCoercible(Integers(), RelativePrecision(F));
  assert bl and (relprecF ge 1);
  assert not IsWeaklyEqual(L,R!0);
  assert IsWeaklyMonic(L);
  assert IsMonic(B);
  bl, s := IsCoercible(Rationals(), s);
  assert bl;
  den:=Denominator(s);
  assert (GCD(Numerator(s), den) eq 1) and (den gt 0);
  if (Rationals()!relprecF) lt 1/den then
    "The relative precision of the series ring is too small.";
    " for calculating a first order left factor.";   
    return R!0;
  end if;  
  valLats:=SlopeValuation(L,s);
  valBats:=SlopeValuation(B,s);
  valAats:=valLats-valBats;
  degA:=Degree(L)-Degree(B);
  monsA:=[];
    // This will contain the terms of A, always including the
    // one belong to the highest order term.
    // A tuple <j,i> corresponds to (F.1)^i*(R.1)^j.
  for j in [0..(degA-1)] do
    bl, int:= IsCoercible(Integers(),(valAats/den+j*s));
    if bl then
      Append(~monsA,<j,int>);
    end if;
  end for;
  Append(~monsA,<degA,0>);
  vprint LocalFactorisation, 2: "Initial monomials for left factor:", monsA;     
    // We construct the matrix and its image vector.
    // We want A of maximal order. To ensure this add an extra column.
    // The matrix is never the zero nor empty, since A has
    // at least one monomial.
  orderB:=Order(B);
  orderL:=Order(L);
  dimspace:=orderL+1;
  nmonsA:=#monsA;  
  mat:=ZeroMatrix(F,nmonsA,dimspace);
  for ord in [1..nmonsA] do       
    row:=Eltseq((F.1)^monsA[ord][2]*(R.1)^monsA[ord][1]*B) 
            cat [F|0: i in [orderB+monsA[ord][1]+1..orderL]];
    row:=[F|ChangePrecision(row[i], Floor((valLats)/den+(i-1)*s+1))
              : i in [1..dimspace]];	    
    mat[ord]:=Vector(F,row);            
  end for; 
  valmatrix:= Integers()!(monsA[1][2] + MinOfValsOfCoefs(B));
  column:=[F|0: i in [1..nmonsA-1]] cat [F|(F.1)^valmatrix];
  mat:=HorizontalJoin(mat,Matrix(F,nmonsA,1,column));  
  seqL:=Eltseq(L);
    // Compute image vector and add line to make sure that the
    // highest order term is monic.
  vector := [F| ChangePrecision(seqL[i], Floor(valLats/den+(i-1)*s)+1) :
               i in [1..dimspace]];     
  vector:=Vector(F, (vector cat [F|(F.1)^valmatrix]));   
  mat:=TruncateEntriesMatrix(mat);
  vector:=TruncateEntriesVector(vector);    
  vprint LocalFactorisation, 3: 
    "Matrix and image vector for solving the first left factor:", mat, vector;
  mat, vector
    := TransferToSystemOverRngSerPow(mat, vector, relprecF, valmatrix);
  vprint LocalFactorisation, 1:"Solving linear system over the base ring.";               
  hasuniquesolution, S := HasUniqueSolutionOverBaseRing(mat,vector);   
  assert hasuniquesolution;  
  S:=ChangeRing(S,F);
  A:=&+([S[i]*(F.1)^monsA[i][2]*(R.1)^monsA[i][1] : i in [1..nmonsA]]);
  if Order(A) lt degA then
    A:=A+(R.1)^degA;
  end if;
  return TruncateCoefficients(A);
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                   Lifting over Laurent Series                  //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in CoprimeLifting
function TruncOperatorWithSlopeValPrec(L,p,s,d)
  R := Parent(L);
  F := BaseRing(R);
  assert IsDifferentialOperatorRing(R) and IsDifferentialLaurentSeriesRing(F);
  seqL := Eltseq(L);
  modL:=[F|];
  for j in [1..(#seqL)] do
    exponent:=Integers()!Ceiling(p/d+(j-1)*s);
      // ChangePrecision adds an order term with given exponent.
    Append(~modL, ChangePrecision(seqL[j],exponent));
  end for;
  return TruncateCoefficients(R!modL);
end function;

// ok
// Used in CoprimeLifting
function AdditionalMonomialsForFactors(orderL,ordermodL, pbound,s, d);
  points := [<j,i>:  i in [Ceiling(pbound[1]/d+j*s)..Floor(pbound[2]/d+j*s)],
		  j in [0..orderL-1]];
      // The positions of j and i coincide with the points of a Newton polygon. 
  if ordermodL lt orderL then
    Include(~points,<orderL,0>);
    addedhighestterm:=true;
  else
    addedhighestterm:=false;
  end if;
  return points, addedhighestterm;       
end function;  

// ok
// The following implementation uses the fact that we have a 
// finite precision ring via truncation.
// ** Note: there is a more efficient way in case that s=0 using the Euclidean
// algorithm, see page 11 of the article. 
//
// intrinsic CoprimeLifting(L::RngDiffOpElt, A::RngDiffOpElt, 
//      B::RngDiffOpElt, s:: RngElt, a::RngIntElt, limitprec::RngIntElt) 
// 		-> BoolElt, RngDiffOpElt, RngDiffOpElt, RngDiffOpElt
function CoprimeLifting(L,A,B,s,a,limitprec)                
  // {Lifts the factorisation A*B that is congruent to L up to and 
  //  including accuracy a-1 with respect to the slope valuation
  //  to precision a.}
  // Assumptions: there is a factorisation L = A*B.
  // Output: True iff the lift succeeded, and the new lifts of A, B and AB,
  //         respectively.
  // In the output the left and right factor are truncated.
  bl, s := IsCoercible(Rationals(), s);
  error if not bl,
    "The slope should be coercible as a non-negative rational.";
  error if not s ge 0,  
    "The slope should be coercible as a non-negative rational.";
  error if not a ge 1,
    "The accuracy should be a positive integer.";
  R:=Parent(L);
  assert IsDifferentialOperatorRing(R);
  error if not ((Parent(A) eq R) and (Parent(B) eq R)),
    "The operators must be elements of the same ring.";  
  error if not ((Degree(L) ge 0) and (Degree(A) ge 0) and (Degree(B) ge 0)),
    "The operators should all be non-zero.";
  error if not (IsWeaklyMonic(L) and IsWeaklyMonic(A) and IsWeaklyMonic(B)),
    "The operators should all be weakly monic.";
  F:=BaseRing(R);  
  error if not IsDifferentialLaurentSeriesRing(F),
    "The operators must be defined over a differential Laurent series ring.";
  error if not Characteristic(F) eq 0,
    "The base ring of the operator must have characteristic 0."; 
  error if not HasProjectiveDerivation(R),
    "The derivation of the operator ring must be of the satandard form t*d/dt.";
  relprecF := RelativePrecision(F);
  bl, relprecF := IsCoercible(Integers(), relprecF);
  error if not bl,
    "The relative precision of the differential series ring must be finite.";      
  orderL:=Order(L);
  orderA:=Order(A);
  orderB:=Order(B);
  error if not orderL eq (orderA+orderB),
    "The degrees of the left and right factors do not add up.";
    // There are no lifts for A if A=1 and B of degree Order(L).
    // This is because A is then of degree 0 and monic.
    // Truncating operators makes the degree smaller if the highest 
    // coefficient is an order term.    
  L:=TruncateCoefficients(L);
  if orderB eq orderL then
    return true, R!1, L, L;
  end if;
  if orderA eq orderL then
    return true, L, R!1, L;
  end if;     
    // As s>=0 and all operators are monic, the valuations of L, A
    // and B at s are less or equal to 0, as these are minima.
    // The total minimum valuation is therefore the one of L.
  num:=Numerator(s);
  den:=Denominator(s);
  assert (GCD(num,den) eq 1) and (den gt 0);
  minimumval:=MinOfValsOfCoefs(L);
  valLats:=SlopeValuation(L,s);
  valAats:=SlopeValuation(A,s);
  valBats:=SlopeValuation(B,s);
  dimspace:=orderL+1;  
  // Define the coprime index t.
  t:=1;
  seqL:=Eltseq(L);
  while (t le a) do
    if relprecF lt (a+t)/den then 
      // The relative precision of the series ring may be too small.
      vprint LocalFactorisation, 2: "Coprime lifting precision now exceeds",
        " relative precision of ring."; 
    end if;
    if limitprec lt (a+t)/den then    
      return false, _, _, _;
    end if;
      // Set up L for the next precision step.
      // Determine which exponents of the powers of F.1 are allowed.
      // The order term can be taken to the ceiling of the
      // (valLats+a+t)/den +j*slope.
      // We use truncated series coefficients.
      // Truncation is important, it is better in future calculations
      // then to use just modL with order terms.
    precisionL:= valLats+a+t;
    modL:= TruncOperatorWithSlopeValPrec(L,precisionL,s,den);
      // Make sure A and B are indeed minimal, so that the order terms in the
      // coefficients have slope valuation valAats+a and valBats, respectively.     
      // The leading coefficients may vanish here.
    modA:= TruncOperatorWithSlopeValPrec(A,valAats+a,s,den);
    modB:= TruncOperatorWithSlopeValPrec(B,valBats+a,s,den);
    ordermodA:=Order(modA);
    ordermodB:=Order(modB);
      // The following calculation of modAB can be improved, 
      // see article page 10/11.
    modAB:=TruncOperatorWithSlopeValPrec(modA*modB,precisionL,s,den);
    modLminmodAB:=TruncateCoefficients(modL-modAB);  
    vprint LocalFactorisation, 3: "The operator modulo slope valuation:", modL;
    vprint LocalFactorisation, 3: "Left factor modulo slope valuation:", modA;
    vprint LocalFactorisation, 3: "Right factor modulo slope valuation:", modB; 
    // vprint LocalFactorisation, 3: 
    // "Product of the factors modulo slope valuation:", modAB; 
    if IsWeaklyEqual(modLminmodAB,R!0) then 
      return true, modA, modB, modAB;
    elif SlopeValuation(modLminmodAB,s) ge (valLats+a+1) then 
      return true, modA, modB, modAB;
    end if;  
      // Calculate monomials in l and r, such that A+l and B+r
      // are the left and right factor, respectively of better precision.
      // In this case modLminmodAB has exactly SlopeValuation valLats+a.
      //
      // At least one of l and r then has terms, since otherwise
      // L - modA*modB  would have SlopeValuation at least valLats+a+1.
      // This case has already been dealt with.
      //
      // When modA (or modB) are not of the degree they are supposed to be, and
      // hence are less, the monic highest order term will be added, 
      // even if it has a valuation that is too high. In this way the 
      // correct degrees are assured at the end.
    assert SlopeValuation(modLminmodAB,s) eq valLats+a; 
    monsl, lhashighestterm := AdditionalMonomialsForFactors(orderA, ordermodA,
                                   [valAats+a,valAats+a+t-1],s,den);
    monsr, rhashighestterm := AdditionalMonomialsForFactors(orderB, ordermodB,
                                   [valBats+a,valBats+a+t-1],s,den);           
    vprint LocalFactorisation, 3: "Monomials for the left operator:", monsl;
    vprint LocalFactorisation, 3: "Monomials for the right operator:", monsr;
    ntermsl:=#monsl;
    ntermsr:=#monsr;
    assert ntermsl+ntermsr gt 0;
      // We start building the matrix, first for l, then for r, and
      // the image vector that corresponds to the difference of modL and modAB.
      // The first row consists of the eltseq belong to multiplication
      // of l_0 with B, the second of l_1*B, etc, as matrix solving
      // goes to the left.
    mat:=ZeroMatrix(F, ntermsl+ntermsr, dimspace); 
    for ord in [1..ntermsl] do       
      row:=Eltseq((F.1)^monsl[ord][2]*(R.1)^monsl[ord][1]*modB);
      row:=row cat [F|0: i in [#row+1..dimspace]];
      row:=[ChangePrecision(row[i],Ceiling(precisionL/den+(i-1)*s)) :
              i in [1..dimspace]];
      mat[ord]:=Vector(F,row);    
    end for;		    
    for ord in [1..ntermsr] do
      row:=Eltseq(modA*(F.1)^monsr[ord][2]*(R.1)^monsr[ord][1]);
      row:=row cat [F|0: i in [#row+1..dimspace]];
      row:=[ChangePrecision(row[i],Ceiling(precisionL/den+(i-1)*s)) :
              i in [1..dimspace]];
      mat[ntermsl+ord]:=Vector(F,row);  		
    end for;    
    vector:=Eltseq(modLminmodAB) cat [F|0:i in [Order(modLminmodAB)+1..orderL]];
    dimrowspace:=ntermsl+ntermsr;
    if ntermsl eq 0 then
      valmatrix:= Minimum([v[2]:v in monsr])+ MinOfValsOfCoefs(modA);
    elif ntermsr eq 0 then
      valmatrix:= Minimum([v[2]:v in monsl])+ MinOfValsOfCoefs(modB);
    else 
      valmatrix:= Minimum([v[2]:v in monsl])+ MinOfValsOfCoefs(modB);
      valmatrix:= Minimum([valmatrix, 
                          Minimum([v[2]:v in monsr])+ MinOfValsOfCoefs(modA)]);
    end if;
    bl, valmatrix := IsCoercible(Integers(), valmatrix);
    assert bl;
      // Add extra condition on the highest term whenever l or r had
      // the highest term added.
      // When l has the highest term we have to make sure the
      // new operator modA becomes monic.This can be achieved via
      // adding the same term, in our case (F.1)^valmatrix, in a
      // new column and a new term to the image vector exactly on the
      // spot corresponding to the highest coefficient of l.
    additionalterm := (F.1)^valmatrix;  
    if lhashighestterm then
      column:=[F|0: i in [1..ntermsl-1]] cat [F|additionalterm] 
                 cat [F|0: i in [ntermsl+1..dimrowspace]];
      mat:=HorizontalJoin(mat,Matrix(F,dimrowspace,1,column));
      vector:=vector cat [F|additionalterm];
    end if;
    if rhashighestterm then 
      column:=[F|0: i in [1..dimrowspace-1]] cat [F|additionalterm];
      mat:=HorizontalJoin(mat,Matrix(F,dimrowspace,1,column));
      vector:=vector cat [F|additionalterm];
    end if; 
    vector:=Vector(F,vector);
    mat:=TruncateEntriesMatrix(mat);
    vector:=TruncateEntriesVector(vector); 
    vprint LocalFactorisation, 3: 
      "Matrix and image vector of the lifting system:", mat, vector;  
      // Note: The matrix is never the zero-matrix, since at least one 
      // of the factors l and r is non-zero.
      //  
      // Calculations of nullspaces and solutions of matrix equations
      // over Laurent series rings is hard. 
      // So that is why we multiply the matrix as well as the image
      // vector with a power of F.1 so that we can view their entries
      // as elements of a power series ring.
      // As the vectors we are interested in are actually vectors over
      // the base ring, we then move to another system over the base ring and
      // solve this.
      // The valuation of the image vector is at least the valuation
      // of the matrix, as it is a linear combination of the colums over
      // the constant ring.
    mat, vector 
      := TransferToSystemOverRngSerPow(mat,vector,relprecF,valmatrix);   
    // vprint LocalFactorisation, 3: "Matrix and image vector after reduction:",
    //   mat, vector; 
    vprint LocalFactorisation, 3: "Solving linear system over the base ring."; 
    
    hasuniquesolution, S := HasUniqueSolutionOverBaseRing(mat,vector);
      // There should be at least one solution in S.
    assert Ncols(S) gt 0;
      // Construct l and r as operators.
    if hasuniquesolution then
      vprint LocalFactorisation, 3:"Unique solution vector of the system:", S;
      S:= ChangeRing(S,F); 
      if ntermsl eq 0 then
        l:=R!0;
      else
        l:=&+([S[i]*(F.1)^monsl[i][2]*(R.1)^monsl[i][1] : 
                 i in [1..ntermsl]]);
      end if;
      if ntermsr eq 0 then
        r:=R!0;
      else
        r:=&+([S[ntermsl+i]*(F.1)^monsr[i][2]*(R.1)^monsr[i][1] : 
                 i in [1..ntermsr]]);  
      end if;  
        // Perform extra test.         
      testprod:= R!Eltseq(modAB+l*modB+modA*r+l*r);	
      difference:= TruncateCoefficients(testprod-modL);
      if difference ne R!0 then
        assert SlopeValuation(difference,s) ge (valLats+a+1);
      end if;
      return true, TruncateCoefficients(modA+l), 
                 TruncateCoefficients(modB+r), modL;      
    end if;     
    vprint LocalFactorisation, 2:"Solution vector is not unique.";
    vprint LocalFactorisation, 2:"Raising coprime index.";
    t:=t+1;
  end while;       
  return false, _,_,_;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                  Shifted polynomials functions                 //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in the next function.
// IsMonic gives false when it the coefficient contains an order term.
function IsShiftedByRingElt(g,h,R) 
  // Input: two univariate monic polynomials g(T) and h(T) in the same ring.
  //        lincoefg is the linear coefficient of g.
  // Output: true iff g(T) = h(T+i), for some i in R, and i itself.
  // Note: The order in which g and h are given matters.
  assert IsMonic(g);
  assert IsMonic(h);
  P := Parent(g);
  assert ISA(RngUPol, Type(P));
  assert Parent(h) eq P;
  deg := Degree(g);
  if not Degree(h) eq deg then
    return false, _;
  elif deg in {-1,0} then
    // return true, Infinity();  
    return false, _;
  end if; 
    // g and h are of degree at least 1.
  linterm := Coefficient(g, deg-1) - Coefficient(h, deg-1);
  bl, int := IsCoercible(R,linterm/deg); 
  if not bl then
    return false, _;
  elif IsWeaklyEqual(g,&+([P|Coefficient(h,i)*(P.1+int)^i: i in [0..deg]])) then
    return true, int;
  else 
    return false,_;
  end if;
end function;

// ok
// Used in the shifted functions below.
function ShiftedPolynomials(S) 
  // Input: S, a sequence of distinct univariate polynomials. 
  // Output: A sequence dividing up S. The entries are sequences of
  //         polynomials in S that are shifted by an integer.
  assert ISA(Type(S), SeqEnum);
  assert #S eq #Seqset(S);
  P:=Universe(S); 
  assert ISA(Type(P), RngUPol);
  // assert infinite precision in coefficient ring.
  pols:=S;
  alldegrees:=[Degree(pol): pol in pols];
  seqdegrees:=Setseq(Seqset(alldegrees));
  polsbydegree := [[pols[i]: i in Indices(alldegrees,deg)] : deg in seqdegrees];
    // This is a division of the polynomials w.r.t. the degree.
    // If n=seqdegrees[i], then polsbydegree[i] consists of the
    // sequence of all polynomials of S of degree n.
    // We will refine the sequence by splitting an sequence entry up
    // into shifted bits.
  seqT := [];
  for h in S do
    if h in &cat(polsbydegree) then
      seqh := [P|];
      index := Index(seqdegrees, Degree(h));
      polSdegh := polsbydegree[index];
        // This includes h itself.
      for g in polSdegh do     
        bl, int := IsShiftedByRingElt(h,g,Integers());
        if bl then  
          Include(~seqh, g);
          Exclude(~polsbydegree[index],g);
	    // The g is now already contained in seqh in seqT. 
            // So no need to see if g occurs again for another h.
        end if;
      end for;
      assert h in seqh;
      Include(~seqT, seqh);
      // When g in S is addressed some time later it is not contained
      // in polsbydegree anymore.
     end if;  
  end for;
  assert #(&cat(seqT)) eq #S;
  return seqT;
end function;

// ok
// Used in FactorisationForStandardScaledOperator.
function ExcessOfShiftedPolynomials(S) 
  // Input: S, a sequence of (distinct) univariate polynomials.
  // Output: The subset T of S, such that
  //         g in T iff there is a polynomial h in the class of g in S 
  //         and a POSITIVE integer i such that g(T)=h(T+i).
  //         In other words, we take out the polynomials g in S that do
  //         not allow any positive shifts to be in S.  
  assert ISA(Type(S), SeqEnum);
  assert #S eq #Seqset(S);
  P:=Universe(S); 
  assert ISA(Type(P), RngUPol);
    // Split up S into sequences of shifted polynomials.
    // Each class contains polynomials of the same degree.
  seqshifts := ShiftedPolynomials(S);
  seqT := [P|];
  for seq in seqshifts do
    deg := Degree(seq[1]);
    coef := Coefficient(seq[1], deg -1);
    coefs := [Integers() |  coef - Coefficient(h, deg - 1) : h in seq ];
    index := Index(coefs, Maximum(coefs));
    seqT := seqT cat Exclude(seq, seq[index]);
  end for;
  return Seqset(seqT);
end function;

// ok
// Used in FactorisationForStandardScaledOperator.
function SetsOfShiftedPolynomials(S,V) 
  // Input: S, a sequence of distinct univariate polynomials and a subset V. 
  // Output: set T of sets of shifted polynomials of V in S.
  assert ISA(Type(S), SeqEnum);
  assert #S eq #Seqset(S);
  assert ISA(Type(V), SetEnum);
  P:=Universe(S); 
  assert ISA(Type(P), RngUPol);
  assert Universe(V) eq P;
  assert V subset Seqset(S);
  W := ShiftedPolynomials(S); 
  assert #(&cat(W)) eq #S;
  indicesW := [[Integers()| Index(S,pol) : pol in seq ] : seq in W];
  setT := {};
  donepols := {};
  for h in V  do
      // No need to consider h if it already occured in a set of
      // one of the previous polynomials in V considered.
    if  not h in donepols then
      seq := [ v : v in W | h in v];
      assert # seq eq 1;
      seq := seq[1];
      index := Index(W,seq);
      seth := Seqset(indicesW[index]); 
        // add all shifted polynomials of h to the sequence of polynomials
        // considered. 
      donepols := donepols join Seqset(seq);
      Include(~setT,seth);
    end if;
  end for;
  return setT;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                      Order terms functions                     //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in FactorWRTNewtPolSlope.
function AddOrderTermsWRTSlope(L,s,p)
  // Input: A (monic) operator L over a series ring, rational s and precision 
  //        factor p.
  // Output: The operator weakly equal to L that is correct up to the
  //         (not including) slope s valuation precision p, with order terms
  //         in all coefficients, except in the leading coefficient.
  assert ISA(Type(L), RngDiffOpElt);
  R:=Parent(L);
  F:=BaseRing(R);
  assert IsDifferentialLaurentSeriesRing(F);
  bl, s := IsCoercible(Rationals(),s);
  assert bl;
  den:=Denominator(s);
  assert (GCD(Numerator(s),den) eq 1) and (den gt 0);
  valLats:=SlopeValuation(L,s);
  seqop:=[F|];
  seqL:=Eltseq(L);
  assert Universe(seqL) eq F;
  for j in [0..Order(L)-1] do
    exponent:=Integers()!Ceiling((valLats+p)/den+j*s);
    Append(~seqop, ChangePrecision(seqL[j+1],exponent));
  end for;
  Append(~seqop, seqL[#seqL]);
  return R!seqop;
end function;

// ok
// Used in the function below.
function ChangePrecisionSeries(x, p)
  // Input: A Laurent or power series x and integer p.
  // Output: The series x with order term changed.
  //         The exponent in the new order term is Valuation(x)+p. 
  F:=Parent(x);
  assert IsDifferentialLaurentSeriesRing(F);
  valx:=Valuation(x);
  bl, valx := IsCoercible(Integers(),valx);
  if bl then
    return F!ChangePrecision(x, valx+p);
  else
    assert x eq F!0;
    return x;
  end if;
end function;

// ok
// Used in FactorWRTNewtPolSlope and factorisation.
function AddRelOrderTermToOperator(L, p)
  // Input: A differential operator L<>0 over a Laurent series ring.
  // Output: The operator whose precision of coefficients are changed,
  //         except for the highest order term.
  //         The new exponent of the order term of coefficient x 
  //         is Valuation(x)+p. 
  R:=Parent(L);
  assert IsDifferentialOperatorRing(R);
  F := BaseRing(R);
  assert IsDifferentialLaurentSeriesRing(F);
  return R!([ ChangePrecisionSeries(v, p) : v in Prune(Eltseq(L))] cat        
              [LeadingCoefficient(L)]);
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                 (Coprime index One) Factorisation              //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// This implementation uses the fact that we have a finite precision ring
// via truncation.
function FactorWRTNewtPolSlope(L,s,h,precval)
  // Input: a differential operator in R over a differential Laurent series
  //        ring F with z*d/dz. Slope s and its newton polynomial h of L. 
  //        Precision for factorisation precval.
  //        A negative precision will lead to factorising until the 
  //        ring precision has been reached.  
  // Output: The highest obtained factorisation of L w.r.t. slope s and
  //         newton polygon h, and the boolean if the algorithm was successful.
  //         The coefficients will not have finite relative precision exceeding
  //         the relative precision of the Laurent series ring.
  R := Parent(L);
  assert ISA(RngDiffOp, Type(R));
  F:=BaseRing(R);
  assert Characteristic(F) eq 0;
  assert IsDifferentialLaurentSeriesRing(F); 
  assert HasProjectiveDerivation(R);
  assert not HasZeroDerivation(R); 
  bl, precF := IsCoercible(Integers(), RelativePrecision(F));
  assert bl; 
  assert precF ge 1;
  bl, precval := IsCoercible(Integers(), precval);
  assert bl;
  assert precval gt 0;
  s := Rationals()!s;
  num:=Numerator(s);
  den:=Denominator(s);
  assert (GCD(Numerator(s),den) eq 1) and (den gt 0);
    // The following will make the function end.
  if precval lt 0 then
    precval := precF;    
  end if;
  assert not IsWeaklyEqual(L,R!0);
  seqh:=Eltseq(h);
  degh:=Degree(h);
  B:= &+([R| seqh[i+1]*(F.1)^(-(degh-i)*num)*(R.1)^(i*den) : i in [0..degh]]);
  B:= TruncateCoefficients(B);
  assert not IsWeaklyEqual(B, R!0);
  vprint LocalFactorisation, 2:"Initial right factor:", B;
    // We lift B to a right hand factor of L.
    // This right hand factor is of the same degee as B.
    // First we need an initial left hand factor before starting lifting.
  orderrightfactor:=Order(B);
  orderleftfactor:=Order(L)-orderrightfactor;	
  A:=InitialLeftFactor(L,B,s); 
    // A and B do not contain order terms.
  assert not IsWeaklyEqual(A, R!0);
  vprint LocalFactorisation, 2:"Initial left factor:", A;
  if L eq A*B then
    seqfactor:=[A,B];
    isfactored:=true;
    vprint LocalFactorisation, 1: "Factorisation over series ring obtained.";
  // elif IsWeaklyEqual(L,A*B) then 
    // seqfactor:=[A,B]; // Or just precF, or precval?
    // seqfactor:=[AddRelOrderTermToOperator(A,Degree(A)+1),
    //             AddRelOrderTermToOperator(B,Degree(B)+1)];
    // isfactored:=true;
    // vprint LocalFactorisation, 1: "Factorisation over series ring obtained.";
  elif precval eq 0 then
    // seqfactor:=[A,B];
    seqfactor:=[AddOrderTermsWRTSlope(A,s,1),
                AddOrderTermsWRTSlope(B,s,1)];
    isfactored:=true;
    vprint LocalFactorisation, 1:
      "Factorisation with valuation accuracy 0 (inclusive) obtained.";    
  else
    isfactored:=false;
    a:=0;
  end if;  
  fails := false; 
    // Do lifting process. This will end the latest when the integer a has
    // reached the precision precval.
  while (not fails) and (not isfactored) do
    a:=a+1;
    vprint LocalFactorisation, 1: "Lifting factors to accuracy", a, "inclusive.";
      // This means that the truncations are correct up to and including
      // accuracy a.
    LeftA := A;
    RightB :=B;  
    bl, A, B, AB := CoprimeLifting(L,A,B,s,a,precval);
    if bl then
      vprint LocalFactorisation, 3: "Obtained Lifts:", [A,B];
      if L eq A*B then
        seqfactor:=[A,B];
        isfactored:=true;
        vprint LocalFactorisation, 1: 
          "Factorisation over series ring obtained.";
      // elif IsWeaklyEqual(L,A*B) then
        // seqfactor:=[A,B]; // Or just precF, or precval?
        // seqfactor:=[AddRelOrderTermToOperator(A,Degree(A)+1),
        //             AddRelOrderTermToOperator(B,Degree(B)+1)];
	// isfactored:=true;
	// vprint LocalFactorisation, 1: 
        //   "Factorisation over series ring obtained.";
      elif (a eq precval) then
        seqfactor:= [AddOrderTermsWRTSlope(A,s,precval+1),
                     AddOrderTermsWRTSlope(B,s,precval+1)];
	isfactored:=true;
	vprint LocalFactorisation, 1: 
          "Factorisation with valuation accuracy", a,"(inclusive) obtained.";    
      else
	if Order(A) lt orderleftfactor then
	  A:=A+(R.1)^orderleftfactor;
        end if;
	if Order(B) lt orderrightfactor then
	  B:=B+(R.1)^orderrightfactor;
	end if;
      end if; 
    else
      vprint LocalFactorisation, 1:
        "Lifting with valuation accuracy", a, "(inclusive) reached limit or",
        "failed.";
      // seqfactor:=[A,B];
      seqfactor:=[AddOrderTermsWRTSlope(LeftA,s,a),
                  AddOrderTermsWRTSlope(RightB,s,a)];
      fails:=true;
      vprint LocalFactorisation, 1:
        "Factorisation with valuation accuracy", a-1 ,"(inclusive) returned.";           
    end if;
  end while; 
  return seqfactor, not fails;  
end function;

// ok
// Improvement: check if the sets can be constructed in an easier way.
function FactorisationForStandardScaledOperator(L,A,ALG,MultFactor)
  // Input:  The differential operator L<>0 over a Laurent series ring
  //         C((t)) with differention t*d/dt. 
  //         Accuracy A w.r.t. the SlopeValuation.
  //         MultFactor means that we multiply the precision A
  //         with the denominator of the slope.
  // Output: All monic coprime index 1 factorisations L=A*B, 
  //         such that B does not have a non-trivial coprime index 1 
  //         factorisation. 
  //         In addition a sequence accordingly is returned stating
  //         if the factorisation is for sure irreducible.
  //         For L=0 a default setting is returned. 
  //         The default accuracy  is maximal w.r.t. 
  //         the relative precision of the series.
  //         The default algorithm is the coprime 1 LCLM algorithm
  R:=Parent(L);
  assert ISA(RngDiffOp, Type(R));
  F:=BaseRing(R); 
  assert Characteristic(F) eq 0;
  assert IsDifferentialLaurentSeriesRing(F); 
  assert HasProjectiveDerivation(R);
  assert not HasZeroDerivation(R); 
  bl, A := IsCoercible(Integers(),A);
  assert bl;
  assert A gt 0;
  bl, precF := IsCoercible(Integers(), RelativePrecision(F));
  assert bl and (precF ge 1);
  assert not IsWeaklyEqual(L,R!0); 
  assert ALG in ["CoprimeIndexOne", "Default", "LCLM"];
  assert ISA(Type(MultFactor), BoolElt);
  if (ALG eq "Default") then
    ALG := "LCLM";
  end if;
  if (ALG eq "CoprimeIndexOne") then
    "Performing coprime index 1 factorisation.";
  else   
    "Performing coprime index 1 LCLM factorisation.";
  end if;  
    // In old versions this was A-1.
  precval := A;
  // L:=AddRelOrderTermToOperator(L,precF);
  np:=NewtonPolygon(L);   
  slopes:=Slopes(np);
  faces:=Faces(np);
  numsdens := [[Integers()|Numerator(sl), Denominator(sl)] : sl in slopes];          
  error if exists {g: g in {GCD(nd[1],nd[2]) : nd in numsdens} | not(g eq 1)}, 
    "The GCD routine returns non-coprime numerators and denominators."; 
  dens := [Integers()| nd[2] : nd in numsdens];                
  error if exists {d: d in dens | d lt 1},
    "The GCD routine returns denominators smaller than 1.";
  vprint LocalFactorisation, 1:"The number of slopes of the Newton polynomial:", #slopes;
  vprint LocalFactorisation, 1:" ";
  seqoffactors:=[];
  areirreducible :=[]; 
  for slope in slopes do
    indexslope := Index(slopes,slope);
    g:=NewtonPolynomial(faces[indexslope]);
    vprint LocalFactorisation, 1:"Slope", slope, "has Newton polynomial", g;
    factors, c:=Factorisation(g);
    for v in factors do
      assert LeadingCoefficient(v[1]) eq BaseRing(g)!1;
    end for;
      // The factors should be monic wrt the same unit.  
      // At the moment this is implemented as 1 for univariate polynomial rings.
      // If this changes in the future, scale the factors, so that
      // they have coefficient 1.
    bl, s:= IsCoercible(Rationals(),slope);
    assert bl and (s ge 0);
    if s eq Rationals()!0 then
      M:=[factor[1]: factor in factors];
        // Take the polynomials in the factorisation, without multiplicity.
      setM := Seqset(M);
      assert #M eq #setM;
      S:=ExcessOfShiftedPolynomials(M);
      assert S subset setM;
      if (ALG eq "CoprimeIndexOne") then
        N:=setM diff S;
      else 
        assert (ALG eq "LCLM"); 
        Mprime:=setM diff S;
        Mdubprime := SetsOfShiftedPolynomials(M,Mprime);
        N := {};
        for h in Mdubprime do
          prod := &*( [factors[i][1]^factors[i][2]: i in h]);
          Include(~N, prod);
        end for;
      end if;
    else 
      N:=[factor[1]^factor[2]: factor in factors];
      expsN := [factor[2]: factor in factors];
    end if;  
    for h in N do
      vprint LocalFactorisation, 1:"Factorisation for slope", s, 
                              "with valuation accuracy", precval;
      vprint LocalFactorisation, 1:"Factor of Newton polynomial used", h;   
        // If the boolean MultFactor is true then we factor the
        // operator to the precision d*precval. As a result the
        // operator should then have precval terms in each 
        // non-leading coefficient for.
        // Otherwise factorisation will be done with respect to the slope
        // valuation that may result in less monomials.   
      if MultFactor then
        seqfactor :=FactorWRTNewtPolSlope(L,s,h,dens[indexslope]*precval); 
      else
        seqfactor :=FactorWRTNewtPolSlope(L,s,h,precval);
      end if;   
        // State if the factors are for sure irreducible.
      if Degree(seqfactor[2]) eq 1 then
          // The operator is of degree one.
        isirreducible := "true"; 
      elif (s gt 0) and (expsN[Index(N,h)] eq 1) then
          // The Newton polynomial of the slope is irreducible
        isirreducible := "true";  
      elif (s gt 0) and (expsN[Index(N,h)] gt 1) then
          // The Newton polynomial of a slope s>0 has one factor,
          // but with with multiplicity at least two.
        isirreducible := "false";    
      elif (s eq 0) and (ALG eq "LCLM") then
        isirreducible := "false";
      else
        isirreducible := "true";
      end if; 
      Append(~seqoffactors,seqfactor);
      Append(~areirreducible, isirreducible);
      vprint LocalFactorisation, 1: " ";
    end for;
  end for;
  return seqoffactors, areirreducible;
end function;


// ok
intrinsic Factorisation(L::RngDiffOpElt:Precision:=-1, Algorithm:="Default") -> 
     SeqEnum, SeqEnum
  {All monic factorisations L=A*B, such that B does not
   have a non-trivial coprime index 1 or LCLM factorisation. 
   The second sequence states if a right hand factor is undisputedly 
   irreducible.}  
     // The default accuracy of the slope valuation for each factor is maximal
     // w.r.t. the relative precision of the series ring.  
     // Algorithms allowed are "CoprimeIndexOne" and "LCLM".
     // One may want to consider a lift with slope valuation
     // precision - minimum of negative vals of the coefficients.    
     // This is done so that exponential parts are always obtained.  
  R:=Parent(L);
  F:=BaseRing(R);  
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsDifferentialLaurentSeriesRing(F):
    "The operator must be defined over a differential Laurent series ring."; 
  require not HasZeroDerivation(R):
    "The derivation of the operator ring must be non-trivial."; 
  bl, Accuracy:= IsCoercible(Integers(), Precision);
  require bl and (Accuracy ge -1) and (Accuracy ne 0):
    "The set accuracy must be a positive integer."; 
  bl, precF := IsCoercible(Integers(), RelativePrecision(F));
  require bl and (precF ge 1):
    "The precision of the differential series ring should be integral", 
    " and positive.";
  require not IsWeaklyEqual(L,R!0):
    "The operator is weakly equal to 0."; 
  vprint LocalFactorisation, 2:"Factorisation is with respect to weak equality.";
  if IsWeaklyEqual(L ,R!1) then
    // return [[R| R!1,L]];
    return [[R|AddRelOrderTermToOperator(R!1,precF),
               AddRelOrderTermToOperator(L,precF) ]];
  end if;
  require IsWeaklyMonic(L):
    "The differential operator should be weakly monic.";
  require HasProjectiveDerivation(R):
    "The derivation is not of the standard form t*d/dt."; 
  if HasProjectiveDerivation(R) then  
    // minvalscoefs := (minvals cmpeq Infinity()) select 0 else
    //                 Minimum(minvals,0) where minvals:=MinOfValsOfCoefs(L);
    if Accuracy lt 0 then 
      accL := precF;
      "Ring precision as default precision taken.";
    else  
      accL := Accuracy;
    end if;
    // "Extending precision with:", -minvalscoefs;
    // accL := accL -minvalscoefs; 
    return FactorisationForStandardScaledOperator(L,accL,Algorithm,false);
  else
    // If L has a derivation that is not t*d/dt then
    // we do not want lost of precision of 
    // the series we get by moving forward and backward.
    // In other words we need a correct implementation for that.
    // To ensure that order terms do not decrease the precision
    // require the following.
    "WARNING: Non standard derivation for series ring detected.",
    " Code is not guaranteed to be correct.";
    require not LossInPrecisionInFactorisation(L):
      "The precision in the leading coefficient or in the derivation is",
      "too small.";
    sL, mptostandard:= Localization(L);
    standardL:=MonicDifferentialOperator(sL);  
    factors, areirreducible := 
      $$(standardL:Precision:=Accuracy, Algorithm := Algorithm);
    factors:=[  [R|v[1]@@mptostandard,v[2]@@mptostandard] : v in factors ];
    seqfactors:=[[R|MonicDifferentialOperator(v[1]*LeadingCoefficient(v[2])),
                    MonicDifferentialOperator(v[2])]: v in factors]; 
    return seqfactors, areirreducible;
  end if;
end intrinsic;

// ok



/////////////////////////////////////////////////////////////////////////
