freeze;


////////////////////////////////////////////////////////////////////
//                                                                //
//                                                                //
//                       Pade' - Hermite forms                    //
//                                                                //
//                             Written by                         //
//                         Alexa van der Waall                    //
//                                                                //
//                            Last updated:                       //
//                            09 June 2009                        //
//                                                                //
//                                                                //
////////////////////////////////////////////////////////////////////



// OK
function IsPositiveInteger(p)
  // Output: True iff p is a positive integer
  if ISA(Type(p),RngIntElt) and (p ge 1) then
    return true;
  else 
    return false;
  end if;
end function;

// OK
function IsProperDistortion(seq,n)
  // Input: A sequence seq and postive integer n
  // Output: true iff seq is a distortion; i.e., 
  //         # seq = n, and
  //         the entries of seq can be coerced as an integer, and
  //         the entries of seq are non-negative.
  assert n ge 1;
  assert ISA(Type(n),RngIntElt);
  if (#seq eq n) and ISA(Type(Universe(seq)),RngInt) and 
    (Minimum(seq) ge 0) then
    return true;
  else
    return false;
  end if;
end function;


// OK
intrinsic MaximumDegree(f::SeqEnum:Distortion:=[]) -> RngIntElt
  {The degree of a sequence of polynomials or power series, defined
   as the maximum of the degrees of f[i]-Distortion[i]. 
   The value -infinity is returned in the case that f is weakly equal 
   to the zero-sequence.}
    // Based on : Harm Derksen - An algorithm to compute generalized
    //            Pade'-Hermite forms.
    // The value -1 for a zero-element is not a proper choice as 
    // -1 may be a proper highest exponent in a Laurent series.
  S := Universe(f);
  n := #f;
  require ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol):
    "The universe of the sequence must be a power series ring",
    "or a univariate polynomial ring.";
  require n ge 1:
    "The sequence must be non-empty.";
  dist := Distortion;
  if #dist eq 0 then
    dist := ZeroSequence(Integers(),n);
  else 
    require IsProperDistortion(dist,n):
      "The distortion must consist of non-negative integers and have",
      "the same length as the length of the first argument.";
  end if; 
  seq := [ <f[i],i> : i in [1..n]| not IsWeaklyZero(f[i])];
  if exists{v : v in seq} then
    return Maximum({Degree(v[1])-dist[v[2]] : v in seq});
  else 
    return -Infinity();
  end if;
end intrinsic; 

// OK
intrinsic TypeOfSequence(f::SeqEnum:Distortion:=[]) -> RngIntElt, RngIntElt
  {The type of a sequence; the highest index i such that the degree of the
   f[i] is (weakly) equal to the maximum of the degrees of all entries.}
    // Based on : Harm Derksen - An algorithm to compute generalized
    //            Pade'-Hermite forms.
    // A sequence P=[P1, P2,..., Pn] is of type i if the Weak Degree(Pi) is
    // equal to the MaximumDegree(P) and the weak degrees of P(i+1)...Pn are
    // less than the maximum degree of the entire sequence P.
  S := Universe(f);
  n := #f;
  require ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol):
    "The universe of the sequence must be a power series ring",
    "or a univariate polynomial ring.";  
  require n ge 1:
    "The sequence must be a non-empty.";
  dist := Distortion;
  if #dist eq 0 then
    dist := ZeroSequence(Integers(),n);
  else 
    require IsProperDistortion(dist,n):
      "The distortion must consist of non-negative integers and have",
      "the same length as the first argument has.";
  end if;     
  degf := MaximumDegree(f:Distortion := dist);
  if degf eq -Infinity() then
    return n, degf;
  end if;  
  seq := [ <f[i],i> : i in [1..n]| not IsWeaklyZero(f[i])];
  return Maximum({v[2]: v in seq | Degree(v[1])-dist[v[2]] eq degf}), degf; 
end intrinsic;

// OK
function SmallerThan(f, g, d)
    // {True iff f is smaller than g.}
    // Based on : Harm Derksen - An algorithm to compute generalized
    //            Pade'-Hermite forms.
    // Input: a sequence f of polynomials or power series, and
    //        a distortion sequence of integers.
    // Output: A boolean; true if f<g, otherwise false.
  S := Universe(f);
  n := #f;
  // requirements 
  error if not (ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol)),
     "The universe of the sequences must be a power series ring",
     "or a univariate polynomial ring.";
  error if not Universe(g) eq S,
    "The first two arguments must have the same universe.";
  error if not ((n ge 1) and (n eq #g)),
    "The first two arguments must be non-empty and have the same lenghts.";
  dist := d;  
  if #dist eq 0 then
    dist := ZeroSequence(Integers(),n);
  else 
    error if not IsProperDistortion(dist,n),
      "The distortion must consist of non-negative integers and have",
      "the same length as the first two arguments have.";
  end if;      
  degf := MaximumDegree(f:Distortion:=dist);
  degg := MaximumDegree(g:Distortion:=dist);
    // If the distortion is a sequence of one and the same integer then
    // comparing degrees with distortion gives the same outcome as comparing
    // without.
    // The same is true for the types.
  if degf lt degg then
    return true;
  elif degf gt degg then
    return false;
  elif TypeOfSequence(f:Distortion:=dist) lt 
       TypeOfSequence(g:Distortion:=dist) then
    return true;
  else
    return false;
  end if;
end function;

// OK
function PrecisionForMinimalVectorSeq(f)
  // Input: A sequence f with power series entries.
  // Output: The minimal precision needed. 
  S := Universe(f);
  assert ISA(Type(S),RngSerPow);
  prec := [AbsolutePrecision(v):v in f|not AbsolutePrecision(v) eq Infinity()];
  relprecS := RelativePrecision(1/(1+S.1));
  if exists{r: r in prec} then
    return Minimum(Minimum(prec),relprecS);
  else 
    return relprecS;
  end if;
end function;

// OK
function PowerMap(S,p)
  // Input: A power series ring or polynomial ring S and positive integer p.
  // Output: The map on S induced by sending (S.1) to (S.1)^p.
  assert ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol);
  assert IsPositiveInteger(p);
  if ISA(Type(S), RngUPol) then
    mp :=  map<S->S| x :-> IsZero(x) select 0 else
                     &+([Coefficient(x,i)*(S.1)^(p*i) :  i in Exponents(x)])>;
  else
    mp :=  map<S->S| x :-> (IsWeaklyZero(x) select 0 else
                        &+([Coefficient(x,i)*(S.1)^(p*i) :  i in Exponents(x)]))
		      + (ISA(Type(v),RngIntElt) select O((S.1)^(p*v)) 
		        else S!0 where v := AbsolutePrecision(x))>;
  end if;
  return mp; 
end function;

// OK
intrinsic MinimalVectorSequence(f::SeqEnum, m::RngIntElt:
                                  Distortion:=[],Power :=1) -> SeqEnum                           
  {A minimal sequence of sequences Q1, Q2, .. Qn with respect to
   the sequence f of polynomials or power series with 
   n entries. The order of the inproduct of each Qi with 
   f is at least m.}
    //
    // -> SeqEnum, SeqEnum for if one wants to know the history of finding the
    //    Qsequence.
    //    then activate the proper returns by adding "bases" below as 
    //    the second argument returned.
    //
    // Based on : Harm Derksen - An algorithm to compute generalized
    //            Pade'-Hermite forms.
    //            Bernhard Beckermann and George Labahn - A uniform approach
    //            for the fast computation of matrix-type Pade' approximants.
    // Note: If the distortion is a sequence of one and the same integer then
    // comparing sequences with distortion gives the same outcome as 
    // comparing without.
    // Qi is a a non-trivial vecor with minimal degree of type i. 
  S := Universe(f);
  n := #f;
  p := Power;  
  dist := Distortion;
  require n ge 1:
    "The first argument must be a non-empty sequence.";
  require m ge 0:
    "The second argument must be non-negative.";
  require IsPositiveInteger(p):
    "The assigned power must be a positive integer.";  
  if #dist eq 0 then
    dist := ZeroSequence(Integers(),n);
  else 
    require IsProperDistortion(dist,n):
      "The distortion must consist of non-negative integers and have",
      "the same length as the first argument has.";
  end if;  
  require ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol):
    "The universe of the first argument must be a power series ring",
    "or a univariate polynomial ring.";  
  if ISA(Type(S),RngSerPow) then
    require m le PrecisionForMinimalVectorSeq(f):
      "The second argument exceeds the relative ring precision or the",
      "absolute precision of one of the entries in the first argument.";
  end if;
  Qsequence := [];
  for i in [1..n] do
    Q := ZeroSequence(S,i-1) cat [S|1] cat ZeroSequence(S, n-i);
    Append(~Qsequence, Vector(Q));
  end for; 
  // Define a sequence that will store the history of finding the Qsequence.
  bases :=[Qsequence];
  if m eq 0 then
    return Qsequence;
    // return Qsequence, bases;
  end if;
  powermap := PowerMap(S,p);	     
  for k in [1..m] do   
    // k=j+1, where j is as in Derksen's article.
    sums := [&+([powermap(Q[i])*f[i]: i in [1..n]]) : Q in Qsequence];
    vals := [Valuation(sum) : sum in sums];
    minvals := Integers()!(Minimum(vals));
    if minvals lt k then
      assert minvals eq k-1;
      indices :=Indices(vals, minvals);
      lowestindex := indices[1];
      Q := Qsequence[lowestindex];
      for l in Exclude(indices,lowestindex) do
        Ql := Qsequence[l];
        if SmallerThan(Eltseq(Ql),Eltseq(Q), dist) then
	  lowestindex := l;
	  Q := Ql;
        end if;
      end for;
        // The choice of Q with respect to the ordering comes from Derksens
	// article. The other article does not really use an ordening,
	// but works as well for getting a basis.
        // The lowestindex is called i in Derksen's article.
      mu := Coefficient(sums[lowestindex],minvals);
      Q := 1/mu*Qsequence[lowestindex];
      Qsequence[lowestindex] := Q;
      for l in Exclude(indices,lowestindex) do
        // l is called k in Derksen's algorithm.
        lambda := Coefficient(sums[l], minvals);
	Ql := [Ql[i]-lambda*Q[i]: i in [1..n]] where Ql := Qsequence[l];
	Qsequence[l] := Vector(Ql);
      end for;
      Qsequence[lowestindex] := (S.1)*Q;
    end if;  
    Append(~bases,Qsequence);
  end for;
  return Qsequence;
  // return Qsequence, bases;
end intrinsic;   

// OK
// This is the general one.
intrinsic PadeHermiteApproximant(f::SeqEnum, d::SeqEnum: Power := 1) -> 
  ModTupRngElt, SeqEnum, RngIntElt
  {Returns a Pade'-Hermite form of type d, smallest with respect
  to the degree on sequences, and the correspondig minimal vector sequence.
  The third argument returned gives the order in the order term.}
    // Based on : Harm Derksen - An algorithm to compute generalized
    //            Pade'-Hermite forms.
  S := Universe(f);
  n := #f;
  p := Power;
  dist := d;
  require n ge 1:
    "The first argument must be a non-empty sequence.";
  require IsPositiveInteger(p):
    "The assigned power must be a positive integer.";    
  require IsProperDistortion(dist,n):
    "The second sequence must consist of postive integers and have",
    "the same length as the first sequence.";    
  require ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol):
    "The universe of the first sequence must be a power series ring",
    "or a univariate polynomial ring."; 
  m := &+(dist)+n-1;
    // Then there is at least one non-zero solution (solution space is
    // at least 1-dimensional. 
  if ISA(Type(S),RngSerPow) then
    require m le PrecisionForMinimalVectorSeq(f):
      "The exponent of the order term exceeds the relative ring precision",
      "or the absolute precision of one of the entries in the first argument.";
  end if;
  basis := MinimalVectorSequence(f, m:Distortion:=dist,Power:=p);
  assert #basis eq n;
  Qp := basis[1];
  for Qk in Exclude(basis,Qp) do
    // if SmallerThan(Eltseq(Qk), Eltseq(Qp), dist) then
    // (This works as well.)
    if MaximumDegree(Eltseq(Qk):Distortion := dist) lt
       MaximumDegree(Eltseq(Qp):Distortion := dist) then 
      Qp := Qk;
   end if;
  end for;
  return Qp, basis, m;
end intrinsic;   



// OK
// Specific case.
intrinsic PadeHermiteApproximant(f::SeqEnum, m::RngIntElt:Power:=1) -> 
  ModTupRngElt, SeqEnum
  {Returns a Pade'-Hermite form of minimal degree in the corresponding
   minimal vector sequence, such that its inproduct with f has order at least m.
  The second argument returned is the minimal vector sequence.}  
  S := Universe(f);
  n := #f;
  p := Power;
  require n ge 1:
    "The first argument must be a non-empty sequence.";
  require m ge 0:
    "The second argument must be a non-negative integer.";
  require IsPositiveInteger(p):
    "The assigned power must be a positive integer";
  if ISA(Type(S),ModTupRng) then
    require p eq 1:
      "The given power must be 1 if the first argument has vector entries.";
    B := BaseRing(S);
    require ISA(Type(B),RngSerPow) or ISA(Type(B), RngUPol):
      "The first argument must consist of vectors over a power series ring",
      "or a univariate polynomial ring.";
    lengths := {Integers()|NumberOfColumns(v): v in f};
    require #lengths eq 1:
      "All vectors in the first argument must have the same length.";
    s := Setseq(lengths)[1];
    require s ge 1:
      "All vectors in the first argument must be non-empty";
    vector := Vector([B.1^i: i in [0..s-1]]);
    vector := Transpose(Matrix(vector));
    newf := [(Vector([powermap(c):c in Eltseq(v)])*vector)[1]: v in f]
           where powermap := PowerMap(B,s);
    order := m*s;
    "Calculating the Pade'-Hermite approximant for the sequence", newf,
    "with order term",  order, "and power", s, ".";
    return $$(newf,order:Power:=s);    
  end if;
  require ISA(Type(S),RngSerPow) or ISA(Type(S), RngUPol):
    "The universe of the first argument must be a power series ring",
    "or a univariate polynomial ring.";
  if ISA(Type(S),RngSerPow) then
    require m le PrecisionForMinimalVectorSeq(f):
      "The order exponent exceeds the relative ring precision or the",
      "absolute precision of one of the entries in the sequence.";
  end if;
  basis := MinimalVectorSequence(f, m:Power:=p);
  assert #basis eq n;
  Qp := basis[1];
  for Qk in Exclude(basis,Qp) do
    // if SmallerThan(Eltseq(Qk), Eltseq(Qp), []) then 
    // (This should work as well.)
    if MaximumDegree(Eltseq(Qk)) lt MaximumDegree(Eltseq(Qp)) then    
      Qp := Qk;
    end if;
  end for;
  return Qp, basis;
end intrinsic;   



//////////////////////////////   END   ///////////////////////////
