freeze;

/*
Miscellaneous LLL functions.
*/

intrinsic LLL(Q::[Mtrx]: Delta := 0.75, Sort := false, Proof) -> []
{Apply LLL to the matrices in the sequence Q}

    if #Q eq 0 then
	return 0;
    end if;

    B := Matrix([Eltseq(x): x in Q]);
    if 1 eq 1 then
	_, T := LLLGram(
	    B*Transpose(B): Delta := Delta, Sort := Sort, Proof := Proof
	);
	B := Matrix(BaseRing(Parent(B)), T)*B;
	delete T;
    else
	B := LLL(B: Delta := Delta, Sort := Sort, Proof := Proof);
    end if;

    if ISA(Type(Q[1]), ModTupRngElt) then
	return Rows(B);
    end if;

    nr := Nrows(Q[1]);
    nc := Ncols(Q[1]);
    return [Matrix(nr, nc, Eltseq(B[i])): i in [1 .. Nrows(B)]];
end intrinsic;

intrinsic QuickLLL(X::Mtrx: Delta := 0.75, UseGram := 0) -> Mtrx
{Quick LLL applied to matrix X (no proof, sort rows)}

    if UseGram cmpeq 0 and Ncols(X) gt 10*Nrows(X) then
	UseGram := true;
    end if;

    if UseGram cmpne 0 then
	//return LLL(X: Proof := false, InitialSort, Sort, UseGram := UseGram);
//time "Get Gram"; time
        F := X*Transpose(X);
//time "Do LLLGram";
	_, T := LLLGram(F: Proof := false, InitialSort, Sort);
	delete F;
//"Gram T:", Parent(T);
	return Matrix(BaseRing(Parent(X)), T)*X, T;
    else
	return LLL(X: Proof := false, InitialSort, Sort, Delta := Delta);
    end if;

end intrinsic;

intrinsic QuickLLLGram(F::Mtrx: Delta := 0.75) -> Mtrx
{Quick LLL applied to Gram matrix F (no proof, sort rows)}
    return LLLGram(F: Proof := false, InitialSort, Sort, Delta := Delta);
end intrinsic;

////////////////////////////////////////////////////////////////////////

function lindep(A,H,DELTA) n:=#A; m:=Max([Abs(a) : a in A]); H:=Ceiling(H);
 if m eq 0 then return Polynomial([1]); end if; A:=[a/m : a in A];
 M:=Matrix([[i eq j select 1 else 0 : i in [1..n]] cat
	      [H^n*Real(A[j]),H^n*Imaginary(A[j])] : j in [1..n]]);
 B,T:=LLL(M : Delta:=DELTA); return Eltseq(T[1]); end function;
// should this depend on real/complex? see also derived H below

intrinsic IntegerRelation
(A::SeqEnum[FldReElt],H::RngIntElt : Delta:=0.75) -> SeqEnum, FldReElt
{Given a sequence of real numbers and a height bound, return the best linear
 relation up to that height, using LLL with Delta}
 require #A ge 1: "A must have at least one element";
 require H ge 1: "H must be at least 1"; v:=lindep(A,H,Delta);
 return v,Abs(&+[A[i]*v[i] : i in [1..#A]]); end intrinsic;

intrinsic IntegerRelation
(A::SeqEnum[FldComElt],H::RngIntElt:Delta:=0.75) -> SeqEnum, FldReElt
{Given a sequence of complex numbers and a height bound,
 return the best linear relation up to that height, using LLL with Delta}
 require #A ge 1: "A must have at least one element";
 require H ge 1: "H must be at least 1"; v:=lindep(A,H,Delta);
 return v,Abs(&+[A[i]*v[i] : i in [1..#A]]); end intrinsic;

intrinsic IntegerRelation
(A::SeqEnum[FldReElt] : Delta:=0.75) -> SeqEnum, FldReElt
{Given a sequence of real numbers, return the best linear relation
 using the height bound from the precision (uses LLL with Delta)}
 require #A ge 1: "A must have at least one element";
 return lindep(A,10^(Precision(Universe(A))/#A),Delta); end intrinsic;

intrinsic IntegerRelation
(A::SeqEnum[FldComElt] : Delta:=0.75) -> SeqEnum, FldReElt
{Given a sequence of complex numbers, return the best linear relation
 using the height bound from the precision (uses LLL with Delta)}
 require #A ge 1: "A must have at least one element";
 return lindep(A,10^(Precision(Universe(A))/#A),Delta); end intrinsic;

function algdep(a,d,H,DELTA,exact,sqfree)
 if exact then A:=[a^i : i in [0..d]];
  f:=Polynomial(IntegerRelation(A,H : Delta:=DELTA));
  if sqfree then f:=&*[g[1] : g in Factorization(f)]; end if;
  if LeadingCoefficient(f) lt 0 then f:=-f; end if;
  return f,Abs(Evaluate(f,a)); end if; BEST:=1.0; Bf:=Polynomial([1]);
 for u in [1..d] do A:=[a^i : i in [0..u]]; // hmm, have H change with u?
  f:=Polynomial(IntegerRelation(A,H : Delta:=DELTA));
  FAC:=Factorization(f); if #FAC eq 0 then continue; end if;
  _,w:=Min([Abs(Evaluate(g[1],a)) : g in FAC]);
  f:=FAC[w][1]; ev:=Abs(Evaluate(f,a));
  if ev lt BEST then BEST:=ev; Bf:=f; end if; end for;
 if LeadingCoefficient(Bf) lt 0 then Bf:=-Bf; end if;
 return Bf,BEST; end function;

intrinsic MinimalPolynomial
(a::FldReElt,d::RngIntElt,H::RngIntElt :
 Delta:=0.75,ExactDegree:=false,Squarefree:=true) ->  RngUPolElt, FldReElt
{Given a real number, a (bound on the) degree and a height,
 compute the best minimal polynomial using LLL with Delta}
 require d ge 1: "The degree must be at least 1";
 return algdep(a,d,H,Delta,ExactDegree,Squarefree); end intrinsic;

intrinsic MinimalPolynomial
(a::FldComElt,d::RngIntElt,H::RngIntElt :
 Delta:=0.75,ExactDegree:=false,Squarefree:=true) ->  RngUPolElt, FldReElt
{Given a complex number, a (bound on the) degree and a height,
 compute the best minimal polynomial using LLL with Delta}
 require d ge 1: "The degree must be at least 1";
 return algdep(a,d,H,Delta,ExactDegree,Squarefree); end intrinsic;

intrinsic MinimalPolynomial
(a::FldReElt,d::RngIntElt :
 Delta:=0.75,ExactDegree:=false,Squarefree:=true) -> RngUPolElt, FldReElt
{Given a real number, a (bound on the) degree,
 compute the best minimal polynomial using LLL with Delta,
 and taking the height from the precision of a}
 require d ge 1: "The degree must be at least 1";
 require d le 1000: "Degrees greater than 1000 are not practical";
 H:=Ceiling(10.0^(Precision(a)/(d+1)));
 return algdep(a,d,H,Delta,ExactDegree,Squarefree); end intrinsic;

intrinsic MinimalPolynomial
(a::FldComElt,d::RngIntElt :
 Delta:=0.75,ExactDegree:=false,Squarefree:=true) -> RngUPolElt, FldReElt
{Given a real number, a (bound on the) degree,
 compute the best minimal polynomial using LLL with Delta,
 and taking the height from the precision of a}
 require d ge 1: "The degree must be at least 1";
 require d le 1000: "Degrees greater than 1000 are not practical";
 H:=Ceiling(10.0^(Precision(a)/(d+1)));
 return algdep(a,d,H,Delta,ExactDegree,Squarefree); end intrinsic;

// could do alpha -> 1/alpha and reverse the poly in some cases
