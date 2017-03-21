freeze;

AddAttribute(CodeQuantum,"StabilizerCode");
AddAttribute(CodeQuantum,"NormalizerCode");

intrinsic ShortenCode(C::CodeQuantum,v::ModTupFldElt)->CodeQuantum
{If possible, shorten the quantum code C=[[n,k,d]] at the positions specified by the complement of the support S of v, yielding a quantum code [[n-s,k'>=k-s,d'>=d]] where s:=n-#S}

  require Length(C) eq #Eltseq(v):"The code and the vector must have the same length";

  G:=StabilizerMatrix(C:ExtendedFormat);
  for i:=1 to Length(C) do
    MultiplyColumn(~G,v[i],i);
  end for; 
  S:={1..Length(C)} diff Support(v);
  stab1:=PunctureCode(QuantumCompactFormat(AdditiveCode(CoefficientRing(C),G)),S);
  if IsSymplecticSelfOrthogonal(stab1) then
    return QuantumCode(stab1);
  else
    error Sprintf("Shortening at the positions in %o not possible",S);
  end if;
end intrinsic;


intrinsic QuantumCode(C::CodeAdd,v::ModTupFldElt)->CodeQuantum
{If possible, shorten the quantum code C=[[n,k,d]] at the positions specified by the complement of the support S of v, yielding a quantum code [[n-s,k'>=k-s,d'>=d]] where s:=n-#S}

  require Length(C) eq #Eltseq(v):"The code and the vector must have the same length";

  G:=GeneratorMatrix(QuantumExtendedFormat(C));
  for i:=1 to Length(C) do
    MultiplyColumn(~G,v[i],i);
  end for; 
  S:={1..Length(C)} diff Support(v);
  stab1:=PunctureCode(QuantumCompactFormat(AdditiveCode(CoefficientRing(C),G)),S);
  if IsSymplecticSelfOrthogonal(stab1) then
    return QuantumCode(stab1);
  else
    error Sprintf("Shortening at the positions in %o not possible",S);
  end if;
end intrinsic;

intrinsic IsPureQuantumCode(C::CodeQuantum)->BoolElt
{True iff the symplectic dual of the stabilizer code S of C contains a word of minimum weight that is not contained in S or the dimension C is zero}

  if Dimension(C) eq 0 then
    return true;
  end if;

  S:=StabilizerCode(C);
  if not assigned C`StabilizerCode then
    C`StabilizerCode:=S;
  end if;

  N:=SymplecticDual(S);
  if not assigned C`NormalizerCode then
    C`NormalizerCode:=N;
  end if;


  if S`MinimumWeightLowerBound gt N`MinimumWeightUpperBound then
//"Fall 1";
    return true;
  elif assigned S`MinimumWeight and VerifyMinimumWeightUpperBound(N,S`MinimumWeight-1) then
//"Fall 2";
    return true;
  else
    //bug in MinimumWeight
    if assigned C`MinimumWeight then
      d:=C`MinimumWeight;
    else
      d:=MinimumWeight(C);
    end if;
    if not VerifyMinimumWeightUpperBound(S,d-1) then
//"Fall 3";
    return true;
    else
//"Fall 4";
//S,N,d;
      return false; //check!
    end if;
  end if;
end intrinsic;

intrinsic ShortenStabilizerCode(C::CodeQuantum,i::RngIntElt)->CodeQuantum
{If C is a pure quantum code [[n,k,d]] with n>1, n>k, return a quantum code [n-1,k'>=k+1,d'>=d-1]]}
  n:=Length(C);
  k:=Dimension(C);

  require n gt 1: "The dimension of the code must be greater than one";
  require n gt k: "The length of the code must be greater than its dimension";

  require IsPureQuantumCode(C): "C must be a pure quantum code";

  stab:=StabilizerCode(C);
  stab1:=ShortenCode(stab,i);
  C1:=QuantumCode(stab1);

  return C1;
end intrinsic;

intrinsic ShortenStabilizerCode(C::CodeQuantum,S::{RngIntElt})->CodeQuantum
{If C is a pure quantum code [[n,k,d]] with n>1, n>k, return a quantum code [n-s,k'>=k+s,d'>=d-s]] wher s:=#S}

  require IsPureQuantumCode(C): "C must be a pure quantum code";


  stab:=StabilizerCode(C);
  if not assigned C`StabilizerCode then
    C`StabilizerCode:=stab;
  end if;

  N:=SymplecticDual(stab);
  if not assigned C`NormalizerCode then
    C`NormalizerCode:=N;
  end if;

  stab1:=ShortenCode(stab,S);
  C1:=QuantumCode(stab1);

  return C1;
end intrinsic;

intrinsic QECCLowerBound(Q::CodeQuantum)->RngIntElt
{}
  return QECCLowerBound(Alphabet(Q),Length(Q),Dimension(Q));
end intrinsic;

intrinsic QECCUpperBound(Q::CodeQuantum)->RngIntElt
{}
  return QECCLowerBound(Alphabet(Q),Length(Q),Dimension(Q));
end intrinsic;


intrinsic QuantumTwistedCode(F::FldFin,n::RngIntElt,A::[RngIntElt],kappa::RngIntElt)->CodeQuantum
{The quantum twisted code over F of length n with defining interval A and parameter kappa (see Bierbrauer and Edel).}

/*
  Juergen Bierbrauer, Yves Edel
  "Quantum twisted codes"
  Journal of Combinatorial Designs
  Volume 8, Issue 3, 2000, pp. 174-188.

*/

  require IsEven(Degree(F)): "Field in not a degree 2 extension";

  F2:=GF(Characteristic(F),Degree(F) div 2);
  gamma0:=Basis(F,F2)[2];

  if IsOdd(n) then
    m:=n;
  else
    m:=n-1;
  end if;

  e:=RootOfUnity(m,F2);
  W:=[e^i: i in [0..m-1]];
  Fe:=Parent(e);
  alpha:=[x^j:j in [0..Degree(Fe)-1]] where x:=PrimitiveElement(Fe);
  alpha:=Basis(Fe);
  gamma:=RootOfUnity(2^kappa-1,Fe);
  B:=KMatrixSpace(Fe,#alpha*#A,m)![a*x^i: x in W,i in A,a in alpha];
  B2:=KMatrixSpace(F,Nrows(B),m)![Trace(x,F2)+gamma0*Trace(gamma*x,F2): x in Eltseq(B)];

  if IsOdd(n) then
    return QuantumCode(B2);
  else
    B0:=KMatrixSpace(Fe,#alpha,m)![a: x in W,a in alpha];
    B20:=KMatrixSpace(F,Nrows(B0),m)![Trace(x,F2)+gamma0*Trace(gamma*x,F2): x in Eltseq(B0)];

    c2:=PadCode(AdditiveCode(F2,B2),1);
    c0:=LinearCode(B20);
    c0:=AdditiveCode(F2,ConstructionX(c0,sub<c0|>,LinearCode<F,1|[-&+Eltseq(c0.1)]>));

    return QuantumCode(c0+c2);
  end if;
end intrinsic;

intrinsic 'subset'(Q1::CodeQuantum,Q2::CodeQuantum)->BoolElt
{True if the quantum code Q1 is contained in Q2}
printf "in 'subset'\n";

  require Length(Q1) eq Length(Q2) and Alphabet(Q1) eq Alphabet(Q2): "Arguments are not compatible";

  fl:=StabilizerCode(Q2) subset StabilizerCode(Q1);

  if fl and Dimension(Q2) gt 0 then
    Q1`MinimumWeightLowerBound:=Q2`MinimumWeightLowerBound;
  end if;

  return fl;

end intrinsic;

intrinsic StandardLengthening(Q::CodeQuantum)->CodeQuantum
{}
  stab:=StabilizerCode(Q);
  norm:=NormalizerCode(Q);

  F:=Alphabet(stab);
  F2:=CoefficientRing(stab);

  rep:=RepetitionCode(F,Length(stab));
  rep_add:=AdditiveCode(F2,rep);
  
  require rep_add subset norm and &+Eltseq(rep.1) ne 0:
    "The code cannot be lengthened";

  c0:=AdditiveCode(F2,ConstructionX(rep,sub<rep|>,LinearCode<F,1|[-&+Eltseq(rep.1)]>));
  

  return QuantumCode(PadCode(stab,1)+c0);
end intrinsic;


intrinsic AdditiveConstaCyclicCode(F::FldFin, n::RngIntElt, f::RngUPolElt, c::FldFinElt) -> CodeAdd
{Return the length n additive code over F generated by consta-cyclic shifts by c of the coefficients
of f};

//check for c in the right field, (with f) and n being longer than f
    FE := BaseRing(f);
    require Type(FE) eq FldFin : "f must be over a finite field";
    require Characteristic(F) eq Characteristic(FE) and F subset FE: "wrong coefficient field F"; 
    require Parent(c) eq FE: "f must be over the same finite field as c";

	//reduce f mod x^n - c
    f mod:= (Parent(f).1)^n - c;
 
    coeffs := Coefficients(f);
    coeffs cat:= [0 : i in [1.. n - #coeffs]];
        //cyclic shifter
    gen := Matrix(FE,1,n,coeffs);
 
    newcoeffs := coeffs;
    repeat
        newcoeffs := [c*newcoeffs[n]] cat newcoeffs[1..n-1];
        gen := VerticalJoin(gen,Matrix(FE,1,n,newcoeffs));
    until newcoeffs eq coeffs;
 
    return AdditiveCode(F,gen);
 
end intrinsic;


//------------------ quasi twisted codes ------------------------------//

poly_to_vec:=function(p,V);
// converts the coefficients of the polynomial p into a vector in V,
// appending zeroes
  n:=Degree(V);
  v:=Eltseq(p mod (Parent(p).1^n-1));
  return V!(v cat [0:i in [#v+1..n]]);
end function;

intrinsic AdditiveQuasiTwistedCyclicCode(F::FldFin,n::RngIntElt,Gen::[RngUPolElt],alpha::FldFinElt)->Code
{Construct the additive quasi-twisted cyclic code over F of length n pasting together the constacylic codes with parameter alpha generated by the polynomials in Gen.}

  require n mod #Gen eq 0 :
      "The length n must be a multiple of the number of generators";

  n0:=n div #Gen;
  F1:=CoefficientRing(Gen[1]);
  V:=KSpace(F1,n0);
  gen_vecs:=[poly_to_vec(g,V):g in Gen];

  return AdditiveQuasiTwistedCyclicCode(F1,gen_vecs,alpha);

end intrinsic;

intrinsic AdditiveQuasiTwistedCyclicCode(F::FldFin,Gen::[ModTupRngElt],alpha::FldFinElt)->Code
{Construct the additive quasi-twisted cyclic code over F generated by simultaneous 
constacylic shifts w.r.t. alpha of the vectors in Gen.}

  F1:=CoefficientRing(Universe(Gen));
  m:=Degree(Universe(Gen));
  p:=#Gen;
  N:=m*p;
  G:=KMatrixSpace(F1,m,N)!0;
  s:=MatrixRing(F1,m)!0;
  for i:=1 to m-1 do 
    s[i,i+1]:=1;
  end for;
  s[m,1]:=alpha;
  for i:=1 to p do
    v:=Gen[i];
    for j:=1 to m do
      InsertBlock(~G,KMatrixSpace(F1,1,m)!v,j,(i-1)*m+1);
      v:=v*s;
    end for;
  end for;

  return AdditiveCode(F,G);

end intrinsic;
