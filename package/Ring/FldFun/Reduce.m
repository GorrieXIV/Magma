freeze;


intrinsic Reduce(M::Mtrx) -> Mtrx, Mtrx
  {}

  k := CoefficientRing(M);
  if Type(k) eq FldFunRat then
    den := Lcm([Denominator(x) : x in Eltseq(M)]);
    k_orig := k;
    k := Parent(den);
    M := Matrix(k, den*M);
  end if;
  require Type(k) eq RngUPol :
    "Matrix must be over a rational function field or a univariate polynomial ring";

  function RowDeg(x) 
    return Maximum([Degree(y) : y in Eltseq(x)]);
  end function;
  function CoefAt(x, d)
    return Vector([Coefficient(y, d) : y in Eltseq(x)]);
  end function;

  T := IdentityMatrix(k, Nrows(M));
  repeat
    d := func<|[RowDeg(M[i]) : i in [1..Nrows(M)]]>();
    m := func<|Matrix([CoefAt(M[i], d[i]) : i in [1..Nrows(M)]])>();
    n := NullspaceMatrix(m);
//    "M:", M, "d:", d, "m:", m, "m:", n;
    for j in [1..Minimum(Nrows(n), 1)] do
//      "doing ", j, ":", n[j];
      s := func<|[i : i in [1..Nrows(m)] | n[j][i] ne 0]>();
      mx, p := Maximum([d[ss] : ss in s]);
      p := s[p];
//      "mx:", mx, p;
      for ss in s do
        if ss ne p then
          AddRow(~M, n[j][ss]/n[j][p]*k.1^(mx-d[ss]), ss, p);
          AddRow(~T, n[j][ss]/n[j][p]*k.1^(mx-d[ss]), ss, p);
        end if;
      end for;
    end for;
//    "M now:", M;
  until Nrows(n) eq 0;
  if assigned k_orig then
    M := Matrix(k_orig, M)/den;
  end if;
  return M, T;
end intrinsic;

intrinsic ReconstructionEnvironment(p::RngFunOrdIdl, k::RngIntElt) -> SetEnum
  {}
  pk := p^k;  
  b := BasisMatrix(pk);
  b, t := Reduce(b);
  bi := Matrix(FieldOfFractions(CoefficientRing(b)), b)^-1;
  ba := [elt<Order(p)|Eltseq(b[i])> : i in [1..Nrows(b)]];
  AddAttribute(SetEnum, "RecoEnv");
  s := {1};
  s`RecoEnv := rec<recformat<p, k, b, t, bi, pk, ba>|
                          p := p,
                          k := k,
                          pk := pk,
                          b := b,
                          bi := bi,  
                          ba := ba,  
                          t := t>;  
  return s;                        
end intrinsic;    

intrinsic Reconstruct(x::RngFunOrdElt, R::SetEnum:UseDenominator := false) -> RngOrdElt
  {}
  if UseDenominator then
    n := Degree(Parent(x));
    k := CoefficientRing(R`RecoEnv`b);
    M := HorizontalJoin(Matrix([[k|0] : i in [1..n]]), R`RecoEnv`b);
    M := VerticalJoin(Matrix([[k!1] cat ChangeUniverse(Eltseq(x), k)]), M);
    M := Reduce(M);
    t := Eltseq(M[1]);
    return elt<Parent(x)|t[2..#t]>/t[1];
  else
    X := Matrix([Eltseq(x)])*R`RecoEnv`bi;
    X := Eltseq(X);
    X := [(Numerator(x) mod Denominator(x))/Denominator(x) : x in Eltseq(X)];
    return &+ [X[i]*R`RecoEnv`ba[i] : i in [1..#X]]; 
  end if;
end intrinsic;

/*
 <example>
   Qt<t> := FunctionField(Q);
   Qty<y> := PolynomialRing(Qt);
   F<a> := FunctionField(y^2-2*t^3);
   MF := MaximalOrderFinite(F);
   MI := MaximalOrderInfinite(F);
   Support(Divisor(a+t+2));
   P := $1[2];
   p := Ideal(P);
   
   R := ReconstructionEnvironment(p, 5);
   R`RecoEnv`pk;
   pk := $1;
   (2*a+t) mod pk;
   z := $1;
   MF!z;
   Reconstruct($1, R);

   R := ReconstructionEnvironment(p, 10);
   pk := R`RecoEnv`pk;
   Minimum(pk);
   _, _, i := Xgcd($1, Qx.1+1);
   ((2*a+t)*i) mod pk;
   zz := MF!$1;
   Reconstruct(zz, R);
   Reconstruct(zz, R:UseDenominator);
   $1 eq ((2*a+t)/(t+1));
 </example>  
   */
