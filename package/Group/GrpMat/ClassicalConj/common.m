freeze;


//==============================================================================
intrinsic DualPolynomial(f::RngUPolElt) -> RngUPolElt
{The dual of the polynomial f}
  eseq := Coefficients(f);
  require eseq[1] ne 0 : "Polynomial must have non-zero constant term";
  return eseq[1]^-1 * Parent(f)!Reverse(eseq);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic StarIrreduciblePolynomials( F::FldFin, d::RngIntElt ) -> SeqEnum
{All monic polynomials of degree d with no proper *-symmetric
 factors}

  P := PolynomialRing(F); t := P.1;

  monicIrreducibles := func< n |
    (n eq 1) select [ t - a : a in F | a ne 0 ]
    else Setseq(AllIrreduciblePolynomials(F,n)) >;

  hatPoly := function( g )
    R := RationalFunctionField( F ); x := R.1;
    return P!( x^Degree(g) * Evaluate( R!g, x + 1/x ) );
  end function;

  pols := {@ P | @};
  if d eq 1 then
    pols := {@ t + 1, t - 1 @};
  elif IsEven(d) then
    allhalf := monicIrreducibles(d div 2 );
    if d eq 2 and IsOdd(Characteristic(F)) then pols := {@ t^2 + 1 @}; end if;
    pols join:= {@ f : g in allhalf | IsIrreducible(f) where f is hatPoly(g) @}
       join {@ g*gstar : g in allhalf | g ne gstar where gstar is DualPolynomial(g) @};
  end if;
  return IndexedSetToSequence( pols );
end intrinsic;
//------------------------------------------------------------------------------

convert := function(partition)
  n := Max(partition);
  mults := [ 0 : i in [1..n] ];
  for lambda in partition do mults[lambda] +:= 1; end for;
  return [<i,mults[i]> : i in [1..n] | mults[i] ne 0 ];
end function;

allPartitions := func<d | [[convert(pi) : pi in Partitions(n)] : n in [1..d]] >;

addSignsSp := function(plist)
  slist := [];
  for pi in plist do
    if forall{ mu : mu in pi | IsEven(mu[1]) or IsEven(mu[2])} then
      ndx := { i : i in [1..#pi] | IsEven(pi[i][1]) };
      for S in Subsets(ndx) do
        lambda := pi;
        for i in S do
          mu := pi[i];
          lambda[i] := < -mu[1],mu[2] >;
        end for;
        Append(~slist,lambda);
      end for;
    end if;
  end for;
  return slist;
end function;

signedPartitionsSp := func< d | [ addSignsSp(pi) : pi in allPartitions(d) ] >;

primaryParts := function(pFact)
  P := Parent(pFact[1][1]);
  pols := [P|  ];
  parts := [];
  duals := [P| ];
  rows := [];
  j := 1;
  rownum := 0;
  for i := 1 to #pFact do
    f := pFact[i][1]; ndx := pFact[i][2];
    if f eq DualPolynomial(f) then
      if j eq 1 or pols[j-1] ne f then
        pols[j] := f;
        parts[j] := [];
        rows[j] := [];
        j +:= 1;
      end if;
      Append(~parts[j-1], ndx);
      r := j - 1;
    elif f notin duals then // skip if in duals
      h := DualPolynomial(f);
      if IsEmpty(duals) or h ne duals[#duals] then
        Append(~duals,h);
        pols[j] := h*f;
        parts[j] := [];
        rows[j] := [];
        j +:= 1;
      end if;
      Append(~parts[j-1], ndx);
      r := j - 1;
    else
      h := DualPolynomial(f);
      r := Index(pols,f*h);
    end if;
    m := Degree(f)*ndx;
    rows[r] cat:= [rownum + i : i in [1..m]];
    rownum +:= m;
  end for;
  return pols, parts, rows;
end function;

type1Companion := function(h)
  d := Degree(h);
  A := CompanionMatrix(h);
  Lambda := ZeroMatrix(BaseRing(h),d,d);
  for i := 1 to d do Lambda[i,d-i+1] := 1; end for;
  return DiagonalJoin(A,Lambda*Transpose(A^-1)*Lambda);
end function;

stdJordanBlock := function(n,a)
  D := ScalarMatrix(n,a);
  for i := 1 to n-1 do D[i,i+1] := 1; end for;
  return D;
end function;

centralJoin := function( A, B )
  d := Nrows(A);
  if d eq 0 then return B; end if;
  e := Nrows(B);
  if e eq 0 then return A; end if;
  assert IsEven(d);
  m := d div 2;
  X := ZeroMatrix(BaseRing(A),d+e,d+e);
  InsertBlock(~X, Submatrix(A, 1,1, m,m), 1,1);
  InsertBlock(~X, Submatrix(A, 1,m+1, m,m), 1,m+e+1);
  InsertBlock(~X, Submatrix(A, m+1,1, m,m), m+e+1,1);
  InsertBlock(~X, Submatrix(A, m+1,m+1, m,m), m+e+1,m+e+1);
  InsertBlock(~X, B, m+1,m+1);
  return X;
end function;

getSubIndices := function(pFact)
  f := pFact[1][1];
  error if exists{ p : p in pFact | p[1] ne f },
    "the component is not homocyclic";
  d := Degree(f);
  ndx := 0;
  base := [];
  last := 0;
  rng := [];
  for j := 1 to #pFact do
    if j gt 1 and pFact[j][2] ne last then
      Append(~base, rng);
      rng := [];
    end if;
    last := pFact[j][2];
    n := last*d;
    rng cat:= [ndx+i : i in [1..n]];
    ndx +:= n;
  end for;
  Append(~base,rng);
  return base;
end function;

restriction := func< M, S | Solution(T,T*M) where T is Matrix(S) >;

homocyclicSplit := function(g,W)
  U := Universe([ W, sub<W|> ]);
  _, T, pFact := PrimaryRationalForm(g);
  baseNdx := getSubIndices(pFact);
  W0 := sub< W | [T[i] : i in baseNdx[#baseNdx]] >;
  D := [U| W0 ];
  while W ne W0 do
    W0p := OrthogonalComplement(W,W0);
    gp := restriction(g,BasisMatrix(W0p));
    _, T, pFact := PrimaryRationalForm(gp);
    baseNdx := getSubIndices(pFact);
    W1 := sub< W | [T[i]*BasisMatrix(W0p) : i in baseNdx[#baseNdx]] >;
    Append(~D, W1);
    W0 := sub< W | W0, W1 >;
  end while;
  return Reverse(D);
end function;

