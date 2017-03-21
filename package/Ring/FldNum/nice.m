freeze;

debug := false;

procedure CheckElement(elt,n)
  x,ff,c := Explode(elt);
  LL := Parent(x);
  OL := RingOfIntegers(LL);
  J := &*[PowerIdeal(LL)|f[1]^f[2]: f in ff];
  C := &*[PowerIdeal(LL)|f[1]^f[2]: f in c];
  assert x*OL eq J*C^n;
end procedure;   

function CreateElement(tup,n)
  x,e,ff := Explode(tup);
  gg := [<f[1], (e*f[2]) mod n> : f in ff | (e*f[2]) mod n ne 0];
  cc := [<f[1], (e*f[2]) div n> : f in ff | (e*f[2]) div n ne 0];
  xx := x^e;
  if debug then CheckElement(<xx,gg,cc>, n); end if;
  return <xx,gg,cc>;
end function;

function MultiplyFactorizations(ff1,ff2)
  ff := ff1;
  for j in [1..#ff2] do
    if exists(i){i : i in [1..#ff] | ff[i][1] eq ff2[j][1]} then
      ff[i][2] +:= ff2[j][2];
    else
      Append(~ff,ff2[j]);
    end if;
  end for;
  return ff;
end function;

function MultiplyElements(elt1,elt2,n)
  x1,ff1,c1 := Explode(elt1);
  x2,ff2,c2 := Explode(elt2);
  xx := x1*x2;
  ff := MultiplyFactorizations(ff1,ff2);
  gg := [<f[1],f[2] mod n> : f in ff | f[2] mod n ne 0];
  cc := c1 cat c2;
  ee := [f[2] div n : f in ff];
  if exists{e: e in ee | e ne 0} then
    cc cat:= [<ff[i][1], ee[i]> : i in [1..#ff] | ee[i] ne 0];
  end if;
  if debug then CheckElement(<xx,gg,cc>, n); end if;
  return <xx,gg,cc>;
end function;

function consolidate(c)
  if #c eq 0 then
    return c;
  end if;
  inds := {};
  cc := [];
  for i := 1 to #c do 
    if i in inds then continue; end if;
    Include(~inds, i);
    t1, t2 := Explode(c[i]);
    for j := i+1 to #c do 
      if t1 eq c[j][1] then // tested IsIdentical, slower overall
        Include(~inds, j);
        t2 +:= c[j][2];
      end if;
    end for;
    Append(~cc, <t1,t2>);
  end for;
  if debug then assert &*[t[1]^t[2] : t in c] eq &*[t[1]^t[2] : t in cc]; end if;
  return cc;
end function;

function TidyUpElement(elt,n : effort:=1);
  alpha,ff,c := Explode(elt);
  LL := Parent(alpha);
  OL := RingOfIntegers(LL);
  c := consolidate(c);
  ci := &*[PowerIdeal(LL)| t[1]^t[2] : t in c];
  aa,r := NiceRepresentativeModuloPowers(alpha,n : FracIdeal:=ci^-1, Effort:=effort);
  cc := [<ci,1>, <r*OL,1>];
  if debug then 
    assert aa eq alpha*r^n;
    CheckElement(<aa,ff,cc>,n); 
  end if;
  return <aa,ff,cc>;
end function;

function MultiplyOutModPowers(v, B, Bfact, n)
  BIG := 10000;
  ff := [<B[i],v[i],Bfact[i]> : i in [1..#B] | v[i] ne 0];
  xx := CreateElement(ff[1],n);
  for j in [2..#ff] do
    elt := CreateElement(ff[j],n);
    xx := MultiplyElements(xx,elt,n);
    if j lt #ff then
      size := Ilog(10,Maximum([Abs(Numerator(x)): x in Eltseq(xx[1])]));
      if size gt BIG then
        // if it looks bad, use stronger reduction that controls infinite places
        e := (size ge 2*BIG) select 1 else 0;
        xx := TidyUpElement(xx,n : effort:=e);
      end if;
    end if;
  end for;
  e := (#ff le 2 or size le BIG) select 0 else 1;
  xx := TidyUpElement(xx,n : effort:=e);
  return xx;
end function;

intrinsic NiceRepresentativesModuloPowers(E::Mtrx, B::SeqEnum, p::RngIntElt : Primes:=0) -> SeqEnum
{Representatives in K^*/(K^*)^p for elements given in 'Raw' format
 (as rows of the exponent matrix E, relative to the factor base B).
 The returned elements generate the same subgroup of K^*/(K^*)^p as 
 the given elements}

  require Ncols(E) eq #B : "Arguments have incompatible lengths";

  require IsPrime(p) : "The third argument should be a prime";

  OL := Integers(Universe(B));
  L := NumberField(OL);
  LL := FieldOfFractions(OL);
  ChangeUniverse(~B, LL);

  if ISA(Type(E), ModTupRngElt) then 
    E := Matrix(E); 
  end if;
  m := Nrows(E);
  n := Ncols(E);

  // make sure trivial cases are handled
  if m eq 0 or IsZero(E) then
    return [L| 1];
  end if;

  vecs := [[E[i,j] mod p : j in [1..n]] : i in [1..m]];
  if p eq 2 then
    // This LLL finds a sparse basis, to minimise the number of products.
    // That's more important here than making the power-products small
    // (which we could do with a weighted LLL, weighting primes by log|NP|.)
    mat2 := VerticalJoin(Matrix(vecs), p*IdentityMatrix(Integers(),n));
    mat3 := LLL(mat2);
    V := VectorSpace(GF(p),n);
    W := sub<V|>;
    vecs := [];
    for i in [1..n] do
      a := mat3[i];
      Include(~W, V!a, ~new);
      if new then
        Append(~vecs, [x mod p : x in Eltseq(a)]);
      end if;
      if #vecs eq m then break; end if;
    end for;
  end if;
  // TO DO: for p > 2, find short vector (in coset mod p) for each element

  Bfact := [* 0 : b in B *];
  inds := [i : i in [1..#B] | exists{v: v in vecs | v[i] ne 0}];
  if Primes cmpeq 0 then
    for i in inds do 
      Bfact[i] := Factorization(B[i]*OL);
    end for;
  else
    for i in inds do 
      Bi := B[i];
      Bfact[i] := [];
      for P in Primes do
        v := Valuation(Bi,P);
        if v ne 0 then
          Append(~Bfact[i], <P,v>);
        end if;
      end for;
      if debug then assert Seqset(Bfact[i]) eq Seqset(Factorization(B[i]*OL)); end if;
    end for;
  end if;

  ans := [L| ];
  for s in vecs do
    xx := MultiplyOutModPowers(s, B, Bfact, p);
    vprint NiceReps: "Product =", xx[1];
    Append(~ans, xx[1]);
  end for;

  assert not IsEmpty(ans);
  return ans;
end intrinsic;
  
