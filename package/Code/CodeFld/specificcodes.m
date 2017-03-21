freeze;

// Requires n to be prime????????????????
// if so should use p as prime and n as power of residue

//Damiens???

intrinsic PowerResidueCode(K::FldFin,n::RngIntElt,p::RngIntElt) -> Code
{Returns the p-th power residue code of length n, |K| must be a p-th power residue of n}
 
    Q := { Integers() | x^p : x in Integers(n) | x ne 0 };
    require #K in Q : "Order of argument 1 is not a p-th power residue of argument 2";
 
    P := PolynomialRing(K);
    L := SplittingField(P.1 ^ n - 1);
    PL := PolynomialRing(L);
    //require GCD(n,#L) gt 1 : "n must be co-prime to the order of the splitting field of x^n-1";
    alpha := RootOfUnity(n,L);
    g := P ! &*[PL.1 - alpha ^ i : i in Q];
    return CyclicCode(n,g);

end intrinsic;


/*------------- Cordaro-Wagner Code --------------------*/

//Damiens??

intrinsic CordaroWagnerCode(n::RngIntElt) -> Code
{Given an integer n, return the CordaroWagner code of length n}
 
  require n ge 2:"length of code must be 2 or more";
 
  // calculate the minumum distance
  r := Floor((n+1)/3);
  d := (2 * r - Floor( (n mod 3) / 2) );
 
  l1 := [ 0 : i in [1..r]];
  l2 := [ 1 : i in [r+1..n]];
 
  // together g1 and g2 form the rows of the Generator Matrix for C;
  g1 := l1 cat l2;
  g2 := l2 cat l1;
 
  //vprintf User1: "a [%o,2,%o] CordaroWagner linear code\n",n,d;
 
  return LinearCode<GF(2),n|g1,g2>;
 
end intrinsic;


//--------------DoublyCirculantQRCode------------------------------//

// conditions???? 2 a QR of p....

//Author: Markus Grassl


intrinsic DoublyCirculantQRCode(p::RngIntElt)->Code
{Construction of doubly circulant linear binary codes C=[2p,p] based
on quadratic residues modulo p. p must be a prime greater than 2}
/* SIMILAR to the constructions in
 
   M. Karlin, New binary coding results by circulants, IEEE Trans.
   Inform. Theory IT-15 (Jan. 1969) 81-92.
 
 
*/

    require p gt 2 : "p must be greater than 2";
    require IsPrime(p) : "p must be a prime";

  P := PolynomialRing(GF(2)); x := P.1;
  q:=1+&+[x^i: i in [0..p-1]|LegendreSymbol(i,p)eq 1];
  m:=x^p-1;
  A:=MatrixRing(GF(2),p)![Coefficient((x^i*q) mod m,j):i,j in [0..p-1]];
  G:=Zero(RMatrixSpace(GF(2),p,2*p));
  InsertBlock(~G,A^0,1,1);
  InsertBlock(~G,A,1,p+1);
  return LinearCode(G);
end intrinsic;



//--------------BorderedDoublyCirculantQRCode------------------------//
// Requires some conditions
// 2 must be a QR of p for starts... anything else???????

//Author: Markus Grassl

intrinsic BorderedDoublyCirculantQRCode(p::RngIntElt,a::RngElt,b::RngElt)->Code
{Construction of a bordered doubly circulant linear binary codes
C=[2p+1,p+1] based on quadratic residues modulo p. The first p rows
are extended by a, the last row by b. p must be a prime greater than 2.}
 
/* SIMILAR to the constructions in
 
   M. Karlin, New binary coding results by circulants, IEEE Trans.
   Inform. Theory IT-15 (Jan. 1969) 81-92.
 
 
*/

    require p gt 2: "p must be greater than 2";
    require IsPrime(p) : "p must be prime";
 
  P := PolynomialRing(GF(2)); x := P.1;
  q:=1+&+[x^i: i in [0..p-1]|LegendreSymbol(i,p)eq 1];
  m:=x^p-1;
  A:=MatrixRing(GF(2),p)![Coefficient((x^i*q) mod m,j):i,j in [0..p-1]];
  G:=Zero(RMatrixSpace(GF(2),p+1,2*p+1));
  InsertBlock(~G,A^0,1,1);
  InsertBlock(~G,A,1,p+1);
  for i:=p+1 to 2*p do
    G[p+1,i]:=1;
  end for;
  for i:=1 to p do
    G[i,2*p+1]:=a;
  end for;
  G[p+1,2*p+1]:=b;
  return LinearCode(G);
end intrinsic;


//---------------------TwistedQRCode---------------------------//

//Conditions???? 2 a QR of anything??
//Author: Markus Grassl

intrinsic TwistedQRCode(l::RngIntElt,m::RngIntElt)->Code
{Construct a binary "twisted QR" code of length l*m. Requires that
l*m must be coprime to 2}
/* see
   Cunsheng Ding, San Ling, and David R. Kohel.
   Split group codes.
   IEEE Transactions on Information Theory, vol. IT-40, no. 2,
   March 2000, pp. 485-495.
*/

    require l gt 0 : "l must be positive";
    require m gt 0 : "m must be positive";
    require GCD(l*m,2) eq 1 : "l*m and 2 not coprime";
 
  n:=l*m;
  R:={0..n-1};
  Ru:={a: a in R|GCD(a,n) eq 1};
  lR:={l*x mod n: x in Ru};
  Z:={m*a: a in {0..l-1}};
  X0:={a: a in Ru|KroneckerSymbol(a,m) eq 1} join
      {a: a in lR|KroneckerSymbol(a,m) eq -1};
  a:=RootOfUnity(n,GF(2));
  K:=Parent(a);
  DFT:=MatrixRing(K,n)![a^(i*j):i,j in [0..n-1]];
  C0:=Dual(LinearCode<K,n|[DFT[i+1]: i in X0]>);
  C0Z:=Dual(LinearCode<K,n|[DFT[i+1]: i in X0 join Z]>);
  C0:=LinearCode<GF(2),n|[[Eltseq(x)[1]:x in Eltseq(g)]: g in Generators(C0)]>;
  C0Z:=LinearCode<GF(2),n|[[Eltseq(x)[1]:x in Eltseq(g)]: g in Generators(C0Z)]>;
 return C0,C0Z;
end intrinsic;



//-----------------------NonPrimitiveAlternant----------------------//

intrinsic NonPrimitiveAlternant(n::RngIntElt,m::RngIntElt,r::RngIntElt) -> Code
{Constructs a non-primitive alternant code of length n over GF(2),
with n - mr <= k <= n - r, and d >= r + 1.}
    requirege n,1;
    requirege m,1;
    requirege r,1;
    lambda := m div 2;
    require 2^lambda ge n : "Must have 2^(m div 2) ge n";
    K := GF(2);
    Kl := ext<K|lambda>;
    Kmu := ext<K|2>;
    Km<w> := ext<K|m>;
 
    _,map := VectorSpace(Km,K);
 
    x := [];
    elts := [ x : x in Kl ];
    for i in [1..n] do
        x[i] := elts[i];
    end for;
 
    H := [ [ 1 / (x[i] - w) ^ j : i in [1..#x] ] : j in [1..r] ];
 
    G := Zero(RMatrixSpace(K,m * r,n));
 
    for j in [1..r] do
        for i in [1..n] do
            mat := RMatrixSpace(K,m,1) ! Eltseq(map(H[j][i]));
            InsertBlock(~G,mat,1 + (j - 1) * m,i);
        end for;
    end for;
 
    return Dual(LinearCode<GF(2),n | [ G[i] : i in [1..Nrows(G)]]>);
end intrinsic;


//--------------------------MDSCode--------------------------------//

intrinsic MDSCode(K::FldFin,n::RngIntElt,k::RngIntElt)->Code
{Given a finite field GF(q), constructs the [n,k,n-k+1] maximum distance seperab
le code provided n <= q+1 or if q=2^m, n=q+2, and k=3,q-1. }
  q:=#K;
  if IsEven(q) and n eq q+2 and k in {3,q-1} then
    a:=PrimitiveElement(K);
    H:=HorizontalJoin(
         KMatrixSpace(K,3,q-1)![a^(i*j):i in [0..q-2],j in [0..2]],
         One(MatrixRing(K,3)));
    if k eq 3 then
      res := LinearCode(H);
      res`MinimumWeight:=n-k+1;
    else
      return Dual(LinearCode(H));
      res`MinimumWeight:=4;
    end if;
  else
    requirerange n,1,q+1;
    requirerange k,0,n;
    res:=ShortenCode(MDSCode(K,k+q+1-n),{n+1..q+1});
    res`MinimumWeight:=n-k+1;
  end if;
  return res;
end intrinsic;

intrinsic MDSCode(K::FldFin,k::RngIntElt) -> Code
{Given a finite field GF(q), constructs the [q + 1,k,q - k + 2]
maximum distance seperable code.}
    q:=#K;
    requirerange k, 0,q+1;
    L := ext<K|2>;
    P := PolynomialRing(L);
    x := P.1;

    if IsOdd(q) and IsEven(k) then
      a := PrimitiveElement(L);
      alpha := a^(q-1);
      r := (q+1-k);
      t := (q+1-k) div 2;
      G := &*[P|(x-a*alpha^i)*(x-a*alpha^(1-i)): i in [1..t]];
      res := ConstaCyclicCode(q+1, PolynomialRing(K) ! G,K!(a^(q+1)));
    else
      a := RootOfUnity(q + 1,L);
      if IsEven(q) then
        if IsEven(k) then
            t := (q-k) div 2;
            G := (x-1)*&*[P|x^2 + (a^i + a^-i) * x + 1 : i in [1..t]];
        else
            t := (q+1-k) div 2;
            G := &*[P|x^2 + (a^i + a^-i) * x + 1 : i in [q div 2 - t + 1..q div
2]];
        end if;
      else //q odd and k odd
        G:=(x-1)*&*[P|x^2 - (a^i + a^-i) * x + 1 : i in [1..(q+1-k) div 2]];
      end if;

      res :=  CyclicCode(q + 1,PolynomialRing(K) ! G);
    end if;

    if k ne 0 then
      res`MinimumWeight := q - k + 2;
    end if;

    return res;

end intrinsic;


//-------------------JustesenCode--------------------------//

intrinsic JustesenCode(N::RngIntElt,K::RngIntElt) -> Code
{ Build a binary linear Justesen code of length 2mN and dimension mK where
N=2^m-1 and 1 < K < N }

    b,m := RealToIntegerExponent(N+1.0);
    require b eq 1 and m ge 0 : " N must be of the form 2^k-1";
    requirerange K,1,N-1;
    q := 2^m;
    F := GF(q);
    delta := q-K;
    R := ReedSolomonCode(F,delta);
    alpha := PrimitiveElement(F);
    G := GeneratorMatrix(R);
    GG := RMatrixSpace(F,K,2*N)!
	&cat&cat[[[G[i][j]] cat [alpha^(j-1)*G[i][j]]
	: j in [1..N]]
	: i in [1..K]];
    return SubfieldRepresentationCode(LinearCode(GG),GF(2));
end intrinsic;
