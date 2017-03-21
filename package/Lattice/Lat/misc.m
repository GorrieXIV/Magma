freeze;

RingIsZ := func<G | BaseRing(G) cmpeq IntegerRing()>;
RingIsQ := func<G | BaseRing(G) cmpeq RationalField()>;



intrinsic HermiteNumber(L::Lat : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> FldReElt
{The Hermite invariant of L, i.e., N(L) / det(L)^(1/Dimension(L))}
   require Rank(L) ge 1: "Argument 1 must be non-zero";
   return Minimum(L: Proof:=Proof, Prune:=Prune) / Determinant(L) ^ (RealField()!1/Dimension(L));
end intrinsic;


intrinsic PackingRadius(L::Lat : Proof := true, Prune := [1.0: i in [1..Dimension(L)]]) -> FldReElt
{The packing radius of L (half the minimal distance between lattice points)}
    require Rank(L) ge 1: "Argument 1 must be non-zero";    
    return Sqrt(Minimum(L: Proof:=Proof, Prune:=Prune)) / 2;
end intrinsic;






intrinsic EnumerationCostArray(L::Lat: Prune := [1.0:i in [1..Dimension(L)]]) -> ModTupFldElt
{Heuristic evaluations of the sizes of all the layers of the tree to be visited during the lattice shortest vector enumeration}
local G, d, total, det, pi, length, minko, R, test, tmp;

  require Rank(L) ge 1: "Argument 1 must be non-zero";
  if Type(Prune) ne Infty then 
    require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
    require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
  end if;  


  G:=GramMatrix (L);
  d:=NumberOfRows (G);
  R:=RealField(Ceiling(53+1.6*d):Bits:=true);
  RL := BaseRing(L);
  if Type(RL) ne FldRe then
    G := ChangeRing(G,R);
  else
    // Symmetrize G (*sigh*)                                                                              
    G := (G+Transpose(G))/2;
  end if;
  pi:=Pi(R);
  length := Sqrt(RealField()!(G[1][1]));
  T:=Cholesky(G);

  test := true;
  for j:=1 to d do test := test and (Prune[j] eq 1.0); end for;
  test := not(test);

  det := 1.0; for i:=1 to d do det := det * T[i][i]; end for;
  minko := (HermiteConstant(d))^(1/(2*d)) * det^(1/d);
  if (minko le length) then length:=minko; end if;

  total := VectorSpace(RealField(3), d)!0;
  det := 1.0; 
  for j:=d to 1 by -1 do
    det:=det*(length/T[j][j])^2; 
    if (test) 
      then tmp:= TruncatedHyperball ([Prune[j+i]: i in [0..d-j]]); 
      else tmp := 1.0;
    end if;
    total[j]:=tmp*Sqrt(det)*pi^((d-j+1)/2.0)/Gamma(1.0+(d-j+1)/2.0);
  end for;

  delete T; delete pi; delete G; delete R;
  return total;
end intrinsic;



intrinsic EnumerationCost(L::Lat: Prune := [1.0:i in [1..Dimension(L)]]) -> FldReElt
{A heuristic evaluation of the size of the tree to be visited during the lattice shortest vector enumeration}
local G, length, d, R, pi, T, det, minko, total, test, tmp;

  require Rank(L) ge 1: "Argument 1 must be non-zero";
  if Type(Prune) ne Infty then 
    require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
    require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
  end if;  

  G:=GramMatrix (L);
  d:=NumberOfRows(G);
  length:=RealField()!G[1][1];
  R:=RealField(Ceiling(53+1.6*d):Bits:=true);
  RL := BaseRing(L);
  if Type(RL) ne FldRe then
    G := ChangeRing(G,R);
   else
     // Symmetrize G (*sigh*) 
   G := (G+Transpose(G))/2;
  end if;
  pi:=Pi(R);
  T:=Cholesky(G);


  test := true;
  for j:=1 to d do test := test and (Prune[j] eq 1.0); end for;
  test := not(test);

  det := 1.0; for i:=1 to d do det := det * T[i][i]; end for;
  minko := (HermiteConstant(d))^(1/(2*d)) * det^(1/d);
  if (minko^2 le length) 
     then length:=minko; 
     else length := Sqrt(length); 
  end if;

  total := 0.0;
  det := 1.0; 
  for j:=d to 1 by -1 do
    det:=det*(length/T[j][j])^2; 
    if (test) 
      then tmp:= TruncatedHyperball ([Prune[j+i]: i in [0..d-j]]); 
      else tmp := 1.0;
    end if;
    total:=total + tmp*Sqrt(det)*pi^((d-j+1)/2.0)/Gamma(1.0+(d-j+1)/2.0);
  end for;

  delete T;
  delete pi;
  delete (G);
  total := RealField(3)!total;
  delete R;
return total;
end intrinsic;



intrinsic EnumerationCost(L::Lat, u::FldReElt: Prune := [1.0:i in [1..Dimension(L)]]) -> FldReElt
{A heuristic evaluation of the size of the tree to be visited during the enumeration of vectors within the prescribed norm}
local G, d, total, det, pi, length, minko, R, test, tmp;

  require Rank(L) ge 1: "Argument 1 must be non-zero";
  require u ge 0.0: "Argument 2 must be non-negative";

  if Type(Prune) ne Infty then 
    require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
    require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
  end if;  



  G:=GramMatrix (L);
  d:=NumberOfRows (G);
  R:=RealField(Ceiling(53+1.6*d):Bits:=true);
  RL := BaseRing(L);
  if Type(RL) ne FldRe then
    G := ChangeRing(G,R);
  else
    // Symmetrize G (*sigh*)
    G := (G+Transpose(G))/2;
  end if;
  pi:=Pi(R);
  length := Sqrt(u);
  T:=Cholesky(G);

  test := true;
  for j:=1 to d do test := test and (Prune[j] eq 1.0); end for;
  test := not(test);

  total := 0.0;
  det := 1.0; 
  for j:=d to 1 by -1 do
    det:=det*(length/T[j][j])^2;     
    if (test) 
      then tmp:= TruncatedHyperball ([Prune[j+i]: i in [0..d-j]]); 
      else tmp := 1.0;
    end if;
    total:=total + tmp*Sqrt(det)*pi^((d-j+1)/2.0)/Gamma(1.0+(d-j+1)/2.0);
  end for;

  total := RealField(3)!total;

  delete T; delete pi; delete G; delete R;
return total;
end intrinsic;





intrinsic EnumerationCostArray(L::Lat, u::FldReElt: Prune := [1.0:i in [1..Dimension(L)]]) -> ModTupFldElt
{Heuristic evaluations of the sizes of all the layers of the tree to be visited during the enumeration of vectors within the prescribed norm}
local G, d, total, det, pi, length, minko, R, test, tmp;

  require Rank(L) ge 1: "Argument 1 must be non-zero";
  require u ge 0.0: "Argument 2 must be non-negative";

  if Type(Prune) ne Infty then 
    require #Prune eq Rank(L): "The length of Prune must be the rank of argument 1";
    require forall{i: i in [1..Rank(L)] | Prune[i] ge 0.0 and Prune[i] le 1.0}:       "The elemements of Prune must be in [0.0, 1.0]"; 
  end if;  
  
  G:=GramMatrix (L);
  d:=NumberOfRows (G);
  R:=RealField(Ceiling(53+1.6*d):Bits:=true);
  RL := BaseRing(L);
  if Type(RL) ne FldRe then
    G := ChangeRing(G,R);
  else
     // Symmetrize G (*sigh*)
    G := (G+Transpose(G))/2;
  end if;

  pi:=Pi(R);
  length := Sqrt(u);
  T:=Cholesky(G);

  test := true;
  for j:=1 to d do test := test and (Prune[j] eq 1.0); end for;
  test := not(test);

  total := VectorSpace(RealField(3), d)!0;
  det := 1.0; 
  for j:=d to 1 by -1 do
    det:=det*(length/T[j][j])^2; 
    if (test) 
      then tmp:= TruncatedHyperball ([Prune[j+i]: i in [0..d-j]]); 
      else tmp := 1.0;
    end if;
    total[j]:=tmp*Sqrt(det)*pi^((d-j+1)/2.0)/Gamma(1.0+(d-j+1)/2.0);
  end for;

  delete T; delete pi; delete G; delete R;
return total;
end intrinsic;



intrinsic ReconstructLatticeBasis(C::ModMatRngElt, B::ModMatRngElt) -> ModMatRngElt
{Reconstruct a basis from a full-dimensional set of linearly independent lattice vectors}
local QQ, ZZ, U, T, tmp, gB, d, n;  

  require RingIsZ(C): "Base ring of argument 1 must be Z";
  require RingIsZ(B): "Base ring of argument 2 must be Z";
  require Dimension(Lattice(C)) eq Dimension(Lattice(B)): "Arguments 1 and 2 must span the same vector space";
  require  forall{i: i in [1..NumberOfRows(C)] | C[i] in Lattice(B)}: "Each row of Argument 1 must belong to the lattice spanned by Argument 2";


  QQ:=Rationals(); ZZ:=Integers();

  U:=ChangeRing(ChangeRing(C, QQ)*ChangeRing(B, QQ)^(-1), ZZ);
// C eq U * B;

  _, T := HermiteForm(Transpose(U));
// Transpose(H) eq U*Transpose(T);

  gB := ChangeRing(ChangeRing(Transpose(T), QQ)^(-1) * ChangeRing(B, QQ), ZZ);
// C eq Transpose(H) * gB;

  d:=NumberOfRows(gB); n:=NumberOfColumns(gB);

// size-reduction step
  for i:=2 to d do
    tmp := RMatrixSpace(ZZ, i, n+1)!0;
    for j:=1 to i do for k:=1 to n do tmp[j][k]:=gB[j][k]; end for; end for;
    tmp[i][n+1] := 2*Max([Norm(gB[j]): j in [1..i-1]]);
    tmp := LLL(tmp);
    for j:=1 to n do gB[i][j]:=tmp[i][j]; end for;
  end for;  

  delete (QQ); delete (ZZ); delete (U); delete (T); delete (tmp); 
  return gB;
end intrinsic;




intrinsic GaussReduce(B::MtrxSpcElt) -> MtrxSpcElt, AlgMatElt
{A Gauss-reduced basis of the lattice spanned by the rows of B};
  require Rank(B) eq 2: "Argument 1 must have rank 2";
  C, T:=HKZ(B);
  return C, T;
end intrinsic;



intrinsic GaussReduceGram(B::MtrxSpcElt) -> MtrxSpcElt, AlgMatElt
{A Gauss-reduced form equivalent to the Gram matrix B};
  require Rank(B) eq 2: "Argument 1 must have rank 2";
  C, T:=HKZGram(B);
  return C, T;
end intrinsic;


intrinsic GaussReduce(L::Lat) -> Lat, AlgMatElt
{Apply Gauss-reduction to L, returning a new lattice and the 
    transformation matrix T};
  require Rank(L) eq 2: "Argument 1 must have rank 2";
  F := GramMatrix(L);
  F, T := HKZGram(F);
  return LatticeWithBasis(
	MatrixRing(BaseRing(L),Rank(L)) !
           T*BasisMatrix(L), InnerProductMatrix(L) ), T;
end intrinsic;


intrinsic HKZ(L::Lat : Prune := [[1.0:j in [1..i]]:i in [1..Dimension(L)]], Proof:=true) -> Lat, AlgMatElt
{A lattice equal to L but with an HKZ-reduced basis, together the
corresponding transformation matrix}
  M, U := HKZGram(GramMatrix(L): Prune:=Prune, Proof:=Proof );
  test := true;
  for i:=1 to Dimension(L) do 
    for j:=1 to i do 
  test:= test and (Prune[i][j] eq 1.0); 
    end for; 
  end for;
  L2:= LatticeWithBasis(U*BasisMatrix(L), InnerProductMatrix(L));
  if (Proof and test) then L`Minimum:=M[1][1]; L2`Minimum:=M[1][1]; end if;
  return L2, U;
end intrinsic;

/* FAILED, still using Allan's coset code, even with its bugs

> LL:=LatticeWithBasis(Matrix(Vector([-36813/32768,95068/32768])));
> vv:=Vector([53687/536870912,-53687/536870912]);
> ClosestVectors(LL,vv);

////////////////////////////////////////////////////////////////////////
// replacements for ClosestVectors and CloseVectors

function gso(L) G:=[]; D:=[]; CR:=ChangeRing;
 RING:=(Type(BaseRing(L)) eq FldRe) select BaseRing(L) else Rationals();
 IPM:=CR(InnerProductMatrix(L),RING);
 function ip(a,b) return (a*IPM,b); end function;
 G[1]:=CR(Vector(L.1),RING); D[1]:=ip(G[1],G[1]);
 for k in [2..Rank(L)] do vk:=CR(Vector(L.k),RING);
  G[k]:=vk-&+[(ip(G[j],vk)/D[j])*G[j] : j in [1..k-1]];
  D[k]:=ip(G[k],G[k]); end for; return G,D; end function;

function babai(L,w) L:=LLL(L : Delta:=0.999); n:=Rank(L);
 RING:=(Type(BaseRing(L)) eq FldRe) select BaseRing(L) else Rationals();
 G,D:=gso(L); IPM:=ChangeRing(InnerProductMatrix(L),RING);
 for j in [n..1 by -1] do
  r:=Round((w*IPM,G[j])/D[j]); w:=w-r*ChangeRing(Vector(L.j),RING); end for;
 return w; end function;

intrinsic ClosestVectors(L::Lat,wi::ModTupRngElt : Max:=0) -> SeqEnum, RngElt
{The vectors of the lattice L closest to wi, and minimal norm difference}
 T:=Type(BaseRing(L)); Tw:=Type(BaseRing(wi)); ZQ:={RngInt,FldRat};
 require Nrows(wi) eq 1: "Vector must have one row";
 require T in {FldRe,FldRat,RngInt}: "Lattice must be over R,Q,Z";
 require Tw in {FldRe,FldRat,RngInt}: "Vector must be over R,Q,Z";
 if T in ZQ and Tw in ZQ then RING:=Rationals(); end if;
 if T eq FldRe and Tw eq FldRe and BaseRing(L) ne BaseRing(wi) then
  require false: "Lattice/vector not over real fields of same prec"; end if;
 if T eq FldRe then RING:=BaseRing(L); end if;
 if T ne FldRe and Tw eq FldRe then RING:=Rationals();
  wi:=Vector([a*2^b where a,b:=MantissaExponent(e) : e in Eltseq(wi)]); end if;
 IPM:=ChangeRing(InnerProductMatrix(L),RING); wi:=ChangeRing(wi,RING);
 function norm(w) return (w*IPM,w); end function;
 w:=babai(L,wi);
 if norm(w) eq 0 then sv:=[]; else sv:=ShortVectors(L,4*norm(w)); end if;
 sv:=[ChangeRing(Vector(v[1]),RING) : v in sv];
 sv cat:=[-e : e in sv]; sv cat:=[ChangeRing(Vector(L!0),RING)];
 E:=[<v+(wi-w),norm(v-w)> : v in sv]; m:=Min([e[2] : e in E]);
 E:=[L!e[1] : e in E | e[2] eq m]; return E,m; end intrinsic;

intrinsic ClosestVectors(L::Lat,w::LatElt : Max:=0) -> SeqEnum, RngElt {"} //"
 return ClosestVectors(L,Vector(w)); end intrinsic;

intrinsic ClosestVectorsMatrix(L::Lat,w::LatElt) -> Mtrx, RngElt
{The vectors of the lattice L closest to wi as a matrix,
 and minimal norm difference}
 return ClosestVectorsMatrix(L,Vector(w)); end intrinsic;

intrinsic ClosestVectorsMatrix(L::Lat,w::ModTupRngElt) -> Mtrx, RngElt {"} //"
 E,m:=ClosestVectors(L,w); return Matrix(E),m; end intrinsic;

////////////////////////////////////////////////

intrinsic CloseVectors(L::Lat,w::LatElt,B::RngElt) -> SeqEnum
{The vectors v of the lattice L close to w so that Norm(v - w) <= B.}
 return CloseVectors(L,Vector(w),0,B); end intrinsic;

intrinsic CloseVectors(L::Lat,w::ModTupRngElt,B::RngElt) -> SeqEnum {"} //"
 return CloseVectors(L,w,0,B); end intrinsic;

intrinsic CloseVectors(L::Lat,w::LatElt,A::RngElt,B::RngElt) -> SeqEnum
{The vectors v of the lattice L close to w so that A <= Norm(v - w) <= B}
 return CloseVectors(L,Vector(w),0,B); end intrinsic;

intrinsic CloseVectors
(L::Lat,wi::ModTupRngElt,A::RngElt,B::RngElt) -> SeqEnum {"} //"
 T:=Type(BaseRing(L)); Tw:=Type(BaseRing(wi)); ZQ:={RngInt,FldRat};
 require Nrows(wi) eq 1: "Vector must have one row";
 require T in {FldRe,FldRat,RngInt}: "Lattice must be over R,Q,Z";
 require Tw in {FldRe,FldRat,RngInt}: "Vector must be over R,Q,Z";
 require B ge 0: "B must be positive";
 if T in ZQ and Tw in ZQ then RING:=Rationals(); end if;
 if T eq FldRe and Tw eq FldRe and BaseRing(L) ne BaseRing(wi) then
  require false: "Lattice/vector not over real fields of same prec"; end if;
 if T eq FldRe then RING:=BaseRing(L); end if;
 if T ne FldRe and Tw eq FldRe then RING:=Rationals();
 wi:=Vector([a*2^b where a,b:=MantissaExponent(e) : e in Eltseq(wi)]); end if;
 IPM:=ChangeRing(InnerProductMatrix(L),RING); wi:=ChangeRing(wi,RING);
 function norm(w) return (w*IPM,w); end function;
 w:=babai(L,wi); sv:=ShortVectors(L,2*B+2*norm(w)); // geom lt arithmetic mean
 sv:=[ChangeRing(Vector(v[1]),RING) : v in sv];
 sv cat:=[-e : e in sv]; sv cat:=[ChangeRing(Vector(L!0),RING)];
 E:=[<v+(wi-w),norm(v-w)> : v in sv];
 E:=[<L!e[1],e[2]> : e in E | A le e[2] and e[2] le B];
 if #E eq 0 then E:=[L|]; end if; return E; end intrinsic;

intrinsic CloseVectorsMatrix(L::Lat,w::LatElt,B::RngElt) -> Mtrx
{The vectors v of the lattice L close to w so that Norm(v - w) <= B,
 returned as a matrix}
 return CloseVectorsMatrix(L,Vector(w),0,B); end intrinsic;

intrinsic CloseVectorsMatrix(L::Lat,w::ModTupRngElt,B::RngElt) -> Mtrx {"} //"
 return CloseVectorsMatrix(L,w,0,B); end intrinsic;

intrinsic CloseVectorsMatrix(L::Lat,w::LatElt,A::RngElt,B::RngElt) -> Mtrx
{The vectors v of the lattice L close to w so that A <= Norm(v - w) <= B,
 returned as a matrix}
 return CloseVectorsMatrix(L,Vector(w),0,B); end intrinsic;

intrinsic CloseVectorsMatrix
(L::Lat,wi::ModTupRngElt,A::RngElt,B::RngElt) -> SeqEnum {"} //"
 CV:=CloseVectors(L,wi,A,B);
 if #CV ne 0 then return Matrix([Vector(e[1]) : e in CV]); end if;
 return Matrix(0,Degree(L),[BaseRing(L)|]); end intrinsic;
*/
