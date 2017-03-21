freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

// Jul 8 2014, MW, clean up AllLinearRelations horror

//19/08/2004 : Nicole Sutherland
// 	       Fix return types to boolean elements rather than structures.

////////////////////////////////////////////////////////////////////////
//                                                                    
//  Finding maps between analytic Jacobians. Isomorphisms, Isogenies and
//  Endomorphism rings.
//  
//  Two methods are used. For 2 dimensional Jacobians Isomorphisms can be
//  found using a fundamental domain for the symplectic action on 2 
//  dimensional Siegel upper half-space. This works even if the precision is
//  pretty low. The other method used is to find linear relations between
//  certain products of the entries of the Siegel upper half-space elements.
//  This method is much more general but only works if things are known
//  to high precision.
//
//  P. van Wamelen (started Sept 2002)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//    RandomSymplecticMatrix
//    IsSymplecticMatrix
//    To2DUpperHalfSpaceFundamentalDomian
//    AllLinearRelations
//    AnalyticHomomorphisms
//    IsIsogenousPeriodMatrices
//    IsIsomorphicSmallPeriodMatrices
//    IsIsomorphicBigPeriodMatrices
//    IsIsomorphic
//    IsIsogenousPeriodMatrices
//    IsIsogenous
//    EndomorphismRing
//    
//     
////////////////////////////////////////////////////////////////////////

import "period.m" : tauFromPerM;


////////////////////////////////////////////////////////////////////
//                                                                //
//                       Random Matrices                          //
//                                                                // 
////////////////////////////////////////////////////////////////////



// Find a random integer matrix with determinant 1 or -1
// no guarantees on the distribution, but most entries will have absolute 
// value below m. n should not be too big, we use LLL.

//intrinsic RandomUnimodularMatrix(n::RngIntElt,m::RngIntElt) -> Mtrx
/* This can't be an intrinsic; since it would be shadowed by the intrinsic
   with the same signature in package/Module/Mtrx/random.m. */
function RandomUnimodularMatrix(n, m) 
/*Returns a random integer nxn matrix with determinant 1 or -1. Most entries
will be between -m and m.*/
  if not n ge 1 then error "First argument should be at least 1"; end if;
  if not m ge 1 then error "Second argument should be at least 1"; end if;
  if n eq 1 then
    return Matrix(IntegerRing(),1,1,[Random({-1,1})]);
  end if;
  repeat
    mat := Matrix(IntegerRing(),n,n,[]);
    for i in [1..n] do
      for j in [1..n-1] do
        mat[i,j] := Random(-m,m);
      end for;
    end for;
    mat1 := RemoveColumn(mat,n);
    lst := [(-1)^(n-i)*Determinant(RemoveRow(mat1,i)) : i in [1..n]];
    g, rs := XGCD(lst);
  until g eq 1;
  mat2 := Matrix(RationalField(),n,n,[]);
  L := Lattice(NullSpace(Matrix(n,1,lst)));
  nulls := Basis(L);
  for i in [1..n-1] do
    InsertBlock(~mat2,Matrix(RationalField(),1,n,
      ElementToSequence(nulls[i])),i,1);
  end for;
  InsertBlock(~mat2,Matrix(RationalField(),1,n,lst),n,1);
  sol := ElementToSequence(Solution(mat2,Matrix(RationalField(),1,n,rs)));
  sol := [Round(s) : s in sol];
  smalln := &+[sol[i]*nulls[i] : i in [1..#nulls]];
  w := (RSpace(IntegerRing(),n) ! rs) - (RSpace(IntegerRing(),n) ! smalln);
  rs := Matrix(n,1,ElementToSequence(w-ClosestVectors(L,w)[1]));
  InsertBlock(~mat,rs,1,n);
  return PermutationMatrix(IntegerRing(),Random(Sym(n)))*mat
    *PermutationMatrix(IntegerRing(),Random(Sym(n)));
end function;

function RandomSymmetricMatrix(n,m)
  mat := Matrix(IntegerRing(),n,n,[]);
  for i in [1..n] do
    for j in [i..n] do
      mat[i,j] := Random(-m,m);
      mat[j,i] := mat[i,j];
    end for;
  end for;
  return mat;
end function;

intrinsic RandomSymplecticMatrix(g::RngIntElt,m::RngIntElt) -> Mtrx
{Returns a random 2gx2g symplectic matrix. Entries will have size the same 
order of magnitude as m. No guarantees on the distribution!}
  require g ge 1: "First argument should be at least 1";
  require m ge 1: "Second argument should be at least 1";
  B := RandomSymmetricMatrix(g,2);
  out := ScalarMatrix(2*g,1);
  InsertBlock(~out,B,1,g+1);

  U := RandomUnimodularMatrix(g,Ceiling(Sqrt(m)));
  Uti := Transpose(U^-1);
  mat := ScalarMatrix(2*g,0);
  InsertBlock(~mat,Uti,1,1);
  InsertBlock(~mat,U,g+1,g+1);
  out := out*mat;

  B := RandomSymmetricMatrix(g,2);
  mat := ScalarMatrix(2*g,-1);
  InsertBlock(~mat,B,g+1,1);
  out := out*mat;

  U := RandomUnimodularMatrix(g,Ceiling(Sqrt(m)));
  Uti := Transpose(U^-1);
  mat := ScalarMatrix(2*g,0);
  InsertBlock(~mat,U,1,1);
  InsertBlock(~mat,Uti,g+1,g+1);
  out := out*mat;

  mat := ScalarMatrix(2*g,0);
  imat := ScalarMatrix(g,1);
  InsertBlock(~mat,imat,1,g+1);
  InsertBlock(~mat,-imat,g+1,1);

  if Random({0,1}) eq 0 then
    out := out*mat;
  end if;

  if Random({0,1}) eq 0 then
    out := mat*out;
  end if;

  return out;
end intrinsic;

function jmatrix(C,g)
  jmat := Matrix(C,2*g,2*g,[]);
  dum := ScalarMatrix(g,C!1);
  InsertBlock(~jmat,dum,1,g+1);
  InsertBlock(~jmat,-dum,g+1,1);
  return jmat;
end function;

intrinsic IsSymplecticMatrix(mat::AlgMatElt[RngInt]) -> BoolElt
{Returns true if mat is an integer symplectic matrix, false otherwise.}
  if NumberOfRows(mat) mod 2 ne 0 then
    return false;
  end if;
  g := NumberOfRows(mat) div 2;
  jmat := jmatrix(IntegerRing(),g);
  return jmat eq Transpose(mat)*jmat*mat;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//       Fundamental Domain for 2-D Siegel upper half-space       //
//                                                                // 
////////////////////////////////////////////////////////////////////
//
//  These programs allow one to move an element of 2 dimensional Siegel
//  upper half-space into a fundamental domain for that space. The
//  fundamental domain is the one described by E. Gottschling in
//  "Explizite bestimmung der randflachen des fundamentalbereiches der
//  modulgruppe zweiten grades", Math. Annalen, 138:
//

// Given a positive definite symmetric matrix q this will find integers a and
// b such that {a,b}.q.{{a},{b}} is non-zero minimal
// It uses Algorithm 1.3.14 in Cohen...
function FindShort(q)
  B := Orthonormalize(q,CoefficientRing(q));
  a := Matrix(2,1,[B[1,1],B[1,2]]);
  b := Matrix(2,1,[B[2,1],B[2,2]]);
  sa := a[1,1]*a[1,1]+a[2,1]*a[2,1];
  sb := b[1,1]*b[1,1]+b[2,1]*b[2,1];
  if sa lt sb then
    dum := a;
    a := b;
    b := dum;
    dum := sa;
    sa := sb;
    sb := dum;
    alin := Matrix(2,1,[0,1]);
    blin := Matrix(2,1,[1,0]);
  else
    alin := Matrix(2,1,[1,0]);
    blin := Matrix(2,1,[0,1]);
  end if;
  n := a[1,1]*b[1,1]+a[2,1]*b[2,1];
  r := Round(n/sb);
  st := sa-2*r*n+r^2*sb;
  while st lt sb do
    t := a - r*b;
    tlin := alin - r*blin;
    a := b;
    alin := blin;
    b := t;
    blin := tlin;
    sa := sb;
    sb := st;
    n := a[1,1]*b[1,1]+a[2,1]*b[2,1];
    r := Round(n/sb);
    st := sa-2*r*n+r^2*sb;
  end while;
  return blin;
end function;

// This finds a unimodular integer matrix M = Matrix(2,2,[[a,b],[c,d]]) 
// such that Matrix(1,2,[a,b])*q*Matrix(2,1,[a,b]) is minimal and (given
// a and b) Matrix(1,2,[c,d])*q*Matrix(2,1,[c,d]) is minimal and
// Matrix(1,2,[c,d])*q*Matrix(2,1,[c,d]) >= 0.
function MinkowskiReduce(q)
  qa := q[1,1];
  qb := (q[1,2]+q[2,1])/2;
  qd := q[2,2];
  qp := Matrix(2,2,[qa,qb,qb,qd]);
  v := FindShort(qp);
  a := v[1,1];
  b := v[2,1];
  if a eq 0 then
    c := -b;
    d := 0;
  elif b eq 0 then
    d := a;
    c := 0;
  else
    d := Solution(a,1,Abs(b));
    c := (a*d-1) div b;
  end if;
  e :=
    Round(-(a*qa*c + b*qd*d + b*c*qb + a*d*qb)/(a^2*qa + b^2*qd + 2*a*b*qb));
  oy := Sign((d + b*e)*(b*qd + a*qb) + (c + a*e)*(a*qa + b*qb));
  if oy eq 0 then
    oy := 1;
  end if;
  outm := Matrix(2,2,[a,oy*(a*e+c),b,oy*(b*e+d)]);
  return outm,Transpose(outm)*qp*outm;
end function;

/* This is realy dumb, but I don't have time to fix magma right now... */
function MyCompInverse(mat);
  C := BaseRing(mat);
  dim := NumberOfRows(mat);
  fullmat := HorizontalJoin(mat,ScalarMatrix(dim,C!1));
  for i in [1..dim] do
    _,ind := Max([Abs(fullmat[j,i]) : j in [i..dim]]);
    ind := ind+i-1;
    SwapRows(~fullmat,i,ind);
    for j in [i+1..dim] do
      AddRow(~fullmat,-fullmat[j,i]/fullmat[i,i],i,j);
    end for;
    MultiplyRow(~fullmat,1/fullmat[i,i],i);
  end for;
  for i:=dim to 2 by -1 do
    for j in [1..i-1] do
      AddRow(~fullmat,-fullmat[j,i],i,j);
    end for;
  end for;
  return Submatrix(fullmat,1,dim+1,dim,dim);
end function;

function SymplecticAction(z,m,g)
  return (ExtractBlock(g,1,1,2,2)*z+ExtractBlock(g,1,3,2,2))*MyCompInverse(ExtractBlock(g,3,1,2,2)*z+ExtractBlock(g,3,3,2,2)), g*m;
end function;

function SymplecticActionS(z,m)
  return SymplecticAction(z,m,Matrix(4,4,[[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]]));
end function;

function SymplecticActionT(z,m,b)
  return SymplecticAction(z,m,InsertBlock(ScalarMatrix(4,1),b,1,3));
end function;

function SymplecticActionU(z,m,u)
  Uti := Transpose(u^-1);
  return SymplecticAction(z,m,InsertBlock(InsertBlock(ScalarMatrix(4,0),u,1,1),Uti,3,3));
end function;

function TranslateToCenter(z,m)
  return SymplecticActionT(z,m,-Matrix(2,2,[Round(Re(z[1,1])),Round(Re(z[1,2])),Round(Re(z[1,2])),Round(Re(z[2,2]))]));
end function;

tstMats := [Matrix(2,2,[[0,0],[0,0]]),
            Matrix(2,2,[[1,0],[0,0]]),
            Matrix(2,2,[[0,0],[0,1]]),
            Matrix(2,2,[[1,0],[0,1]]),
            Matrix(2,2,[[1,0],[0,-1]]),
            Matrix(2,2,[[0,1],[1,0]]),
            Matrix(2,2,[[1,1],[1,0]]),
            Matrix(2,2,[[0,1],[1,1]])];

tstM1 := Matrix(4,4,[[0, 0,-1, 0], [0, 1, 0, 1], [1, 0, 0, 0], [0, 0, 0, 1]]);
tstM2 := Matrix(4,4,[[1, 0, 0, 0], [0, 0, 0,-1], [0, 0, 1, 0], [0, 1, 0, 0]]);
tstM3 := Matrix(4,4,[[0, 0,-1, 0], [0, 1, 1, 1], [1,-1, 1, 0], [0, 0, 1, 1]]);
tstM4 := Matrix(4,4,[[0, 0,-1, 0], [0, 1, 1, 1], [1,-1,-1, 0], [0, 0, 1, 1]]);

Cmat := Matrix(4,4,[[0,0,-1,0],[0,0,0,-1],[1,0,0,0],[0,1,0,0]]);

intrinsic To2DUpperHalfSpaceFundamentalDomian(z::Mtrx[FldCom]) -> Mtrx, Mtrx
{First return value is an element of a fundamental domain for 2 dimensional 
Siegel upper half-space that is equivalent to input. The second return value 
is a symplectic matrix that takes the input to the first return value.}
  require NumberOfRows(z) eq 2   : "The argument should be a 2x2 matrix.";
  require NumberOfColumns(z) eq 2: "The argument should be a 2x2 matrix.";
  dum := ElementToSequence(z - Transpose(z));
  dum := Max([Abs(d) : d in dum]);
  require dum lt 10^-10: "The argument should be a symmetric matrix.";
  Itau := Matrix(2,2,[Im(t) : t in ElementToSequence(z)]);
  e := Min([Re(e[1]) : e in Eigenvalues(Itau)]);
  require e gt 0: "The argument should have positive definite imaginary part.";

  R := BaseRing(z);
  pres := Precision(R);

  one := 1 - 10^-Floor(4*pres/5);
  mat := ScalarMatrix(4,1);
  notdone := true;
  while notdone do
    z,mat := SymplecticActionU(z,mat,Transpose(MinkowskiReduce(
      Matrix(2,2,[Im(z[1,1]),Im(z[1,2]),Im(z[2,1]),Im(z[2,2])]))));
    z,mat := TranslateToCenter(z,mat);
    if Abs(z[1,1]) lt one then
      z,mat := SymplecticAction(z,mat,tstM1);
      continue;
    elif Abs(z[2,2]) lt one then
      z,mat := SymplecticAction(z,mat,tstM2);
      continue;
    elif Abs(z[1,1]+z[2,2]-2*z[1,2]+1) lt one then
      z,mat := SymplecticAction(z,mat,tstM3);
      continue;
    elif Abs(z[1,1]+z[2,2]-2*z[1,2]-1) lt one then
      z,mat := SymplecticAction(z,mat,tstM4);
      continue;
    end if;
    cflag := false;
    for tstmat in tstMats do
      if Abs(Determinant(z+tstmat)) lt one then
        z,mat := SymplecticAction(z,mat,InsertBlock(Cmat,tstmat,3,3));
        cflag := true;
        break;
      end if;
      if Abs(Determinant(z-tstmat)) lt one then
        z,mat := SymplecticAction(z,mat,InsertBlock(Cmat,-tstmat,3,3));
        cflag := true;
        break;
      end if;
    end for;
    if not cflag then notdone := false; end if;
  end while;
  return z,mat;
end intrinsic;

/* This takes two taus and if they are equivalent under Symp(4,Z) it returns
a symplectic matrix such that SymplecticAction(tau1,smat) = tau2. 

In case the two taus are equivalent and on the boundary of the
fundamental domain it doesn't work that well. In fact, I don't know
the right solution so we do the following: Move taus to fundamental
domain, say ftau1 and ftau2. Now check whether any of the tstMlst
matrices (found by a lot of experimenting and probably not complete) 
takes ftau1 to an integer translate of ftau2. If this still
doesn't give anything, apply a random symplectic matrix to ftau1, move
to fundamental domain again and recheck. We do this 10 times and if it
still fails we give up.
*/

tstM5 := Matrix(4,4,[1,-1,0,0,0,1,0,0,0,0,1,0,0,0,1,1]);
tstM6 := Matrix(4,4,[0,0,-1,-1,-1,1,-1,1,1,0,0,-1,0,0,0,1]);
tstM7 := Matrix(4,4,[0,0,-1,0,0,0,0,1,1,0,0,0,0,-1,0,0]);
tstM8 := Matrix(4,4,[0,1,0,0,1,0,0,0,0,0,0,1,0,0,1,0]);
tstM9 := Matrix(4,4,[0,0,0,1,0,0,1,1,1,-1,0,0,-1,0,0,0]);

tstMlst := [ScalarMatrix(4,1),
  tstM1, tstM2, tstM2^2, tstM3, tstM4, tstM1^-1, tstM2^-1, tstM3^-1, tstM4^-1,
  tstM8,tstM5, tstM5^-1,tstM6,tstM6^-1,tstM7,tstM9];

function IsIntegerTranslate(tau1,tau2,pres)
  mat := tau1-tau2;
  imat := Matrix(2,2,[Round(Re(d)) : d in ElementToSequence(mat)]);
  intmat := Matrix(BaseRing(tau1),imat);
  if Max([Abs(d) : d in ElementToSequence(mat-intmat)]) lt 10^(-pres) then
    return true, -imat;
  else
    return false, 0;
  end if;
end function;

function EquivQ0(ftau1,ftau2,pres)
  Id := ScalarMatrix(4,1);
  for tstM in tstMlst do
    bool, T := IsIntegerTranslate(SymplecticAction(ftau1,Id,tstM),ftau2,pres);
    if bool then
      return true, InsertBlock(Id,T,1,3)*tstM;
    end if;
  end for;
  return false, 0;
end function;

function D2IsIsomorphic(tau1,tau2,pres)
  ftau1, smat1 := To2DUpperHalfSpaceFundamentalDomian(tau1);
  ftau2, smat2 := To2DUpperHalfSpaceFundamentalDomian(tau2);
  bool, smat3 := EquivQ0(ftau1,ftau2,pres);
  if bool then
    return true, smat2^-1*smat3*smat1;
  end if;
  for k in [1..10] do
    rmat := RandomSymplecticMatrix(2,4);
    tau3, smat3 := SymplecticAction(ftau1,smat1,rmat);
    ftau3, smat4 := To2DUpperHalfSpaceFundamentalDomian(tau3);
    smat3 := smat4*smat3;
    bool, smat5 := EquivQ0(ftau3,ftau2,pres);
    if bool then
      return true, smat2^-1*smat5*smat3;
    end if;
  end for;
  return false, 0;
end function;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      AllLinearRelations                        //
//                                                                // 
////////////////////////////////////////////////////////////////////
//
// An extension of IntegerRelation. This finds all linear relations with 
// resonably small coefficients.

function AllLinearRelations0(lst,pres)
  if #lst eq 2 then
    return [];
  end if;
  R := RealField(20);
  lindep := IntegerRelation(lst);
  // printf "found %o\n",lindep;
  zero := Abs(&+[lindep[i]*lst[i] : i in [1..#lst]]);
  if &+[Max(0,Log(Abs(l) + R!1/10)/Log(10)) : l in lindep] lt pres
    and zero lt 10^(-pres) then
    ind := 1;
    while lindep[ind] eq 0 do
      ind +:= 1;
    end while;
    ans := AllLinearRelations0(Remove(lst,ind),pres);
    return [lindep] cat [Insert(ld,ind,0) : ld in ans];
  else
    return [];
  end if;
end function;

intrinsic AllLinearRelationsOld(q::SeqEnum,p::RngIntElt) -> Lat
{Given a sequence with entries from a real or complex field, return
the lattice of all (small) integer linear dependencies among the
entries. The precision, p, given as second argument is used for two
purposes. First "small" is defined to be any relation such that the
sum of the digits of the coefficients is less than p. Second, a linear
relation must be zero to within 10^-p.}
  U := Universe(q);
  require Type(U) in {FldCom,FldRe}: 
    "The sequence should contain real or complex entries";
  require p gt 0: "The precision should be a positive integer";
  if Type(U) in {FldCom,FldRe} then
    pres := Precision(U);
    oldpres := Precision(RealField());
    SetDefaultRealFieldPrecision(pres);
    CC := ComplexField();
    lst := [CC | c : c in q];
  else
    lst := q;
  end if;
  olst := [U |];
  indlst := [];
  zlst := [];
  for i in [1..#lst] do
    if lst[i] ne 0 then
      Append(~olst,lst[i]);
      Append(~indlst,i);
    else
      Append(~zlst,i);
    end if;
  end for;
  sans := AllLinearRelations0(olst,p);
  if Type(U) in {FldCom,FldRe} then
    SetDefaultRealFieldPrecision(oldpres);
  end if;

  ans := [];
  for ld in sans do
    lld := [0 : i in lst];
    for i in [1..#indlst] do
      lld[indlst[i]] := ld[i];
    end for;
    Append(~ans,lld);
  end for;
  for i in zlst do
    lld := [0 : i in lst];
    lld[i] := 1;
    Append(~ans,lld);
  end for;
  // the integer vectors in the Q-span of ans give all integer relations.
  if #ans eq 0 then
    dum := [0 : i in lst]; // because this is dumb, but how else do I define
                           // a zero dimensional lattice?
    d1 := dum; d1[1] := 1;
    d2 := dum; d2[2] := 1;
    return Lattice(Matrix(1,#lst,d1)) meet Lattice(Matrix(1,#lst,d2));
  end if;
  ans := HermiteForm(Matrix(ans));
  ans := Matrix(RationalField(),ans);
  j := 1;
  den := 1;
  for i in [1..NumberOfRows(ans)] do
    while ans[i,j] eq 0 do
      j +:= 1;
    end while;
    den := den/ans[i,j];
    MultiplyRow(~ans,den,i);
  end for;
  // the integer vectors in the Z-span of ans now give all integer relations. 
  return Lattice(ans) meet 
         Lattice(ScalarMatrix(NumberOfColumns(ans),1));
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    FindAnalyticHomomorphisms                   //
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic AnalyticHomomorphisms(tau1::Mtrx[FldCom], tau2::Mtrx[FldCom]) -> SeqEnum
{For two small period matrices tau1 and tau2 this finds 2gx2g integer
matrices M such that there exists a complex gxg matrix alpha such that
alpha (tau1 1) = (tau2 1) M.}
  g := NumberOfRows(tau1);
  require NumberOfColumns(tau1) eq g:
    "The first argument must be a square matrix";
  require NumberOfRows(tau2) eq g:
    "Arguments must be matrices of the same size";
  require NumberOfColumns(tau2) eq g:
    "The second argument must be a square matrix";
  C := BaseRing(tau1);
  require BaseRing(tau2) eq C:
    "The arguments must be defined over the same field";
  pres := Precision(C);
  oldpres := Precision(RealField());
  SetDefaultRealFieldPrecision(pres);
  CC := ComplexField();
  tau := ChangeRing(tau1,CC);
  taup := ChangeRing(tau2,CC);
  gg := g*g;
  TTR := PolynomialRing(IntegerRing(),6*gg);
  vtau := Matrix(TTR,g,g,[TTR.i : i in [1..gg]]);
  vtaup := Matrix(TTR,g,g,[TTR.i : i in [gg+1..2*gg]]);
  amat := Matrix(TTR,g,g,[TTR.i : i in [2*gg+1..3*gg]]);
  bmat := Matrix(TTR,g,g,[TTR.i : i in [3*gg+1..4*gg]]);
  cmat := Matrix(TTR,g,g,[TTR.i : i in [4*gg+1..5*gg]]);
  dmat := Matrix(TTR,g,g,[TTR.i : i in [5*gg+1..6*gg]]);
  dum := (vtaup*bmat+dmat)*vtau - (vtaup*amat+cmat);
  dlst := ElementToSequence(dum);
  slst := ElementToSequence(tau) cat ElementToSequence(taup) cat 
            [0 : i in [2*gg+1..6*gg]];
  L := AllLinearRelationsOld([Evaluate(Coefficient(dlst[1],i,1),slst) : 
         i in [2*gg+1..6*gg]],Floor(2*pres/3));
  for j in [2..#dlst] do
    Ln := AllLinearRelationsOld([Evaluate(Coefficient(dlst[j],i,1),slst) : 
         i in [2*gg+1..6*gg]],Floor(2*pres/3));
    L := L meet Ln;
  end for;
  SetDefaultRealFieldPrecision(oldpres);
  smatlst := [];
  for v in Basis(L) do
    lst := ElementToSequence(v);
    amat := Matrix(g,g,[lst[i] : i in [     1..gg]]);
    bmat := Matrix(g,g,[lst[i] : i in [  gg+1..2*gg]]);
    cmat := Matrix(g,g,[lst[i] : i in [2*gg+1..3*gg]]);
    dmat := Matrix(g,g,[lst[i] : i in [3*gg+1..4*gg]]);
    smat := Matrix(IntegerRing(),2*g,2*g,[]);
    InsertBlock(~smat,amat,1,1);
    InsertBlock(~smat,bmat,1,g+1);
    InsertBlock(~smat,cmat,g+1,1);
    InsertBlock(~smat,dmat,g+1,g+1);
    Append(~smatlst,smat);
  end for;
  return smatlst;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//           Isomorhisms, Isogenies and Endomorphisms             //
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic IsIsomorphicSmallPeriodMatrices(tau1::Mtrx[FldCom],tau2::Mtrx[FldCom]) -> BoolElt, Mtrx
{For two small period matrices tau1 and tau2 this finds a 2gx2g
symplectic integer matrix M such that there exists a complex gxg
matrix alpha such that alpha (tau1 1) = (tau2 1) M. Such matrices
define isomorphisms between the corresponding analytic Jacobians. The
first return value is true if such a matrix is found, false
otherwise. The second return value is the matrix, if found. Zero
matrix otherwise.}
  g := NumberOfRows(tau1);
  require NumberOfColumns(tau1) eq g:
    "The first argument must be a square matrix";
  require NumberOfRows(tau2) eq g:
    "Arguments must be matrices of the same size";
  require NumberOfColumns(tau2) eq g:
    "The second argument must be a square matrix";
  C := BaseRing(tau1);
  require BaseRing(tau2) eq C:
    "The arguments must be defined over the same field";
  if g eq 2 then
    pres := Precision(C);
    bool, smat := D2IsIsomorphic(tau2,tau1,Floor(4*pres/5));
    if not bool then return bool,Matrix(IntegerRing(),2*g,2*g,[]);; 
    else return bool, Transpose(smat); end if;
  else
    mlst := AnalyticHomomorphisms(tau1,tau2);
    for smat in mlst do
      if IsSymplecticMatrix(smat) then
        return true, smat;
      end if;
    end for;
    if #mlst gt 0 then
      blst := CartesianPower({-1..1},#mlst);
      for plst in blst do
        if IsSymplecticMatrix(&+[plst[j]*mlst[j] : j in [1..#mlst]]) then
          return true, &+[plst[j]*mlst[j] : j in [1..#mlst]];
        end if;
      end for;
    end if;
    g := NumberOfRows(tau1);
    return false, Matrix(IntegerRing(),2*g,2*g,[]);
  end if;
end intrinsic;

intrinsic IsIsomorphicBigPeriodMatrices(PM1::Mtrx[FldCom],PM2::Mtrx[FldCom]) -> BoolElt, Mtrx, Mtrx
{For two big period matrices PM1 and PM2 this finds a 2gx2g symplectic
integer matrix M such that there exists a complex gxg matrix alpha
such that alpha PM1 = PM2 M. Such matrices define isomorphisms between
the corresponding analytic Jacobians. The first return value is true
if such a matrix is found, false otherwise. The second and third
return values are M and alpha, if found. Zero matrices otherwise.}
  g := NumberOfRows(PM1);
  require NumberOfColumns(PM1) eq 2*g:
    "The first argument must be a gx2g matrix";
  require NumberOfRows(PM2) eq g:
    "Arguments must be matrices of the same size";
  require NumberOfColumns(PM2) eq 2*g:
    "The second argument must be a gx2g matrix";
  C := BaseRing(PM1);
  require BaseRing(PM2) eq C:
    "The arguments must be defined over the same field";
  success, M := 
    IsIsomorphicSmallPeriodMatrices(tauFromPerM(PM1),tauFromPerM(PM2));
  if success then
    PM1p := PM2*Matrix(C,M);
    alpha := Submatrix(PM1p,1,1,g,g)*Submatrix(PM1,1,1,g,g)^-1;
    max := Max([Abs(d) : d in ElementToSequence(alpha*PM1 - PM1p)]);
    assert max lt 10^-10;
    return true, M, alpha;
  else
    return false, Matrix(IntegerRing(),2*g,2*g,[]), Matrix(C,g,g,[]);
  end if;
end intrinsic;

intrinsic IsIsomorphic(A1::AnHcJac,A2::AnHcJac) -> BoolElt, Mtrx, Mtrx
{For two analytic Jacobians A1 and A2 with big period matrices PM1 and
PM2 this finds a 2gx2g symplectic integer matrix M such that there
exists a complex gxg matrix alpha such that alpha PM1 = PM2 M. Such
matrices define isomorphisms between the corresponding analytic
Jacobians. The first return value is true if such a matrix is found,
false otherwise. The second and third return values are M and alpha,
if found. Zero matrices otherwise.}
  require Genus(A1) eq Genus(A2): "The Jacobians must have the same dimensions";
  require BaseRing(A1) eq BaseRing(A2): 
    "The Jacobians must have the same base ring";
  return 
    IsIsomorphicBigPeriodMatrices(BigPeriodMatrix(A1), BigPeriodMatrix(A2));
end intrinsic;

intrinsic IsIsogenousPeriodMatrices(P1::Mtrx,P2::Mtrx) -> BoolElt, Mtrx
{For two period matrices (small or big) P1 and P2 this finds a nonsingular 
2gx2g integer matrix M such that there exists a complex gxg
matrix alpha such that alpha (P1 1) = (P2 1) M, in case of small period 
matrices, or alpha P1 = P2 M for big period matrices. Such a matrix
defines an isogeny between the corresponding analytic Jacobians. The
first return value is true if such a matrix is found, false
otherwise. The second return value is M, if found. Zero
matrix otherwise. In case of big period matrices alpha is the third 
return value.}
  g := NumberOfRows(P1);
  C := BaseRing(P1);
  require BaseRing(P2) eq C:
    "The two marices must have the same qoefficient rings";
  require NumberOfRows(P2) eq g: "The two matrices must have the same size";
  if NumberOfColumns(P1) eq g then
    small := true;
    require NumberOfColumns(P2) eq g: 
      "The two matrices must have the same size";
    tau1 := P1;
    tau2 := P2;
  else
    require NumberOfColumns(P1) eq 2*g: "The matrices must be gxg or gx2g";
    require NumberOfColumns(P1) eq 2*g:
      "The two matrices must have the same size";
    small := false;
    tau1 := tauFromPerM(P1);
    tau2 := tauFromPerM(P2);
  end if;
      
  mlst := AnalyticHomomorphisms(tau1,tau2);
  success := false;
  if #mlst gt 0 then
    min := 0;
    blst := CartesianPower({-1..1},#mlst);
    for plst in blst do
      mat := &+[plst[j]*mlst[j] : j in [1..#mlst]];
      det := Determinant(mat);
      if det gt 0 then
        if not success then
          min := det;
          success := true;
          smat := mat;
        else
          if det lt min then
            min := det;
            smat := mat;
          end if;
        end if;
      end if;
    end for;
  end if;
  if success then
    if small then
      return true, smat;
    else
      P1p := P2*Matrix(C,smat);
      alpha := Submatrix(P1p,1,1,g,g)*Submatrix(P1,1,1,g,g)^-1;
      max := Max([Abs(d) : d in ElementToSequence(alpha*P1 - P1p)]);
      assert max lt 10^-10;
      return true, smat, alpha;
    end if;
  else
    if small then
      return false, Matrix(IntegerRing(),2*g,2*g,[]);
    else
      return false, Matrix(IntegerRing(),2*g,2*g,[]), Matrix(C,g,g,[]);
    end if;
  end if;
end intrinsic;

intrinsic IsIsogenous(A1::AnHcJac,A2::AnHcJac) -> BoolElt, Mtrx, Mtrx
{For two analytic Jacobians A1 and A2 with big period matrices PM1 and
PM2 this finds a nonsingular 2gx2g integer matrix M such that there
exists a complex gxg matrix alpha such that alpha PM1 = PM2 M. Such
a matrix defines an isogeny between the corresponding analytic
Jacobians. The first return value is true if such a matrix is found,
false otherwise. The second and third return values are M and alpha,
if found. Zero matrices otherwise.}
  require Genus(A1) eq Genus(A2):
    "The Jacobians must have the same dimensions";
  require BaseRing(A1) eq BaseRing(A2): 
    "The Jacobians must have the same base ring";
  return 
    IsIsogenousPeriodMatrices(BigPeriodMatrix(A1), BigPeriodMatrix(A2));
end intrinsic;

intrinsic EndomorphismRing(P::Mtrx) -> AlgMat
{Returns the endomorphism ring, as a matrix algebra, of the analytic
Jacobian associated to the period matrix given. If a big period
matrix, P, is given then also return a list containing an alpha for
each generator, M, of the matrix algebra such that alpha P = P M.}
  g := NumberOfRows(P);
  if NumberOfColumns(P) eq g then
    small := true;
    tau := P;
  else
    require NumberOfColumns(P) eq 2*g: "The input must be gxg or gx2g matrix";
    small := false;
    tau := tauFromPerM(P);
  end if;

  mlst := AnalyticHomomorphisms(tau,tau);
  MA := MatrixAlgebra<IntegerRing(),2*g | mlst >;
  // greedily drop generators:
  for i := #mlst to 1 by -1 do
    if(MA eq MatrixAlgebra<IntegerRing(),2*g | Remove(mlst,i) >) then
      Remove(~mlst,i);
    end if;
  end for;
  MA := MatrixAlgebra<IntegerRing(),2*g | mlst >;
  if not small then
    C := BaseRing(P);
    alst := [];
    for M in mlst do
      Pp := P*Matrix(C,M);
      alpha := Submatrix(Pp,1,1,g,g)*Submatrix(P,1,1,g,g)^-1;
      max := Max([Abs(d) : d in ElementToSequence(alpha*P - Pp)]);
      assert max lt 10^-10;
      Append(~alst,alpha);
    end for;
    return MA, alst;
  else
    return MA;
  end if;
end intrinsic;

intrinsic EndomorphismRing(A::AnHcJac) -> AlgMat, SeqEnum
{Returns the endomorphism ring, as a matrix algebra, of the analytic
Jacobian given. If the analytic Jacobian has big period matrix P, also
return a list containing an alpha for each generator, M of the matrix
algebra such that alpha P = P M.}
  return EndomorphismRing(BigPeriodMatrix(A));
end intrinsic;

intrinsic AllLinearRelations(q::SeqEnum[FldReElt], p::RngIntElt) -> Lat
{Given a sequence with entries from a real field, return the lattice of all
(small) integer linear dependencies among the entries. The precision p is
used for two purposes, namely a relation must be zero to approximately 10^(-p),
and secondly the coefficients themselves must be bounded approximately by p.}
 require p gt 0: "The precision must be a positive integer"; U:=Universe(q);
 require p le Precision(U): "Given precision exceeds Universe precision";
 I:=[1..#q];
 M:=Matrix([[q[j]] cat [i eq j select 10^(-p) else 0 : i in I] : j in I]);
 A,B:=LLL(M); E:=Rows(B)[[i : i in I | Norm(A[i]) lt p^2*#q^2*10^(-2*p)]];
 return Lattice(Matrix(E)); end intrinsic;

intrinsic AllLinearRelations(q::SeqEnum[FldComElt], p::RngIntElt) -> Lat
{Given a sequence with entries from a complex field, return the lattice of all
(small) integer linear dependencies among the entries. The precision p is
used for two purposes, namely a relation must be zero to approximately 10^(-p),
and secondly the coefficients themselves must be bounded approximately by p.}
 require p gt 0: "The precision must be a positive integer"; U:=Universe(q);
 require p le Precision(U): "Given precision exceeds Universe precision";
 L1:=AllLinearRelations([Real(x) : x in q],p);
 L2:=AllLinearRelations([Imaginary(x) : x in q],p);
 return L1 meet L2; end intrinsic;

