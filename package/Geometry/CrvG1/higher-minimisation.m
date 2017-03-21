freeze;

// Minimisation for higher descents 
// (called by routines 6-, 8- and 12-descent)
// N.B. method is ad hoc, but seems to work in most cases
// Version March 2010
// T. Fisher

MC := MonomialCoefficient;
MD := MonomialsOfDegree;

function MyRowReduce(mat)
  L := PureLattice(Lattice(mat));
  return LLL(Matrix(Rationals(),[Eltseq(x): x in Basis(L)]));
end function;

function MyRowReduceEqns(quads,d)  
  R := Universe(quads);
  mons := MonomialsOfDegree(R,d);
  mat := Matrix(#quads,#mons,[MC(q,mon):mon in mons,q in quads]);
  mat := MyRowReduce(mat);
  quads := [&+[mat[i,j]*mons[j]: j in [1..#mons]]:i in [1..Nrows(mat)]];
  return quads;
end function;

function MyPureLatticeAtp(qq,p)
  n := Rank(Universe(qq));
//  m := Integers()!(n*(n-3)/2);
//  assert #qq eq m;
  m := #qq;
  Rp<[y]> := PolynomialRing(GF(p),n);
  mons := MD(Rp,2);
  qq1 := qq;
  cob := IdentityMatrix(Rationals(),m);
  gain := 0;
  bigmat := Matrix(GF(p),m,#mons,[MC(Rp!q,mon): mon in mons,q in qq1]);
  r := Rank(bigmat);
  while r lt m do
    gain +:= (m-r);
    km := KernelMatrix(bigmat);
    V := VectorSpace(GF(p),m);
    U := sub<V|[V!km[i] : i in [1..Nrows(km)]]>;
    mm := Matrix(Integers(),m-r,m,Basis(U));
    _,_,mat := SmithForm(mm);
    mat := mat^(-1);
    dd := [1/p: i in [1..m-r]] cat [1: i in [1..r]];
    mat1 := DiagonalMatrix(Rationals(),dd);
    mat := mat1*mat;
    qq1 := [&+[mat[i,j]*qq1[j]: j in [1..m]]: i in [1..m]];
    bigmat := Matrix(GF(p),m,#mons,[MC(Rp!q,mon): mon in mons,q in qq1]);
    r := Rank(bigmat);
  end while;
  return qq1,gain;
end function;

function MinimisationAttempt(qq,U) 
  R := Universe(qq);
  n := Rank(R);
  assert BaseRing(R) cmpeq Rationals();
  mons := MD(R,2);
  coeffs := [MC(q,mon): mon in mons,q in qq];
  assert forall{c: c in coeffs|IsIntegral(c)};
  K := Field(U);
  p := Characteristic(K);
  d := Dimension(U);
  mm := Matrix(Integers(),d,n,Basis(U));
  _,_,mat := SmithForm(mm);
  dd := [p: i in [1..d]] cat [1: i in [d+1..n]];
  mat1 := DiagonalMatrix(Rationals(),dd);
  mat := mat*mat1;
  mat := Transpose(LLL(Transpose(mat)));
  subst := [&+[mat[i,j]*R.j : j in [1..n]]: i in [1..n]];
  qq1 := [Evaluate(q,subst): q in qq];
  qq2,gain := MyPureLatticeAtp(qq1,p);
  gain := gain - (n-3)*d;
  vprintf Minimisation,2 : "Gain is %o\n",gain;
  if gain gt 0 then
    qq2 := MyRowReduceEqns(qq2,2);
  end if;
  return qq2,mat,gain;
end function;

function RandomSubset(r,n)
  assert r le n;
  S := {};
  for ctr in [1..r] do
    T := {j : j in [1..n] | j notin S};
    S join:= {Random(T)};
  end for;
  return S;
end function;

function LinearFormsInRadical(I)
  R := Generic(I);
  k := BaseRing(R);
  n := Rank(R);
  W := VectorSpace(k,n);
  V := W;
  d := Dimension(I)-1;
  p := Characteristic(k);
  vprintf Minimisation,2 : "Reduction mod %o has dimension %o\n",p,d;
  flag := false;
  for ctr in [1..10] do
    S := RandomSubset(d,n);
    J := ideal<R|[R.i: i in S]>;
    II := I + J;
    if p notin {} then 
      try  
        vtime Minimisation,2 : dimn := Dimension(II);
        vprint Minimisation,2 : "Dimension =",dimn;
        vprint Minimisation,2 : "computing radical";
        vtime Minimisation,2 :
        rad := Radical(II); 
     // rad := Radical(II:Direct);  
        vprint Minimisation,2 : "radical computed";
        ff := [f : f in MinimalBasis(rad)| TotalDegree(f) eq 1];
        V1 := sub<W|[W![MC(f,R.i): i in [1..n]]: f in ff]>;
        V := V meet V1;
//      printf "dim(V1) = %o  dim(V) = %o\n",Dimension(V1),Dimension(V);
      catch e
        print "There was an error computing the radical";
//        SetOutputFile("bugdetails");
//        printf "Error computing radical of \n%m\n",II;
//        UnsetOutputFile();
      end try;
    end if;
    if Dimension(V) eq 0 then flag := true; break; end if;
    ff := [&+[v[i]*R.i: i in [1..n]]: v in Basis(V)];
    ff := [f : f in ff | f^4 in I];
//    vprintf Minimisation : "We find %o linear forms in the radical\n",#ff;
    if #ff eq Dimension(V) then flag := true; break; end if;
    I := I + ideal<R|ff>;
  end for;
  dimV := Dimension(V);
  vprintf Minimisation,2 : "We find %o linear forms in the radical\n",dimV;
  if not flag then 
    vprint Minimisation,1 : "Warning : linear forms not necessarily in radical";
  end if;
//  print "Computing radical directly";
//  time rad := Radical(I);
//  ff := [f : f in MinimalBasis(rad)| TotalDegree(f) eq 1];
//  V := sub<W|[W![MC(f,R.i): i in [1..n]]: f in ff]>;
  return V;  
end function;

intrinsic MinimisationMatrix(qq,primes)-> AlgMatElt 
{Attempts to minimise the variety defined by the system of quadrics qq,
at the given primes}

  n := Rank(Universe(qq));
//  assert #qq eq n*(n-3)/2;
  cob := IdentityMatrix(Rationals(),n);
  for p in primes do
    vprintf Minimisation : 
      "Attempting to minimise at p = %o\n",p;
    IndentPush();
    gain := 0;
    repeat
      Rp<[x]> := PolynomialRing(GF(p),n);
      Ip := ideal<Rp|[Rp!q : q in qq]>;
      Vp := LinearFormsInRadical(Ip);
      gain := 0;
      if Dimension(Vp) gt 0 then 
        qq1,cob1,gain := MinimisationAttempt(qq,Vp);
      end if;
      if gain gt 0 then 
        qq := qq1; 
        cob := cob*cob1;
      end if;
    until gain le 0;
    IndentPop();
  end for;
  return Transpose(LLL(Transpose(cob)));
end intrinsic;
