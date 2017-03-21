freeze;

//////////////////////////////////////////////////////////////////////////
// Naive code for reduction of an arbitrary system of quadrics over Q   //
//                                                                      //
// Steve Donnelly, 2005                                                 //
//////////////////////////////////////////////////////////////////////////

declare verbose Reduce, 3;

import "../CrvEll/ThreeDesc/trivialize.m" : UpperR;

function matsize(mat)
  return &+[c^2 : c in Eltseq(mat)];
end function;

function LLLR(Fseq)
  mons := MonomialsOfDegree(Parent(Fseq[1]), 2);
origmat := Matrix([[MonomialCoefficient(f, m) : m in mons] : f in Fseq]);
  fmat, LLLtr := LLL(Matrix([[MonomialCoefficient(f, m) : m in mons] : f in Fseq]));
assert fmat eq ChangeRing(LLLtr,Rationals())*origmat;
  return [&+[fmat[i,j]*mons[j] : j in [1..#mons]] : i in [1..#Fseq]], LLLtr;
end function;

function Red2(Fseq, i, j)
  PP := Universe(Fseq);
  n := Rank(PP);
  P := PolynomialRing(CoefficientRing(PP));
  subst := [k eq i select P.1 else k eq j select 1 else 0 : k in [1..n]];
  F1 := &+[Evaluate(F, subst)^2 : F in Fseq];
  tr := IdentityMatrix(Integers(), n);
  deg := 2*TotalDegree(Fseq[1]);
  if F1 eq 0 or Degree(F1) lt deg-1 or Discriminant(F1) eq 0 then
     return Fseq, tr;
  end if;
  F1, mat := Reduce(F1, deg);
  tr[i,i] := mat[1,1];
  tr[i,j] := mat[1,2];
  tr[j,i] := mat[2,1];
  tr[j,j] := mat[2,2];
  Fseq := [Evaluate(F, [k eq i select mat[1,1]*PP.i + mat[1,2]*PP.j else
                        k eq j select mat[2,1]*PP.i + mat[2,2]*PP.j
                                else PP.k
                        : k in [1..n]])
           : F in Fseq];
  return Fseq, tr;
end function;

function RedForms(Fseq)   // [RngMPolElt] -> SeqEnum
  
  vprintf Reduce, 1: "RedForms ...\n";

  s1 := &+[&+[c^2 : c in Coefficients(F)] : F in Fseq];
  PP := Universe(Fseq);
  n := Rank(PP);
  tr := IdentityMatrix(Integers(), n);
  LLLtr := IdentityMatrix(Integers(), #Fseq);
  repeat
    s := s1;
    Fs := [<f, t> where f, t := Red2(Fseq, i, j) : j in [i+1..n], i in [1..n]];
    Fs := [<f, a[2], LLLt> where f, LLLt := LLLR(a[1]) : a in Fs];
    s1, pos := Min([&+[&+[c^2 : c in Coefficients(p)] : p in F[1]] : F in Fs]);
    Fseq, tr1, LLLtr1 := Explode(Fs[pos]);
    tr := tr*tr1; 
    LLLtr := LLLtr1*LLLtr;
    vprintf Reduce, 3: "    size = %o\n", s1;
  until s1 ge s;
  tr := Transpose(tr);
  
  return Fseq, tr, LLLtr;
end function;


// TO DO: Sort out stopping conditions in inner and outer loops!
//        (The stuff with s1min etc is nonsence!)

intrinsic ReduceQuadrics(Qs:: SeqEnum[RngMPolElt] : Rescale:=false) -> SeqEnum, Map
{Takes a sequence of quadrics in x_0,..x_n defined over Q and finds
a good basis for the space that the quadrics span and a linear
change of coordinates so that the quadrics in the transformed basis
have small, integral coefficients. Returns the transformed basis
and the coordinate change map.}

  R := Universe(Qs);
  require (BaseRing(R) eq Rationals()) or (BaseRing(R) eq Integers()):
      "Quadrics should be defined over the rationals or integers";
  if BaseRing(R) eq Integers() then
      R := ChangeRing(R,Rationals());
      Qs := ChangeUniverse(Qs,R);
  end if;
  origQs := Qs;
  
  // Rescale ...
  for i := 1 to #Qs do 
     Q := Qs[i];
   commondenom := LCM([Denominator(c): c in Coefficients(Q)]);
     if Rescale then Q *:= commondenom;
     else require commondenom eq 1 : "The coefficients should not have denominators,", 
                                     " unless Rescale is set to true";
     end if;
  end for;
  require &and[&and[TotalDegree(t) eq 2 : t in Terms(Q)] : Q in Qs] :
      "The given sequence must contain homogeneous quadatric forms";

  mons := MonomialsOfDegree(R,2);
  V := VectorSpace(Rationals(), #mons);
  toV := map< R -> V | pol :-> V![ MonomialCoefficient(pol,mon) : mon in mons ] >;
  n := Rank(R);

  tr := IdentityMatrix(Integers(), n);
  LLLtr := IdentityMatrix(Integers(), #Qs);
  s1 := &+[&+[c^2 : c in Coefficients(Q)] : Q in Qs]; //size measure
  s1min := s1;   // smallest size so far!
  s1s := {s1};   // all sizes encountered so far!
  vprintf Reduce,1: "size: %o\n",s1;

  T := IdentityMatrix(Integers(),n);
  while true do
    olds1 := s1;
    s1min_inner := s1;
    while true do
        s := s1;
        // convert to symmetric matrices
        Ms := [ M+Transpose(M) where M is (1/2)*
                UpperTriangularMatrix([MonomialCoefficient(Q,R.i*R.j):
                    j in [i..n], i in [1..n]]) : Q in Qs ];
        // get sum of +ive def upper bounds for the Ms
        M := &+[f(M) : M in Ms]
             where f := func<m | 1/Sqrt(matsize(m))*U1
                   where U1 := ChangeRing(U, RealField())
                   where U := UpperR(m + Transpose(m))>;
        M := (1/2)*(M + Transpose(M)); // guarantee it's exactly symmetric!

        // get unimodular matrix to LLL-reduce M (as a Gram matrix)
        _,T,_ := LLLGram(M);
        lin := hom<R->R| Eltseq( ChangeRing(Transpose(T),R)*
                Matrix(n,1,[R.i:i in [1..n]]) ) >;
        Qs := [lin(Q):Q in Qs];
        tr := T*tr;
        vprint Reduce,2: "transformation of variables was ", T;

        // get LLL reduced basis for Qs    
        Qs, LLLtr1 := LLLR(Qs);
        LLLtr := LLLtr1*LLLtr;
        s1 := &+[&+[c^2 : c in Coefficients(Q)] : Q in Qs];
        vprintf Reduce,1:  "size: %o\n",s1;
        if s1 ge s1min_inner then break; end if;
        s1min_inner := Min(s1, s1min_inner);
         // print "transformation of equations was ", fmat;

    end while;
    vprint Reduce,2:  "sensible step yields ", Qs;

    /*
    // Random hit
    list := [];
    for i := 1 to 10 do
       r := Random(4,7);
       T := RandomSLnZ(7, Random(2,2), Random(12,15)+Ceiling(6/4*Log(s1)) );
       lin := hom<R->R| Eltseq( ChangeRing(Transpose(T),R)*
                Matrix(n,1,[R.i:i in [1..n]]) ) >;
       Qstemp := [lin(Q):Q in Qs];
       sizetemp := &+[&+[c^2 : c in Coefficients(Q)] : Q in Qstemp];
       Append(~list, <T,sizetemp>);
    end for;
    sizes := [ pair[2] : pair in list ];
    print "random sizes are ", sizes;
    index := Index(sizes, Min(sizes));
    T := list[index][1];
    lin := hom<R->R| Eltseq( ChangeRing(Transpose(T),R)*
                Matrix(n,1,[R.i:i in [1..n]]) ) >;
    Qs := [lin(Q):Q in Qs];
    tr *:= T;
    print "Random hit by ", T;
    */

    // Silly step (best of the possible 2 by 2 transformations):
    Qs, T, LLLtr1 := RedForms(Qs);
    tr := T*tr;
    LLLtr := LLLtr1*LLLtr;
    
    // Qs, LLLtr1 := LLLR(Qs);
    // LLLtr := LLLtr1*LLLtr;
    vprint Reduce,2: "silly step gives transformation ",T;
    s1 := &+[&+[c^2 : c in Coefficients(Q)] : Q in Qs];
    vprintf Reduce,1: "size: %o\n",s1;
    // if s1 eq s1min or s1 eq olds1 then break; end if;
    if s1 in s1s or s1 eq olds1 then break; end if;
    s1min := Min(s1, s1min);
    Include( ~s1s, s1);
  end while;

  // check
  VQs := sub< V | [toV(Q) : Q in Qs] >;
  lin := hom<R->R| Eltseq( ChangeRing(Transpose(tr),R)*Matrix(n,1,[R.i:i in [1..n]]) ) >;
  assert &and[ toV(lin(Q)) in VQs : Q in origQs ];  // this checks tr only (not LLLtr)
  for i := 1 to #Qs do 
  assert sub< V | toV(Qs[i])> eq sub< V | toV(&+[ LLLtr[i,j]*lin(origQs[j]) : j in [1..#Qs] ]) >;
  end for; 

  return Qs, tr, LLLtr;
end intrinsic;


