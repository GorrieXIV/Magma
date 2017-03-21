freeze;

/////////////////////////////////////////////////////////////////////
//                                                                 //
// Local solvability of a homogeneous quartic over F(T) where      //
// f is a finite field.                                            //
//                                                                 //
// Also includes IsELS - true iff the quartic is everywhere        //
// locally solvable.                                               //
//                                                                 //
/////////////////////////////////////////////////////////////////////

// Preliminary functions...

function reverseQ(f);
    K:=Parent(f);
    return hom<K->K|K.2,K.1>(f);
    end function;

function findroot(f)
  assert TotalDegree(f[1]) eq 1;
  a,b:=Explode([MonomialCoefficient(f[1],x): x in [[1,0],[0,1]]]);
  if a eq 0 then return "infinity"; end if;
  assert Evaluate(f[1],[-b/a,1]) eq 0;
  return -b/a;
  end function;

function plc(f)
  g:=Integers(Parent(f))!f;
  facg:=Factorization(g);
  if #facg eq 1 then return Zeroes(f)[1]; end if;
  return Zeroes(f);
  end function;

function cleardenom(f)
  cfs:=Coefficients(f);
  h:=LCM([Denominator(c): c in cfs]);
  if h eq 1 then return f; end if;
  return h^2*f;
  end function;

function specialize(f,x);
  cfs:=Coefficients(f);
  cfs1:=[Evaluate(c,x): c in cfs];
  return &+[cfs1[i]*Monomials(f)[i]: i in [1..#cfs1]];
  end function;

function ispmatrix(M,p);
  R:=Integers(Parent(p));
  return &and[IsCoercible(R,(x/p)): x in Eltseq(M)];
  end function;

/////////////////////////////////////////////////////////////////

function one_recursion(f,M,p:debug:=false)

KUV:=Parent(f);
K:=BaseRing(KUV);
R:=Integers(K);
F:=BaseRing(K);
uv:=PolynomialRing(F,2);
alpha:=F!1;
while IsSquare(alpha) do
  alpha:=Random(F);
  end while;


cfs:=Coefficients(f);
// we assume denominators have been cleared - this only needs to be done once
// so will have been done before this function is called.


// remove even powers of p from the coefficients
if debug then print "removing even powers of p..."; end if;
minval:=Min([Valuation(c,plc(p)): c in cfs]);
mv:=2*(minval div 2);
if minval gt 1 then
  g:=f/(p^mv);
  return [<g,M,0>],"even power of p removed";
  end if;

// next we deal with the case where f is divisible by p

if minval eq 1 then if debug then print "f is divisible by p"; end if;

  f1:=f/p;
  e:=Roots(R!p)[1][1];
  f2:=uv!specialize(f1,e);

  if debug then print "reduced quartic: ",f2; end if;
  fac:=Factorization(f2); if debug then print "Factorization: ",fac; end if;

  // examining the factorization and roots of f2

  deg_mult:=[<TotalDegree(r[1]),r[2]>: r in fac];
   if <1,1> in deg_mult then
    return [<f,M,1>],"non-repeated root of reduced quartic"; end if;

  dm1:=[d[1]: d in deg_mult];
  if not (1 in dm1) then
    return [<f,M,-1>],"reduced quartic has no roots"; end if;

  if debug then print "examining the repeated roots of reduced quartic:"; end if;
  fc1:=[fc: fc in fac|TotalDegree(fc[1]) eq 1];
  assert #fc1 in [1,2];
  if #fc1 eq 2 then TWO:=true; else TWO:=false; end if;

  if not TWO then
    root:=findroot(fc1[1]);
    if root cmpeq "infinity" then
      return [<Evaluate(f,[KUV.1,p*KUV.2])/(p^2),M*DiagonalMatrix(K,[1,p]),0>],
      "repeated root at infinity, recursing..."; end if;
      // return [<reverseQ(f),M*Matrix(K,[[0,1],[1,0]]),0>],"repeated root at infinity, recursing...";
      // end if;
    return [<Evaluate(f,[p*KUV.1+root*KUV.2,KUV.2])/(p^2),M*Matrix([[p,root],[0,1]]),0>],
    "repeated root, recursing..."; end if; // end if not TWO

  r1:=findroot(fc1[1]);
  r2:=findroot(fc1[2]);
  if r1 cmpeq "infinity" then
    g1:=Evaluate(f,[KUV.1,p*KUV.2])/(p^2); mat1:=DiagonalMatrix(K,[1,p]);
    // g1:=reverseQ(f); mat1:=Matrix(K,[[0,1],[1,0]]);
    else
    g1:=Evaluate(f,[p*KUV.1+r1*KUV.2,KUV.2])/(p^2); mat1:=Matrix([[p,r1],[0,1]]);
    end if;
  if r2 cmpeq "infinity" then
    g2:=Evaluate(f,[KUV.1,p*KUV.2])/(p^2); mat2:=DiagonalMatrix(K,[1,p]);
    // g2:=reverseQ(f); mat2:=Matrix(K,[[0,1],[1,0]]);
    else
    g2:=Evaluate(f,[p*KUV.1+r2*KUV.2,KUV.2])/(p^2); mat2:=Matrix([[p,r2],[0,1]]);
    end if;
  return [<g1,M*mat1,0>,<g2,M*mat2,0>], "two repeated roots, recursing...";

  end if; // end if minval eq 1

// The case where f is not divisible by p

assert minval eq 0;
if debug then print "f is not divisible by p"; end if;

e:=Roots(R!p)[1][1];
f1:=specialize(f,e);
if debug then print "reduced quartic is: ",f1; end if;
  if IsSquare(f1) or (not IsSquare(f1/alpha)) then
    if IsSquare(f1) then
    if debug then print "reduced quartic is a square"; end if;
    else if debug then print "specialized quartic is not constant x square"; end if;
    end if;
  return [<f,M,1>],"at f=a*g^2 test";
  end if;

isq,g:=IsSquare(f1/alpha); assert isq;
if debug then print "reduced quartic is non-square-constant x square. g = ",g; end if;
if debug then print "factorizing g..."; end if;
facg:=Factorization(g);
if debug then print "factorization of g: ",facg; end if;
deg_mult:=[<TotalDegree(r[1]),r[2]>: r in facg];
dm1:=[d[1]: d in deg_mult];
if not 1 in dm1 then
  if debug then print "g has no roots"; end if;
  return [<f,M,-1>],"f = a*g^2, g has no roots"; end if;

if debug then print "creating a and G"; end if;
r:=K.1;
a:=alpha*(r+1-e);
G:=g*(r+1-e);
assert ((Evaluate(a,e) eq alpha) and (specialize(G,e) eq g));

hp:=f-a*G^2;
cfhp:=Coefficients(hp);
mvhp:=Min([Valuation(c,plc(p)): c in cfhp]);
assert mvhp gt 0;
 h:=hp/p;
h1:=specialize(h,e);

assert 1 in dm1;
if debug then print "g has roots - examining the roots of g"; end if;
if #facg eq 2 then TWO:=true; else TWO:=false; end if;
if not TWO then
  root:=findroot(facg[1]);
  if root cmpeq "infinity" then rt:=[1,0];
    f2:=Evaluate(f,[KUV.1,p*KUV.2])/p^2; mx:=DiagonalMatrix(K,[1,p]);
    else rt:=[root,1];
    f2:=Evaluate(f,[p*KUV.1+root*KUV.2,KUV.2])/p^2; mx:=Matrix([[p,root],[0,1]]);
    end if;
  assert Evaluate(g,rt) eq 0;
  if Evaluate(h1,rt) eq 0 then
      return [<f2,M*mx,0>],"root of g is a root of h1, recursing...";
    end if;
  return [<f,M,-1>],"only root of g not a root of h1";
  end if; //end if not TWO

r1:=findroot(facg[1]); r2:=findroot(facg[2]);
if r1 cmpeq "infinity" then rt1:=[1,0];
  f2:=Evaluate(f,[KUV.1,p*KUV.2]); mx2:=DiagonalMatrix(K,[1,p]);
  else rt1:=[r1,1];
  f2:=Evaluate(f,[p*KUV.1+r1*KUV.2,KUV.2])/p^2; mx2:=Matrix([[p,r1],[0,1]]);
  end if;
assert Evaluate(g,rt1) eq 0;
if r2 cmpeq "infinity" then rt2:=[1,0];
  f3:=Evaluate(f,[KUV.1,p*KUV.2]); mx3:=DiagonalMatrix(K,[1,p]);
  else rt2:=[r2,1];
  f3:=Evaluate(f,[p*KUV.1+r2*KUV.2,KUV.2])/p^2; mx3:=Matrix([[p,r2],[0,1]]);
  end if;
assert Evaluate(g,rt2) eq 0;
if (Evaluate(h1,rt1) ne 0) and (Evaluate(h1,rt2) ne 0) then
  return [<f,M,-1>],"roots of g not roots of h1"; end if;
if (Evaluate(h1,rt1) eq 0) and (Evaluate(h1,rt2) eq 0) then
  return [<f2,M*mx2,0>,<f3,M*mx3,0>], "two roots of g are roots of h1, recursing..."; end if;
if Evaluate(h1,rt1) eq 0 then
  return [<f2,M*mx2,0>], "one root of g is a root of h1, recursing..."; end if;
return [<f3,M*mx3,0>], "one root of g is a root of h1, recursing...";

end function;// end function one_recursion

///////////////////////////////////////////////////////////////////

function check_once(seq,p:debug:=false)
  ends:=[x: x in seq|x[3] ne 0];
  others:=[x: x in seq|x[3] eq 0];
  news:=[];
  for o in others do
    new,reason:=one_recursion(o[1],o[2],p:debug:=debug);
    if debug then print reason; end if;
    news:=news cat new;
    end for;
  seq2:=ends cat news;
  notpmatrices:=[x: x in seq2| not ispmatrix(x[2],p)];
  pmatrices:=[x: x in seq2|ispmatrix(x[2],p)];
  pends:=[<x[1],x[2],-1>: x in pmatrices];
  return notpmatrices cat pends;
  end function;

///////////////////////////////////////////////////////////////////
//Now the main function...

function LocSol(f,p:debug:=false);

isz:=&or[IsZero(MonomialCoefficient(f,x)): x in [[4,0],[0,4]]];
if isz then
  if debug then print "one of the end coefficients is zero"; end if;
  return true; end if;

//first if p is the place at infinity...
T:=BaseRing(Parent(f)).1;
if p eq 1/T then
  if debug then print "place at infinity - replacing T by 1/T..."; end if;
  cfs:=Coefficients(f);
  mons:=Monomials(f);
  assert f eq &+[cfs[i]*mons[i]: i in [1..#cfs]];
  cfs2:=[Evaluate(c,1/T): c in cfs];
  f1:=&+[cfs2[i]*mons[i]: i in [1..#cfs]];
  f:=cleardenom(f1); p:=T;
  end if;

// Create the appropriate fields and rings if p has degree > 1...
DP:=(Degree(p) gt 1);
if DP and debug then
  print "degree of p >1: creating extensions of rings"; end if;
if DP then
  rts,F1:=RootsInSplittingField(Integers(Parent(p))!p);
  K1:=FunctionField(F1);
  R1:=Integers(K1);
  KUV1:=PolynomialRing(K1,2);
  f:=KUV1!f;
  fctr:=Factorization(R1!Integers(Parent(p))!p);
  e:=rts[1][1];
  assert <R1.1-e,1> in fctr;
  p:=(K1.1-e);
  if debug then print "rings extended"; end if;
  end if;

K:=BaseRing(Parent(f)); F:=BaseRing(K);
p:=K!p;
e:=Roots(Integers(K)!p)[1][1];
isnzsqp:=&or[(not IsZero(mcf)) and (IsSquare(mcf))
  where mcf is Evaluate(MonomialCoefficient(f,x),e): x in [[4,0],[0,4]]];
if isnzsqp then
  if debug then print "one of the end coefficients is a non-zero p-adic square"; end if;
  return true; end if;

seq:=[<f,IdentityMatrix(K,2),0>];
flags:=[0];
i:=0;
while 0 in flags do
  seq:=check_once(seq,p:debug:=debug);
  i+:=1;
  if debug then print "sequence is currently ",seq; end if;
  flags:=[x[3]: x in seq];
  if 1 in flags then
    if debug then print "number of recursions:",i; end if;
    return true; end if;
  end while;
if debug then print "number of recursions:",i; end if;
assert #[x: x in flags| x eq -1] eq #flags;
return false;

end function;  //end function LocSol

/////////////////////////////////////////////////////////////////////////////////

function qI(f);
  K:=BaseRing(Parent(f));
  a,b,c,d,e:=Explode([MonomialCoefficient(f,[4-i,i]): i in [0..4]]);
  return 12*a*e-3*b*d+c^2;
  end function;

function qJ(f);
  K:=BaseRing(Parent(f));
  a,b,c,d,e:=Explode([MonomialCoefficient(f,[4-i,i]): i in [0..4]]);
  return 72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3;
  end function;


function bad_places(f);
  K:=BaseRing(Parent(f));
  R:=Integers(K);
  D:=R!(4*qI(f)^3-qJ(f)^2);
  return [K!x[1]: x in Factorization(D)];
end function;

function istrivial(f); // if f has a root we can clearly take y = 0
  fac:=Factorization(f);
  for g in fac do
    if TotalDegree(g[1]) eq 1 then return true;
      end if;
    end for;
  return false;
  end function;

function isELS(f);
  if istrivial(f) then return true; end if;
  for p in (bad_places(f) cat [1/BaseRing(Parent(f)).1]) do
    if not LocSol(f,p) then return false,p; end if;
    end for;
  return true,_;
end function;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function IsLocallySolvable(f,p)
// (f::RngMPolElt,p::FldFunRatUElt) -> BoolElt
// {returns true if there is a local solution to y^2 = f(U,V) at the "prime" p.
// p must be an irreducible element of the base-ring or, (e.g.), 1/T for the place at infinity}

//require Type(plc(p)) eq PlcFunElt: "p is not a valid place";
//R2:=Parent(f);
//require IsHomogeneous(f) and Rank(R2) eq 2: "f must be a homogenous quartic in two variables";
//require Characteristic(R2) gt 3: "characteristic of base-ring must be 5 or more";

return LocSol(f,p);
end function;

////////////////////////////////////////////////////////////////////////

function IsELS(f)
// (f::RngMPolElt) ->BoolElt,FldFunRatUElt
// {true if y^2 = f(U,V) is everywhere-locally-solvable. If not, then also
//  returns a place where f is not locally-solvable.}

//R2:=Parent(f);
//require IsHomogeneous(f) and Rank(R2) eq 2: "f must be a homogenous quartic in two variables";
//require Characteristic(R2) gt 3: "characteristic of base-ring must be 5 or more";

return isELS(f);
end function;
