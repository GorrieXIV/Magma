
// minred-demo2.m
// Some examples to test minimisation and reduction
// Version 22nd July 2008

SetVerbose("Reduction",1);
SetVerbose("Minimisation",2);
SetVerbose("QuarticReduce",0);

Q := Rationals();
Id := IdentityMatrix;

function RationalGCD(S)
   Z := Integers();
   Q := Rationals();
   d := LCM([Denominator(Q!x):x in S| x ne 0] cat [1]);
   return Universe(S)!(GCD([Z!(x*d): x in S])/d);
end function;

PRIM := func<seq|[Integers()|x/d: x in seq] where d is RationalGCD(seq)>;

model := GenusOneModel(Q,5,
  [-1,-3,-3,4,0,1,0,-2,1,-1,0,0,0,-1,-2,1,0,1,-1,-1,1,1,1,-2,1,
  -1,-1,-2,0,1,-1,-1,-1,0,-1,-1,0,0,-1,0,0,1,0,0,-1,0,0,-1,-1,1]);

print "We start with the model with coefficients";
print Eltseq(model);
print "We apply a random unimodular transformation";
tr := RandomTransformation(5:Unimodular,Size:=100);
phi := tr*model;
phi1,tr1 := Reduce(phi : Minkowski);
assert tr1*phi eq phi1;
print "After reducing the model has coefficients";
print Eltseq(phi1);
print "Overall transformation";
print tr1*tr;

print "";

print "We double the model, i.e. multiply by 2 in H^1(Q,E[5])";
time model2 := DoubleGenusOneModel(model);
print "The new model has coefficients";
print Eltseq(model2);
phi,tr := Minimise(model2);
assert tr*model2 eq phi;
phi,tr1 := Reduce(phi : Minkowski);
tr := tr1*tr;
assert tr*model2 eq phi;
print "After minimising and reducing it has coefficients";  
print Eltseq(phi);

print "Doubling again gives"; // would just give (-1)*(original model)";
time model4 := DoubleGenusOneModel(phi);
_,tr1 := IsTransformation(5,<Transpose(m): m in Tuple(tr)>);
phi1 := tr1*model4;
print Eltseq(phi1);
print "which is simply (-1)*(original model)";
assert Vector(Eltseq(phi1)) eq -Vector(Eltseq(model));

print "/////////////////////////////////////////////////////////////";
print "/////////////////////////////////////////////////////////////";

E := EllipticCurve([ 1, 0, 1, -3961560, -3035251137 ]);
P := E![-10343/9,15502/27];
print "E =",aInvariants(E);
print "P =",P;
print "h(P)  =",Height(P); 

phi,pt := GenusOneModel(5,P);
print "Model has coefficients";
print Eltseq(phi);
print "Searching for points .....";
C := Curve(phi);
pts := PointSearch(C,10^4);
P4Z := ProjectiveSpace(Integers(),4);
print {P4Z!PRIM(Eltseq(pt)): pt in pts};
print "The point that maps down to P is:  Q =",P4Z!PRIM(Eltseq(pt));
// print "Computing covering map";
// C,_,pi := nCovering(phi:E:=E);
// print "These points map down to";
// print [pi(C!Eltseq(pt)): pt in pts]; 

print "/////////////////////////////////////////////////////////////";
print "/////////////////////////////////////////////////////////////";

E := EllipticCurve([ 1, 0, 1, -3961560, -3035251137 ]);
r := 1444067711193161151653909885248174530531193797834370513997358074997\
  370310404457472012138726088286265069724174055954168887973156173644540\
  5185451187391361335833;
s := -53879482447658061183722803305824349047504913109038237184003453833845\
  450236551860699170659516701341037148199683612682243476423780974589591\
  787079465837072436296880764527226540521645634714128124387816154105110\
  218383771518121927100986107530;
t := 38696980895872965778173140061667235695331988051796572460157672420992532650171;
P := E![r/t^2,s/t^3];
print "E =",aInvariants(E);
// print "P =",P;
print "h(P)  =",Height(P); 
phi,pt := GenusOneModel(5,P);
print "Model has coefficients";
print Eltseq(phi);
print "The point that maps down to P is:  Q =",P4Z!PRIM(Eltseq(pt));

SetVerbose("Reduction",0);

print "";
print "The same calculation for n = 2,3,4 :";
print "";
for n in [2..4] do
  model,pt := GenusOneModel(n,P);
  print model;
  pt := Eltseq(pt);
  if n gt 2 then pt := PRIM(pt); end if;
  print "Q =",pt;
  C,_,pi := nCovering(model:E := E);
  QQ := C!Eltseq(pt);
  assert pi(QQ) in {-P,P};
  print "";
end for;

SetVerbose("Minimisation",0);

print "A comparison in the case n = 3";

printf "Old version takes ";
time F,map,pt := CubicFromPoint(E,P);  
// used to make longer, but now calls new version
model1 := GenusOneModel(F);
assert map(pt) in {-P,P};

printf "New version takes ";
time  model2,pt := GenusOneModel(3,P); // 0.420 seconds
C,_,map := nCovering(model2:E := E);
pt := C!Eltseq(pt);
assert map(pt) in {-P,P};
tr1 := RandomTransformation(3);
tr2 := RandomTransformation(3);
assert IsEquivalent(tr1*model1, tr2*model2);

print "/////////////////////////////////////////////////////////////";
print "/////////////////////////////////////////////////////////////";

E := EllipticCurve([0,7823]);
phi0 := GenusOneModel(Rationals(),4,
          [0,2,1,1,0,0,1,1,0,-2,1,0,1,-1,2,-1,2,-1,-1,1]);
assert cInvariants(phi0) eq cInvariants(E);
C,_,pi := nCovering(phi0:E:=E);
pts := PointsQI(C,10^3);
P := pi(pts[1]);
// print Height(P);

mymodels := [];
pts := [];

for n in [2..5] do
  phi,pt := GenusOneModel(n,P);
  if n eq 4 then assert IsEquivalent(phi,phi0); end if;
  mymodels cat:= [phi];
  pts cat:= [PRIM(Eltseq(pt))];
end for;

print "The generator for E(Q) where E : y^2 = x^3 + 7823";
printf "has height h(P) = %o\n",Height(P);
print "It may be found by searching for points on any of the following n-coverings.";
for n in [2..5] do
  printf "n = %o  coeffs = %o\n",n,Eltseq(mymodels[n-1]);
end for;
print "The points we would need to find are";
for n in [2..5] do
 printf "n = %o  Q = %o\n",n,pts[n-1];
end for;

print "/////////////////////////////////////////////////////////////";
print "/////////////////////////////////////////////////////////////";

print "Continuing with the last example with n = 5";
E := EllipticCurve([0,7823]);
phi := GenusOneModel(Rationals(),5,
   [-1,0,-1,0,0,0,1,-1,0,-1,1,1,0,1,-1,0,0,1,-1,0,1,1,0,0,0,
    0,0,1,1,-1,0,0,0,0,1,0,0,1,2,0,0,-1,0,0,0,-1,0,-1,0,0]);
assert cInvariants(phi) eq cInvariants(E);
C := Curve(phi);
print "The genus one model with coefficients";
print Eltseq(phi);
print "has rational points";
time pts := PointSearch(C,10^2);
print {ProjectiveSpace(Integers(),4)!PRIM(Eltseq(pt)): pt in pts};

print "We double this genus one model";
time model2 := DoubleGenusOneModel(phi);
R<x1,x2,x3,x4,x5> := PolynomialRing(phi);
cc := Discriminant(phi);
mat1 := Matrix(Rationals(),5,5,
   [ 0, 0, 0, 1, -1, 
     0, 0, -1, 0, -1, 
     0, 0, 0, 0, 1, 
     -1, 0, 0, 0, 0, 
     -1, -1, -1, 0, 0 ]);
mat2 := Matrix(Rationals(),5,5,
   [  50, 58, 86, -74, -70, 
      49, 95, -59, -34, -26, 
      -7, -65, 27, -92, -72, 
      54, -6, 4, 66, -104, 
      86, -80, 56,-14, -4 ]);
assert Determinant(mat2) eq cc;
_,tr := IsTransformation(5,<mat1,(1/cc)*mat2>);
phi2 := tr*model2;
print "The result has coefficients";
print Eltseq(phi2);
assert Eltseq(phi2) eq [1,0,1,-1,-1,-1,0,0,0,1,0,0,-1,0,-1,0,-1,0,0,0,0,
      0,0,0,-1,0,-1,-1,1,0,0,-1,0,-1,-1,0,0,0,-1,1,0,1,-1,0,0,1,0,0,0,0];
print "Searching for rational points";
C2 := Curve(phi2);
time pts := PointSearch(C2,10^4);
print {ProjectiveSpace(Integers(),4)!PRIM(Eltseq(pt)): pt in pts};
print "Nothing found - but then we are looking on the wrong curve.";
eqns := Equations(phi2);
jmat := Matrix(R,5,5,[Derivative(q,R.i):i in [1..5],q in eqns]);
S := (1/2)*Determinant(jmat);
mypt := [0,2,2,3,-1];
assert Evaluate(S,mypt) eq 0;
printf "However, P0 = %o is a point on the secant variety S,\n",P4Z!mypt;
R<x1,x2,x3,x4,x5> := PolynomialRing(phi2);
tgt := &+[Evaluate(Derivative(S,R.i),mypt)*R.i:i in [1..5]];
P4 := Proj(R);
C := Scheme(P4,Equations(phi2));
H := Scheme(P4,tgt);
X := C meet H;
pt := Points(X)[1];
print "and the tangent space to S at P0 meets the curve at";
print P4Z!PRIM(Eltseq(pt));
print "Searching for points on S (a degree 5 hypersurface in P^4)";
time pts := PointSearch(Scheme(P4,S),5);
print [P4Z!PRIM(Eltseq(x)): x in pts];
