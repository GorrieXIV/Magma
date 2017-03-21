Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;


">>> TESTS #1 <<<";

K:=pAdicField(5,20);
O:=Integers(K);
R<x>:=PR(K);
U<X>:=PR(Q);

F:=SplittingField(x^5-2); 
assert AbsoluteDegree(F) eq 20;
F:=SplittingField(x^10-2); 
assert AbsoluteDegree(F) eq 40;

">>> TESTS #2 <<<";

GS:=[<40,12>,<40,12>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<8,3>,
     <4,2>,<6,1>,<20,3>,<20,3>,<16,7>,<1,1>,<16,7>,<8,2>];
GS4:=[<5,1>,<10,2>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<1,1>,<4,2>,
      <2,1>,<3,1>,<5,1>,<5,1>,<4,2>,<1,1>,<4,2>,<4,1>];

for prec in [25,40,200] do
K:=pAdicField(2,prec);
R<x>:=PR(K);
i:=0;
for f in [x^10+2, x^10-2, x, x-1, x*(x-1), 2*x*(x-1), x*(x-1)/2, x*(x-2), x*(x+1/8),
          x^4-3, x^4+1, x^3-2, x^5-8, x^5-2, x^8+2, x*(x-1)*(x-2), 2*x^8+1, 2*x^8+2] do
  i+:=1;
  prec,i,PR(Q)!f;  
  G:=GaloisGroup(f);
  IdentifyGroup(G);
  assert IdentifyGroup(G) eq GS[i];
end for;
end for;


">>> TESTS #3 <<<";

K:=pAdicField(2,20);
K1:=ext<K|2>;
K2<r>:=ext<K1|Polynomial([K1|2,0,1])>;
K3:=ext<K2|2>;
K4:=ext<K3|Polynomial([K3|r,0,1])>;

R<x>:=PR(K4);

i:=0;
for f in [x^10+2, x^10-2, x, x-1, x*(x-1), 2*x*(x-1), x*(x-1)/2, x*(x-2), x*(x+1/8),
          x^4-3, x^4+1, x^3-2, x^5-8, x^5-2, x^8+2, x*(x-1)*(x-2), 2*x^8+1, 2*x^8+2] do
  i+:=1;
  i;
  G:=GaloisGroup(f);
  assert IdentifyGroup(G) eq GS4[i];
end for;


">>> TESTS #4 <<<";


K0:=pAdicField(2,20);
R<x>:=PR(K0);

for K in [K0,ext<K0|(x+1)^2+1>] do
  K;
  R<x>:=PR(K);

  for i,j,k in [1..3] do 
    f:=x^i*(x^2-2)^j*(x^2+x+1)^k;
    assert GroupName(GaloisGroup(f)) eq "C2^2";
  end for;
end for;


">>> TESTING DONE <<<";
