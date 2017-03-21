freeze;

/////////////////////////////////////////////////////////////////////
//                                                                 //
// Two Descent algorithm for Elliptic Curves over function fields  //
// of positive characteristic greater than 3.                      //
//                                                                 //
// Author: David Roberts                                           //
//                                                                 //
/////////////////////////////////////////////////////////////////////

declare attributes CrvEll: descent_results;

import "pointsearch.m": PointsOfDegreeH;
import "quartlocsol.m": IsELS;

debug:=false;

/////////////////////////////////////////////////////////////////////
// preliminary functions needed for the full two-torsion case

function two_torsion(E);
  DP:=DefiningPolynomial(E);
  CR:=Parent(DP);
  DPX:=Evaluate(DP,[CR.1,0,1]);
  tors:=[-Evaluate(f[1],[0,0,0]): f in Factorization(DPX)|TotalDegree(f[1]) eq 1];
  return tors;
  end function;

function xpoly(E);
  DP:=DefiningPolynomial(E);
  CR:=Parent(DP);
  DPX:=Evaluate(DP,[CR.1,0,1]);
  R := PolynomialRing(BaseRing(E)); x := R.1;
  g:=hom<CR->R|x,0,0>(DPX);
  return -g;
  end function;

function QuarticCoefficients(f);
    K:=Parent(f);
    A:=[[4-x,x]: x in [0..4]];
    return [MonomialCoefficient(f,a): a in A];
    end function;

function diagonal_conic(abc);
  P2:=ProjectivePlane(Parent(abc[1]));
  eqn:=&+[abc[i]*P2.i^2: i in [1..3]];
  C:=Scheme(P2,eqn);
  flag,con:=IsConic(C);
  if not flag then return "error"; end if;
  return con;
  end function;

function quartic_IJ(q);
  a,b,c,d,e:=Explode(QuarticCoefficients(q));
  return [12*a*e-3*b*d+c^2,72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3];
  end function;

function check_conics(d1d2,eqns);
  if debug then print "checking conics for pair",d1d2; end if;
  d1:=d1d2[1]; d2:=d1d2[2];
  conics:=[Conic(Coefficients(Evaluate(eqn,[d1,d2]))): eqn in eqns];
  R3:=Parent(Evaluate(eqns[1],[d1,d2]));
  K:=BaseRing(conics[1]);
  R:=Integers(K);
  for c in conics do
    if debug then print "checking conic",Index(conics,c), "of 4"; end if;
    flag,p:=HasRationalPoint(c);
    if not flag then return false,_,_; end if;
    if c eq conics[1] then P:=p; end if;
    end for;
  con:=conics[1];
  par:=Parametrization(con,P);
  q0,q1,q2:=Explode(DefiningEquations(par));
  R1<U,V>:=Parent(q1);
  R2<X,Y,Z>:=PolynomialRing(R1,3);
  map1:=hom<R3->R2|X,0,Y,Z>;
  map2:=hom<R2->R1|0,0,0>;
  mapcon:=map1(Evaluate(eqns[2],[d1,d2]));
  g:=Evaluate(mapcon,[q0,Y,q2]);
  cf:=MonomialCoefficient(g,Y^2);
  g1:=g*cf; Y1:=cf*Y;
  f:=map2(Y1^2-g1);

  return true,<d1d2,f>,[q0,q1,q2];
  end function; // end function check_conics

//////////////////////////////////////////////
function e123(E);
  e1,e2,e3:=Explode([p[1]: p in DivisionPoints(E!0,2)|p[3] ne 0]);
  F:=Factorization(Numerator((e1-e2)*(e2-e3)*(e1-e3)));
  return [f[1]: f in F]; end function;

// full 2 torsion case function

function full_2_tors(e1,e2,e3);

e1,e2,e3:=Explode([e1,e2,e3]); // coerces them all into the same ring
// if all are "constant" then coerce into K first.
K:=Parent(e1);
R:=Integers(K);
F:=BaseRing(K);
alpha:=PrimitiveElement(F);
assert not IsSquare(alpha);

e12:=R!(e1-e2);
e13:=R!(e1-e3);
e23:=R!(e2-e3);
if IsCoercible(F,e12) then e12:=1; end if;
if IsCoercible(F,e13) then e13:=1; end if;
if IsCoercible(F,e23) then e23:=1; end if;

P3<z1,z2,z3,z4>:=ProjectiveSpace(K,3);
sd1:=[alpha] cat [fcr[1]: fcr in Factorization(e12*e13)];
sd2:=[alpha] cat [fcr[1]: fcr in Factorization(e12*e23)];
nd1:=#sd1; nd2:=#sd2;
Gd1:=AbelianGroup([2: i in [1..nd1]]);
Gd2:=AbelianGroup([2: i in [1..nd2]]);
d1map:=map<Gd1->R|x:->PowerProduct(sd1,Eltseq(x))>;
d2map:=map<Gd2->R|x:->PowerProduct(sd2,Eltseq(x))>;
d1d2:=[<d1map(x),d2map(y)>: x in Gd1, y in Gd2];
if debug then print #d1d2, "(d1,d2) pairs to check"; end if;

R3:=CoordinateRing(P3);
RR3<d1,d2>:=PolynomialRing(R3,2);
eqA:=d1*z1^2-d2*z2^2+(e1-e2)*z4^2;
eqB:=d1*z1^2-d1*d2*z3^2+(e1-e3)*z4^2;
eqC:=d2*z2^2-d1*d2*z3^2+(e2-e3)*z4^2;
eqD:=(e2-e3)*d1*z1^2+(e3-e1)*d2*z2^2+(e1-e2)*d1*d2*z3^2;


list_d1d2:=[]; list_quartics:=[]; /* list_I:=[]; list_J:=[] */; maps:=[];
for d in d1d2 do
  if debug then print "calling function check_conics..."; end if;
  flag,f,par:=check_conics(d,[eqA,eqB,eqC,eqD]);
  if flag then
    list_d1d2:=list_d1d2 cat [d];
    q:=f[2];
    if #list_quartics gt 0 then q:=Parent(list_quartics[1])!q; end if;
    if debug then print "quartic is:",q,"list is:",list_quartics; end if; I,J:=Explode(quartic_IJ(q));
    list_quartics:=list_quartics cat [q];
    f:=map<ProjectiveSpace(K,2)->ProjectiveSpace(K,3)|
	p:->[Evaluate(par[1],[p[1],p[3]]),
	Evaluate(par[2],[p[1],p[3]]),
	Sqrt(Evaluate(q,[p[1],p[3]]))/(d[1]*d[2]),
	Evaluate(par[3],[p[1],p[3]])]>;
    maps cat:=[f];
    //list_I:=list_I cat [I];
    //list_J:=list_J cat [J];
    end if;
  end for;
return list_d1d2,list_quartics,[eqA,eqB],maps;
end function;

////////////////////////////////////////////////////////////////

function TD_full(EC,H:WS:=false,debug:=true);
debug_TD:=debug;

tests:=[]; // 1=found point, 2=undecided
if WS then if Characteristic(BaseRing(EC)) gt 4 then E,ece:=WeierstrassModel(EC); wm:=(ece)^-1; end if;
  else E:=EC; wm:=Isomorphism(E,E); end if;
	if debug_TD then print "Weierstrass Model is:",E; end if;
tors:=two_torsion(E);
d1d2,quartics,eqns:=full_2_tors(tors[1],tors[2],tors[3]);
	if debug_TD then print "after elimination via conic solving the following pairs remain:",d1d2; end if;
pairs:=[d1d2[i]: i in [1..#d1d2]|IsELS(quartics[i])];
	if debug_TD then print "after checking local-solvability the following pairs remain:",pairs; end if;
eqA,eqB:=Explode(eqns);
quadrics:=[[Evaluate(eqA,d),Evaluate(eqB,d)]: d in pairs];
	if debug_TD then print #quadrics, "quadric-intersections to analyze"; end if;
P3:=ProjectiveSpace(Parent(quadrics[1][1]));
QIs:=[Curve(P3,q): q in quadrics];
found_points:=[]; epts:=[];
for i in [1..#pairs] do
  C:=QIs[i];
	if debug_TD then print "checking quadric-intersection",Index(QIs,C),"of",#QIs,":",C; end if;
  pts:=PointsQI(C,H : OnlyOne); 
  if #pts eq 0 then found_points cat:=[[]]; tests cat:=[2];
    else found_points cat:=[Eltseq(pts[1])]; tests cat:=[1];
	if debug_TD then print "found a point:",pts[1]; end if;
    if pts[1][4] ne 0 then z1,z2,z3:=Explode(Eltseq(pts[1]));
      b1:=pairs[i][1]; b2:=pairs[i][2];
      e1:=tors[1];
      xy:=[b1*z1^2+e1,b1*b2*z1*z2*z3];
      isonE,pE:=IsCoercible(E,xy); if isonE then
	pEC:=wm(pE); if debug_TD then print "found a point on elliptic curve:",pEC; end if;
	epts cat:=[pEC]; end if;
      end if;
    end if;
  end for;
gens:=IndependentGenerators([ x: x in epts ]);
lb:=#[x: x in tests|x eq 1];
ub:=#tests;
flag1,elb:=IsPowerOf(lb,2);
if not flag1 then elb:=Ceiling(Log(2,lb)); end if;
flag2,eub:=IsPowerOf(ub,2); assert flag2;
elb:=Max({#gens+2,elb});
if elb eq eub then print "rank computed exactly =",eub-2;
  else print "rank bounds:",[elb-2,eub-2]; end if;
return gens,tests,[elb-2,eub-2]; end function;

function TD_full_via_quartics(E,H);
e1,e2,e3:=Explode(two_torsion(E));
ds,qs,eqns,maps:=full_2_tors(e1,e2,e3);
n:=#ds;
idx:=[i: i in [1..n]|IsELS(qs[i])];
ds:=[ds[i]: i in idx];
qs:=[qs[i]: i in idx];
maps:=[maps[i]: i in idx];
n:=#idx;

Epts:=[];
for i in [1..n] do
  qpts:=PointsOfDegreeH(qs[i],H);
  if #qpts gt 0 then
    m:=maps[i];
    QIpt:=m(Domain(m)!Eltseq(qpts[1]));
    b1:=ds[i][1];b2:=ds[i][2];
    z1,z2,z3:=Explode(Eltseq(QIpt));
    isonE,Ept:=IsCoercible(E,[b1*z1^2+e1,b1*b2*z1*z2*z3]);
    if isonE then Epts cat:=[Ept]; end if;
    end if;
  end for;
gens:=IndependentGenerators({@ x: x in Epts @});
return gens;
end function;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

// Descent via two isogeny

function TD_part(E:debug:=false);
K:=BaseRing(E); g:=xpoly(E);
alpha:=PrimitiveElement(BaseRing(K));

c:=Coefficient(g,2); d:=Coefficient(g,1);
fac_d:=Factorization(Numerator(d));
sd:=[fac[1]: fac in fac_d] cat [alpha];
nd:=#sd;
Gd:=AbelianGroup([2: i in [1..nd]]);
dmap:=map<Gd->K|x:->PowerProduct(sd,Eltseq(x))>;
D1:=[dmap(x): x in Gd];
if debug then print #D1,"d1 to check"; end if;

function make_quartic(d1);
  KUV<U,V>:=PolynomialRing(K,2);
  return d1*U^4+c*U^2*V^2+(d/d1)*V^4;
  end function;

list_d1:=[]; list_QI:=[];
for i in [1..#D1] do
  d1:=D1[i]; d2:=d/d1;
  if debug then print "checking d1",i,"of,",#D1,":",d1; end if;
  q:=make_quartic(d1);
  if IsELS(q) then if debug then print "quartic is ELS"; end if;
    list_d1 cat:=[d1];
    M1:=SymmetricMatrix(K,[1,0,0,0,0,0,0,0,-1/2,0]);
    M2:=SymmetricMatrix(K,[0,0,-1,0,0,d1,0,0,c/2,d2]);
    C:=QuadricIntersection([M1,M2]);
    list_QI cat:=[C];
    end if;
  end for;
n1:=#list_QI;
if debug then print "after checking local solvability",n1,"d1 remain:";
  print list_d1; end if;
return list_QI,list_d1,D1;
end function; // end function TD_part

function map_backQI(p,d1,E);//maps back from quadric-intersection to EC1
  x,y,z,w:=Explode(Eltseq(p));
  assert w ne 0;
  X:=x/w; Y:=y/w; Z:=z/w;
  assert Z-X^2 eq 0;
  p1:=[X,Y];
  return E![d1*X^2,d1*X*Y];
  end function;

///////////////////////////////////////////////////////////////////

function solve_conic(ABC);
// complete the square then solve and parametrize the diagonal conic
a,b,c:=Explode(ABC);
F:=FieldOfFractions(Parent(a));
C:=Conic([F|a,-1,c,0,0,b]);
if a eq 0 then return true,[1,0,0],Parametrization(C,C![1,0,0]); end if;
flag,p:=HasRationalPoint(C);
if flag then
  p1:=Eltseq(p); assert IsCoercible(C,p1);
  return true,p1,Parametrization(C,C!p1);
  end if;
return false,_,_;
end function;

///////////////////////////////////////////////////////////////////

function second_descent(S,H:debugSD:=false);
  if debugSD then print "in function second_descent..."; end if;
c,d,d1:=Explode(S);
K:=Parent(c);
flag,p,q123:=solve_conic([d1,c,d/d1]);
assert flag;
q1,q2,q3:=Explode(DefiningEquations(q123));
m:=hom<Parent(q1)->A|A.1,1> where A is PolynomialRing(K);
res:=Resultant(m(q1),m(q3));
sD3:=[f[1]: f in Factorization(Numerator(res))] cat [PrimitiveElement(BaseRing(K))];
nD3:=#sD3;
GD3:=AbelianGroup([2: i in [1..nD3]]);
D3map:=map<GD3->K|x:->PowerProduct(sD3,Eltseq(x))>;
D3:=[D3map(x): x in GD3];
if debug then print #D3,"d3 to check"; end if;

	function check_descendant(d3)
	if debugSD then print "checking descendant",Index(D3,d3),"of",#D3;
	  print "d3 =",d3; end if;
	cfs1:=[d3*MonomialCoefficient(q1,[2-i,i]): i in [0..2]];
	cfs3:=[d3*MonomialCoefficient(q3,[2-i,i]): i in [0..2]];
	flag1,_,param:=solve_conic(cfs1);
	if not flag1 then
	  if debugSD then print "conic not solvable"; end if;
	  return false,_; end if;
	flag3,_,_:=solve_conic(cfs3);
	if not flag3 then
	  if debugSD then print "conic not solvable"; end if;
	  return false,_; end if;
	P3<s,t,a,b>:=ProjectiveSpace(K,3);
	C:=Curve(P3,[-s^2+cfs1[1]*a^2+cfs1[2]*a*b+cfs1[3]*b^2,
		-t^2+cfs3[1]*a^2+cfs3[2]*a*b+cfs3[3]*b^2]);
	Q1,Q2,Q3:=Explode(DefiningEquations(param));
	quartic:=(cfs3[1]*Q1^2+cfs3[2]*Q1*Q3+cfs3[3]*Q3^2);
	flagELS,place:=IsELS(quartic);
	if not flagELS then
	  if debugSD then print "quartic not solvable at place",place; end if;
	  return false,_; end if;
	pt:=PointsQI(C,H : OnlyOne);
	if #pt eq 0 then return true,{@ @}; end if;
	if debugSD then print "point found on second descendant",pt[1]; end if;
	return true,pt; end function;

j:=0;
for d3 in D3 do
  flagd3,pt:=check_descendant(d3);
  if flagd3 then j+:=1; if #pt gt 0 then return true,pt,d3,[q1,q2,q3]; end if; end if;
  if (d3 eq D3[#D3]) and (j gt 0) then return true,{@ @},d3,[q1,q2,q3]; end if;
  end for;
return false,{@ @},_,[q1,q2,q3]; end function;

///////////////////////////////////////////////////////////////////

function TD_2iso(E,H:SD:=true,Debug:=false);

// first move the two-torsion point to (0,0):
a1,_,a3,_,_:=Explode(aInvariants(E)); if (a1 ne 0) or (a3 ne 0) then
  EWS,ws:=WeierstrassModel(E); flag_ws:=true;
  if Debug then print "Making a1 and a3 zero. New curve =",EWS; end if;
  else EWS:=E; flag_ws:=false; end if;
f:=xpoly(E); R:=Parent(f);
e1:=-Evaluate([f1[1]:f1 in Factorization(f)|Degree(f1[1]) eq 1][1],0);
g:=Evaluate(f,R.1+e1);
E1:=EWS; E2:=EllipticCurve(g);
map1:=map<E2->E1|p:->E1![p[1]+e1,p[2]]>;
EC1:=E2; if Debug then print "Set 2-torsion point to (0,0). New curve =",EC1; end if;
c:=Coefficient(g,2); d:=Coefficient(g,1);
h:=R!Polynomial([0,c^2-4*d,-2*c,1]);
EC2:=EllipticCurve(h);
phi12:=TwoIsogeny(EC1![0,0]);
phi21:=DualIsogeny(phi12);
assert EC2 eq Codomain(phi12);
e:=Coefficient(h,2); f:=Coefficient(h,1);
if Debug then print "2-isogenous curve =",EC2; end if;

// now call function TD_part for each of the isogenous curves EC1 and EC2
// Points on EC1 can be mapped back to the original curve (E) via "map1" and "ws"
curves1,D1,ND1:=TD_part(EC1:debug:=Debug);
curves2,D2,ND2:=TD_part(EC2:debug:=Debug);
found_points1:={@ EC1!0 @}; found_points2:={@ EC2!0 @};
tests1:=[]; tests2:=[];
n1:=#curves1; n2:=#curves2;

// the lists tests1 and tests2 indicate what happens to each "d1" that has
// passed through TD_part - that is has not been eliminated via conic solving
// or quartic local-solvability.
// 1 = a point found without second descent
// 2 = a point found only after second descent
// 3 = undecidable (the bad case)
// 4 = d1 eliminated after second descent

// first EC1...
for i in [1..n1] do
  if Debug then print "Analysing QIs for EC1: Checking curve",i,"of",n1; end if;
  C:=curves1[i]; d1:=D1[i];
  if Debug then print "d1 =",d1 /*,"C =",C */; end if;
  pts:=PointsQI(C,H : OnlyOne);
  if #pts gt 0 then pt:=pts[1]; tests1 cat:=[1];
    if Debug then print "found point on C!",pt; end if;
    if pt[4] eq 0 then continue; end if;
    Ept:=map_backQI(pt,d1,EC1);
    if Debug then print "point on EC1:",Ept; end if;
    found_points1 join:= {@ Ept @};
    else if SD then flag,pt,d3,q123:=second_descent([c,d,d1],H:debugSD:=Debug);
      if flag and #pt eq 0 then tests1 cat:=[3]; end if;
      if flag and #pt gt 0 then tests1 cat:=[2];
        s,t,a,b:=Explode(Eltseq(pt[1]));
	q1,q2,q3:=Explode(q123);
        X:=Evaluate(q1,[a,b]);
        Y:=Evaluate(q2,[a,b]);
        Z:=Evaluate(q3,[a,b]);
        v:=Y/Z;
        u:=s/t;
	Ept:=EC1![d1*u^2,d1*u*v];
        found_points1 join:= {@ Ept @};
        if Debug then print "point on EC1:",Ept; end if; end if; //flag
        if not flag then tests1 cat:=[4]; end if;
      end if; //SD
    end if; //#pts gt 0
  if not SD and #pts eq 0 then tests1 cat:=[3]; end if;
  end for;

// then EC2...
for i in [1..n2] do
  if Debug then print "Analysing QIs for EC2: Checking curve",i,"of",n2; end if;
  C:=curves2[i]; d1:=D2[i];
  if Debug then print "d1 =",d1 /*,"C =",C */; end if;
  pts:=PointsQI(C,H : OnlyOne);
  if #pts gt 0 then pt:=pts[1]; tests2 cat:=[1];
    if Debug then print "found point on C!",pt; end if;
    if pt[4] eq 0 then continue; end if;
    Ept:=map_backQI(pt,d1,EC2);
    if Debug then print "point on EC2:",Ept; end if;
    found_points2 join:= {@ Ept @};
    else if SD then flag,pt,d3,q123:=second_descent([e,f,d1],H:debugSD:=Debug);
      if flag and #pt eq 0 then tests2 cat:=[3]; end if;
      if flag and #pt gt 0 then tests2 cat:=[2];
	s,t,a,b:=Explode(Eltseq(pt[1]));
	q1,q2,q3:=Explode(q123);
        X:=Evaluate(q1,[a,b]);
        Y:=Evaluate(q2,[a,b]);
        Z:=Evaluate(q3,[a,b]);
        v:=Y/Z;
        u:=s/t;
	Ept:=EC2![d1*u^2,d1*u*v];
	found_points2 join:= {@ Ept @};
        if Debug then print "point on EC2:",Ept; end if; end if; //flag
        if not flag then tests2 cat:=[4]; end if;
      end if; //SD
    end if;
  if not SD and #pts eq 0 then tests2 cat:=[3]; end if;
  end for;

// gens1:=IndependentGenerators(found_points1);
// gens2:=IndependentGenerators(found_points2);

if Debug then
  print "________________________________________";
  print " ";
  print "****************************************";
  print "**  Summary of descent via 2-isogeny  **";
  print "****************************************";

  print "for EC1:";
  print n1, "quadric-intersections to check after local solvability test";
  print #found_points1,"points found";
  print "points on EC1:",found_points1;
  // print #gens1,"generators of EC1/phi(EC2) found:";
  // print gens1;
  print "***************************************************************";
  print "for EC2:";
  print n2, "quadric-intersections to check after local solvability test";
  print #found_points2,"points found";
  print "points on EC2:",found_points2;
  // print #gens2,"generators of EC2/phi'(EC1) found:";
  // print gens2;
  print "***************************************************************";
  end if;

EC1points:={@ EC1!phi21(p): p in found_points2 @} join found_points1;
gens:=IndependentGenerators([p:p in EC1points]);
gensEWS:=[map1(p): p in gens];
gensE:=gensEWS;
if flag_ws then
  gensE:=[E!ws(p): p in gensE];
  end if;
// print tests1,tests2;
lb1:=#[x: x in tests1|x in [1,2]];
lb2:=#[x: x in tests2|x in [1,2]];
ub1:=#[x: x in tests1|x ne 4];
ub2:=#[x: x in tests2|x ne 4];
j1,elb1:=IsPowerOf(lb1,2);
if not j1 then elb1:=Ceiling(Log(2,lb1)); end if;
j2,elb2:=IsPowerOf(lb2,2);
if not j2 then elb2:=Ceiling(Log(2,lb2)); end if;
i1,eub1:=IsPowerOf(ub1,2); //assert i1;
i2,eub2:=IsPowerOf(ub2,2); //assert i2;
rlb:=Max({#gensE,elb1+elb2-2}); rub:=eub1+eub2-2;

/* if rlb eq rub then print "rank computed exactly =",rlb;
assert rlb eq #gensE;
  else print "rank bounds:", [rlb,rub]; end if; */

return gensE,<tests1,tests2>,[rlb,rub]; end function; // end function TD_2iso


/////////////////////////////////////////////////////////////////////////////////////
/*
intrinsic RankBounds(E::CrvEll[FldFunRat]:Bound:=0) -> RngIntElt,RngIntElt
{The lower and upper bounds of the rank of the Mordell-Weil group of E.}

flag:=false;
if assigned E`descent_results then
  if Bound le E`descent_results[3] then flag:=true;
    end if;
  end if;
if flag then
  gens:=E`descent_results[1];
  bds:=E`descent_results[2];
  H:=Bound;
  if bds[1] eq bds[2] then H:=Infinity(); end if;
else

  require Bound ge 0: "Bound must be a non-negative integer";
  two_tors:=DivisionPoints(E!0,2);
  require #two_tors gt 1: "Currently only implemented for curves with 
                           at least one non-trivial two-torsion point";

  if #two_tors eq 4 then gens,_,bds:=TD_full(E,Bound);
    else gens,_,bds:=TD_2iso(E,Bound); end if;
  H:=Bound;
  if bds[1] eq bds[2] then H:=Infinity(); end if;
end if; // flag
 E`descent_results:=<gens,bds,H>;

return bds[1],bds[2];
end intrinsic;
*/
/////////////////////////////////////////////////////////////////////////////////////

function MordellWeilGroupByDescent(E : Bound:=0)
// E::CrvEll[FldFunRat] -> GrpAb,Map

flag:=false;
if assigned E`descent_results then
  if Bound le E`descent_results[3] then flag:=true;
    end if;
  end if;
if flag then gens:=E`descent_results[1];
  bds:=E`descent_results[2];
  else
  two_tors:=DivisionPoints(E!0,2);
  if #two_tors le 1 then G,m:=MordellWeilGroup(E);
    return G,m; end if;

  if #two_tors eq 4 then gens,_,bds:=TD_full(E,Bound);
    else gens,_,bds:=TD_2iso(E,Bound); end if;
  end if; // flag

H:=Bound;
if bds[1] ne bds[2] then
  print "*** WARNING: only computed a lower bound on the rank ***";
  H:=Infinity(); end if;
E`descent_results:=<gens,bds,H>;
G_tors,m_tors:=TorsionSubgroup(E);
i_tors:=Invariants(G_tors); t:=#i_tors;
tors:=[m_tors(G_tors.i):i in [1..t]];
r:=#gens;
G:=AbelianGroup(i_tors cat [0: i in [1..r]]);
m:=map<G->E|g:->&+[E|Eltseq(g)[i]*tors[i]: i in [1..t]]
	+ &+[E|Eltseq(g)[t+i]*gens[i]: i in [1..r]]>;

return G,m;
end function;


/////////////////////////////////////////////////////////////////////////////////////

function Roots(f) // RngMPolElt -> SeqEnum
//{Roots of the two-variable homogeneous polynomial f}

R:=Parent(f);
//require Rank(R) eq 2: "f must be homogeneous in 2 variables";
//require IsHomogeneous(f): "f is not homogeneous";

fac:=Factorization(f);
frts:=[x: x in fac|TotalDegree(x[1]) eq 1];
cfs:=[<[MonomialCoefficient(x[1],[1,0]),MonomialCoefficient(x[1],[0,1])],x[2]>: x in frts];
rts:=[<[-c[1][2],c[1][1]],c[2]>: c in cfs];
for i in [1..#rts] do
  a:=rts[i][1][2]; b:=rts[i][1][1]; c:=rts[i][2];
  if a ne 0 then rts[i]:=<[b/a,1],c>;
    else rts[i]:=<[1,0],c>;
    end if;
  end for;

return [r: r in rts];
end function;
