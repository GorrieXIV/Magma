freeze;
 
/* Stuff to get hints for 2-descent --- vis-a-vis Algaem */

function EC_RHS(E,x)
 return x^3+aInvariants(E)[2]*x^2+aInvariants(E)[4]*x+aInvariants(E)[5];
end function;

/* Kludge while Roots for a p-adic polynomial is broken */
// It seems to be working better now (at least in the GetHintsNils routine)  ---Steve
function LinearFactors(FAC)
 return [x[1] : x in FAC | Degree(x[1]) eq 1]; end function;
function ROOTS2(F) return [x[1] : x in Roots(F)];  end function;
function ROOTS(F)
 return [-Coefficient(f,0)/Coefficient(f,1) :
     f in LinearFactors(Factorization(F))]; end function;

////////////////////////////////////////////////////////////////

/***********   WARNING!! These functions assume a1 = a3 = 0   ************/

// Return all rational x-coords of 2-division points of P.
function div2_resultant_Nils(Ep,P)
 a1,a2,a3,a4,a6:=Explode(aInvariants(Ep));
 assert 2*Min(Valuation(a1),Valuation(a3)) ge AbsolutePrecision(BaseRing(Ep)!1);
 X := PolynomialRing(BaseRing(Ep)).1;
 rhs:=P^3+a2*P^2+a4*P+a6;
 if Valuation(rhs) ge Min(AbsolutePrecision(BaseRing(Ep)!1)/2, AbsolutePrecision(rhs)-5) then
   // Special case where P is in Ep[2] (the 2-division points of P come in opposite pairs)
   bool,rr := IsSquare(3*P^2+2*a2*P+a4);
   return bool select [P+rr,P-rr] else []; end if;
 f1:=((a2^2-3*a4)*X^2+X*(X^3+a2*X^2+a4*X+a6)
      +(a2*a4-9*a6)*X-a2*(X^3+a2*X^2+a4*X+a6)-3*a2*a6+a4^2);
 poly:=f1-4*(X^3+a2*X^2+a4*X+a6)*P; 
 // Switched back from ROOTS to ROOTS2 here.   --- Steve
 L:=ROOTS(poly); return L; end function;

function add_pts_Nils(Ep,P,Q) /* can do better when P is near Q */
 y:=EC_RHS(Ep,P); W:=AbsolutePrecision(BaseRing(Ep)!1);
 if 2*Valuation(y) gt W then y:=0; else y:=Sqrt(y); end if;
 z:=EC_RHS(Ep,Q); if 2*Valuation(z) gt W then z:=0; else z:=Sqrt(z); end if;
 m:=(y-z)/(P-Q); return -P-Q-aInvariants(Ep)[2]+m^2; end function;

function double_pt_Nils(Ep,P)
 a1,a2,a3,a4,a6:=Explode(aInvariants(Ep));
 x:=((a2^2-3*a4)*P^2+P*(P^3+a2*P^2+a4*P+a6)+
     (a2*a4-9*a6)*P-a2*(P^3+a2*P^2+a4*P+a6)-3*a2*a6+a4^2);
 return x/(4*(P^3+a2*P^2+a4*P+a6)); end function;

function half_pt_Nils(Ep,P)
 M:=[x : x in div2_resultant_Nils(Ep,P)]; W:=AbsolutePrecision(BaseRing(Ep)!1);
 for x in M do ys:=EC_RHS(Ep,x); b,y:=IsSquare(ys);
  if b and 2*Valuation(P-double_pt_Nils(Ep,x)) gt W then
   return true,x; end if; end for; /* valuation bound is a guess */
 return false,P; end function;

function GetHints2DescentNils(Ep)
// if Prime(BaseRing(Ep)) eq 2 then return []; end if;
 T:=ROOTS(DivisionPolynomial(Ep,2));
 if #T eq 0 then return [];
 elif #T eq 1 then b:=true; P:=T[1];
  while b do b,P:=half_pt_Nils(Ep,P); end while; return [P]; end if;
 x1:=T[1]; x2:=T[2]; b1:=true; b2:=true;
 while b2 do b2,x2:=half_pt_Nils(Ep,x2);
   if b1 then b1,x1:=half_pt_Nils(Ep,x1); end if;
   if not b2 then
    if not b1 then b2,x2:=half_pt_Nils(Ep,add_pts_Nils(Ep,x1,x2));
    else t:=b1; b1:=b2; b2:=t; t:=x1; x1:=x2; x2:=t; end if; end if;
 end while; return [x1,x2]; end function;

////////////////////////////////////////////////////////////////

/***********   WARNING!! These functions assume a1 = a3 = 0   ************/

// Return all rational x-coords of 2-division points of P.
function div2_resultant(E,P,p,W)
 a1,a2,a3,a4,a6:=Explode(aInvariants(E));
 assert a1 eq 0 and a3 eq 0;
 X := PolynomialRing(pAdicField(p,W)).1;
 if Valuation(P^3+a2*P^2+a4*P+a6) gt W div 2 then
   // Special case where P is in E[2] (the 2-division points of P come in opposite pairs)
   bool,rr := IsSquare(3*P^2+2*a2*P+a4);
   return bool select [P+rr,P-rr] else []; end if;
 f1:=((a2^2-3*a4)*X^2+X*(X^3+a2*X^2+a4*X+a6)
      +(a2*a4-9*a6)*X-a2*(X^3+a2*X^2+a4*X+a6)-3*a2*a6+a4^2);
 poly:=f1-4*(X^3+a2*X^2+a4*X+a6)*P; L:=ROOTS(poly); return L; end function;

function add_pts(E,P,Q,W) /* can do better when P is near Q */
 y:=EC_RHS(E,P); if 2*Valuation(y) gt W then y:=0; else y:=Sqrt(y); end if;
 z:=EC_RHS(E,Q); if 2*Valuation(z) gt W then z:=0; else z:=Sqrt(z); end if;
 m:=(y-z)/(P-Q); return -P-Q-aInvariants(E)[2]+m^2; end function;

function double_pt(E,P)
 a1,a2,a3,a4,a6:=Explode(aInvariants(E));
 x:=((a2^2-3*a4)*P^2+P*(P^3+a2*P^2+a4*P+a6)+
     (a2*a4-9*a6)*P-a2*(P^3+a2*P^2+a4*P+a6)-3*a2*a6+a4^2);
return x/(4*(P^3+a2*P^2+a4*P+a6)); end function;

function half_pt(E,P,p,W)
 M:=[x : x in div2_resultant(E,P,p,W)];
 for x in M do ys:=EC_RHS(E,x); b,y:=IsSquare(pAdicField(p,W)!ys);
  if b and 2*Valuation(P-double_pt(E,pAdicField(p,W)!x)) gt W then
   return true,x; end if; end for; /* valuation bound is a guess */
 return false,P; end function;

function GetHints2Descent(E,p,W)
 dp:=DivisionPolynomial(E,2); T:=ROOTS(PolynomialRing(pAdicField(p,W))!dp);
 if #T eq 0 then return [],0,0;
 elif #T eq 1 then b:=true; P:=T[1]; i:=0;
  while b do b,P:=half_pt(E,P,p,W); i:=i+1; end while; return [P],i,0; end if;
 x1:=T[1]; x2:=T[2]; b1:=true; b2:=true; i1:=0; i2:=0;
 while b2 do b2,x2:=half_pt(E,x2,p,W); i2:=i2+1;
  if b1 then b1,x1:=half_pt(E,x1,p,W); i1:=i1+1; end if;
  if not b2 then
   if not b1 then b2,x2:=half_pt(E,add_pts(E,x1,x2,W),p,W);
   else t:=b1; b1:=b2; b2:=t; t:=x1; x1:=x2; x2:=t; end if; end if;
 end while; return [x1,x2],i2,i1; end function;

/*
function GetHints4Descent(f,p,W) pAF:=pAdicField(p,W);
 x := PolynomialRing(Rationals()).1; h1:=0;
 while h1 eq 0 do b,r:=GetLocalQuarticSolution(f,p,W); assert b;
  y2:=Evaluate(f,r); h:=reverse_poly(Evaluate(f,x+r))/y2;
  f0,f1,f2,f3:=Explode(Coefficients(h)); h1:=-1/2*f3*f2+1/8*f3^3+f1; end while;
 g1:=1/2*f3; g0:=1/2*f2-1/8*f3^2; h0:=-1/4*f2^2+1/8*f2*f3^2-1/64*f3^4+f0;
 poly:=x^3-4*g0*x^2-4*h0*x+(g1*x+h1)^2;
 M,m:=IntegralModel(EllipticCurve(poly)); DE:=DefiningEquations(Inverse(m));
 H,o1,o2:=GetHints2Descent(M,p,3*Valuation(Discriminant(M),p)+50);
 H:=[Rationals()!Evaluate(DE[1],1,x) : x in H];
 xy:=[[x,Rationals()!Evaluate(poly,x)] : x in H];
 XY:=[[x[1],2*Valuation(x[2],p) lt W
                          select Rationals()!Sqrt(pAF!x[2]) else 0] : x in xy];
 z:=[(2*P[1])/(P[2]-g1*P[1]-h1)+r : P in XY | P[2]-g1*P[1]-h1 ne 0];
 for o in z do assert IsSquare(pAF!Evaluate(f,o)); end for;
 return [r] cat z,o1,o2; end function;

*/


/********* EVERYTHING ABOVE HERE SHOULD DISAPPEAR IN THE END ****************/

/***************** Hints from halving **************************************/

function HALVE_IT(P) D:=DivisionPoints(P,2);
 if #D eq 0 then return false,P; else return true,D[1]; end if; end function;

function iHintsEC(E,W) T:=DivisionPoints(E!0,2);
 if #T eq 1 then return [],0,0; // uses that first return value is point at oo
 elif #T eq 2 then b:=true; P:=T[2]; i:=0;
  while b do b,P:=HALVE_IT(P); i:=i+1; end while; return [P],i,0; end if;
 P1:=T[3]; P2:=T[4]; b1:=true; b2:=true; i1:=0; i2:=0;
 while b2 do b2,P2:=HALVE_IT(P2); i2:=i2+1;
  if b1 then b1,P1:=HALVE_IT(P1); i1:=i1+1; end if;
  if not b2 then
   if not b1 then b2,P2:=HALVE_IT(P1+P2);
   else t:=b1; b1:=b2; b2:=t; t:=P1; P1:=P2; P2:=t; end if; end if;
 if i1 gt W or i2 gt W then error "Precision error"; end if;
 end while; return [P1,P2],i2,i1; end function;

/******************** Code for 2-desc, uses number fields for Nils ******/

function GetHintsEC(E,P,W) b:=true; //version for Nils
 while b do Kp,toKp:=MyCompletion(P);
  Kp`DefaultPrecision:=W;
  Ep:=EllipticCurve([toKp(c) : c in aInvariants(E)]);
  try PTS,i1,i2:=iHintsEC(Ep,W); b:=false; catch ERROR vprint Selmer,2:
  "Increase precision"; W:=5+Ceiling(W*1.25); b:=true; end try; end while;
 return [Inverse(toKp)(p[1]) : p in PTS],i1,i2; end function;

/******************** Code to get local sol for 4-desc ***********************/

function reverse_poly(f) d:=Degree(f);
 return &+[Coefficient(f,i)*Parent(f).1^(d-i) : i in [0..d]]; end function;

function IsNonzeroSquare(x) return (x ne 0) and IsSquare(x); end function;

function good_maybe(f,p) G:=GF(p);
 f:=PolynomialRing(G)!PolynomialRing(Integers())!f;
 if p lt 15 then
  R:=[[x,Evaluate(f,x)] : x in G]; R:=[x : x in R | IsSquare(x[2])];
  M:=[x[1] : x in R | IsZero(x[2])]; Y:=[x[1] : x in R | not IsZero(x[2])];
  return ChangeUniverse(Y,Integers()),ChangeUniverse(M,Integers());
 else F:=Factorization(PolynomialRing(G)!f);
  if (not IsSquare(Coefficient(f,Degree(f))))
    and &and[x[2] mod 2 eq 0 : x in F] then
   return [Integers()|],ChangeUniverse
             ([-Coefficient(x[1],0) : x in F | Degree(x[1]) eq 1 ],Integers());
  else while true do x:=Random(G);
   if IsNonzeroSquare(Evaluate(f,x)) then return [Integers()!x],[Integers()|];
   end if; end while; end if; end if; end function;

function localsol(f,p) v:=Min([Valuation(x,p) : x in Coefficients(f)]);
 if v mod 2 eq 0 then f:=f/p^v; Y,M:=good_maybe(f,p);
  if #Y ne 0 then return true,Random(Y)+Random(p)*p; end if;
  if #M eq 0 then return false,_; end if;
  for u in M do g:=Evaluate(f,p*Parent(f).1+u); b,x:=localsol(g,p);
   if b then return b,p*x+u; end if; end for; return b,_; end if;
 f:=f/p^v; R:=Roots(PolynomialRing(GF(p))!PolynomialRing(Integers())!f);
 R:=ChangeUniverse([x[1]: x in R],Integers());
 for r in R do g:=Evaluate(f*p,p*Parent(f).1+r);
   b,x:=localsol(g,p); if b then return b,p*x+r; end if; end for;
 return false,_; end function;

function good_maybe2(f) Z:=Integers(); f:=PolynomialRing(Z)!f;
 R:=[[x,Evaluate(f,x)] : x in Integers(8)];
 M:=[x[1] : x in R | x[2] eq 4 or x[2] eq 0]; Y:=[x[1] : x in R | x[2] eq 1];
 return ChangeUniverse(Y,Z),ChangeUniverse(M,Z); end function;

function localsol2(f) f:=PolynomialRing(Rationals())!f;
 v:=Min([Valuation(x,2) : x in Coefficients(f)]);
 f:=f div 4^(v div 2); Y,M:=good_maybe2(f);
 if #Y ne 0 then return true,Random(Y)+8*Random(10); end if;
 if #M eq 0 then return false,_; end if;
 for u in M do g:=Evaluate(f,8*Parent(f).1+u); b,x:=localsol2(g);
  if b then return b,8*x+u; end if; end for; return b,_; end function;

function testit(f,p) if p eq 2 then return localsol2(f); end if;
 return localsol(f,p); end function;

function GetLocalQuarticSolution(f,p,W)
 b,x:=testit(PolynomialRing(Rationals())!f,p);
 if b then assert IsSquare(pAdicField(p,W)!Evaluate(f,x)); return b,x; end if;
 x:=0; while x eq 0 do
  b,x:=testit(PolynomialRing(Rationals())!reverse_poly(f),p); assert b;
  if x ne 0 then assert IsSquare(pAdicField(p,W)!Evaluate(f,1/x));
   return b,1/x; end if; end while; end function;

/******************** Code for 4-desc hints ********************************/

function HintsQI(f,p,W) x := PolynomialRing(Rationals()).1; h1:=0;
 while h1 eq 0 do b,r:=GetLocalQuarticSolution(f,p,W); assert b;
  y2:=Evaluate(f,r); h:=reverse_poly(Evaluate(f,x+r))/y2;
  f0,f1,f2,f3:=Explode(Coefficients(h)); h1:=-1/2*f3*f2+1/8*f3^3+f1; end while;
 H:=ChangeRing(HyperellipticCurve(f),pAdicField(p,W));
 r:=pAdicField(p,W)!r; P:=H![r,Sqrt(Evaluate(f,r))]; M,m:=EllipticCurve(H,P);
 PT,i1,i2:=iHintsEC(M,W);
 PT:=[Inverse(m)(p) : p in PT];
 if #{p[1] : p in PT} ne #[p[1] : p in PT] then return HintsQI(f,p,W); end if;
 if Rationals()!P[1] in [Rationals()!p[1] : p in PT] then
  return HintsQI(f,p,W); end if;
 return [P] cat PT,i1,i2; end function;

function GetHints4Descent(f,p,W) b:=true;
 while b do try PTS,i1,i2:=HintsQI(f,p,W); b:=false; catch ERROR
  vprint LocalQuartic,2: "Increasing prec"; W:=5+Ceiling(W*1.25); b:=true;
  end try; end while; return [Rationals()!p[1] : p in PTS],i1,i2; end function;
