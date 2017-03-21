freeze;

/** 
     1) FUNCTIONS FOR GETTING THE MIN POLY OF THE TEICHMULLER LIFT
        OF A GENERATOR OF THE RES CLASS FLD OF AN UNRAM EXT OF Qp
**/

/*** slightly more efficient version for p = 3 ************/

function tmi3(Fs,V)

    R := BaseRing(Parent(V));
    prec := Precision(R);
    if prec eq 1 then return -V; end if;

    N := Ceiling(prec/2);
    PR1 := PolynomialRing(ChangePrecision(R,N));
    delta := tmi3(ChangeUniverse(Fs,PR1),PR1!V);

    P := Parent(V);
    delta := P![R| c : c in Coefficients(delta)];
    d := Degree(delta);
    d0,d1,d2 := Explode([P![c[i+3*r] : r in [0..Floor((d-i+1)/3)]] :
    		 i in [1..3]]) where c is Coefficients(delta);
    V := V+delta-3*((F0^2-P.1*F1*F2)*d0+P.1*((F1^2-F0*F2)*d1+
    	  (P.1*F2^2-F0*F1)*d2)) where F0,F1,F2 := Explode(Fs);

    if IsOdd(prec) then
      PR1 := PolynomialRing(ChangePrecision(R,prec-N));
    end if;
    V := PR1![ShiftValuation(c,-N) : c in Coefficients(V)];

    delta1 := tmi3(ChangeUniverse(Fs,PR1),V);
    return delta + P![ShiftValuation(R!c,N): c in Coefficients(delta1)];

end function;

function tm3(f,R)

    prec := Precision(R);
    if prec eq 1 then return f; end if;

    N := Ceiling(prec/2);
    F := tm3(f,ChangePrecision(R,N));

    P := PolynomialRing(R);
    F := P![R| c: c in Coefficients(F)];
    d := Degree(F);
    F0,F1,F2 := Explode([P![c[i+3*r] : r in [0..Floor((d-i+1)/3)]] :
    		 i in [1..3]]) where c is Coefficients(F);
    V := F-F0^3-P.1*F1*(F1^2-3*F0*F2)-P.1^2*F2^3;
    R1 := ChangePrecision(R,prec-N);
    PR1 := PolynomialRing(R1);
    V := PR1![ShiftValuation(c,-N) : c in Coefficients(V)];

    delta := tmi3([PR1|F0,F1,F2],V);
    return F + P![ShiftValuation(R!c,N): c in Coefficients(delta)];

end function;

/******* General version **************************************/

function hks(R)
    p := Rank(R);
    R1 := PolynomialRing(R);
    P := PolynomialRing(R1);
    F := &+[P|R.(i+1)*(R1.1*P.1)^i : i in [0..p-1]];
    G := P.1^p-1;
    res := Resultant(G,F);
    return [Coefficient(res,p*k): k in [0..p-1]];
end function;

function tmip(Fs,hs,V)

    R := BaseRing(Parent(V));
    prec := Precision(R);
    if prec eq 1 then return -V; end if;

    N := Ceiling(prec/2);
    PR1 := PolynomialRing(ChangePrecision(R,N));
    delta := tmip(ChangeUniverse(Fs,PR1),hs,PR1!V);

    P := Parent(V);
    delta := P![R| c : c in Coefficients(delta)];
    d := Degree(delta);
    ds := [P![c[i+(#hs)*r] : r in [0..Floor((d-i+1)/#hs)]] :
               i in [1..#hs]] where c is Coefficients(delta);
    V := V+delta-&+[&+[Evaluate(Derivative(hs[i],j),Fs)*P.1^(i-1):
    	i in [1..#hs]]*ds[j] : j in [1..#hs]];

    if IsOdd(prec) then
      PR1 := PolynomialRing(ChangePrecision(R,prec-N));
    end if;
    V := PR1![ShiftValuation(c,-N) : c in Coefficients(V)];

    delta1 := tmip(ChangeUniverse(Fs,PR1),hs,V);
    return delta + P![ShiftValuation(R!c,N): c in Coefficients(delta1)];

end function;

function tmp(f,hs,R)

    prec := Precision(R);
    if prec eq 1 then return f; end if;

    N := Ceiling(prec/2);
    F := tmp(f,hs,ChangePrecision(R,N));

    P := PolynomialRing(R);
    F := P![R| c: c in Coefficients(F)];
    d := Degree(F);
    p := #hs;
    Fs := [P![c[i+p*r] : r in [0..Floor((d-i+1)/p)]] :
    		 i in [1..p]] where c is Coefficients(F);
    V := F-&+[Evaluate(hs[i],Fs)*P.1^(i-1) : i in [1..p]];
    R1 := ChangePrecision(R,prec-N);
    PR1 := PolynomialRing(R1);
    V := PR1![ShiftValuation(c,-N) : c in Coefficients(V)];

    delta := tmip(ChangeUniverse(Fs,PR1),hs,V);
    return F + P![ShiftValuation(R!c,N): c in Coefficients(delta)];

end function;

/******************* intrinsics ***************************/

intrinsic TMPolyCharOddCheck(F::RngUPolElt) -> BoolElt
{}
    if not IsMonic(F) then return false; end if;
    P := Parent(F);
    R := BaseRing(P);
    k,rm := ResidueClassField(R);
    Pk := PolynomialRing(k);
    f := Pk![rm(c) : c in Coefficients(F)];
    if not IsIrreducible(f) then return false; end if;
    boo := IsDivisibleBy(Evaluate(F,P.1^Prime(R)),F);
    return boo;
end intrinsic;


// R1 is a  pAdic quotient ring with residue field k=GF(p) and x lies in Fq.
// The function computes the min poly over R1 of the Teichmuller lift of
// x in an unramified extension of R of R1.
intrinsic TMPolyCharOdd(R::RngPadResExt,x::FldFinElt) -> RngUPolElt
{}
    k,rm := ResidueClassField(R);
    require x in k: "Argument 2 must lie in the residue field of argument 1";
    mx := MinimalPolynomial(x);
    R1 := BaseRing(R);
    mx := PolynomialRing(ResidueClassField(R1))!mx;
    if Prime(R1) eq 3 then
	return tm3(mx,R1);
    else
	hs := hks(PolynomialRing(Integers(),Prime(R1)));
        return tmp(mx,hs,R1);
    end if;

end intrinsic;


// R1 is a  pAdic quotient ring with residue field k=GF(p).
// The function computes the min poly over R of the Teichmuller lift of
// a generator of the res class field of an unramified extension of R of R1.
intrinsic TMPolyCharOdd(R::RngPadResExt) -> RngUPolElt
{}
    R1 := BaseRing(R);
    k,rm := ResidueClassField(R);
    mx := PolynomialRing(k)![rm(c) : c in Coefficients(DefiningPolynomial(R))];
    if Prime(R1) eq 3 then
	return tm3(mx,R1);
    else
	hs := hks(PolynomialRing(Integers(),Prime(R1)));
        return tmp(mx,hs,R1);
    end if;

end intrinsic;

/** 
     2) FUNCTIONS FOR FINDING THE TEICHMULLER LIFT OF AN
         ELT IN THE RES CLASS FLD OF AN UNRAM EXT OF Qp
**/

/**** Harley's recursive lift functions to solve phi(x,Fx) = 0
                    with phi(x,y)=y-x^p                     ****/

DIRECT_LIM := 7;

function recurseA(Eval,Dx)

  R := Parent(Eval);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    v := Eval;

    x := R.1;
    xx := GaloisImage(x, 1);
    pp := p;
    while Valuation(xx-x^pp) eq 0 do
      pp*:= p;
    end while;

    inc_x := R!0;
    for i := 0 to prec - 1 do
      dx := R!(Root(red(-v),pp));
      dy := GaloisImage(dx,1);
      inc_x +:= ShiftValuation(dx,i);
      if i lt prec-1 then
          v := ShiftValuation(v+Dx*dx+dy,-1);
      end if;
    end for;
    return inc_x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // first recursion
    inc_x := R!recurseA(R1!Eval,R1!Dx);
    inc_y := GaloisImage(inc_x,1);
    //update Eval
    tmp := ShiftValuation(Eval+Dx*inc_x+inc_y,-prec3);
    //second recursion
    ChangePrecision(~R1,prec2);
    inc_x1 := R!recurseA(R1!tmp,R1!Dx);

    return inc_x+ShiftValuation(inc_x1,prec3);
  end if;

end function;

function recurse(a)

  R := Parent(a);
  p := Prime(R);
  prec := Precision(R);

  x := a;
  xx := GaloisImage(x, 1);
  pp := p;
  while Valuation(xx-x^pp) eq 0 do
    pp*:= p;
  end while;

  if prec le DIRECT_LIM then
    _, red := ResidueClassField(R);
    for i := 1 to prec - 1 do
      tmp := ShiftValuation(GaloisImage(x,1)-x^pp,-i);
      dx := R!(Root(-red(tmp),pp));
      x +:= ShiftValuation(dx,i);
    end for;
    return x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // first recursion
    x := R!recurse(R1!a);
    y := GaloisImage(x,1);
    E := -(x^(pp-1)); 
    ChangePrecision(~R1,prec2);
    //second recursion : with (y-x^p)/p^prec3 & -px^(p-1) prec prec2
    x1 := R!recurseA(R1!ShiftValuation(y+x*E,-prec3),ShiftValuation(R1!E,1));
    return x+ShiftValuation(x1,prec3);
  end if;

end function;

intrinsic TeichmuellerLift(a::FldFinElt,R::RngPadRes) -> RngElt
{Computes the Teichmueller lift of a in R.}
    boo,a1 := IsCoercible(R,a);
    require boo: 
	"First argument must lie in the residue class field of the second";
    return recurse(a1);
end intrinsic;

intrinsic TeichmuellerLift(a::FldFinElt,R::RngPadResExt) -> RngElt
{Computes the Teichmueller lift of a in R.}
    require RamificationIndex(R) eq 1:
	"Second argument must have ramification index 1";
    boo,a1 := IsCoercible(R,a);
    require boo: 
	"First argument must lie in the residue class field of the second";
    return recurse(a1);
end intrinsic;
