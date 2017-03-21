freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    CANONICAL LIFT TRACE ALGORITHMS                 //
//			     FOR GENERAL p			      //
//                             Mike Harrison                          //
//                   Adapted from some original code                  //
//                          by P. Gaudry                              //
//		      Uses classical modular polys.		      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

RECURSE_LIM := 100;

/* 
   Computes norm of a by splitting a as a0*a1 with a0 a 
   TeichMuller lift and a1 = 1 mod p. Norm(a1) computed as
   Exp(Trace(Log(a1))) and Norm(a0) by a residue class fld norm
   followed by Teichmueller lift at the bottom.
*/
function SatohNorm(a)
    R := Parent(a);
    _,red := ResidueClassField(R);
    a0 := red(a);
    a1 := a*TeichmuellerLift(1/a0,R);
    n1 := Exp(Trace(Log(a1)));
    n2 := TeichmuellerLift(Norm(a0),BaseRing(R));
    return n1*n2;
end function;

/* X and Y are input at a cetain precision (p_big, say)
   and R1 has precision  >= p_big-p_div.
   The function E3  computes each of
   R1!(E(X,Y)/p^p_div), Ex(R1!X,R1!Y), Ey(R1!X,R1!Y).
   Used by Lercier lift and Harley's recursive method. */

function E3(E,X,Y,R1,p_div)
    Eval := R1!ShiftValuation(Evaluate(E,[X,Y]),-p_div);
    X1 := R1!X; Y1 := R1!Y;
    Eder := Derivative(E,1);
    Ex := Evaluate(Eder,[X1,Y1]);
    Ey := Evaluate(Eder,[Y1,X1]);
    return Eval,Ex,Ey;
end function;

function NormParam(E,x,use_log)
    c := -Evaluate(DE,[y,x]) div ShiftValuation(Evaluate(DE,[x,y]),-1) 
		where y is GaloisImage(x,1)
		where DE is Derivative(E,1);
    c := ChangePrecision(R,Precision(R)-1)!c where R is Parent(c);
    return SquareRoot(Norm(c));
end function;

procedure doSign(~t,E)

    ord1 := #BaseRing(E)+1-t;
    ord2 := ord1+2*t;
    
    for i in [1..10] do
	pt := Random(E);
	pt1 := ord1*pt;
	pt2 := pt1+(2*t)*pt;
	boo1 := (pt1 eq E!0);
	boo2 := (pt2 eq E!0);
	assert (boo1 or boo2);
	if boo1 and (not boo2) then
	    return;
	elif boo2 and (not boo1) then
	    t := -t;
	    return;
	end if;
    end for;
    
    error "Failed to find sign of trace by random tests";
    
end procedure;


/*
    SST lifting suitable for use with Cyclotomic Unramified
    pAdic rings. The inverse Frobenius map is effected mod p
    in the finite field and lifted.
*/
function SSTLift(E, c, W, finalprec)

  K := Parent(c);
  p := Prime(K);
  n := Degree(K);
  
  R := ChangePrecision(K,W);
  _, red := ResidueClassField(R);
  x := R!c;

  vprintf SEA,4: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  Dyi := 1/(rx^(p^2)-rx) where rx is red(x);
  for i := 1 to W-1 do
    y := GaloisImage(x,1);
    x := y - Evaluate(E,[x, y])*(R!Dyi);
    Dyi := Dyi^p;
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;

  numloops := Ceiling(finalprec/W)-1;
  inner_lim := W;

  y := GaloisImage(x,1);
  Dx,Dy := Explode([Evaluate(DE,[x,y]),Evaluate(DE,[y,x])])
	where DE is Derivative(E,1);

  for m := 1 to numloops do
    if m eq numloops then
        inner_lim := finalprec-numloops*W;
    end if;
    vprintf SEA,4: "Increasing precision from %o to %o.. ",m*W,m*W+inner_lim;
    tyme := Cputime();
    x := ChangePrecision(K,m*W+inner_lim)!x;
    y := GaloisImage(x,1);
    V := Evaluate(E,[x, y]);
    v := R!ShiftValuation(V,-m*W);

    for i := 0 to inner_lim - 1 do
      dx := R!(Root(red(-v)*Dyi,p));
      dy := GaloisImage(dx,1);
      x +:= ShiftValuation(Parent(x)!dx,m*W+i);
      v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
    end for;
    vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
    
  end for;

  return x;

end function;

/*********** Harley's recursive version of SST ********************
* used instead of straight SST with cyclotomic bases for n large */

DIRECT_LIM := 7;

function recurseA(Eval,Dx,Dy)

  R := Parent(Eval);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    v := Eval;
    Dyi := 1/red(Dy);
    inc_x := R!0;
    for i := 0 to prec - 1 do
      dx := R!(Root(red(-v)*Dyi,p));
      dy := GaloisImage(dx,1);
      inc_x +:= ShiftValuation(dx,i);
      if i lt prec-1 then
          v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
      end if;
    end for;
    return inc_x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // firest recursion
    inc_x := R!recurseA(R1!Eval,R1!Dx,R1!Dy);
    inc_y := GaloisImage(inc_x,1);
    //update Eval
    tmp := ShiftValuation(Eval+Dx*inc_x+Dy*inc_y,-prec3);
    //second recursion
    ChangePrecision(~R1,prec2);
    inc_x1 := R!recurseA(R1!tmp,R1!Dx,R1!Dy);

    return inc_x+ShiftValuation(inc_x1,prec3);
  end if;

end function;

function recurse(E,a6l)

  R := Parent(a6l);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    x := a6l;
    Dyi := 1/(rx^(p^2)-rx) where rx is red(x);
    for i := 1 to prec - 1 do
      tmp := ShiftValuation(Evaluate(E,[x,GaloisImage(x,1)]),-i);
      dx := R!(Root(-red(tmp)*Dyi,p));
      x +:= ShiftValuation(dx,i);
    end for;
    return x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // firest recursion
    x := R!recurse(E,R1!a6l);
    y := GaloisImage(x,1);
    //compute E(x,y), Ex(x,y), Ey(x,y) to half precision
    ChangePrecision(~R1,prec2);
    Eval,Dx,Dy := E3(E,x,y,R1,prec3);
    //second recursion
    x1 := R!recurseA(Eval,Dx,Dy);
    return x+ShiftValuation(x1,prec3);
  end if;

end function;

/************* END OF RECURSIVE HARLEY FUNCTIONS *****************/

/*
   used to get to an initial small precision before the
   Lercier/Lubicz lift. Actually computes a lift of Frob^-1(c).
*/
function BasicGNBLift(E,c,W)
  K := Parent(c);
  p := Prime(K);
  n := Degree(K);

  R := ChangePrecision(K,W);
  y := R!c;
  _, red := ResidueClassField(R);

  if W eq 1 then return y; end if;
  vprintf SEA,3: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  _, red := ResidueClassField(R);
  Dyi := GaloisImage(R!(1/(ry^(p^2)-ry)), n-1) where ry is red(y);
  for i := 1 to W-1 do
    x := GaloisImage(y, n-1);
    y := y - (Evaluate(E,[x,y])*Dyi);
  end for;
  vprintf SEA,3 : "Time %o\n",Cputime()-tyme;

  return y;
end function;

/* 
   LERCIER/LUBITZ NEWTON LIFT METHOD. Used with GNB when
   high precision is required.
   prec0 is the precision that the input a6 is correct to.
   precAdjs is the boolean list of adjustments to get to
   the final precision exactly:
   ie if precAdjs = [boo1,boo2,...], the precision sequence
      is  prec1 := 2*prec0 - (1 if boo1 else 0)
          prec2 := 2*prec1 - (1 if boo2 else 0)  ....
*/
function LercierLift(E,a6,prec0,precAdjs)

  K := Parent(a6);
  p := Prime(K);
  n := Degree(K);

  prec := prec0;
  R := ChangePrecision(K,prec);
  x := R!a6;
  for boo in precAdjs do

    precinc := prec - (boo select 1 else 0);
    vprintf SEA,4: "Increasing precision from %o to %o.. ",prec,prec+precinc;
    tyme := Cputime();
    R := ChangePrecision(K,prec+precinc);
    x1 := R!x;
    y := GaloisImage(x1,1);
    Eval,Ex,Ey := E3(E,x1,y,Parent(x),prec);
    Dyinv := (-Ey)^-1;
    a1 := Ex * Dyinv;
    b1 := Eval * Dyinv;
    
    exp := 1;
    seq := Prune(Intseq(precinc,2));
    a := a1;
    b := b1;

    for i := #seq to 1 by -1 do
      tmp := GaloisImage(a,exp);
      b := GaloisImage(b,exp) + tmp*b;
      a *:= tmp;
      exp *:= 2;
      if seq[i] eq 1 then
        tmp := GaloisImage(a,1);
        b := GaloisImage(b,1) + tmp*b1;
        a := a1*tmp;
        exp +:= 1;
      end if;
    end for;
    
    x := x1 + ShiftValuation(R!GaloisImage(b,n-precinc),prec);
    prec +:= precinc;
    vprintf SEA,4 : "Time: %o\n",Cputime()-tyme;
    
  end for;

  return x;
  
end function;


function CanonicalLiftTraceMain(j)

  // j a non-supersingular jInv in GF(p^n), p odd. n>=3 is assumed!
  // The function returns +/- the trace of Frobenius on an ordinary
  // elliptic curve/GF(p^n) with that j invariant.

  vprint SEA, 1: "Computing trace via canonical lift.";
  tracetime := Cputime();
  n := Degree(Parent(j));
  p := Characteristic(Parent(j));
  a6 := j;
  precfin := Ceiling(n/2)+2;
  if IsOdd(n) and (p ge 17) then
    precfin -:= 1;
  end if;
  vprintf SEA, 2: "Getting Modular j Polynomial. Time: ";
  tyme := Cputime();
  E := ClassicalModularPolynomial(p);
  vprintf SEA, 2: "%o.\n",Cputime()-tyme;

  if n ge 3 then
    gnb_type := 1;
    R := pAdicQuotientRing(p,1);
    while gnb_type le 2 do //possible GNB types
     booGNB := HasGNB(R,n,gnb_type);
     if booGNB then break; end if;
     gnb_type +:= 1;
    end while;
  else
    booGNB := false;
  end if;
  if booGNB and (gnb_type eq 2) /*and (n le 50)*/ then
    booGNB := false;
  end if;
  // compute Norm(1+x) as exp(trace(log(1+x))) ?
  use_log := false; 


  if booGNB then  // will use GNB basis for local ring
    vprintf SEA, 1: "Working with Gaussian normal basis type %o\n",gnb_type;
    precmid := precfin;
    bAdjs := [Booleans()|];
    while precmid gt 3 do
      Append(~bAdjs,IsOdd(precmid));
      precmid := Ceiling(precmid/2);
    end while;
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    R := UnramifiedExtension(
	pAdicQuotientRing(p, precfin), n : GNBType := gnb_type
    );
    Embed(Parent(a6),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;
    if GetVerbose("SEA") ge 3 then
      printf "\nPerforming basic GNB lift\n";
      if #bAdjs gt 0 then printf "to reach precision %o.\n",precmid; end if;
      tyme := Cputime();
    end if;
    c := BasicGNBLift(E,R!a6,precmid);
    if #bAdjs gt 0 then
      vprint SEA, 3: "Beginning full NewtonLift phase.\n";
      Reverse(~bAdjs);
      c := LercierLift(E,R!c,precmid,bAdjs);
    end if;
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
  else // will use Cyclotomic basis for local ring
    vprint SEA, 1: "Working with simple pAdic basis.";
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    R := UnramifiedExtension(
	pAdicQuotientRing(p, precfin), n : Cyclotomic := false
      );
    Embed(Parent(a6),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;

    if n lt RECURSE_LIM then //use straight MSST
       tyme := Cputime();
       W := Min(precfin,Floor(30*Log(2)/Log(p)));
       c := SSTLift(E,R!a6,W,precfin);
       vprintf SEA,3 : "Total lifting time: %o\n",Cputime()-tyme;
    else //use recursive Harley MSST
       vprintf SEA, 3: "Using Harley's recursive method.\n";
            //"Using MSST with precision increment of %o.\n",W;
       tyme := Cputime();
       c := recurse(E,R!a6);//MSSTLift(R!a6,W,precfin);
       vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
     end if;
  end if;

  c := ChangePrecision(R,precfin)!c;

  vprint SEA,3 : "Computing norm.. ";
  tyme := Cputime();
  c := NormParam(E,c,use_log); // precision reduced by 1 here!
  vprintf SEA, 3: "Time: %o.\n",Cputime()-tyme;
  c := Integers()!c;
  if c gt Isqrt(4*p^n) then
    c := c - p^(precfin-1);
  end if;

  vprintf SEA,1 : "Total trace time: %o\n",Cputime(tracetime);
  return c;
  
end function;

intrinsic ECCanonicalLiftTraceGen(E::CrvEll) -> RngIntElt
{}
    p := Characteristic(BaseRing(E));
    if (p lt 37) or (p in \[41,47,59,71]) then
	// Use faster Hyperelliptic Model code.
	t := ECCanonicalLiftTraceHyp(E);
    else
        t := CanonicalLiftTraceMain(jInvariant(E));
    end if;
    doSign(~t,E);
    return t;
end intrinsic;

