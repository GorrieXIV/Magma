freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   CANONICAL LIFT TRACE ALGORITHMS                  //
//                             Mike Harrison                          //
//                   Adapted from some original code                  //
//                          by P. Gaudry                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

LERCIER_LIM := 600;
RECURSE_LIM := 350;

function E(X,Y)
  return  Y - (X*(ShiftValuation(Y,2)+1))^2; //Y - (X*(4*Y+1))^2
end function;

function Ex(X,Y)
  return ShiftValuation(-X*(ShiftValuation(Y,2)+1)^2,1);//-2*X*(4*Y+1)^2;
end function;

function Ey(X,Y)
  return 1 - ShiftValuation((ShiftValuation(Y,2)+1)*X^2,3);//1-8*(4*Y+1)*X^2;
end function;

/* X and Y are input at a cetain precision (p_big, say)
   and R1 has precision  >= p_big-p_div.
   The function E3 efficiently computes each of
   R1!(E(X,Y)/2^p_div), Ex(R1!X,R1!Y), Ey(R1!X,R1!Y).
   Used by Lercier lift and Harley's recursive method. */
 
function E3(X,Y,R1,p_div)

  v := ShiftValuation(Y,2)+1; //4*Y+1
  w := X*v;
  Eval := R1!ShiftValuation(Y-w^2,-p_div);
  w := R1!w;
  Ex := ShiftValuation(-w*(R1!v),1); //-2*(w*(R1!v))
  Ey := R1!1 - ShiftValuation(w*(R1!X),3); //R1!1 - 8*(w*(R1!X))
  return Eval,Ex,Ey;

end function;


/*
    MSST lifting suitable for use with Cyclotomic Unramified
    pAdic rings. The inverse Frobenius map is effected mod p
    in the finite field and lifted.
*/
function MSSTLift(c, W, finalprec)

  K := Parent(c);
  p := Prime(K);
  n := Degree(K);
  
  R := ChangePrecision(K,W);
  _, red := ResidueClassField(R);
  x := R!c;

  vprintf SEA,4: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  for i := 1 to W-1 do
    y := GaloisImage(x,1);
    x := y - E(x, y);
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;

  numloops := Ceiling(finalprec/W)-1;
  inner_lim := W;

  y := GaloisImage(x,1);
  Dx := Ex(x, y);
  Dy := Ey(x, y);

  for m := 1 to numloops do
    if m eq numloops then
        inner_lim := finalprec-numloops*W;
    end if;
    vprintf SEA,4: "Increasing precision from %o to %o.. ",m*W,m*W+inner_lim;
    tyme := Cputime();
    x := ChangePrecision(K,(m+1)*W)!x;
    y := GaloisImage(x,1);
    V := E(x, y);
    v := R!ShiftValuation(V,-m*W);

    for i := 0 to inner_lim - 1 do
      dx := R!Root(red(-v),p);
      dy := GaloisImage(dx,1);
      x +:= ShiftValuation(Parent(x)!dx,m*W+i);
      v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
    end for;
    vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
    
  end for;

  return x;

end function;

/*********** Harley's recursive version of MSST ********************
* used instead of straight MSST with cyclotomic bases for n large */

DIRECT_LIM := 7;

function recurseA(Eval,Dx,Dy)

  R := Parent(Eval);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    _, red := ResidueClassField(R);
    v := Eval;
    inc_x := R!0;
    for i := 0 to prec - 1 do
      dx := R!SquareRoot(red(v));
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

function recurse(a6l)

  R := Parent(a6l);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    _, red := ResidueClassField(R);
    x := a6l;
    for i := 1 to prec - 1 do
      tmp := ShiftValuation(E(x,GaloisImage(x,1)),-i);
      dx := R!SquareRoot(red(tmp));
      x +:= ShiftValuation(dx,i);
    end for;
    return x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // firest recursion
    x := R!recurse(R1!a6l);
    y := GaloisImage(x,1);
    //compute E(x,y), Ex(x,y), Ey(x,y) to half precision
    ChangePrecision(~R1,prec2);
    Eval,Dx,Dy := E3(x,y,R1,prec3);
    //second recursion
    x1 := R!recurseA(Eval,Dx,Dy);
    return x+ShiftValuation(x1,prec3);
  end if;

end function;

/************* END OF RECURSIVE HARLEY FUNCTIONS *****************/


/* 
   ADAPTED VERSION OF LERCIER/LUBITZ USED TO GET TO MODERATE PRECISION
   WHEN USING GAUSSIAN NORMAL BASIS.
   The lift function takes a p-adic c [(c,p) = 1] and returns c1 where
      c1 = x mod p^((prec+1)*W),   x the root of
        E(x,GaloisImage(x,1)) = 0 with x=c mod p.
   Currently only used for p=2 (E(x,y) specific to p=2) and it is assumed
   that W <= 30 [currently: 24<=W<=30].
   
   The method used is Lercier's Newton lift method, adapted by me to
   increase precision by the fixed increment W as in MSST. This is
   faster than Lercier's direct method for precisions required in the
   usual cryptographic ranges (GF(p^n), 100<=n<=1000, say) but is worse
   asymptotically [O(n^(3+epsilon) as opposed to O(n^(2+epsilon)*logn)].
   
   Assume n>=W. The method rests on solving an equation of the form
       Fx = a1*x + b1 mod p^W where F is Frobenius and a1=0 mod p.
   Iterating gives (F^r)x = ar*x+br mod p^W with ar=0 mod p^r so
     x = (F^(n-W))bW mod p^W.
   The ar,br up to r=W are calculated following the binary expansion of W
   and the obvious relations between the as,bs for increasing s.
   For W fixed, the a1 mod p^W is independant of iterations, so all the
   ar needed to get from b1 to bW are precomputed at the beginning and
   reused.
   
   There are 2 fixed precision increment stages: the first to get to
   c1 mod p^W using (precisional) increments of 6, and the second
   with increments of W to get to c1.
   
   It is assumed that n>=6 and if n<W then prec <=0.
*/
function LercierSSTLift(c, W, prec)

  K := Parent(c);
  p := Prime(K);
  n := Degree(K);

  R := ChangePrecision(K,6*Ceiling(W/6));
  y := R!c;//ChangePrecision(c,W);

  // first get to precision 30ish using the general method but
  // with a fixed precision increase of 6.
  vprintf SEA,4: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  for i := 1 to 5 do
    x := GaloisImage(y, n-1);
    y := y - E(x, y);
  end for;
    // make precomputes
  x := GaloisImage(y, n-1);// x,y correct to prec 6.
  Dyinv := (-Ey(x, y))^-1;
  a1 := Ex(x,y) * Dyinv;
  precomps := [a,GaloisImage(a*a1,1)] where a is GaloisImage(a1,1);
  Append(~precomps,GaloisImage(precomps[2]*a1,3));
    // precision increment loop
  for m in [1..Ceiling(W/6)-1] do
    b1 := ShiftValuation(E(x, GaloisImage(x,1)),-6*m)*Dyinv;
    b := GaloisImage(b1,1) + precomps[1]*b1; //b=b2
    b := GaloisImage(b,1) + precomps[2]*b1;  //b=b3
    b := GaloisImage(b,3) + precomps[3]*b;   //b=b6
    x +:= ShiftValuation(GaloisImage(b,n-6),6*m);
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;

  R := ChangePrecision(K,W);
  x := R!x;

  if prec le 0 then return x; end if;

  //now use precisional increments of W
    // make precomputes
  vprint SEA,4: "Making precomputes.. ";
  tyme := Cputime();
  y := GaloisImage(x,1);
  Dyinv := (-Ey(x, y))^-1;
  a1 := Ex(x,y) * Dyinv;
  seq := Prune(Intseq(W,2)); // binary expansion of W
  precomps := [R|];
  exp := 1;
  a := a1;
  for i := #seq to 1 by -1 do
    tmp := GaloisImage(a,exp);
    Append(~precomps,tmp);
    a := a *tmp;
    exp *:= 2;
    if seq[i] eq 1 then
      tmp := GaloisImage(a,1);
      Append(~precomps,tmp);
      a := a1*tmp;
      exp +:= 1;
    end if;
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
    //precision incremental loop
  for m := 1 to prec do
    vprintf SEA,4: "Increasing precision from %o to %o.. ",m*W,(m+1)*W;
    tyme := Cputime();
    x := ChangePrecision(K,(m+1)*W)!x;
    b1 := (R!ShiftValuation(E(x, GaloisImage(x,1)),-m*W))*Dyinv;
    b := b1;
    exp := 1;
    ind := 1;

    for i := #seq to 1 by -1 do
      b := GaloisImage(b,exp) + precomps[ind]*b;
      exp *:= 2; ind +:= 1;
      if seq[i] eq 1 then
        b := GaloisImage(b,1) + precomps[ind]*b1;
        exp +:= 1; ind +:= 1;
      end if;
    end for;
    x +:= ShiftValuation(Parent(x)!GaloisImage(b,n-W),m*W);
    vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
  end for;

  return x;

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
function LercierLift(a6,prec0,precAdjs)

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
    Eval,Ex,Ey := E3(x1,y,Parent(x),prec);
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


function CanonicalLiftTraceChar2(a6)

  // a6 in GF(2^n), a6 != 0,  n>=6 is assumed!
  // The function returns the trace of Frobenius on the ordinary
  // elliptic curve: y^2 + x*y = x^3 + a6.

  vprint SEA, 1: "Computing trace via canonical lift.";
  tracetime := Cputime();
  n := Degree(Parent(a6));
  precfin := Ceiling(n/2);
  gnb_type := 1;
  R := pAdicQuotientRing(2,1);
  while gnb_type le 2 do //possible GNB types
     booGNB := HasGNB(R,n,gnb_type);
     if booGNB then break; end if;
     gnb_type +:= 1;
  end while;       

  if booGNB then  // will use GNB basis for local ring
    vprintf SEA, 1: "Working with Gaussian normal basis type %o\n",gnb_type;
    precmid := precfin;
    bAdjs := [Booleans()|];
    while precmid gt LERCIER_LIM do
      Append(~bAdjs,IsOdd(precmid));
      precmid := Ceiling(precmid/2);
    end while;
    // choose best precision increment W (24 <= W <= 30)
    // for the "adapted" Lercier stage.
    if precmid le 30 then
      W := precmid; n_its := 1;
    else
      valarr := [5,6,6,7,6,7,7];
      bestval := Infinity();
      for w in [24..30] do
        p0 := Ceiling((precmid)/w);
        val := 4*p0+valarr[w-23];
        if val lt bestval then
           bestval := val;
           W := w; n_its := p0;
        end if;
      end for;
    end if;
    Rprec := Max(W*n_its,precfin+2);
    R := UnramifiedExtension(
	pAdicQuotientRing(2, Rprec), n : GNBType := gnb_type
    );
    Embed(Parent(a6),ResidueClassField(R));
    if GetVerbose("SEA") ge 3 then
      printf "\nLifting by ArtinSchreier at fixed precision %o\n",W;
      if #bAdjs gt 0 then printf "to reach precision %o.\n",precmid; end if;
      tyme := Cputime();
    end if;
    a61 := LercierSSTLift(R!a6,W,n_its-1);
    if #bAdjs gt 0 then
      vprint SEA, 3: "Beginning full NewtonLift phase.\n";
      Reverse(~bAdjs);
      a61 := LercierLift(R!a61,precmid,bAdjs);
    end if;
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
  else // will use Cyclotomic basis for local ring
    vprint SEA, 1: "Working with Cyclotomic basis.";
   if n le RECURSE_LIM then //use straight MSST
       c := InternalMSST(a6);
       vprintf SEA,1 : "Total trace time: %o\n",Cputime(tracetime);
       return c;
   else //use recursive Harley MSST
    //W := 30;
    Rprec := precfin+2;//Max(W*Ceiling(precfin/W),precfin+2);

    // First, create R to precision log_prec -- this is the precision required
    // to compute the Log.  Doing this here saves creating the higher
    // precision in the Log() call.
    log_prec := Rprec + Isqrt(Rprec div 2);
    R := UnramifiedExtension(
	pAdicQuotientRing(2, log_prec), n : Cyclotomic := true
    );
    R := ChangePrecision(R, Rprec);

    Embed(Parent(a6),ResidueClassField(R));
    vprintf SEA, 3: "Using Harley's recursive method.\n";
            //"Using MSST with precision increment of %o.\n",W;
    tyme := Cputime();
    a61 := recurse(R!a6);//MSSTLift(R!a6,W,precfin);
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
   end if;
  end if;

  c := 1+4*ChangePrecision(R,precfin+2)!a61;
  vprint SEA,3 : "Computing norm.. ";
  tyme := Cputime();
  if booGNB then 
      c := Norm(c);
  else 
      c := Exp(Trace(Log(c)));
  end if;
  vprintf SEA, 3: "Time: %o.\n",Cputime()-tyme;
  c := Integers()!c;
  if c gt Isqrt(2^(n+2)) then
    c := c - 2^(precfin+2);
  end if;

  vprintf SEA,1 : "Total trace time: %o\n",Cputime(tracetime);
  return c;
  
end function;

