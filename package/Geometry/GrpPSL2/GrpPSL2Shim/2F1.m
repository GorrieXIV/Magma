freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Fast numerical evaluation of hypergeometric series
// May 2006, June 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "triangle.m" : ReduceToFD;

//-------------
//
// Auxiliary functions.
//
//-------------

HyperRoot := function(z,q);
  CC := Parent(z);
  if z eq 0 then
    return CC ! 0;
  else
    m := Arg(z);
    return Abs(z)^q*(Cos(q*m) + CC.1*Sin(q*m));
  end if;
end function;

Hypergeometric2F1At1 := function(A,B,C,z);
  CC := Parent(z);
  if C eq A+B then // log-pole in this case
    return Gamma(CC ! (A+B))/Gamma(CC ! A)/Gamma(CC ! B);
  elif Re(C-A-B) lt 0 then // these are wrong, has a pole: this is a limit
    return Gamma(CC ! C)*Gamma(CC! (A+B-C))/
           (Gamma(CC ! A)*Gamma(CC ! B));
  else
    return Gamma(CC ! C)*Gamma(CC ! (C-A-B))/
           (Gamma(CC ! (C-A))*Gamma(CC ! (C-B)));
  end if;
end function;

Hypergeometric2F1Atoo := function(A,B,C,z);
  CC := Parent(z);
  return Gamma(CC ! C)*Gamma(CC ! (A-B))/
         (Gamma(CC ! (A))*Gamma(CC ! (C-B)));
end function;

Hypergeometric2F1Kernel := function(A,B,C,zin);
  w := Parent(zin) ! 1;
  dwdz := Parent(zin) ! 0;
  lc := Parent(zin) ! 1;
  a := A;
  b := B;
  c := C;
  z := 1;
  n := 1;
  wOld := 0;

  while Abs(wOld-w) gt 10^(-Precision(Parent(zin))+2) do
    wOld := w;
    lc *:= (a*b)/c; // c must not be a negative integer
    dwdz +:= lc*z;
    lc /:= n;
    z *:= zin;
    w +:= lc*z;
    a +:= 1;
    b +:= 1;
    c +:= 1;
    n +:= 1;
  end while;

  return w,dwdz;
end function;

Hypergeometric2F1Series := function(A,B,C,z,tau,Ftauin,dFdztauin : ReturnSeries := 0);
  CC := Parent(z);

  Ftau := Ftauin;
  dFdztau := dFdztauin;
  zmtau := z-tau;
  zmtaupow := zmtau;
  w := Ftau + dFdztau*zmtau;
  dwdz := dFdztau;
  i := 0;
  lc := CC ! 1;
  wOld := 0;

  dFcoeff := (A+B+1)*tau-C;
  dFcoeffadd := 2*tau-1;
  Fcoeff := A*B;
  Fcoeffadd := A+B+1;
  den := tau*(1-tau);
  if ReturnSeries ne 0 then
    PowSrs := PowerSeriesRing(CC,ReturnSeries);
    w := Ftau + dFdztau*PowSrs.1;
    dwdz := dFdztau;
    zmtau := PowSrs.1;
    zmtaupow := zmtau;

    if tau eq 0 then
      w := PowSrs ! 1;
      dwdz := PowSrs ! 0;
      lc := PowSrs ! 1;
      a := CC ! A;
      b := CC ! B;
      c := CC ! C;
      for i := 0 to ReturnSeries-1 do
        lc *:= (a*b)/c;
        dwdz +:= lc*PowSrs.1^i;
        lc /:= (i+1);
        w +:= lc*PowSrs.1^(i+1);
        a +:= 1;
        b +:= 1;
        c +:= 1;
      end for;
    else
      for i := 0 to ReturnSeries-1 do
        dF2d2ztau := (dFcoeff*dFdztau + Fcoeff*Ftau)/den;
        dFcoeff +:= dFcoeffadd;
        Fcoeff +:= Fcoeffadd + 2*i;
        dwdz +:= dF2d2ztau/lc*zmtaupow;
        lc *:= i+2;
        zmtaupow *:= zmtau;
        w +:= dF2d2ztau/lc*zmtaupow;
        Ftau := dFdztau;
        dFdztau := dF2d2ztau;
      end for;
    end if;
  else
    while Abs(wOld-w) gt 10^(-Precision(Parent(z))+2) do
      wOld := w;

      dF2d2ztau := (dFcoeff*dFdztau + Fcoeff*Ftau)/den;
      dFcoeff +:= dFcoeffadd;
      Fcoeff +:= Fcoeffadd + 2*i;
      dwdz +:= dF2d2ztau/lc*zmtaupow;
      lc *:= i+2;
      zmtaupow *:= zmtau;
      w +:= dF2d2ztau/lc*zmtaupow;
      Ftau := dFdztau;
      dFdztau := dF2d2ztau;
      i +:= 1;
    end while;
  end if;
  return w,dwdz;
end function;

Hypergeometric2F1KernelRho := procedure(A,B,C,z,~knownValues,~w,~dwdz);
  nearOtherValue := false;
  CC := Parent(z);
  rho := 1/2*(1+CC.1);
  for val in knownValues do
    if [A,B,C] eq val[1] and Abs(z-rho) lt 1/100 then
      Frho := val[3];
      dFdzrho := val[4];
      nearOtherValue := true;
      break val;
    end if;
  end for;
  if not nearOtherValue then
    Frho,dFdzrho := Hypergeometric2F1Kernel(A,B,C,rho);  
    Append(~knownValues,<[A,B,C],rho,Frho,dFdzrho>);
  end if;

  w,dwdz := Hypergeometric2F1Series(A,B,C,z,rho,Frho,dFdzrho);
end procedure;

//-------------
//
// Function to call.
//
//-------------

function GammaQuotient(L1,L2,CF) assert #L1 eq 2 and #L2 eq 2;
 p1:=[Floor(l) : l in L1 | l le 0 and l eq Floor(l)];
 p2:=[Floor(l) : l in L2 | l le 0 and l eq Floor(l)];
 if #p2 gt #p1 then return CF!0; end if;
 if #p1 gt #p2 then error "Pole in GammaQuotient"; end if;
 if #p1 eq 1 then
  n:=[Gamma(CF!l) : l in L1 | not l in p1][1];
  d:=[Gamma(CF!l) : l in L2 | not l in p2][1];
  rn:=(-1)^p1[1]/Factorial(-p1[1]); rd:=(-1)^p2[1]/Factorial(-p2[1]);
  return n/d*rn/rd; end if;
 if #p1 eq 2 then
  rn1:=(-1)^p1[1]/Factorial(-p1[1]); rn2:=(-1)^p1[2]/Factorial(-p1[2]);
  rd1:=(-1)^p2[1]/Factorial(-p2[1]); rd2:=(-1)^p2[2]/Factorial(-p2[2]);
  return rn1*rn2/rd1/rd2; end if;
 res:=Gamma(CF!L1[1])*Gamma(CF!L1[2])/Gamma(CF!L2[1])/Gamma(CF!L2[2]);
 return res; end function;

Hypergeometric2F1 := procedure(A,B,C,z,~knownValues,~w,~dwdz);
  if Type(z) eq FldComElt then
    CC := Parent(z);
  else
    CC := ComplexField();
    z := CC!z;
  end if;
  rho := 1/2*(1+CC.1);

  if z eq 0 then
    w := 1;
    dwdz := A*B/C;
  elif z eq 1 then
    w := Hypergeometric2F1At1(A,B,C,z);
    dwdz := A*B/C*Hypergeometric2F1At1(A+1,B+1,C+1,z);
  elif Abs(z) lt 1/4 then
    w,dwdz := Hypergeometric2F1Kernel(A,B,C,z);
  else
    nearOtherValue := 0;
    minabs := 1/4;
    for i := 1 to #knownValues do
      if [A,B,C] eq knownValues[i][1] and Abs(z-knownValues[i][2]) lt minabs then
        nearOtherValue := i;
        minabs := Abs(z-knownValues[i][2]);
      end if;
    end for;

    if nearOtherValue ne 0 then
      val := knownValues[nearOtherValue];
      w,dwdz := Hypergeometric2F1Series(A,B,C,z,val[2],val[3],val[4]);
    else
      if Abs(z) lt 2/3 then
        w,dwdz := Hypergeometric2F1Kernel(A,B,C,z);
        Append(~knownValues,<[A,B,C],z,w,dwdz>);
      elif Abs(z-rho) lt 1/2 then
        Hypergeometric2F1KernelRho(A,B,C,z,~knownValues,~w,~dwdz);
      elif (Abs(1-z) lt 2/3 or Abs((1-z)-rho) lt 1/2) then
        w1 := CC ! 0; dw1dz := CC ! 0;
        w2 := CC ! 0; dw2dz := CC ! 0;
        ($$)(A,B,A+B-C+1,1-z,~knownValues,~w1,~dw1dz);
        ($$)(C-A,C-B,C-A-B+1,1-z,~knownValues,~w2,~dw2dz);

//        H11 := Hypergeometric2F1At1(A,B,C,z);
//        H12 := Hypergeometric2F1At1(C-A,C-B,C,z);
        H11:=GammaQuotient([C,C-A-B],[C-A,C-B],Parent(z)); // MW Sep 2014
        H12:=GammaQuotient([C,A+B-C],[A,B],Parent(z));

        zCAB := HyperRoot(1-z,C-A-B);
        w := H11*w1 + H12*zCAB*w2;
        dwdz := -H11*dw1dz + H12*( (A+B-C)*zCAB/(1-z)*w2 - zCAB*dw2dz );      
      elif Abs(1/z) lt 2/3 or Abs(1/z-rho) lt 1/2 then
        w1 := CC ! 0; dw1dz := CC ! 0;
        w2 := CC ! 0; dw2dz := CC ! 0;
        ($$)(A,A+1-C,A+1-B,1/z,~knownValues,~w1,~dw1dz);
        ($$)(A,A+1-C,A+1-B,1/z,~knownValues,~w2,~dw2dz);

        zA := HyperRoot(-z,-A);
        zB := HyperRoot(-z,-B);
//        Hoo1 := Hypergeometric2F1Atoo(B,A,C,z);
//        Hoo2 := Hypergeometric2F1Atoo(A,B,C,z);
        Hoo1:=GammaQuotient([C,B-A],[B,C-A],Parent(z));
        Hoo2:=GammaQuotient([C,A-B],[A,C-B],Parent(z));
        w := Hoo1*zA*w1 + Hoo2*zB*w2;
        dwdz := Hoo1*(zA*(-1/z^2)*dw1dz + A*HyperRoot(-z,-A-1)*w1) +
                Hoo2*(zB*(-1/z^2)*dw2dz + B*HyperRoot(-z,-B-1)*w2);
      else
        w1 := CC ! 0; dw1dz := CC ! 0;
        ($$)(A,C-B,C,z/(z-1),~knownValues,~w1,~dw1dz);
        zA := HyperRoot(1-z,-A);
        w := zA*w1;
        dwdz := A*HyperRoot(1-z,-A-1)*w1 - 1/(z-1)^2*zA*dw1dz;
      end if; 

      Append(~knownValues, <[A,B,C],z,w,dwdz>);
    end if;
  end if;
end procedure;

// Returns the reversion the hypergeometric series with parameters A,B,C
// corresponding to the group G evaluated at the points in zArray.
HypergeometricReversion := function(G, zArray);
  // Could be optional parameters, in case of heavy usage.
  knownIn := [];
  jEstimates := [];

  if not assigned G`TriangleABC then
    ignored := jParameter(G, UpperHalfPlane().1);
  end if;

  A,B,C := Explode(G`TriangleABC[1]);
  A2,B2,C2 := Explode(G`TriangleABC[2]);
  p,q,r := Explode(G`TriangleSig);

  if #zArray eq 0 then
    return [], [];
  end if;
  CC := Parent(ComplexValue(zArray[1]));
  prec := Precision(CC);
  erreps := 10^(-19/20*prec);

  rho := 1/2*(1+CC.1);
  // Frho,dFdzrho := Hypergeometric2F1Kernel(A,B,C,rho);  
  // knownValues := [<[A,B,C],rho,Frho,dFdzrho>];
  knownValues := [];

  zOutArray := [];
  zArray := [ComplexValue(z) : z in zArray];

  for i := 1 to #zArray do
    zin := zArray[i];

    foundConj := false;
    for j := 1 to #zOutArray do
      if Abs(zin-ComplexConjugate(-zArray[j])) lt 10^(-Precision(CC)+10) then
        zout := ComplexConjugate(zOutArray[j]);
        foundConj := true;
        break j;
      end if;
    end for;

    if not foundConj then
      if Re(zin) gt 0 then
        zin := -ComplexConjugate(zin);
        conjugatedFlag := true;
      else
        conjugatedFlag := false;
      end if;

      proot, qroot, rroot := Explode(G`TriangleHRoots);
      proot := ComplexValue(proot);
      qroot := ComplexValue(qroot);
      rroot := ComplexValue(rroot);

      D := Universe(G`ShimFDDisc);
      D`prec := Precision(zin);
      zin := ReduceToFD(G, D, zin);

      wp := (zin[1]-proot)/(zin[1]-ComplexConjugate(proot));
      wq := (zin[2]-qroot)/(zin[2]-ComplexConjugate(qroot));
      wr := (zin[3]-rroot)/(zin[3]-ComplexConjugate(rroot));

      valatp := G`Trianglephip0(zin[1]);
      valatq := G`Trianglephiq0(zin[2]);
      valatr := G`Trianglephir0(zin[3]);

      if Abs(valatp) lt Min([2,Abs(valatq),Abs(valatr)]) then
        As1 := A; Bs1 := B; Cs1 := C;
        As2 := A2; Bs2 := B2; Cs2 := C2;

        s := p;
        Fp1_1 := Hypergeometric2F1At1(A,B,C,wp);   // wp is just used for precision's sake
        Fp2_1 := Hypergeometric2F1At1(A2,B2,C2,wp);

        cp := (qroot-proot)/(qroot-ComplexConjugate(proot))*Fp2_1/Fp1_1;
        ws := wp/cp;
  
        if #jEstimates eq 0 then
          zout := CC ! valatp;
        else
          zout := CC ! jEstimates[i];
        end if;
      elif Abs(valatq) lt Min([1,Abs(valatr)]) then
        As1 := C-A; Bs1 := C-B; Cs1 := 1-A-B+C; 
        As2 := A; Bs2 := B; Cs2 := 1+A+B-C;

        s := q;
        Fq1_1 := Hypergeometric2F1At1(1-B,1-A,Cs1,wq);
        Fq2_1 := Hypergeometric2F1At1(1+B-C,1+A-C,Cs2,wq);

        cq := (proot-qroot)/(proot-ComplexConjugate(qroot))*Fq2_1/Fq1_1;
        ws := wq/cq;

        if #jEstimates eq 0 then
          zout := CC ! valatq;
        else
          zout := CC ! 1-jEstimates[i];
        end if;
      else
        As1 := B; Bs1 := B-C+1; Cs1 := B-A+1;
        As2 := A; Bs2 := A-C+1; Cs2 := A-B+1;

        s := r;
        Fr1_1 := Hypergeometric2F1At1(As1,Bs1,Cs1,wr);
        Fr2_1 := Hypergeometric2F1At1(As2,Bs2,Cs2,wr);

        cr := (qroot-rroot)/(qroot-ComplexConjugate(rroot))*Fr2_1/Fr1_1;
        ws := wr/cr;

        if #jEstimates eq 0 then
          zout := CC ! valatr;
        else
          zout := CC ! 1/jEstimates[i];
        end if;
      end if;

      u := HyperRoot(zout,1/s);
      umin := u;
      for zzeta in [Exp(2*Pi(CC)*CC.1*kk/s) : kk in [1..s]] do
        if Abs(zzeta*u-ws) lt Abs(umin-ws) then
          umin := zzeta*u;
        end if;
      end for;
      u := umin;

      F1 := CC ! 0; dF1du := CC ! 0;
      F2 := CC ! 0; dF2du := CC ! 0;

      uadd := 1/10;
      repeat
        uOld := u;
        uOldAdd := uadd;
        Hypergeometric2F1(As1,Bs1,Cs1,uOld^s,~knownValues,~F1,~dF1du);
        Hypergeometric2F1(As2,Bs2,Cs2,uOld^s,~knownValues,~F2,~dF2du);

        F1s,dF1sdu := Hypergeometric2F1Series(As1,Bs1,Cs1,u^s,uOld^s,
                                              F1,dF1du : ReturnSeries := 5);
        F2s,dF2sdu := Hypergeometric2F1Series(As2,Bs2,Cs2,u^s,uOld^s,
                                              F2,dF2du : ReturnSeries := 5);

        uu := u^s-uOld^s;
        if Abs(u*Evaluate(F1s,uu) - ws*Evaluate(F2s,uu)) gt erreps then
          u := umin;
          PCC := PolynomialRing(CC);
          fSolve := PCC.1*Evaluate(PCC ! Eltseq(F1s)[1..3],PCC.1^s-uOld^s) -
                    (CC!ws)*Evaluate(PCC ! Eltseq(F2s)[1..3],PCC.1^s-uOld^s);
          frts := RootsNonExact(fSolve);
          m,rtind := Min([Abs(frts[i]-umin): i in [1..#frts]]);
          if m gt 1/10 then
            u := umin;
          else
            u := frts[rtind];
          end if;
        end if; 
      until Abs(uOld-u) lt erreps;

      if s eq p then
        zout := u^p;
      elif s eq q then
        zout := 1-u^q;
      else 
        if u eq 0 then
          u := CC ! 10^(-Precision(CC));
        end if;
        zout := 1/u^r;
      end if;
       
      if conjugatedFlag then
        zout := ComplexConjugate(zout);
      end if;

    end if;

    Append(~zOutArray,zout);
  end for;

  // Could also return knownValues, if desired.
  return zOutArray;
end function;

intrinsic HypergeometricSeries2F1(A::RngElt, B::RngElt, C::RngElt, z::RngElt)
  -> FldComElt, FldComElt
  {Returns the value of the 2F1-hypergeometric function 
   with parameters (A, B; C) at the complex number z.}

// should check (A,B,C) to be reals/complexes
// and that C is not a nonpositive integer

  w := 0;
  dwdz := 0;
  knownValues := [];

  Hypergeometric2F1(A,B,C,z,~knownValues,~w,~dwdz);
  return w;
end intrinsic;

