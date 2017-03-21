freeze;

/****************************************************************************
pointlift.m

November 2002, Nils Bruin,
last modified March 2010, Steve Donnelly

functions for multidimensional hensel lifting
******************************************************************************/

import "loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate, 
       CoefficientByExponentVector;

please_report := "A bug in Hensel has been detected!\n"*
                 "Please send this example to magma-bugs@maths.usyd.edu.au";

function Hensel(F,dim,P,tprc:rand:=false,Strict:=true)
  /*****
    Everything over a local ring of dimension R (unif pi)
    takes a list of multivariate polynomials F defining a variety of dimension
    dim locally at P and a point P that lies on F mod pi. P mod pi must be a
    non-singular point.
    
    This function uses quadratic lifting to lift P to a solution mod pi^tprec.
    (that is to say, the digits of the point P agree up to pi^tprec)
  *****/

  F:=[MyPrimitivePart(G):G in F];
  Rx:=Universe(F); 
  R:=BaseRing(Rx);
  pi:=UniformizingElement(R);
  if tprc lt 0 then
    return [O(pi^0):i in P];
  end if;    
  assert ISA(Type(R),RngPad);
  k,Rtok:=ResidueClassField(R);
  kx:=PolynomialRing(k,Rank(Universe(F)));
  Rxtokx:=hom<Rx->kx|Rtok*Bang(k,kx),[kx.i:i in [1..Rank(kx)]]>;

  // get rid of big O terms in coords of P (they play no role below, 
  // except if they are too low, the lifting loop will end too soon)
  dprc := Precision(R);
  if dprc eq Infinity() then
    dprc := R`DefaultPrecision;
  end if;
  dprc := Max(dprc, tprc);
  P := [Precision(x) gt dprc select x else ChangePrecision(x,dprc) : x in P];

  repeat
    B:=Matrix([[Rtok(CoefficientByExponentVector(f,
                  [j eq i select 1 else 0: j in [1..Rank(Rx)]] )):
                           i in [1..Rank(Rx)]]:f in F]);
    E,T:=EchelonForm(B);
    TT:=Matrix(Rx,Ncols(T),Nrows(T),[a@@Rtok:a in Eltseq(T)]);
    F:=Eltseq(Vector(F)*Transpose(TT));
    flag:=false;
    for i in [1..#F] do
      v:=MinValuation(F[i]);
      if v gt 0 then
        F[i]:=ShiftVal(F[i],-v);
        vprint LocSol,2:"Extra content",v,"removed from",i,"th polynomial";
        flag:=true;
      end if;
    end for;
  until not(flag); 

  f:=[Rxtokx(G):G in F];
  p:=[Rtok(c):c in P];
   
  assert forall{g:g in f| Evaluate(g,p) eq 0};

  // tJp:=Matrix([[Evaluate(Derivative(f[i],j),p):i in [1..#f]]:j in [1..#p]]);
  tJp:=Matrix(
    #P, #F, Evaluate([Derivative(f[i],j): i in [1..#f], j in [1..#p]], p)
  );
  E:=EchelonForm(tJp);
  C:=[Min(S): i in [1 .. Nrows(E)] | #S ne 0 where S := Support(E[i])];     
  error if #C ne #p - dim,
          "LiftPoint: point is singular on reduction, this is not handled";
  delete E;
  F:=[F[i]:i in C];

  PR := Universe(F);
  n := Rank(PR);
  SL := SLPolynomialRing(BaseRing(PR), n);

  if 0 eq 1 then
     SLG := [SL.i: i in [1 .. n]];
     // "conv to SL"; time
     F := [Evaluate(f, SLG): f in F];
  end if;

  jacmat := [Derivative(F[i],j): j in [1..#P], i in [1..#F]];

  // Add linear equations that cut out a 0-dimension subvariety (intersecting transversally).
  // We do this simply by appending some constant rows to jacmat (Steve, Nov 2007)
  tJP:=Matrix(#F, #P, Evaluate(jacmat, P));
  normalised_rows := [row*pi^-v where v is Min([Valuation(rr) : rr in Eltseq(row)]) where row is tJP[i] 
                      : i in [1..Nrows(tJP)] ];
  rows_modp := [[Rtok(rr) : rr in Eltseq(row)] : row in normalised_rows];
  Vp := VectorSpace(k,#P);
  rows_modp := sub<Vp|rows_modp>;
  extra_rows_modp := Basis(Complement(Vp, rows_modp));
  if rand then // randomize choice of complement mod p
    ChangeUniverse(~extra_rows_modp, Vp);
    r := Random([1..#extra_rows_modp]);
    extra_rows_modp[r] +:= Random(rows_modp); 
  end if;
  extra_rows := [[rr@@Rtok : rr in Eltseq(extra_rows_modp[i])] : i in [1..#extra_rows_modp]];
  if rand then // randomize lift of complement
    for r in [1..#extra_rows], i in [1..#P] do 
      extra_rows[r][i] +:= pi^Random([1..5]);
    end for;
  end if;
  // TO DO: should be more random? (here we modified the standard choice mildly)
  extra_lin_eqns := [&+[ row[i]*Rx.i : i in [1..#row]] : row in extra_rows];
  extra_lin_eqns := [eqn - Evaluate(eqn,P) : eqn in extra_lin_eqns]; 
  if rand then 
    for r in [1..#extra_lin_eqns] do
      extra_lin_eqns[r] +:= pi^Random([1..5]);
    end for;
  end if;
  F cat:= extra_lin_eqns;
  jacmat cat:= Flat(extra_rows);

  while true do
    //"eps eval", #F, #P; time
    eps:=Evaluate(F, P);
    //"tJP eval", #F, #P; time
    tJP:=Matrix(#F, #P, Evaluate(jacmat, P));

    error if Valuation(Determinant(tJP)) ne 0, please_report;

    Delta:=Eltseq(Solution(Transpose(tJP),-Vector(eps)));

    // Stop if point coords have stabilized modulo O(p^tprc)
    if MinValuation(Delta) ge tprc then
       return [c+O(pi^tprc): c in P];
    end if;

    if forall{c:c in eps| RelativePrecision(c) eq 0} then
      if Strict then
        error "Insufficient precision to lift point to desired level.";
      else
        return [c+O(pi^v): c in P] where v:=MinValuation(Delta);
      end if;
    end if;

    P:=[P[i]+Delta[i]:i in [1..#P]];
  end while;  

end function;

intrinsic LiftPoint(P::Pt,prc::RngIntElt:Random:=false,Strict:=true)->Pt
  {Lifts a point on a scheme to the given precision. Presently does so linearly
  and using solution enumeration over a finite field. Replace if someone does
  proper higher dimensional Hensel lifting.}

  Ppar:=Parent(P);
  X:=Scheme(Ppar);
  if IsProjective(X) then
    grd:=Gradings(X);
    require #grd eq 1:
      "Only projective spaces with a single grading are supported.";
    grd:=grd[1];
    r:=#grd;
    require grd[r] eq 1:
      "Only gradings with the last one 1 are supported.",
      "(fix this if you need it)";
    patch:=1;
    minval:=Infinity();
    for i in [1..r] do
      if grd[r+1-i] eq 1 and Valuation(P[r+1-i]) lt minval then
        minval:=Valuation(P[r+1-i]);
        patch:=i;
      end if;
    end for;
    Xa:=AffinePatch(X,patch);
    prA:=ProjectiveClosureMap(Ambient(Xa));
    Pa:=PointSet(Xa,RingMap(Ppar))!Inverse(prA)(P);
    Palift:=LiftPoint(Pa,prc+minval:Random:=Random,Strict:=Strict);
    return Ppar!prA(Palift);
  elif IsAffine(X) then
    X:=Scheme(Ppar);
    A:=Ambient(X);
    m:=RingMap(Ppar);
    K:=Codomain(m);
    R:=IntegerRing(K);

    // Choose working precision (TO DO: how much is really needed?)
    free := Precision(R) cmpeq Infinity();
    if free then
      prec0 := R`DefaultPrecision;
      R`DefaultPrecision := Max(prec0, prc+10);
    end if;

    pi:=UniformizingElement(K);
    AK:=PolynomialRing(K,Dimension(A));
    AR:=PolynomialRing(R,Dimension(A));
    AtoAK:=hom<CoordinateRing(A)->AK|m*Bang(K,AK),[AK.i:i in [1..Rank(AK)]]>;
    F:=[AtoAK(f):f in DefiningEquations(X)];

    minprec:=MinPrec(Eltseq(P));
    sbs:=[ChangePrecision(P[i],K`DefaultPrecision)+pi^(AbsolutePrecision(P[i])-1)*AK.i:i in [1..Dimension(A)]];
    Fsbs:=[Evaluate(f,sbs):f in F];
    Fsbs:=[AR!ShiftVal(f,-MinValuation(f)):f in Fsbs];
    
    Psbs:=Hensel(Fsbs,Dimension(X),[R!0:i in [1..Dimension(A)]],prc-minprec+1:rand:=Random,Strict:=Strict);

    if free then
      R`DefaultPrecision := prec0;
    end if;

    return Ppar![Evaluate(f,Psbs):f in sbs];
  else
    require false: "The scheme of P must either be affine or projective";
  end if;
end intrinsic;  

intrinsic LiftPoint(F::[RngMPolElt],d::RngIntElt,P::[FldPadElt],prc::RngIntElt
                   :Random:=false,Strict:=true)->SeqEnum
  {Lift a solution P (up to given precision) to a system of equations L,
  locally non-singular of dimension d around P, up to absolute precision prc}
  AK:=Universe(F);
  K:=BaseRing(AK);
  pi:=UniformizingElement(K);
  R:=IntegerRing(K);
  AR:=PolynomialRing(R,Rank(AK));
  
  minprec:=MinPrec(Eltseq(P));    
  sbs:=[ChangePrecision(P[i],K`DefaultPrecision)+pi^(AbsolutePrecision(P[i])-1)*AK.i:i in [1..Rank(AK)]];
  Fsbs:=[Evaluate(f,sbs):f in F];
  Fsbs:=[AR!ShiftVal(f,-MinValuation(f)):f in Fsbs];
  Psbs:=Hensel(Fsbs,d,[R!0:i in [1..Rank(AK)]],prc-minprec+1:rand:=Random,Strict:=Strict);
  return [Evaluate(f,Psbs):f in sbs];
end intrinsic;
