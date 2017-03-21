freeze;

/*************************************************************
 *                                                           *
 *  Some functions for elliptic curves over function fields  *
 *                                                           *
 *            By Jasper Scholten, Februari 2006              *
 *                                                           *
 *************************************************************


 ************
  CHANGE LOG:

              **** PLEASE RECORD ALL CHANGES HERE ****
                                       Thanks! 
                                     -- Steve
  Nov 2010, Steve:
      + Torsion bound was for the exponent, supposed to be for
        the order (so TorsionSubgroup was wrong all this time!)
  May 2006, Steve: 
      + Trivial change to the order of Generators(E)
      + Renamed FrobActionOnPoints as FrobeniusActionOnPoints, 
        made gram a vararg, and put it in the HB
  June 2006, Steve:
      + Bug fix in Frobenius: Eltseq of the zero polynomial is [],
        but [0] was desired.
      + Specify a universe for the sequence given by Generators(E)
      + Fixed an error in MordellWeilGroup, in the definition 
        of the map G -> E (for torsion points).
  Juli 2006, Jasper:
      + Excluded constant curves from GeometricMordellWeilLattice
  July 19, 2006, Steve:
      + GeometricTorsionBound: 
          Don't try to divide B by p^Infinity when B is 0. 

                                                    ************/


import "../../Algaem/newell.m": pPowerGenerators;

import "descent2isog.m": MordellWeilGroupByDescent;

declare attributes CrvEll:
   MordellWeilLattice,
   GeometricMordellWeilLattice;


intrinsic Frobenius(P::PtEll[FldFunRat],q::RngIntElt) -> PtEll
  { q-power Frobenius action on point }
  if IsZero(P) then 
    return P;
  end if;
  coor:=Eltseq(P);
  K:=Parent(P[1]);
  coorn:=[ c eq 0 select [0] else Eltseq(Numerator(c)) : c in coor];  
  coord:=[Eltseq(Denominator(c)) : c in coor]; 
  x:=(K!Polynomial([x^q : x in coorn[1]]))/
             (K!Polynomial([x^q : x in coord[1]]));
  y:=(K!Polynomial([x^q : x in coorn[2]]))/
             (K!Polynomial([x^q : x in coord[2]]));
  return Parent(P)![x,y];
end intrinsic;

// Fixed Nov 2011, SRD
intrinsic Frobenius(P::PtEll[FldFunRat]) -> PtEll
  { Frobenius action on point }
  q:=Characteristic(BaseRing(Ring(Parent(P))));
  require q ne 0 : "The base field should have positive characteristic";
  return Frobenius(P,q);
end intrinsic;


intrinsic FrobeniusActionOnPoints(s::SeqEnum[PtEll], q::RngIntElt : gram:=0) -> AlgMatElt
  { Assuming s is a basis of a subgroup of the geometric Mordell-Weil group 
    modulo torsion that is invariant under the q-power Frobenius map, and gram
    is the gram matrix with respect to the height pairing of the points in s,
    returns the action of this Frobenius on the subgroup, as a matrix.}

  if IsEmpty(s) then
    return Matrix(0,[Rationals()|]);
  end if;

  if gram cmpeq 0 then 
     M:=HeightPairingMatrix(s);
     n:=NumberOfRows(M);
     gram:=MatrixAlgebra(Rationals(),n)!M;
  end if;

  if Type(CoefficientRing(gram)) ne FldRat then
    gram:=ChangeRing(gram,Rationals());
  end if;
  n:=#s;
  graminv:=gram^-1;
  coef:=[];
  for P in s do
    Pf:=Frobenius(P,q);
    M1:=Matrix(1,n,[HeightPairing(b,Pf) : b in s]);
    coef cat:=Eltseq(M1*graminv);
/*
ChangeUniverse(~coef, Integers());
assert Pf eq &+ [coef[i]*s[i] : i in [1..#s]];
*/
  end for;
  M:=Matrix(n,n,coef);
  return M;
end intrinsic;


intrinsic Basis(s::SeqEnum[PtEll], r::RngIntElt, disc::RngIntElt) 
                                                   -> SeqEnum, ModMatFldElt
  {  Given a sequence of points on an elliptic curve defined over a 
     function field, this returns a sequence containing generators 
     for the free part of the subgroup generated by the given points, 
     unless this has rank greater than r.  In that case, the answer
     is returned as soon as the routine finds a subgroup of rank r for
     which the height pairing lattice has discriminant less than or equal to disc. }

  require ISA(Type(Ring(Universe(s))), FldFunG) : 
         "The given points should be on an elliptic curve defined over a function field";

  torsion:=[];

  // skip leading torsionpoints
  ii:=0;
  repeat
    if not IsZero(ii) then
      Append(~torsion,s[ii]);
    end if;
    if ii lt #s then
      ii+:=1;
      h:=Height(s[ii]);
    else
      return [Universe(s)|],IdentityMatrix(Rationals(),0);
    end if; 
  until not IsZero(h);
 
  basis:=[s[ii]];
  gram:=Matrix(1,[h]);
  graminv:=gram^(-1);
  
  
  rankcheck:=(#basis ge r);
  if rankcheck then disccheck:=(Determinant(gram) le disc);
  else disccheck:=false; end if;


  for k in [ii+1..#s] do
    n:=#basis;
    M1:=Matrix(1,n,[HeightPairing(b,s[k]) : b in basis]);
    coef:=Eltseq(M1*graminv);

    norm1:=&+[coef[i]*coef[j]*gram[i,j] : i,j in [1..n]];
    norm2:=Height(s[k]);
        // test if rank increases
    if norm1 eq norm2 then 
          // rank stays the same.                         
          // test if point is already in lattice mod torsion 
      if &and[Denominator(a) eq 1 : a in coef] then  
        P:=&+[Numerator(coef[i])*basis[i] : i in [1..n]];
            // test if point is already in lattice
        if P ne s[k] then Append(~torsion,P-s[k]); end if;
      else
            // Enlarge lattice by finite index
        singgram:=HorizontalJoin(VerticalJoin(gram,M1),Transpose(HorizontalJoin(M1,Matrix(1,[norm2]))));
        redgram,T:=LLLGram(singgram);
        newbasis:=[];
        Append(~basis,s[k]);
        for i in [1..n+1] do
          if IsZero(redgram[i,i]) then
            gram:=RemoveRowColumn(redgram,i,i);
          else
            Append(~newbasis,&+[T[i,j]*basis[j] : j in [1..n+1]]);          
          end if;
        end for;
        graminv:=gram^-1;
        basis:=newbasis;
        if rankcheck then disccheck:=(Determinant(gram) le disc); end if;
      end if;
    else
      // rank increases    
      Append(~basis, s[k]);
      gram:=HorizontalJoin(VerticalJoin(gram,M1),Transpose(HorizontalJoin(M1,Matrix(1,[norm2]))));
      graminv:=gram^-1;

      rankcheck:=(#basis ge r);
      if rankcheck then disccheck:=(Determinant(gram) le disc); end if;
    end if;

  // test if desired rank and discriminant has been reached

    if rankcheck and disccheck then 
      return basis,gram;
    end if;
    
  end for;

  return basis,gram;
end intrinsic;

// TO DO: make ReducedBasis call this?

intrinsic Basis(s::SeqEnum[PtEll]) -> SeqEnum, ModMatFldElt
  {  Given a sequence of points on an elliptic curve defined over a 
     function field, this returns a sequence containing generators 
     for the free part of the subgroup generated by the given points. }

  require ISA(Type(Ring(Universe(s))), FldFunG) : 
         "The given points should be on an elliptic curve defined over a function field";
  return Basis(s,#s,0);
end intrinsic;

function systemincoefs(E)
// Assuming the a_i are polynomials of degree le i, returns a system
// of equations of which the solutions correspond to (x,y) on E with
// x and y polynomials of degree 2 and 3. 

  K:=BaseRing(E);
  F:=CoefficientRing(K);

  if not Type(F) eq FldFin then 
    error "E is not defined over a function field over a finite field";
  end if;

// generic case:
  R<y3,x2,y2,x1,y1,y0,x0>:=PolynomialRing(F,7);
  RR := FunctionField(R); tt := RR.1;

  X:=x2*tt^2+x1*tt+x0;
  Y:=y3*tt^3+y2*tt^2+y1*tt+y0;
  a1,a2,a3,a4,a6:=Explode([Evaluate(ai,tt) : ai in aInvariants(E)]);

  rel1:=Y^2+a1*X*Y+a3*Y-(X^3+a2*X^2+a4*X+a6);
  rel2:=Eltseq(Numerator(rel1));
  return rel2,R;
end function;

MordellWeilFldFin:=function(E)
// returns a basis for the free part of the Mordell-Weil group of an
// elliptic curve over a function field over a finite field.

//  if assigened E`MordellWeilLattice then 
//    MWL:=E`MordellWeilLattice


  K:=BaseRing(E);
  F:=CoefficientRing(K);
  q:=#F;

  rel,R:=systemincoefs(E);
  zerodimscheme:=Cluster(Spec(R),rel);
  Allsol:=PointsOverSplittingField(zerodimscheme);
  geomscheme:=Universe(Allsol);
  F1:=Ring(geomscheme);
  galorbits:=[];
  for punt in Allsol do
    nextpoint:=Eltseq(punt);
    newpoint:=true;
    for g in galorbits do
      if nextpoint in g then
        newpoint:=false; 
        break; 
      end if;
    end for;
    if newpoint then
      gnew:=[];
      
      repeat
        Append(~gnew,nextpoint);
        nextpoint:=[x^q : x in nextpoint];
      until nextpoint eq gnew[1];  
      Append(~galorbits,gnew);  
    end if;
  end for;

  K1:=FunctionField(F1);
  R1<Y3,X2,Y2,X1,Y1,Y0,X0>:=PolynomialRing(K1,7);
  
  E1:=ChangeRing(E,K1);
  ratpoints:=[ E! &+[
    E1![Evaluate(X2*K1.1^2+X1*K1.1+X0,p),Evaluate(Y3*K1.1^3+Y2*K1.1^2+Y1*K1.1+Y0,p)]
    : p in orbit] : orbit in galorbits];

  basis:=Basis(ratpoints);
  return basis;
end function;


intrinsic MordellWeilLattice(E::CrvEll[FldFunRat]) -> Lat, Map
{The height pairing lattice of the free quotient of the Mordell-Weil
 group of E, together with a map to the elliptic curve.}
  
  if assigned E`MordellWeilLattice then
    MWL:=E`MordellWeilLattice;
    return MWL[1],MWL[2];
  end if;

  K:=BaseRing(E);
  F:=CoefficientRing(K);
  require Type(K) eq FldFunRat and IsFinite(F) : 
          "E must be defined over a rational function field over a finite field";
  q:=#F;
  Lgeom,f:=GeometricMordellWeilLattice(E);
  r:=Rank(Lgeom);
  geombasis:=[f(x) : x in Basis(Lgeom)];
    
  Frob:=ChangeRing(FrobeniusActionOnPoints(geombasis,q:gram:=GramMatrix(Lgeom)),Integers());
  inv:=Kernel(Frob-IdentityMatrix(Integers(),r));
  basinv:=Basis(inv);
  basis:=[E! &+[f(Lgeom.i*b[i]) : i in [1..r]] : b in basinv];
  basisL:=[&+[Lgeom.i*b[i] : i in [1..r]] : b in basinv];  
  MWLgram:=Matrix(#basinv,[Rationals()|(x,y) : x in basisL, y in basisL]); 
  MWL:=LatticeWithGram(MWLgram);
  MWLmap:=hom<MWL -> E | v :-> &+[E| (Integers()!v[i])*basis[i] : i in [1..#basinv] ] >;
  E`MordellWeilLattice:=<MWL,MWLmap>;
  return MWL,MWLmap;
end intrinsic;

intrinsic MordellWeilGroup(E::CrvEll[FldFunRat] : Al:="Geometric") -> GrpAb, Map
  {The Mordell-Weil group of an elliptic curve defined over a rational function field}

  if Al eq "Descent" then 
    return MordellWeilGroupByDescent(E); end if;
  require Al cmpeq "Geometric": 
    "The optional argument Al must be \"Geometric\" or \"Descent\""; 

  L,f:=MordellWeilLattice(E);
  basis:=[f(x) : x in Basis(L)];
  tor,tormap:=TorsionSubgroup(E);
  torinv:=Invariants(tor);
  t:=#torinv;
  inv:=torinv cat [0 : i in basis];
  G:=AbelianGroup(inv);
//  mp:=map<G->E | a:-> &+[E| tormap(tor.Eltseq(a)[i]): i in [1..t]] +  
//                      &+[E| Eltseq(a)[i+t]*basis[i]: i in [1 .. #basis]]>;
  mp:=map<G->E | a:-> &+[E| Eltseq(a)[i]*tormap(tor.i): i in [1..t]] + 
                      &+[E| Eltseq(a)[i+t]*basis[i]: i in [1 .. #basis]]>;

  return G,mp;
end intrinsic;

intrinsic GeometricMordellWeilLattice(E::CrvEll[FldFunG]) -> Lat, Map
{The height pairing lattice of the free quotient of the Mordell-Weil
 group of E, together with a map to the elliptic curve.}

  require not IsConstantCurve(E) :
    "Curve is a constant curve. This case is not yet implemented";

  if assigned E`GeometricMordellWeilLattice then
    GMWL:=E`GeometricMordellWeilLattice;
    return GMWL[1],GMWL[2];
  end if;

  K:=BaseRing(E);
  F:=CoefficientRing(K);

  ai:=aInvariants(E);
  require ([Denominator(a) : a in ai] eq [K| 1,1,1,1,1]) and
    (&and[Degree(Numerator(ai[i])) le [1,2,3,4,6][i] : i in [1..5]]) :
    "At the moment only the case that the a_i are polynomials of degree <= i is implemented";

  rel,R:=systemincoefs(E);
  if IsZero(Dimension(Scheme(Spec(R),rel))) then
    zerodimscheme:=Cluster(Spec(R),rel);
    Allsol:=PointsOverSplittingField(zerodimscheme);
    F1:=Ring(Universe(Allsol));

    K1:=FunctionField(F1);
    R1<Y3,X2,Y2,X1,Y1,Y0,X0>:=PolynomialRing(K1,7);
  
    E1:=ChangeRing(E,K1);
    points:=[E1![Evaluate(X2*K1.1^2+X1*K1.1+X0,Eltseq(p)),
                 Evaluate(Y3*K1.1^3+Y2*K1.1^2+Y1*K1.1+Y0,Eltseq(p))] : p in Allsol];

    basis,gram:=Basis(points,8,1);
    L:=LatticeWithGram(gram);
    r:=Rank(L);
    f := hom< L -> E1 | v :-> &+[ E1 | (Integers()!v[i])*basis[i] : i in [1..r] ] >;
  else
    L:=LatticeWithGram(Matrix(0,[Rationals()|]));
    f:= hom< L -> E | v :-> 0>;
  end if;
  GMWL:=<L,f>;
  E`GeometricMordellWeilLattice:=GMWL;
  return GMWL[1],GMWL[2];
end intrinsic;


intrinsic HeightPairingMatrix(S::SeqEnum[PtEll[FldFunG]] : Precision := 0) -> AlgMatElt
{Given a sequence of points P_i on an elliptic curve over a function field, 
this returns the matrix  (<P_i, P_j>), where < , > is the canonical height pairing}
  n := #S;
  if IsEmpty(S) then 
    return IdentityMatrix(Rationals(),0);
  else
    return Matrix(n, [HeightPairing(i,j) : i,j in S]);
  end if;
end intrinsic;


intrinsic HeightPairingLattice(S::[PtEll[FldFunG]] : Precision := 0) -> AlgMatElt, Map
   {The height pairing lattice of a sequence of independent points on
   an elliptic curve over a function field. The Precision parameter is
   ignored.}

   E := Curve(Universe(S));
//   require IsLinearlyIndependent(S) : "Argument is not linearly independent";

   L := LatticeWithGram(HeightPairingMatrix(S));
   f := hom< L -> E | v :-> &+[ E | (Integers()!v[i])*S[i] : i in [1..#S] ] >;
   return L, f;
end intrinsic;


intrinsic Generators(E::CrvEll[FldFunRat]) -> SeqEnum
  {  The generators of the abelian group isomorphic to E.}

  G, toE :=MordellWeilGroup(E);
  setofgens := Generators(G);
  // try and put them in a sensible order 
  // (this still does not necessarily match the print summands of G, though)
  torsgens := [ g : g in setofgens | Order(g) ne 0 ];
  Sort(~torsgens, func< g,h | Order(g)-Order(h) > );
  nontorsgens := [ g : g in setofgens | Order(g) eq 0 ];
  return [ E(BaseField(E)) | g @ toE : g in torsgens cat nontorsgens ];
end intrinsic;



intrinsic GeometricTorsionBound(E::CrvEll[FldFunG]) -> RngIntElt
  { Returns bound for torsion defined over function field with algebraically closed constant field. Returns zero if no bound was found.}

  locinfo:=LocalInformation(E);
  K:=BaseRing(E);
  p:=Characteristic(K);
  if IsZero(p) then p:=1; end if;

  h:=0;
  eulerchar:=0;
  B:=0;
  C:=0;
  for li in locinfo do
    d:=Degree(li[1]);
    eulerchar+:=d*li[2];
    KS:=li[5];
    case KS :
    when KodairaSymbol("In"):
      n:=NumberOfComponents(KS);
      h+:=d*Floor(n/2)*(n-Floor(n/2))/n;
      C:=GCD(C,n);
    when KodairaSymbol("II"):
      B:=GCD(B,p);
    when KodairaSymbol("III"):
      B:=GCD(B,2*p);
      h+:=d/2;
    when KodairaSymbol("IV"):
      B:=GCD(B,3*p);
      h+:=2*d/3;
    when KodairaSymbol("I0*"):
      B:=GCD(B,2*p);
      h+:=d;
    when KodairaSymbol("In*"):
      n:=NumberOfComponents(KS);
      if IsEven(n) then
        B:=GCD(B,4*p);
      else
        B:=GCD(B,2*p);
      end if;
      h+:=d*(1+(n-5)/4);
    when KodairaSymbol("IV*"):
      B:=GCD(B,3*p);
      h+:=d*4/3;
    when KodairaSymbol("III*"):
      B:=GCD(B,2*p);
      h+:=d*3/2;
    when KodairaSymbol("II*"):
      B:=GCD(B,p);
    end case;
  end for;

  if 6*h lt eulerchar then return 1;
  else 
    // if (p gt 1) and (C ne 0) then
    if (p gt 1) and (C ne 0) and (B ne 0) then
      vB:=Valuation(B,p);
      vC:=Valuation(C,p);
      B div:=p^Max(vB-vC,0);
    end if;
    return B;
  end if;

end intrinsic;


intrinsic TorsionBound(E::CrvEll[FldFunG],n::RngIntElt) -> RngIntElt
  {Returns a bound on the size of the torsion subgroup of E by looking at
   the torsion in n fibers.}
  return TorsionBound(E,n,0);
end intrinsic;


intrinsic TorsionBound(E::CrvEll[FldFunRat],n::RngIntElt,B::RngIntElt) 
                                                            -> RngIntElt
  {Returns a bound on the size of the subgroup of the torsion group of E 
   consisting of elements with order dividing B, by looking at the 
   torsion in n fibers.}

  tries:=0;
  if (tries ge n) or (B eq 1) then 
    return B; 
  end if;
  ainvs:=aInvariants(E);
  K:=BaseRing(E);
  F:=CoefficientRing(K);
  if Characteristic(F) eq 0 then
    Floop:=[1..2*n];
    ChangeUniverse(~Floop,F);
  elif Type(F) eq FldFin then 
    Floop:=F;
  else error "Unsupported base ring";
  end if;

  e:=1;
  badred:=LCM([Denominator(ai) : ai in ainvs] cat [Numerator(Discriminant(E))]);

  repeat
    for v in Floop do
      if not IsZero(Evaluate(badred,v)) then 
        tries+:=1;
        Ered:=EllipticCurve([Evaluate(ai,v) : ai in ainvs]);
        B:=GCD(B,#TorsionSubgroup(Ered));
      end if;
      if (tries ge n) or (B eq 1) then 
        return B; 
      end if;
    end for;
    e+:=1;
    if Type(F) eq FldFin then 
      Floop:=ext<F | e>;
    else
      Floop:=[F | e*n+1..(e+1)*n];
    end if;
  until false;  
end intrinsic;

intrinsic TorsionBound(E::CrvEll[FldFun],n::RngIntElt,B) -> RngIntElt
  {Returns a bound on the size of the subgroup of the torsion group of E 
   consisting of elements with order dividing B, by computing torsion 
   on the special fibres at n places of good reduction.}

  tries:=0;
  if (tries ge n) or (B eq 1) then 
    return B; 
  end if;

  K:=AbsoluteFunctionField(BaseRing(E));
  E:=ChangeRing(E,K);
  F:=CoefficientRing(K);


  ainvs:=aInvariants(E);

  if Characteristic(F) eq 0 then
    Floop:=[F | 1];
   elif Type(F) eq FldFin then 
    Floop:=F;
   else error "Unsupported base ring";
  end if;

  e:=1;
  K2:=K.2;

  factoren:=&join[SequenceToSet(Poles(a)): a in ainvs| not IsZero(a)];
  factoren join:=SequenceToSet(Zeroes(Discriminant(E)));

  repeat
    for ff in Floop do
      for v in Zeroes(K.1+K2+ff) do
        if not (v in factoren) then 
          tries+:=1;
          Ered:=EllipticCurve([Evaluate(ai,v) : ai in ainvs]);
          B:=GCD(B,#TorsionSubgroup(Ered));
          if (tries ge n) or (B eq 1) then 
            return B; 
          end if;
        end if;
      end for;
    end for;
    e+:=1;
    if Type(F) eq FldFin then 
      K2:=K.2^e+K.2;
    else
      Floop:=[F | e];
    end if;
  until false;  
end intrinsic;



// slight adjustment of TorsionSubgroup for number fields

intrinsic TorsionSubgroup(E::CrvEll[FldFunG])->GrpAb, Map
  {Computes the torsion subgroup of E over its base field}

  if assigned E`TorsionSubgroup then
     mp := E`TorsionSubgroup;
     return Domain(mp), mp;
  end if;

  T1:=E!0;ordT1:=1;
  T2:=E!0;ordT2:=1;
  B:=GeometricTorsionBound(E);
  B:=TorsionBound(E,7,B);
  // quick fix, there are instances where GeometricTorsionBound 
  // and TorsionBound are wrong when char = p = 2
  if Characteristic(BaseField(E)) eq 2 then B *:= 2; end if;
  for tup in Factorisation(B) do
    bound:=(tup[1] eq 2 and Characteristic(BaseField(E)) eq 2) 
            select -1  
             else  tup[1]^tup[2];
    tor:=pPowerGenerators(E,tup[1]:Bound:=bound);
    if #tor ge 1 then
      T1+:=tor[1][1];
      ordT1*:=tor[1][2];
    end if;
    if #tor eq 2 then
      T2+:=tor[2][1];
      ordT2*:=tor[2][2];
    end if;
  end for;
  if ordT1 eq 1 then
    grp:=AbelianGroup([]);
    mp:=map<grp->E|a:->E!0>;
  elif ordT2 eq 1 then
    grp:=AbelianGroup([ordT1]);
    mp:=map<grp->E|a:->Eltseq(a)[1]*T1>;
  else
    grp:=AbelianGroup([ordT2,ordT1]);
    mp:=map<grp->E|a:->Eltseq(a)[1]*T2+Eltseq(a)[2]*T1>;
  end if;

  E`TorsionSubgroup:=mp;
  return grp,mp;
end intrinsic;

