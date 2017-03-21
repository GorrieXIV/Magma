freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// Thank you!

////////////////////////////////////////////////////////////////////////
//                                                                    
//  Computations with the analytic jacobian of a hyperelliptic curve.
//  This file mainly computes the period matrix.
//  Adds the type AnHcJac
//
//  P. van Wamelen (started Nov 2002)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//    AnalyticJacobian,
//    Print,
//    HyperellipticPolynomial,
//    SmallPeriodMatrix,
//    BigPeriodMatrix,
//    HomologyBasis,
//    Dimension,
//    Genus,
//    CoefficientRing,
//    BaseField,
//    BaseRing
//     
//     
////////////////////////////////////////////////////////////////////////

forward PeriodMatrix, halfloops, hypint, newsites, tauFromPerM, hypintinf;

////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare attributes CrvHyp: AnalyticJacobian, AnalyticJacobians;

declare type AnHcJac;

// see below for a description of each...
declare attributes AnHcJac:
  Genus,
  SmallPeriodMatrix,
  BigPeriodMatrix,
  HyperellipticPolynomial,
  OddDegree,
  EvenLeadingCoefficient,
  OddLeadingCoefficient,
  InfiniteRoot,
  Roots,
  EndPoints,
  AHomologyBasis,
  TransformMatrix,
  BasePoint,
  DirectedEdges,
  PathIntegrals,
  PathSigns,
  PathGraph,
  InfiniteIntegrals,
  ThetaNullCharacteristics,
  ThetaNullValues,
  DifferentialChangeMatrix,
  B2Inverse;

function CompareRoots(x,y)
  if Im(x) eq Im(y) then
    return Sign(Re(x) - Re(y));
  else
    return Sign(Im(x) - Im(y));
  end if;
end function;

/*
This computes analytic data for computation with the jacobian of a
hyperelliptic curve defined over a subfield of the complex
numbers. In particular it computes the period matrix of the curve, but
also the integral to infinity from a certain base point. This makes
later computations faster.  

If the curve is given as a monic degree 2g+1 polynomial we compute the
period matrix with respect to the usual basis of differentials (x^i/y
dx, i in [0..g-1]) and a canonical choice for the homology basis as
described by Mumford in his Tata lectures on Theta. See Chapter IIIa
section 5, also Chapter II section 2. Note that this depends on a
choice of ordering of the roots. We order the roots using CompareRoots
above. If the curve is not given in this form we first transform it
into this form and then compute the period matrix as above.

The computed data/AnHcJac attributes are:
  Genus: Genus, g, of the curve for which this is the Jacobian.
  SmallPeriodMatrix: The gxg matrix in Siegel-upperhalf space
  BigPeriodMatrix: The gx2g period matrix
  HyperellipticPolynomial: Polynomial f such that y = f(x) defines the 
    hyperelliptic curve
  OddDegree: Boolean value. True if f has odd degree, false otherwise
  EvenLeadingCoefficient: If f was given with even degree, it's leading 
    coefficient. Otherwise undefined
  OddLeadingCoefficient: If f was given with odd degree, it's leading 
    coefficient. Otherwise the leading coefficient of the polynomial obtained 
    by sending InfiniteRoot to infinity.
  InfiniteRoot: If f had even degree, one of its roots. This root is sent to 
    infinity in order to get a odd degree model.
  Roots: Roots of the odd degree polynomial. Either the polynomial
    given or after it was put in odd degree form. The order of these roots
    are fixed (using CompareRoots).
  EndPoints: Points in the complex plane used as endpoints of straight line 
    segments used to build up a homology basis.
  AHomologyBasis: A list of 2g lists of indices into EndPoints giving closed
    loops on the Riemann surface forming a homology basis.
  TransformMatrix: The 2gx2g matrix with which AHomologyBasis must be 
    multiplied to form a symplectic homology basis (which has a nice 
    SmallPeriodMatrix).
  BasePoint: Base point for the paths. Also used as the base point from 
    which the integral to infinity is computed.
  DirectedEdges: A list of pairs of indices into EndPoints. Each pair [i,j] 
    represents the straight line from EndPoints[i] to EndPoints[j].
  PathIntegrals: For each entry in DirectedEdges this contains a corresponding
    entry giving the integral with respect to all g differentials along this 
    straight line.
  PathSigns: Whether analytic continuation of y along the path changes the 
    sign of (magma's value of) Sqrt[f(x)].
  PathGraph: The graph formed by the DirectedEdges.
  InfiniteIntegrals: The integrals with respect to the g differentials from 
    BasePoint to infinity.
  ThetaNullCharacteristics: List of theta characteristics at which the 
    thetanuls (at SmallPeriodMatrix) are known. Not computed here, but in 
    jacmaps.m
  ThetaNullValues: The thetanull values at these characteristics
  DifferentialChangeMatrix: Change of variable matrix for the difference in
    using x^i dx/y for the even and odd degree models.
*/


intrinsic AnalyticJacobian(C::CrvHyp : Precision:=0) -> AnHcJac
{This computes analytic data for computation with the jacobian of a
hyperelliptic curve defined over a subfield of the complex numbers. 
In particular it computes the period matrix of the curve, but also 
the integral to infinity from a certain base point. This makes
later computations faster}

  prec := Precision;
  _, Precision := IsIntrinsic("Precision");

  if assigned C`AnalyticJacobian then
    tup := C`AnalyticJacobian;
    if tup[1] eq prec or prec eq 0 then
      return tup[2];
    end if; 
  end if; 
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve must be in the form y^2 = f(x)";
  require Degree(f) ge 3: "The curve must have degree at least 3";

  R := BaseRing(C);
  if not ISA(Type(R), FldCom) then
    if prec gt 0 then
      require prec ge 20: "Precision must be at least 20";
      CC := ComplexField(prec);
    elif not IsExact(R) then
      require Precision(R) ge 20: "Precision of the base field must be at least 20";
      CC := ComplexField(Precision(R));
    else
      CC := ComplexField();
    end if;
    f := PolynomialRing(CC)!f; 
  end if;

  J := AnalyticJacobian(f);
  C`AnalyticJacobian := <Precision(BaseRing(f)), J>;
  return J;
end intrinsic;

intrinsic AnalyticJacobian(C::CrvHyp, sigma::PlcNumElt : Precision:=0) -> AnHcJac
{This computes analytic data for computation with the jacobian of a
hyperelliptic curve defined over a number field and embedded using sigma. 
In particular it computes the period matrix of the curve, but also 
the integral to infinity from a certain base point. This makes
later computations faster}

  R := BaseRing(C);
  require IsInfinite(sigma): "Argument 2 must be an archimedean place.";
  require R eq NumberField(sigma): "Argument 2 must be an archimedean place of
    the base ring of argument 1";

  prec := Precision;
  _, Precision := IsIntrinsic("Precision");

  if not assigned C`AnalyticJacobians then
    C`AnalyticJacobians := AssociativeArray();
  else
    bool, tup := IsDefined(C`AnalyticJacobians, sigma);
    if bool and (tup[1] eq prec or prec eq 0) then
      return tup[2];
    end if; 
  end if;
 
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve must be in the form y^2 = f(x)";
  require Degree(f) ge 3: "The curve must have degree at least 3";

  if prec gt 0 then
    require prec ge 20: "Precision must be at least 20";
    CC := ComplexField(prec);
  else
    CC := ComplexField();
  end if;

  // embed f using sigma
  f := Polynomial([CC!Evaluate(c, sigma): c in Coefficients(f)]);

  J := AnalyticJacobian(f);
  C`AnalyticJacobians[sigma] := <Precision(BaseRing(f)), J>;
  return J;
end intrinsic;




intrinsic AnalyticJacobian(f::RngUPolElt[FldCom]) -> AnHcJac
{"} // "
  C := BaseRing(f);
  require Precision(C) ge 20: "The curve must be defined over a fixed precision complex field of decimal precision at least 20";
  require Degree(f) ge 3: "The curve must have degree at least 3";
  Jac := New(AnHcJac);
  Jac`HyperellipticPolynomial := f;
  // put the curve in the form y^2 = f(x), with f(x) monic and of odd degree
  deg := Degree(f);
  if deg mod 2 eq 0 then
    Jac`OddDegree := false;
    Jac`EvenLeadingCoefficient := LeadingCoefficient(f);
    evenrts := Roots(f);
    evenrts := [rt[1] : rt in evenrts];
    require #evenrts eq Degree(f): "This curve appears to be singular";
    x := Parent(f).1;
    f := &*[(evenrts[deg] - rt)*x+1 : rt in Prune(evenrts)];
    b := LeadingCoefficient(f);
    Jac`OddLeadingCoefficient := b;
    f := f/b;
    Jac`InfiniteRoot := evenrts[deg];
  else
    Jac`OddDegree := true;
    b := LeadingCoefficient(f);
    Jac`OddLeadingCoefficient := b;
    f:= f/b;
  end if;
  rts := Roots(f);
  rts := [rt[1] : rt in rts];
  require #rts eq Degree(f): "This curve appears to be singular";
  Sort(~rts,CompareRoots);
  PM, rts, dum := PeriodMatrix(rts);
  // fix the BigPeriodMatrix so that it is with respect to x^idx/y on the
  // even degree model
  if Jac`OddDegree then
    b := 1/Sqrt(Jac`OddLeadingCoefficient);
         // This should be the correct sqrt, see jacmaps
    g := NumberOfRows(PM);
    M := ScalarMatrix(C,g,b);
    Jac`BigPeriodMatrix := M*PM;
    Jac`PathIntegrals := [M*d : d in dum[7]];
    Jac`PathSigns     := dum[8];
    Jac`InfiniteIntegrals := M*hypintinf(dum[1][dum[4]], rts);
    Jac`DifferentialChangeMatrix := M;
  else
    b := 1/(Sqrt(Jac`OddLeadingCoefficient)*Sqrt(Jac`EvenLeadingCoefficient));
         // This should be the correct sqrt, see jacmaps
    alpha := Jac`InfiniteRoot;
    g := NumberOfRows(PM);
    M := ScalarMatrix(C,g,0);
    for i in [0..g-1] do
      for k in [0..g-1] do
        M[i+1,k+1] := -b*Binomial(i,k+i-g+1)*alpha^(k+i-g+1);
        if k+i eq g-1 and alpha eq 0 then
          M[i+1,k+1] := -b;
        end if;
      end for;
    end for;
    Jac`BigPeriodMatrix := M*PM;
    Jac`PathIntegrals := [M*d : d in dum[7]];
    Jac`PathSigns     := dum[8];
    Jac`InfiniteIntegrals := M*hypintinf(dum[1][dum[4]], rts);
    Jac`DifferentialChangeMatrix := M;
  end if;
  Jac`Roots := rts;
  Jac`SmallPeriodMatrix := tauFromPerM(PM);
  Jac`Genus := NumberOfRows(PM);
  Jac`EndPoints := dum[1];
  Jac`AHomologyBasis := dum[2];
  Jac`TransformMatrix := dum[3];
  Jac`BasePoint := dum[4];
  Jac`PathGraph := dum[5];
  Jac`DirectedEdges := dum[6];
  Jac`ThetaNullCharacteristics := [];
  Jac`ThetaNullValues := [];
  return Jac;
end intrinsic;

/* The homology basis is computed as follows. We want the integrals to
be as cheap as possible. We use Gaussian Quadrature and its error
estimates. It turns out that the computation is cheaper the farther
you are from the roots of f(x). As we need to go between all roots
anyway we start by computing the Voronoi cells of the roots. The edges
of the Voronoi cells can then be strung together to make the homology
basis as follows. First we make "half loops" by going from the
basepoint to cell i, around it, and back to the basepoint. This is
only a half loop on the Riemann surface because we only go around one
root and therefore change sheets. Now we must figure out what linear
combination of half loops make Mumford's A and B loops. We do this by
computing the intersection numbers of the half loops with the
horizontal lines going to the left of each root. We know what these
should be for the A and B loops. A little linear algebra then give us
the correct linear combinations of the half loops.

To get the integrals along the A and B loops, we only need to compute
the integrals along all edges of the Voronoi cells. Adding these up in
the correct way give us the period matrix.
*/


/* This returns a matrix containing the intersection numbers we want */
function MakeABCuts(g);
  LoopList := [Matrix(IntegerRing(),1,2*g+1,[]) : i in [1..2*g]];
  for i in [1..g] do
    LoopList[g+i][1,2*i-1] :=  1;
    LoopList[g+i][1,2*i  ] := -1;
  end for;
  for i := 1 to g do
    for j := 2*i to 2*g+1 do
      LoopList[i][1,j] := (-1)^(j+1);
    end for;
  end for;
  return LoopList;
end function;

// returns 1 if the line from a to b intersects the horizontal line to the 
// left of c. 0 if it doesn't
function IntersectBranchCutQ(a,b,c)
  ia := Im(a);
  ib := Im(b);
  ic := Im(c);
  if ia eq ib then
    if ia eq ic then
      return 1;
    else
      return 0;
    end if;
  end if;
  t := (ic-ia)/(ib-ia);
  if t lt 0 or t gt 1 then
    return 0;
  else
    if Re(a) + t*(Re(b)-Re(a)) lt Re(c) then
      return 1;
    else
      return 0;
    end if;
  end if;
end function;

// For a line from a to b, starting on the "+" sheet, return a row vector of 
// length
// #rts where the i'th entry is 0,-1 or +1
// depending on what sheet you are on when you cross the branch cut
// horizontally to the left of rts[i]. If there are more than one cut at
// that height, consider the cuts starting further to the right to be
// higher (see CompareRoots). As a second return value give the sheet you end 
// up on at b. This asumes that the rts are ordered by CompareRoots above.
function CutIntersectionVector(a,b,rts)
  v := Matrix(1,#rts,[IntersectBranchCutQ(a,b,r) : r in rts]);
  if Im(a) lt Im(b) then
    bg := 1;
    ed := #rts;
    st := 1;
  else
    bg := #rts;
    ed := 1;
    st := -1;
  end if;
  sgn := 1;
  for i := bg to ed by st do
    if v[1,i] eq 1 then
      v[1,i] := sgn;
      sgn := -sgn;
    end if;
  end for;
  return v,sgn;
end function;

/* Returns the small period matrix given the big one */
function tauFromPerM(PerM);
  g := NumberOfRows(PerM);
  return Submatrix(PerM,1,g+1,g,g)^-1*Submatrix(PerM,1,1,g,g);
end function;

/* 
Determinant of the imaginary part of tau. This is a 
good measure of how long it will take to evaluate a theta function at tau.
*/
function tauqual(tau)
  g := NumberOfRows(tau);
  Itau := Matrix(g,g,[Im(t) : t in ElementToSequence(tau)]);
  return Determinant(Itau);
end function;

/* This swaps root 2*i and 2*i+1 */
function swapmatrix1(g,i)
  smat := ScalarMatrix(2*g,1);
  if i lt g then
    smat[i,g+i] := 1;
    smat[i+1,g+i] := -1;
    smat[i,g+i+1] := -1;
    smat[i+1,g+i+1] := 1;
  else
    smat[g,2*g] := 1;
  end if;
  return smat;
end function;

/* This swaps root 2*i-1 and 2*i */
function swapmatrix2(g,i)
  smat := ScalarMatrix(2*g,1);
  smat[g+i,i] := 1;
  return smat;
end function;

/* swap root i and i+1 */
function swapmatrix(g,i)
  if i mod 2 eq 0 then
    return swapmatrix1(g,i div 2);
  else
    return swapmatrix2(g,(i+1) div 2);
  end if;
end function;

/*
This tries to find a symplectic matrix (and the corresponding
permutation of the roots) such that the imaginary part of the small
period matrix has larger eigenvalues. This makes evaluation of theta
functions at such elements of Siegel upper-half space faster.
This is random but always uses the same seed.
*/
function maximizePeriodMatrix(Pmat,n)
  Clow := BaseRing(Pmat);
  g := NumberOfRows(Pmat);
  num := 5; // seems to work ok...
  dum  := tauqual(tauFromPerM(Pmat));
  maxlst := [dum : i in [1..num]];
  done := 1;
  Sm := Sym(2*g+1);
  Seeds, Seedc := GetSeed();
  SetSeed(1);
  dlst := [[* ScalarMatrix(2*g,1), Sm!1 *] : i in [1..num]];
  while done le num do
    for i in [1..n] do
      lst := [Random(1,2*g) : i in [1..4]];
      perm := &*Reverse([Sm!(i,i+1) : i in lst]);
      smat := &*[swapmatrix(g,i)^Random({-1,1}) : i in lst];
      dum  := tauqual(tauFromPerM(Pmat*Matrix(Clow,dlst[done][1]*smat)));
      if dum gt maxlst[num]+10^-5 then
        maxlst[num] := dum;
        dlst[num][1] := dlst[done][1]*smat;
        dlst[num][2] := perm*dlst[done][2];
        maxlst,prm := Sort(maxlst,func<x,y | y-x>);
        dlst := [dlst[p] : p in ElementToSequence(prm)];
        done := ElementToSequence(prm^-1)[num]-1;
        break;
      end if;
    end for;
    done +:= 1;
  end while;
  SetSeed(Seeds, Seedc);
  return dlst[1][1], dlst[1][2];
end function;

/* This computes the Period Matrix of an hyperelliptic curve y^2 = f(x) where
f(x) = prod_{r in rts}(x-r) and there are 2*g+1 roots. It is assumed that 
the roots are ordered by CompareRoots above */
function PeriodMatrix(rts)
  C := Universe(rts);
  I := Name(C,1);
  g := (#rts-1) div 2;
  coords, loops, edges, base, G := halfloops(rts);
  points := [C!(ds[1]+I*ds[2]) : ds in coords];
  directededges := [SetToSequence(e) : e in edges];
  integrals := [];
  lst := [[points[de[1]],points[de[2]]] : de in directededges];
  intlst, sgnlst := HyperellipticIntegral(lst,rts);
  integrals := [Matrix(C,g,1,intlst[i]) : i in [1..#intlst]];
  halfintegrals := [];
  for loop in loops do
    sgn := 1;
    int := Matrix(C,g,1,[]);
    for j in [1..#loop-1] do
      e := [loop[j],loop[j+1]];
      ind := Index(directededges,e);
      if ind gt 0 then
        int +:= sgn*integrals[ind];
        sgn *:= sgnlst[ind];
      else
        ind := Index(directededges,Reverse(e));
        sgn *:= sgnlst[ind];
        int +:= -sgn*integrals[ind];
      end if;
    end for;
    Append(~halfintegrals,int);
    error if sgn ne -1, "not a half loop!?",loop;
  end for;        
  fullloops := [Prune(loops[i]) cat loops[i+1] : i in [1..2*g]];
  PMatrix := Transpose(Matrix([ElementToSequence(halfintegrals[i] 
    - halfintegrals[i+1]) : i in [1..2*g]]));
  CutIntM := Matrix(IntegerRing(),#fullloops,#rts,[]);
  for i := 1 to #fullloops do
    fl := fullloops[i];
    sgn := 1;
    sum := Matrix(IntegerRing(),1,#rts,[]);
    for j := 1 to #fl-1 do
      s,sgn2 := CutIntersectionVector(points[fl[j]],points[fl[j+1]],rts);
      sum +:= sgn*s;
      sgn *:= sgn2;
    end for;
    InsertBlock(~CutIntM,sum,i,1);
  end for;
  ABCuts := MakeABCuts(g); // these are cut intersections we want
  transform := Transpose(Matrix([Solution(CutIntM,ABc) : ABc in ABCuts]));
  PMatrix := PMatrix*ChangeRing(transform,C);
  smat, perm := maximizePeriodMatrix(Matrix(ComplexField(20),PMatrix),50);
  PMatrix := PMatrix*ChangeRing(smat,C);
  rts := [rts[p] : p in ElementToSequence(perm)];
  return PMatrix, rts, [* points,fullloops,transform*smat,base,G,directededges,integrals,sgnlst *];
end function;

/* We don't want infinite Voronoi cells, so we add four points around
the outside of the Roots in such a way that the Voronoi cells for the
Roots are all finite. */
function newsites(sites)
  xs := [xy[1] : xy in sites];
  ys := [xy[2] : xy in sites];
  maxx := Maximum(xs);
  minx := Minimum(xs);
  maxy := Maximum(ys);
  miny := Minimum(ys);
  a := (maxx-minx)/2;
  b := (maxy-miny)/2;
  len := Maximum(a+b+Sqrt(2*a*b),Maximum(a,b)*(#sites+4)/#sites);
  //    len := Maximum(a,b)*(#sites+4)/#sites;
  cx := (maxx+minx)/2;
  cy := (maxy+miny)/2;
  Append(~sites,<cx+len,cy>);
  Append(~sites,<cx-len,cy>);
  Append(~sites,<cx,cy+len>);
  Append(~sites,<cx,cy-len>);
  return sites;
end function;

// This computes the one-half loops 
// We compute the Voronoi diagram to low precision (20 places?) and
// then raise the precision. We also move things up by a small
// amount. This is a poor attempt at making sure that no edge begins or
// ends on a branch cut...
function halfloops(rts);
  Rbig := Parent(Re(Name(Universe(rts),1)));
  R := RealField(20);
  sites := [<R!Re(x), R!Im(x)> : x in rts];
  sites := newsites(sites);
  delaunayedges, dualsites, cells := Voronoi(sites);
//  ShowVoronoi("tmp.ps", sites, delaunayedges, dualsites, cells, 1);
  del := 1;
  for i in [1..#rts] do
    for j in delaunayedges[i] do
      if j gt i then
        dum := Abs(sites[i][1]-sites[j][1])+Abs(sites[i][2]-sites[j][2]);
        if dum lt del then
          del := dum;
        end if;
      end if;
    end for;
  end for;
  del := del*Pi(Rbig)^-8;
  dualsites := [<Rbig!dualsite[1], (Rbig!dualsite[2])+del, dualsite[3]> : dualsite in dualsites];
  repeat
    done := true;
    edges := [];
    for i in [1..#rts] do
      for j in [1..#cells[i]-1] do
        Append(~edges,{cells[i][j],cells[i][j+1]});
      end for;
      Append(~edges,{cells[i][#cells[i]],cells[i][1]});
    end for;
    // check for edges of length zero. These will occur if 4 or more roots 
    // lie on the same circle (with no root in the interior)
    edges := SequenceToSet(edges);
    for edge in edges do
      dedge := SetToSequence(edge);
      if Abs(dualsites[dedge[1]][1] - dualsites[dedge[2]][1]) lt 10^-10 and
         Abs(dualsites[dedge[1]][2] - dualsites[dedge[2]][2]) lt 10^-10 then
        for i in [1..#rts] do
          for j in [1..#cells[i]] do
            if cells[i][j] eq dedge[2] then
              if cells[i][((j-2) mod #cells[i])+1] eq dedge[1] or
                 cells[i][(j mod #cells[i])+1] eq dedge[1] then
                Remove(~cells[i],j);
                break;
              else
                cells[i][j] := dedge[1];
              end if;
            end if;
          end for;
        end for;
        done := false;
      end if;
    end for;
  until done;
  // now throw away what we don't need and re-index
  inds := {};
  for e in edges do;
    inds := inds join e;
  end for;
  inds := SetToSequence(inds);
  dualsites := [dualsites[i] : i in inds];
  edges := {{Index(inds,e) : e in edge} : edge in edges};
  cells := [[Index(inds,c) : c in cell] : cell in cells];
  _, G := Graph<#dualsites | edges>;
  _,base := Maximum([ds[1] : ds in dualsites]);
  loops := [];
  tails := [];
  for i in [1..#rts] do
    tail0 := [Index(v) : v in Geodesic(G!base,G!cells[i][1])];
    tail := [];
    j := 0;
    repeat
      j +:= 1;
      Append(~tail,tail0[j]);
    until tail0[j] in cells[i];
    k := Index(cells[i],tail0[j]);
    Append(~loops,[cells[i][j] : j in [k..#cells[i]]] cat [cells[i][j] : j in [1..k]]);
    Append(~tails,tail);
  end for;
  loops := [tails[i] cat Remove(Prune(loops[i]),1) cat Reverse(tails[i]) : i in [1..#loops]];
  return dualsites,loops,edges, base, G;
end function;

/* This recursively subdivides the interval [a,b] until the integral
on [a,b] agrees with the sum of the integrals on [a,c] and [c,b].
These integrals are computed by first making the substitution x = (1/y
-1)^2+a0. This transforms the infinite integral into an integral on
the interval [0,1], without a pole at 0. This is integrated using
Gaussian Quadrature with 200 points, no error estimates */
function hypintinf0(lst,a,b,a0,rts)
  R := RealField(Universe(rts));
  pres := Precision(R);
  d := (b-a)/2;
  lst1, sgn1 := HyperellipticInfiniteIntegral0(a0,R!a,R!(a+d),rts);
  lst2, sgn2 := HyperellipticInfiniteIntegral0(a0,R!(a+d),R!b,rts);
  max := Max([Abs(lst[i]-lst1[i]-sgn1*lst2[i]) : i in [1..#lst]]);
  if max lt 10^-(pres-5) then
    return [lst1[i]+sgn1*lst2[i] : i in [1..#lst]], sgn1*sgn2;
  else
    lst1, sgn1 := hypintinf0(lst1,a,a+d,a0,rts);
    lst2, sgn2 := hypintinf0(lst2,a+d,b,a0,rts);
    return [lst1[i]+sgn1*lst2[i] : i in [1..#lst]], sgn1*sgn2;
  end if;
end function;

/* This computes the integrals with respect to the g differentails
from a0 to infinity. */
function hypintinf(a0,rts)
  R := Parent(Re(Name(Universe(rts),1)));
  lst, sgn := HyperellipticInfiniteIntegral0(a0,R!0,R!1,rts);
  lst, sgn :=  hypintinf0(lst,0,1,a0,rts);
  return Matrix(#lst,1,[sgn*ls : ls in lst]);
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                           Printing                             //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Print(A::AnHcJac, level::MonStgElt)
   {}
   printf "Analytic Jacobian of the hyperelliptic curve defined by y^2 = %o over %o", HyperellipticPolynomial(A), BaseRing(HyperellipticPolynomial(A));
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute Access Functions                  //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic HyperellipticPolynomial(A::AnHcJac) -> RngUPolElt
   {The polynomial defining the hyperelliptic curve whose Jacobian this is.}
   return A`HyperellipticPolynomial;
end intrinsic;

intrinsic SmallPeriodMatrix(A::AnHcJac) -> AlgMatElt
   {The small gxg period matrix of A.}
   return A`SmallPeriodMatrix;
end intrinsic;

intrinsic BigPeriodMatrix(A::AnHcJac) -> AlgMatElt
   {The big gx2g period matrix of A.}
   return A`BigPeriodMatrix;
end intrinsic;

intrinsic HomologyBasis(A::AnHcJac) -> SeqEnum, SeqEnum, Mtrx
  {Returns a description of the homology basis used for computing the period 
   matrix.}
  return A`EndPoints, A`AHomologyBasis, A`TransformMatrix;
end intrinsic;

intrinsic Dimension(A::AnHcJac) -> RngIntElt
   {The dimension of A as an complex abelian variety.}
   return A`Genus;
end intrinsic;

intrinsic Genus(A::AnHcJac) -> RngIntElt
   {The genus of the curve of which this is the Jacobian.}
   return A`Genus;
end intrinsic;

intrinsic BaseField(A::AnHcJac) -> Rng
{The base field of the Jacobian A. }
    return CoefficientRing(HyperellipticPolynomial(A));
end intrinsic;

intrinsic BaseRing(A::AnHcJac) -> Rng
{The base field of the Jacobian A. }
    return CoefficientRing(HyperellipticPolynomial(A));
end intrinsic;
