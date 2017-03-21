freeze;
//////////////////////////////////////////////////////////////////////////////
///  Functions that parametrise rational plane curves with only           ////
///   ordinary singularities avoiding function field methods.              ///
///    [Often much quicker + can lead to nicer params]                     ///
///      mch with thanks to Frank-Olaf Schreyer - 2006                     ///
//////////////////////////////////////////////////////////////////////////////

function Annihilator(M)
 // M is an r*s matrix in R giving a map from R^s to R^r.
 //  Function returns the annihilator of the cokernel.
 
 R := BaseRing(M);
 r := Nrows(M);
 s := Ncols(M);
 
 // do special cases first
 if r eq 1 then
    return ideal<R|Eltseq(M)>;
 end if;
 if s eq 1 then
    return &meet[ideal<R|m> : m in Eltseq(M)];
 end if;
  
 I := ideal<R|R!1>;
 F := Module(R,r-1);
 
 for i in [1..r] do
   modu := sub<F|[F!Eltseq(M1[j]) : j in [1..s]]>
	where M1 is Transpose(Matrix(R,[Eltseq(M[k]):k in [1..r] | k ne i]));
   syzs := [Eltseq(b) : b in Basis(SyzygyModule(modu))];
   I meet:= ideal<R | [ &+[row[j]*syz[j]:j in [1..s]] : syz in syzs]>
	where row is Eltseq(M[i]);
 end for;
 
 return I;
 
end function;

function LinearInverses(I,F,P)
/* I is the ideal of X in P^r=Proj[x_0,..,x_r]. F is an isomorphism
   of X to Y in P^s=Proj[y_0,..,y_s]=P which has a linear inverse.
   Function finds a basis for these linear inverses.
   It is assumed that X,Y are integral schemes and Y lies in
   no hyperplane (<=> Fi lin indep mod I).
*/

    R := Generic(I);
    K := BaseRing(R);
    n := Rank(R);
    m := #F;
    d := TotalDegree(F[1]);

    V := KSpace(K,2*m);
    Ws := [**];
    seq1 := [NormalForm(-f*R.1,I): f in F];
    mons1 := &join[Seqset(Monomials(f)): f in seq1];
    for i in [2..n] do
	seq := [NormalForm(f*R.i,I): f in F];
	mons := Setseq(mons1 join &join[Seqset(Monomials(f)): f in seq]);
	mat := Matrix(
	    K, [[MonomialCoefficient(f,m):m in mons]: f in seq cat seq1]
	);
	B := Basis(Kernel(mat));
	Append(~Ws,sub<V|[V!Eltseq(b) : b in B]>);
    end for;

    if n eq 2 then // bit quicker in this case
      return [[&+[es[i]*P.i : i in [1..m]],&+[es[i+m]*P.i : i in [1..m]]]
		where es is Eltseq(b) : b in Basis(Ws[1])];
    end if;
    V1 := KSpace(K,m);
    prj := Hom(V,V1)!VerticalJoin(IdentityMatrix(K,m),ZeroMatrix(K,m,m));
    W1 := &meet[sub<V1|[b*prj: b in Basis(W)]>: W in Ws];
    mps := [];
    /*mats := [Matrix([Partition(Eltseq(v),m)[i] : v in Basis(Wi)]) :
			Wi in Ws, i in [1,2]];*/
    mats1 := [**]; mats2 := [**];
    for W in Ws do
	Append(~mats1,Matrix([Partition(Eltseq(v),m)[1] : v in Basis(W)]));
	Append(~mats2,Matrix([Partition(Eltseq(v),m)[2] : v in Basis(W)]));
    end for;
    for w in Basis(W1) do
	mp := [&+[(Eltseq(w))[i]*P.i : i in [1..m]]];
	for i in [1..n-1] do
	    v := Solution(mats1[i],w);
	    es := Eltseq(v*mats2[i]);
	    Append(~mp,&+[es[j]*P.j : j in [1..m]]);
	end for;
	Append(~mps,mp);
    end for;
    return mps;
end function;

/*
function planeInverse(I,F1,F2,P1)
// C is a degree d plane rational curve (ideal I) with birational
// map to P^1 (P1) given by [F1,F2], Fi homog of degree d-2.
// Finds an inverse - [G1,G2,G3] with the Gi of degree d.
    d := TotalDegree(F1)+2;
    R := Generic(I);
    K := BaseRing(R);

    P := PolynomialRing(K,d+1);
    F := [(F1^i)*(F2^(d-i)) : i in [0..d]];
    lins := LinearInverses(I,F,P);
    assert #lins gt 0;

    lin := lins[1];
    F := [(P1.1^i)*(P1.2^(d-i)) : i in [0..d]];
    return [Evaluate(lin[i],F): i in [1..3]];

end function;
*/

function planeInverse(C,F1,F2,P1)
// C is a degree d plane rational curve (ideal I) with birational
// map to P^1 (P1) given by [F1,F2], Fi homog of degree d-2.
// Finds an inverse - [G1,G2,G3] with the Gi of degree d.
//  USE FUNCTION FIELDS HERE AS SEEMS BETTER THAN ELIMINATION!
    d := TotalDegree(F1)+2;
    K := BaseRing(C);

    FF := FunctionField(C);
    AFF,fmp := AlgorithmicFunctionField(FF);
    Ff := fmp(FF!(F1/F2));
    seq := [Ff^i : i in [0..d]];
    seq1 := [-xz*f: f in seq] where xz is fmp(FF!(C.1/C.3));
    seq2 := [-xy*f: f in seq] where xy is fmp(FF!(C.1/C.2));
    V1 := Relations(seq cat seq1,K);
    assert Dimension(V1) gt 0;
    V2 := Relations(seq cat seq2,K);
    assert Dimension(V2) gt 0;
    // get "V1 meet V2"
    V := KSpace(K,d+1);
    W := sub<V|[V!(Partition(Eltseq(b),d+1)[1]): b in Basis(V1)]> meet
		sub<V|[V!(Partition(Eltseq(b),d+1)[1]): b in Basis(V2)]>;
    assert Dimension(W) gt 0;
    // now recover relations
    //mats := [Matrix([Partition(Eltseq(v),d+1)[i] : v in Basis(Vi)]) :
    //			Vi in [V1,V2], i in [1,2]];
    mats := [**];
    for i in [1,2], Vi in [V1,V2] do
	Append(~mats,Matrix([Partition(Eltseq(v),d+1)[i] : v in Basis(Vi)]));
    end for;
    w := Basis(W)[1];
    ws := [];
    for i in [1..2] do
	v := Solution(mats[i],w);
	Append(~ws,Eltseq(v*mats[i+2]));
    end for;

    lin := [Eltseq(w),ws[2],ws[1]];
    F := [(P1.1^i)*(P1.2^(d-i)) : i in [0..d]];
    return [&+[lin[i][j]*F[j] : j in [1..d+1]]: i in [1..3]];

end function;

function myElimination(M,r)
/* R = k[x1,..xn], M is an n*m matrix of homogeneous forms in k[y1,y2,yt]
   with degree(M[i,j]) = d for i <= r and = 2 for i > r.
   s.t. the matrix equation (x1,x2,..,xn)*M has a unique solution with
   x1,..xr homogeneous of degree d+2 if r=n or, if r < n, a solution with
   the x1,..xr homog of degree d+1 + maybe solutions homog of degree 2
   and the first soln is essentially unique up to multiples of the second.
   Returns a degree d+2 (resp. d+1) solution */

   S := BaseRing(M);
   n := Nrows(M); m := Ncols(M);
   F := Module(S,m);
   Mo := sub<F|[F!Eltseq(M[i]) : i in [1..n]]>;
   B := Basis(SyzygyModule(Mo));
   if r eq n then
     assert #B eq 1;
     return Eltseq(B[1]);
   else
     d := TotalDegree([e:e in Eltseq(M)|e ne 0][1]);
     B := [[bs[i]:i in [1..r]] where bs is Eltseq(b): b in B];
     B := [b: b in B | &and[(p eq 0) or (TotalDegree(p) eq d+1) : p in b]];
     // "trivial" solutions should lead to basis elements with
     // only one non-zero entry!
     B := [b: b in B | #[e:e in b | e ne 0] gt 1];
     assert #B ge 1;
     return B[#B];
   end if;

end function;

function RecurseAdjointMap(I)
/*
   I is the ideal defining a rational normal curve X in P^(d-1) [d >= 4].
   Recursively computes the images of the adjoint maps until reaching
   P^1 or a plane conic C.
   Returns the equation Q of the final image (0 in the P^1 case) and the
   explicit parametrisation of X in terms of a sequence of d polynomials
   of degree (d-2) in the coordinate ring of Q
*/
    R := Generic(I);
    K := BaseRing(R);
    d := Rank(R);

    M := QuotientModule(I);
    mat_xy := BoundaryMap(MinimalFreeResolution(M),d-2);
    delete M;
    assert (Nrows(mat_xy) eq d-2) and (Ncols(mat_xy)eq (d-1)*(d-3));
   
    R1 := PolynomialRing(BaseRing(R),d-2,"grevlex");
    mat_yx := Matrix(R1,[ [&+[(R1.k)*(K!Derivative(mat_xy[k,j],i)) :
    	k in [1..d-2]]: j in [1..(d-1)*(d-3)]] : i in [1..d] ]);
    if d ge 5 then
      I1 := Annihilator(mat_yx);
    end if;

    
    if d gt 5 then
	eqns,Q := RecurseAdjointMap(I1);
	mat_yx := Matrix(Universe(eqns),d,(d-1)*(d-3),mp(Eltseq(mat_yx)))
			where mp is hom<R1->Universe(eqns) | eqns>;
    elif d eq 5 then
	eqns := [R1.1,R1.2,R1.3];
	Q := GroebnerBasis(I1)[1];
    else
	assert d eq 4;
	eqns := [R1.1,R1.2];
	Q := 0;
    end if;

    if IsOdd(d) then
	mat_yx := VerticalJoin(mat_yx,ScalarMatrix((d-1)*(d-3),Q));
    end if;

    return myElimination(mat_yx,d),Q;

end function;

intrinsic ParametrizeRationalNormalCurve(C::Crv) -> MapIsoSch
{ C is a rational normal curve of degree d in P^d (warning: this is
  not fully checked!). Finds an isomorphism from the projective line
 (resp. a plane conic) to C if d is odd (resp. even) using adjunction
 maps.}
    require IsOrdinaryProjective(C):
	"Curve must lie in ordinary projective space";
    Pd := Ambient(C);
    Rd := CoordinateRing(Pd);
    d := Rank(Rd)-1;

    // deal with trivial cases
    if d eq 1 then
	return IdentityMap(C);
    end if;
    if d eq 2 then
	require (Degree(C) eq 2) and (IsNonsingular(C)):
		"Curve is not rational normal curve.";
	return iso<Conic(Pd,Equation(C))->C|[Pd.i : i in [1..3]],
			[Pd.i : i in [1..3]] : Check := false>;
    end if;

    I := Ideal(C);
    prm,Q := RecurseAdjointMap(I);
    R1 := Universe(prm);
    prmi := LinearInverses(ideal<R1|Q>,prm,Rd);
    rat_crv := IsOdd(d) select Curve(Proj(R1)) else Conic(Proj(R1),Q);
    return iso<rat_crv->C|prm,prmi : Check := false>;

end intrinsic;

function parametrise_ord_curve(C,Iadj,p)
// C is an (irreducible) ordinary rational plane curve with adjoint
// ideal Iadj. p is a non-sing. rational point on C or a degree 1
// place of its function field or 0. Returns a parametrisation.
    P2 := Ambient(C);
    d := Degree(C);
    assert d ge 3;

    adj_sys := Sections(AdjointLinearSystemFromIdeal(Iadj,d-2));
    assert #adj_sys eq d-1;
    X := CanonicalImage(C,adj_sys);

    // find image of p on X
    if Type(p) eq RngIntElt then
	ptX := 0;
    elif Type(p) eq Pt then
	ptX := X![Evaluate(f,Eltseq(p)) : f in adj_sys];
    else
	K := FunctionField(C);
	fns := [K!(adj_sys[i]/adj_sys[1]) : i in [1..d-1]];
	_,i := Min([Valuation(f,p) : f in fns]);
	fns := [f/fm : f in fns] where fm is fns[i];
	ptX := X![BaseRing(C)|Evaluate(f,p) : f in fns];
    end if;
    boo_pt := (Type(p) ne RngIntElt);

    prmX := ParametrizeRationalNormalCurve(X);
    if IsEven(d) then // prmX to conic
	co := Domain(prmX);
	ptco := (boo_pt select Inverse(prmX)(ptX) else 0);
	P1 := Curve(ProjectiveSpace(BaseRing(C),1));
	if boo_pt then
	    prm1 := Parametrization(co,ptco,P1);
	else
	    prm1 := Parametrization(co,P1);
	end if;
	ptseq := (boo_pt select Eltseq(ptX) else 0);
	for lin1 in AllInverseDefiningPolynomials(prm1),
		lin2 in  AllInverseDefiningPolynomials(prmX) do
	    lin := [Evaluate(lin1[i],lin2) : i in [1..2]];
	    if not boo_pt then break; end if;
	    ptP1 := [Evaluate(f,ptseq): f in lin];
	    if (ptP1[1] ne 0) or (ptP1[2] ne 0) then
		break;
	    end if;
	end for;
    else // prmX to line
	P1 := Domain(prmX);
	for l in AllInverseDefiningPolynomials(prmX) do
	    lin := l;
	    if not boo_pt then break; end if;
	    ptP1 := [Evaluate(f,Eltseq(ptX)): f in lin];
	    if (ptP1[1] ne 0) or (ptP1[2] ne 0) then
		break;
	    end if;
	end for;
    end if;
    delete prmX;
    if boo_pt then assert (ptP1[1] ne 0) or (ptP1[2] ne 0); end if;
    Fs := [Evaluate(lin[i],adj_sys): i in [1..2]];

    // C->P1 given by Fs (of degree d-2) - now get inverse polys (deg d)
    Gs := planeInverse(C,Fs[1],Fs[2],P1);

    // for d odd, translate so p -> infty (automatic for d even!)
    if IsOdd(d) and boo_pt and (ptP1[2] ne 0) then
	if ptP1[1] eq 0 then
	    tmp := Fs[2]; Fs[2] := Fs[1]; Fs[1] := tmp;
	    Gs := [Evaluate(g,[P1.2,P1.1]) : g in Gs];
	else
	    Fs[2] -:= (ptP1[2]/ptP1[1])*Fs[1];
	    Gs := [Evaluate(g,[P1.1,P1.2+(ptP1[2]/ptP1[1])*P1.1]) : g in Gs];
	end if;	
    end if;
    return iso<P1->C | Gs,Fs : Check := false>;
end function;

intrinsic ParametrizeOrdinaryCurve(C::Crv,p::Pt,Iadj::RngMPol) -> MapIsoSch
{ C is an (irreducible) ordinary rational plane curve with adjoint
  ideal Iadj. p is a non-singular rational point on C. Returns a 
  parametrisation of C taking infinity to p.}
    boo,p := IsCoercible(C,p);
    require boo: 
	"Argument 2 must be a point of argument 1 over its base ring.";
    require IsNonsingular(p):
	"Argument 2 must be a non-singular point on argument 1.";
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    require Generic(Iadj) eq CoordinateRing(Ambient(C)):
	"Argument 3 must be the adjoint ideal of argument 1.";
    require IsIrreducible(Equation(C)) and 
		HasOnlyOrdinarySingularities(C : Adjoint := false):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,p);
end intrinsic;

intrinsic ParametrizeOrdinaryCurve(C::Crv,p::PlcCrvElt,Iadj::RngMPol) 
				-> MapIsoSch
{ C is an (irreducible) ordinary rational plane curve with adjoint
  ideal Iadj. p is a degree 1 place of C. Returns a 
  parametrisation of C taking infinity to p.}
    boo,p := IsCoercible(Places(C),p);
    require boo and (Degree(p) eq 1): 
	"Argument 2 must be a place on argument 1 of degree 1.";
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    require Generic(Iadj) eq CoordinateRing(Ambient(C)):
	"Argument 3 must be the adjoint ideal of argument 1.";
    require IsIrreducible(Equation(C)) and 
		HasOnlyOrdinarySingularities(C : Adjoint := false):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,p);
end intrinsic;

intrinsic ParametrizeOrdinaryCurve(C::Crv,p::Pt) -> MapIsoSch
{ C is an (irreducible) ordinary rational plane curv. p is a 
  non-singular rational point on C. Returns a parametrisation 
  of C taking infinity to p.}
    boo,p := IsCoercible(C,p);
    require boo: 
	"Argument 2 must be a point of argument 1 over its base ring.";
    require IsNonsingular(p):
	"Argument 2 must be a non-singular point on argument 1.";
    if IsAffine(C) then C := ProjectiveClosure(C); p := C!p; end if;
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    boo,_,Iadj := HasOnlyOrdinarySingularities(C);
    require boo and IsIrreducible(Equation(C)):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,p);
end intrinsic;

intrinsic ParametrizeOrdinaryCurve(C::Crv,p::PlcCrvElt) -> MapIsoSch
{ C is an (irreducible) ordinary rational plane curve. p is a degree 
  1 place of C. Returns a parametrisation of C taking infinity to p.}
    if IsAffine(C) then C := ProjectiveClosure(C); end if;
    boo,p := IsCoercible(Places(C),p);
    require boo and (Degree(p) eq 1): 
	"Argument 2 must be a place on argument 1 of degree 1.";
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    boo,_,Iadj := HasOnlyOrdinarySingularities(C);
    require boo and IsIrreducible(Equation(C)):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,p);
end intrinsic;

intrinsic ParametrizeOrdinaryCurve(C::Crv) -> MapIsoSch
{ C is an (irreducible) ordinary rational plane curve. Returns a 
  parametrisation of C. If the degree of C is even, must be able to
  find a point on a conic over the basefield.}
    if IsAffine(C) then C := ProjectiveClosure(C); end if;
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    boo,_,Iadj := HasOnlyOrdinarySingularities(C);
    require boo and IsIrreducible(Equation(C)):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,0);
end intrinsic;

intrinsic ParametrizeOrdinaryCurve(C::Crv,Iadj::RngMPol) -> MapIsoSch
{ C is an (irreducible) ordinary rational plane curve with adjoint
  ideal Iadj. Returns a parametrisation of C. If the degree of C is even,
  must be able to find a point on a conic over the basefield.}
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must lie in an ordinary projective plane";
    require Generic(Iadj) eq CoordinateRing(Ambient(C)):
	"Argument 3 must be the adjoint ideal of argument 1.";
    require IsIrreducible(Equation(C)) and 
		HasOnlyOrdinarySingularities(C : Adjoint := false):
	"Argument 1 must be an irreducible, ordinary plane curve";

    return parametrise_ord_curve(C,Iadj,0);
end intrinsic;
