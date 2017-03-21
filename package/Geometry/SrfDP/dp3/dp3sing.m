freeze;
/////////////////////////////////////////////////////////////////////////////////
//          PARAMETRISATION OF DEGREE 3 DEL PEZZO SURFACES                     //
//                 Main functions. mch - 11/10                                 //
/////////////////////////////////////////////////////////////////////////////////

import "../dp6/geom_proj.m": PointProjection;

/// MAIN INTRINSIC /////////////////////////////////////////////////////

intrinsic ParametrizeSingularDegree3DelPezzo(X::Sch,P2::Prj)
-> BoolElt, MapSch
{ Determines whether a singular, anticanonically-embedded degree 3 Del Pezzo surface X
  is parametrizable over the base field. If so,
  also returns a parametrization from P2 (2D projective space) to X. }

    Xsng := ReducedSubscheme(SingularSubscheme(X));
    require Dimension(Xsng) eq 0 : "First argument should be a SINGULAR degree 3 Del Pezzo";
    
    ksngs := Support(Xsng);
    // any k-rational singular points?
    if #ksngs gt 0 then //project from singular point to P2
	sng_pt := Representative(ksngs);
	prj := PointProjection(X,sng_pt,3);
	prm := Expand(im*Inverse(prj)) where im is iso<P2->D|[P2.1,P2.2,P2.3],[D.1,D.2,D.3]>
		where D is Codomain(prj);
	return true,prm;
    end if;

    d := Degree(Xsng);
    if d eq 4 then //4A1 case
	// twisted form of Cayley surface xy(z+t)+zt(x+y)=0.
	//  eqn of X is given as the sum of 4 cubics
        //  These 4 cubics span the space of deg 3 forms on P^3, vanishing to degree
        //  >= 2 at each singular point.

        // 1. find this space of cubics
	I2 := Saturation(Ideal(Xsng)^2);
	B := MinimalBasis(I2);
	assert #B eq 10;
	B := [b : b in B | TotalDegree(b) eq 3];
	assert #B eq 4;

	// 2. Get eqn for X as lin comb of elts of B
	R := CoordinateRing(Ambient(X));
	m3 := Setseq(MonomialsOfDegree(R,3));
	eqn := GroebnerBasis(Ideal(X))[1];
	mat := Matrix([[MonomialCoefficient(b,m) : m in m3] : b in B cat [-eqn]]);
	L := Basis(Kernel(mat));
	assert #L eq 1;
	L := L[1];
	assert L[5] ne 0;
	L := [L[i]/L[5] : i in [1..4]];

 	// 3. Now use B and eqn to get a parametrisation
	j := Max([i : i in [1..4] | L[i] ne 0]);
	cubs := [B[i] : i in [1..4] | i ne j];
	 // cubs gives the map to P2 - must also get the birat inverse
	cubi := [P2.i : i in [1..3]];
	Insert(~cubi,j,0);
	cubi[j] := -&+[L[i]*cubi[i]:i in [1..4]]/L[j];
              //cubi are linear forms giving B from cubs on X
	 // let B := [c1,c2,c3,c4]. Exists a unique (up to scalar) deg 4 poly F
         // s.t. F vanishes to order 3 at each of the singularities (F=xyzt for
	 // the Cayley curve). then xF^2=px(c1,..c4), yF^2=py(c1,..c4) ...
         // for unique deg 3 polys px,py,pz,pt. These give the inverse map
	I3 := Saturation(I2*Ideal(Xsng));
	B3 := MinimalBasis(I3);
	B3 := [b : b in B3 | TotalDegree(b) eq 4];
	assert #B3 eq 1;
        F := B3[1];
	F2 := F^2;
	m3 := Setseq(MonomialsOfDegree(R,3));
	m9 := Setseq(MonomialsOfDegree(R,9));
	cub3 := [Evaluate(m,B) : m in m3];
	mat :=  Matrix([[MonomialCoefficient(b,m) : m in m9] : b in cub3]);
	vecs := [Vector([MonomialCoefficient((R.i)*F2,m) : m in m9]) : i in [1..4]];
	ps := Solution(mat,vecs);
	ipols := [Polynomial(Eltseq(p),m3) : p in ps];
	ipols := [Evaluate(pol,cubi) : pol in ipols];
	return true,iso<P2->X|ipols,cubs : Check := false>;
    end if;

    // remaining cases should be 2 conjugate A1 or A2 singularities P1 & P2.
    // or 3 conjugate A1 or A2 singularities P1, P2 & P3.
    //  X or it intersects X only in P1 and P2.

    // The 2 conj sings case:
    if d eq 2 then
    // projection from the line joining the two singularities gives X as a 
    // line or conic bundle over P^1 - always parametrizable
	P3 := Ambient(X);
	L := LinearSystem(P3,1);
	Leqns := Sections(LinearSystem(L,Xsng));
	P1 := ProjectiveSpace(BaseRing(P3),1);
	prj := map<X->P1|Leqns>;
	return ParametrizePencil(prj,P2);
    end if;

    assert d eq 3;
    // the linear system given by all quadrics on P^3 passing through the 3
    // singular points restrict to the desingularised X, X1, and blow down 3
    // non-interesting (and conjugate) -1 curves to give a nonsingular deg
    // 6 Del Pezzo anticanonically embedded in P^6. We then parametrise by
    // the Lie algebra method.
    P3 := Ambient(X);
    L := LinearSystem(P3,2);
    Leqns := Sections(LinearSystem(L,Xsng));
    assert #Leqns eq 7;
    P6 := ProjectiveSpace(BaseRing(P3),6);
    Y := Image(map<X->P6|Leqns>);
    // get inverse equations for X->Y
    Hsecs := Sections(LinearSystem(LinearSystem(L,Xsng),Xsng));
    assert #Hsecs eq 1;
    H := Hsecs[1]; // equation for the hyperplane through the 3 singular points
    R3 := CoordinateRing(P3);
    mons := Setseq(MonomialsOfDegree(R3,2));
    mat := Matrix([[MonomialCoefficient(b,m) : m in mons] : b in Leqns]);
    vecs := [Vector([MonomialCoefficient((R3.i)*H,m) : m in mons]) : i in [1..4]];
    ipols := [Polynomial(Eltseq(p),m1) : p in Solution(mat,vecs)] where m1 is
		[CoordinateRing(P6).i : i in [1..7]];
    imXtoY := iso<X->Y|Leqns,ipols : Check := false>;
    // now try to parametrize Y
    boo, prm := ParametrizeDegree6DelPezzo(Y);
    if not boo then return false,_; end if;
    prm := Expand(prm*Inverse(imXtoY));
    prm := Expand(im*prm) where im is iso<P2->D|[P2.1,P2.2,P2.3],[D.1,D.2,D.3]>
		where D is Domain(prm);
    return true,prm;

end intrinsic;
