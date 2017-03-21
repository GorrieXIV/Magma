freeze;
/****  Gives intrinsic functions for generating random plane ***/
/**        curves with specified singularities.               **/
/**   mch with thanks to Frank-Olaf Schreyer - 2005           **/

/*
   Random(d, R) - finds a random homogeneous polynomial of degree d
		in polynomial ring R (the base ring of R should be
		the integers, rationals or have its own Random function).
   RandomPlanePoints(N, R) - returns the ideal defining N random
		points in the projective plane with coordinate ring R
   IsNodalCurve(C) - tests if plane curve C only has nodes as singularities.
   RandomNodalCurve(d, g, P) - returns a random nodal curve of degree d and 
		genus g in the projective plane P.
   RandomPlaneCurve(d, sings, P) - returns a random plane curve in the
		projective plane P of degree d and with specified
		ordinary singularities sings.
*/

intrinsic Random(d::RngIntElt, R::RngMPol, N ::RngIntElt) -> RngMPolElt
{Chooses random homogeneous element of degree d in polynomial ring R.
 If the base ring of R is the integers or rationals, random
 means random integer coefficients between -N and N incl.}
    pols := MonomialsOfDegree(R,d);
    S := BaseRing(R);
    N := Abs(N);
    case Type(S):
      when RngInt: return &+[Random(-N,N)*pol : pol in pols]; 
      when FldRat: return &+[Random(-N,N)*pol : pol in pols];
    end case;
    return &+[Random(S)*pol : pol in pols];

end intrinsic;

/** some functions for random matrices over polynomial rings ******/

function RandomMatrixM(M,R,N)
// takes an m*n integer matrix M and polynomnial ring R and returns
// a random m*n matrix over R s.t. the (i,j)th entry has degree M[m,n]
    return Matrix(R,Nrows(M),Ncols(M),[Random(seq[i],R,N): i in [1..#seq]])
			where seq is Eltseq(M);
end function;

function RandomMatrix(v,w,R,N)
// produces a random matrix of polys in R of degrees given by
// v[i]-w[j] in the (i,j)th place. [v,w are sequences of ints]
    return Matrix(R,[[Random(i-j,R,N): j in w] : i in v]);
end function;

/***************************************************************/

intrinsic RandomPlanePoints(N::RngIntElt, R::RngMPol :
		RndP := 9) -> SeqEnum
{Returns the ideal defining N (not necessarily distinct)
 points in the projective plane with coordinate ring R}
    k := Ceiling((-3+Sqrt(9+8*N))/2);
    eps := N-Binomial(k+1,2);
    if k ge 2*eps then
	return Minors(Matrix(R,
	    [[Random(1,R,RndP):i in [1..k+1-eps]]: j in [1..k-2*eps]] cat
	    [[Random(2,R,RndP):i in [1..k+1-eps]]: j in [1..eps]]),k-eps);
    else
	return Minors(Matrix(R,
	    [[Random(2,R,RndP):i in [1..eps]]: j in [1..k+1-eps]] cat
	    [[Random(1,R,RndP):i in [1..eps]]: j in [1..2*eps-k]]),eps);
    end if;
	    
end intrinsic;

intrinsic IsNodalCurve(C::Crv) -> BoolElt
{Checks if plane curve C is a curve with only nodes as singularities}
    if assigned C`b_ord then
	return C`b_ord and (C`ord_mult le 2);
    end if;

    if IsAffine(C) then C := ProjectiveClosure(C); end if;
    require IsOrdinaryProjective(Ambient(C)) and
		(Dimension(Ambient(C)) eq 2):
	"Curve must line in affine or ordinary projective plane";

    if IsNonSingular(C) then
	C`b_ord := true; C`ord_mult := 1;
	return true;
    end if;

    F := DefiningEquation(C);
    R := Parent(F);
    X := Scheme(Ambient(C),ideal<R|[F] cat [Derivative(F,i): i in [1..3]]>);
    if (Dimension(X) lt 1) and IsNonsingular(X) then
	C`b_ord := true; C`ord_mult := 2;
	return true;
    else
	return false;
    end if;
    
end intrinsic;

intrinsic RandomNodalCurve(d::RngIntElt, g::RngIntElt, P::Prj :
		RandomBound := 9) -> CrvPln
{Finds a random nodal plane curve of degree d and genus g in the
 ordinary projective plane P}
    require IsOrdinaryProjective(P) and (Dimension(P) eq 2):
       "Last function argument must be an ordinary projective plane";
    N := Binomial(d-1,2)-g;
    require N ge 0: "First two arguments don't give plane curves";
    require 3*(g-1) ge d*(d-6): 
		"First two arguments don't give a generic solution";

    R := CoordinateRing(P);
    bNodal := false;
    while not bNodal do
	if N eq 0 then
	    C := Curve(P,Random(d,R,RandomBound));
	    if IsNonSingular(C) then break; end if;
	else
	    eqns := RandomPlanePoints(N,R: RndP := RandomBound);
	    if IsSingular(Scheme(P,eqns)) then // points not distinct
		continue;
	    end if;
	    I := Saturation(ideal<R|eqns>^2);
	    L := LinearSystem(LinearSystem(P,d),Scheme(P,I));
	    for i in [1..5] do
		repeat
		    F := Random(L);
		until F ne 0;
		C := Curve(P,F);
		bNodal := (Dimension(S) lt 1) and (Degree(S) eq N)
		   where S is SingularSubscheme(C);
		if bNodal then break; end if;
	    end for;
	end if;	    
    end while;
    C`b_ord := true;
    C`ord_mult := ((N eq 0)  select 1 else 2);
    return C;
    
end intrinsic;

myDegree := func<I| Integers()!Coefficient(HilbertPolynomial(I),0)>;

/* simplified ordinary singularity test when the ordinary sings
   <=> the jacobian ideal has a certain degree                  */
function SimpleOrdSingTest(F,deg)
    R := Generic(Parent(F));
    p := Characteristic(BaseRing(R));
    boo := ((p gt 0) and IsDivisibleBy(LeadingTotalDegree(F),p));    
    J0 := ideal<R|JacobianSequence(F)>;
    J  := boo select J0 + ideal<R|F> else J0;
    d := myDegree(J0);
    if (Dimension(J0) gt 1) or ( boo and ( (Dimension(J0) ne Dimension(J))
	 or (myDegree(J) ne d) ) ) then 
	return false; 
    end if;
    return (d eq deg);
end function;

intrinsic RandomPlaneCurve(d::RngIntElt, sings::SeqEnum, P::Prj :
    Adjoint := true, Proof := true, RandomBound := 9) -> CrvPln, RngMPol
{Finds a random plane curve in the proj plane P of degree d with
 prescribed ordinary singularities (sings[1] double points,
 sings[2] triple points etc.). If parameter Adjoint is true then,
 the adjoint ideal is also computed and returned returned.
 If parameter Proof is true then the produced curve is definitely
 tested to have no worse singularities than specified. Otherwise
 this may not be true.}
    require IsOrdinaryProjective(P) and (Dimension(P) eq 2):
       "Last function argument must be an ordinary projective plane";
    retAdj := Adjoint;
    s := &+[Integers()|sings[i]*Binomial(i+1,2): i in [1..#sings]];
    N := Binomial(d-1,2)-s;
    require N ge 0: "First two arguments don't give plane curves";

    R := CoordinateRing(P);
    R1 := PolynomialRing(BaseRing(R),3,"grevlex"); P1 := Proj(R1);
    s := &+[Integers()|sings[i]*i^2: i in [1..#sings]];
    if s eq 0 then
	Iadj := ideal<R|MonomialsOfDegree(R,1/*Max(0,d-3)*/)>;
    end if;
    while true do
	if s eq 0 then //no sings!
	    C := Curve(P,Random(d,R,RandomBound));
	    if IsNonSingular(C) then break; end if;
	else
	    I := ideal<R1|1>;
	    if retAdj then Iadj := ideal<R1|1>; end if;
	    for i in [1..#sings] do
		si := sings[i];
		if si eq 0 then continue; end if;
		repeat
		  eqns := RandomPlanePoints(si,R1: RndP := RandomBound);
		until (Dimension(I+ideal<R1|eqns>) le 0) and 
		    IsNonSingular(Scheme(P1,eqns));
		// points distinct from themselves and others in I
		I meet:= ideal<R1|eqns>^(i+1);
		I := ideal<R1|MinimalBasis(I)>; //good to do here ??
		if retAdj then
		    Iadj meet:= ideal<R1|eqns>^i;
		    Iadj := ideal<R1|MinimalBasis(Iadj)>; //good to do here ??
		end if;
	    end for;
	    I := Saturation(I);
	    I := ideal<R|MinimalBasis(I)>;
	    L := LinearSystem(LinearSystem(P,d),Scheme(P,I));
	    if Dimension(L) eq 0 then continue; end if;
	    repeat
		F := Random(L);
	    until F ne 0;	
	    C := Curve(P,F);
	    // should add test for ordinary sings here!
	    if Proof and not SimpleOrdSingTest(R1!Equation(C),s) then
		continue;
	    end if;
	    if retAdj then
		Iadj := ideal<R|MinimalBasis(Saturation(Iadj))>;
	    end if;
	    break;
	end if;	    
    end while;
    C`b_ord := true;
    C`ord_mult := 1+#sings;
    if retAdj then
	C`Iadj := Iadj;
	return C,Iadj;
    else
	return C;
    end if;
    
end intrinsic;

/**** functions for random curves of genus 11-13 in P3 *****************/

myDegree1 := func<I| Integers()!Coefficient(HilbertPolynomial(I),1)>;

function LeftKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the left kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
   Mmod := Module(BaseRing(M),Ncols(M));
   S := sub<Mmod|[M[i]:i in [1..Nrows(M)]]>;
   return [Eltseq(b): b in Basis(SyzygyModule(S))];
end function;

function RightKernel(M)
// returns a sequence of sequences, s,  s.t. the s give a
//  basis for the right kernel of polynomial matrix M
//  (seq s gives the coordinates of a kernel vector)
    return LeftKernel(Transpose(M));
end function;

function RandomGenus11Curve(R,rnd)

    u := [2,2,2,2,2,2,1,1];
    v := [2,2,2,2,2,2,3,3];
    w := [1,1,1];

    tries := 0;
    while tries lt 5 do
	tries +:=1;
	mat := RandomMatrix(v,w,R,rnd);
	// get a basis for the syzygys
	B := LeftKernel(mat);
	// make sure it's minimal
	B := MinimalBasis(sub<Module(R,8)|B>); 
	mat := Matrix(R,[Eltseq(b): b in B]);
	if (Nrows(mat) ne 11) then continue; end if;
        // get the "8R(5) -> 2R(6)+6R(2)" submatrix
	mat := Matrix(R,[ri : i in [1..11] |
	    &and[(ri[j] eq 0) or (TotalDegree(ri[j]) eq u[j]):
		j in [1..8]] where ri is Eltseq(mat[i])]);
	if (Nrows(mat) ne 8) then continue; end if;
	// random map "6R(5)->8R(5)"
	matc := RandomMatrixM(ZeroMatrix(Integers(),8,6),R,rnd);
	// compose maps
	mat := Transpose(mat)*matc;
	// I is generated by the elements of the (free rank 1) kernel map
	B := RightKernel(mat);
	B := MinimalBasis(sub<Module(R,6)|B>);
	if #B ne 1 then continue; end if;
	I := ideal<R|Eltseq(B[1])>;
	// check right dimension and degree
	if (Dimension(I) eq 2) and (myDegree1(I) eq 12) then
	    return ideal<R|Eltseq(B[1])>;
	end if;
    end while;
    error "Function failed after 5 tries!";

end function;

function RandomGenus12Curve(R,rnd)

    v := [2,2,2];
    w := [1,1,1,1,1,1,1];

    tries := 0;
    while tries lt 5 do
	tries +:=1;
	mat := RandomMatrix(v,w,R,rnd);
	// get a basis for the syzygys
	B := RightKernel(mat);
	// make sure it's minimal
	B := MinimalBasis(sub<Module(R,7)|B>); 
	mat := Matrix(R,[Eltseq(b): b in B]);
	if (Nrows(mat) ne 10) then continue; end if;
        // get a basis for the syzygys (of the transpose)
	B := LeftKernel(mat);
	mat := Matrix(R,[Eltseq(b): b in B]);
	// random map "7R(5)->10R(5)"
	matc := RandomMatrixM(ZeroMatrix(Integers(),10,7),R,rnd);
	// compose maps
	mat := mat*matc;
	// I is generated by the elements of the (free rank 1) kernel map
	B := RightKernel(mat);
	B := MinimalBasis(sub<Module(R,7)|B>);
	if #B ne 1 then continue; end if;
	I := ideal<R|Eltseq(B[1])>;
	// check right dimension and degree
	if (Dimension(I) eq 2) and (myDegree1(I) eq 12) then
	    return ideal<R|Eltseq(B[1])>;
	end if;
    end while;
    error "Function failed after 5 tries!";

end function;

function RandomGenus13Curve(R,rnd)

    v := [2,2,2,2];
    w := [1,1,1,1,1];

    tries := 0;
    while tries lt 5 do
	tries +:=1;
	// start with the 6*4 Koszul matrix
	mk := Matrix(R,6,4,[-R.2,R.1,0,0,-R.3,0,R.1,0,0,-R.3,R.2,0,
	  -R.4,0,0,R.1,0,-R.4,0,R.2,0,0,-R.4,R.3]);
	// and get 4 random linear combinations of rows
	// for a 4R(-3)->4R(-2) map with a linear syzygy
	mat := RandomMatrixM(ZeroMatrix(Integers(),4,6),R,rnd)*mk;
	//"add" a random 5R(-3) -> 4R(-2) map
	mat := HorizontalJoin(mat,RandomMatrix(v,w,R,rnd));
	// get a basis for the syzygys
	B := RightKernel(mat);
	// make sure it's minimal
	B := MinimalBasis(sub<Module(R,9)|B>);
	mat := Matrix(R,[Eltseq(b): b in B]);
	if (Nrows(mat) ne 13) then continue; end if;
        // get a basis for the syzygys (of the transpose)
	B := LeftKernel(mat);
	//mat := Matrix(R,[Eltseq(b): b in B]);
	// minimise
	B := MinimalBasis(sub<Module(R,[-3] cat [-2 : i in [1..6]] cat
			[-1: i in [1..6]])|B>);
	mat := Matrix(R,[Eltseq(b): b in B]);
	if (Nrows(mat) ne 13) then continue; end if;
	mat := Transpose(mat);
	//pick out the 6 rows of degree 2 and degree 1 entries
	mat1 := Matrix(R,[ri : i in [1..13] |
	    &and[(ri[j] eq 0) or (TotalDegree(ri[j]) eq 2):
		j in [1..13]] where ri is Eltseq(mat[i])]);
	if (Nrows(mat1) ne 6) then continue; end if;
	mat2 := Matrix(R,[ri : i in [1..13] |
	    &and[(ri[j] eq 0) or (TotalDegree(ri[j]) eq 1):
		j in [1..13]] where ri is Eltseq(mat[i])]);
	if (Nrows(mat2) ne 6) then continue; end if;
	mat := VerticalJoin(mat1,mat2);
	// random degree 0 map + identity "3R(5)+6R(6)->6R(5)+6R(6)"
	matc := DiagonalJoin(RandomMatrixM(ZeroMatrix(Integers(),3,6),R,rnd),
				IdentityMatrix(R,6));
	// compose maps
	mat := matc*mat;
	// I is generated by the elements of the (free rank 1) kernel map
	B := LeftKernel(mat);
	B := MinimalBasis(sub<Module(R,9)|B>);
	if #B ne 1 then continue; end if;
	I := ideal<R|Eltseq(B[1])>;
	// check right dimension and degree
	if (Dimension(I) eq 2) and (myDegree1(I) eq 13) then
	    return ideal<R|Eltseq(B[1])>;
	end if;
    end while;
    error "Function failed after 5 tries!";

end function;

/**********************************************************************/

intrinsic RandomCurveByGenus(g::RngIntElt, K::Fld : 
				RandomBound := 9) -> Crv
{ Generates a random curve of genus g over the field K (which should
  be Q or finite). RandomBound controls the size of the coefficients
  of the result when K is Q.}
    require (g ge 0) and (g le 13):
	 "Genus must be between 0 and 13 inclusive";

    if g le 10 then
	P2<x,y,z> := ProjectiveSpace(K,2);
	return RandomNodalCurve(g+2-Floor(g/3),g,P2:
				RandomBound := RandomBound);
    end if;

    R<x,y,z,t> := PolynomialRing(K,4);
    P3 := Proj(R);
    rnd := Max(1,Floor(RandomBound/4));
    while true do
	case g:
	    when 11: I := RandomGenus11Curve(R,rnd);
	    when 12: I := RandomGenus12Curve(R,rnd);
	    when 13: I := RandomGenus13Curve(R,rnd);
	end case;
	C := Curve(P3,Basis(I));
	if IsNonsingular(C) then return C; end if;
	delete C,I;
    end while;
end intrinsic;
