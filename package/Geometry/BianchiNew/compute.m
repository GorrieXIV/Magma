freeze;

// 02/10/2012
/* Voronoi for Hermitian forms in n variables over imaginary quadratic
field */
/*
NOTES:
Revision for BianchiCuspForms.  Make compatible the general code for Voronoi computations with existing Bianchi package.
*/

import "defs.m" : CellRec;

setup := recformat< n, basefield, conjugate, ipmat, ideals >;

homologybasering := Integers(); // can be changed as long as it is
                                // done before homology file loads

forward cone_ip_matrix;

function initialize(M)
    F := M`Field;
    OF := Integers(F);
    conjugate := Automorphisms(F)[2];
    init := rec<setup | n := 2, basefield := F, conjugate := conjugate>;
    init`ipmat := cone_ip_matrix(init);
    return init;
end function;



function star(M)
    c:=NumberOfRows(M);
    return Matrix(c,[Trace(e)-e : e in Eltseq(Transpose(M))]);
end function;


// Change to make group smaller when there are torsion units.
function matrix_stabilizer(A)
    // compute representatives for the PGL group of g such that
    // g*A*star(g) = A;
    G := HermitianAutomorphismGroup(A);
    F := CoefficientRing(G.1);
    U,f := TorsionUnitGroup(F);
    S := sub<G | [ ScalarMatrix(F,NumberOfRows(A),f(a)) : a in U ]>;
    PGL,pi := quo<G | S>;
    return [ a@@pi : a in PGL ],G;
end function;

function cone_to_hermitian(D,vv)
    // given a vector in Q^n, returns the corresponding Hermitian
    // matrix
    // Should be inverse to hermitian_to_cone
    F := D`basefield;
    OF := Integers(F);
    a, b1, b2, c := Explode(Eltseq(vv));
    b := b1*OF.1 + b2*OF.2;
    bb := F`Conjugate(b);
    A := Matrix(F, 2, [a, b, bb, c] );
    return A;
end function;

function hermitian_to_cone(A)
    // given hermitian matrix with coefficients in F, return the cone
    // coordinates.
    F := Parent(A[1,1]);
    return ToBianchiCone(F,A);
end function;

function cone_ip_matrix(D)
    n := D`n;
    m := n^2;
    Q := ZeroMatrix(Rationals(),m,m);
    B := IdentityMatrix(Rationals(),m);
    for i,j in [1..n^2] do
	Q[i,j] := Trace(cone_to_hermitian(D,B[i])*cone_to_hermitian(D,B[j]));
    end for;
    return Q;
end function;

// TO DO: into C
// IsGLConj calls this + further processing before calling IsIsomorphic
//
function hermitian_to_fat(H)
    // given Hermitian matrix HH, return the pair (R,I) of rational
    // matrices, where R represents HH as a positive definite
    // qudadratic form in 2n variables (x,y), and I is such that R +
    // sI = HH, where s is the imaginary component of w.  It follows
    // that rational matrices that fix (R,I) can be converted to
    // GL_n(F) matrices that fix HH.
    F := Parent(H[1,1]);
    w := F!(Integers(F).2);
    A := MatrixRing(F, 4) ! 0;
    InsertBlock(~A, H, 1, 1);
    InsertBlock(~A, w*H, 1, 3);
    InsertBlock(~A, (Trace(w) - w)*H, 3, 1);
    InsertBlock(~A, Norm(w)*H, 3, 3);
    R := ChangeRing(A+Transpose(A),Rationals())/2;
    s := w-Trace(w)/2;
    bool, I := CanChangeRing((A - R)/s,Rationals());
    assert bool;
    return [R,I];
end function;

function hermitian_to_symmetric(H)
    // Given a hermitian matrix H with coefficients in F, return the
    // symmetric matrix representing the quadratic form.  The
    // ordering of basis is all xs, then all ys, where elements of F are written
    // as x + wy
    return hermitian_to_fat(H)[1];
end function;


function q(v)
    // this is faster but only for n = 3.
    a := v[1];
    b := v[2];
    A := Trace(a) - a;
    B := Trace(b) - b;
    return Matrix(2,[a*A, a*B, b*A, b*B]);
end function;


function ip(A,B)
    // return inner product in cone space
    // assumes A, B are symmetric matrices.
    return  Rationals()!Trace(A*B);
end function;

function minimum(H)
    // return minimum of hermitian H
    // quadratic form associated to A
    A := hermitian_to_symmetric(H);
    if IsPositiveDefinite(A) then 
	L := LatticeWithGram(A);
	m := Minimum(L);
    else
	m := 0;
    end if;
    return m;
end function;



function minimal_vectors(H)
    // assumes H is a Hermitian matrix.
    // returns a list of representatives in F^n for the vertices on
    // the cone.  Specifically, removes vectors that are a torsion
    // scalar difference
    F := Parent(H[1,1]);
    w := F!(Integers(F).2);
    A := hermitian_to_symmetric(H);
    L := LatticeWithGram(A);
    MM := ShortestVectors(L);
    ZM := [Eltseq(v): v in MM];
    M := [];
    AM := [];
    qvsofar :=[];
    for zv in ZM do
	//v := [ F| zv[i] + w*zv[n + i]: i in [ 1..n ] ];
	v := [ F| zv[1] + w*zv[3],  zv[2] + w*zv[4]];
	Append(~AM,v);
	qv := q(v);
	if not qv in qvsofar then
	    Append(~qvsofar, qv);
	    Append(~M, v);
	end if;
    end for;
    if #M ne #MM then
	vprint Bianchi,2: "minimal vectors removed due to torsion.";
    end if;
    Sort(~M);
    return M;
end function;

function ispositivedefinite(H)
    A := hermitian_to_symmetric(H);
    return IsPositiveDefinite(A);
end function;
    
function get_rho(A, R, M)
    // Output rho such that A + rho*R is perfect
    // assumes R is chosen in the correct direction. i.e. R is
    // perpendicular to minimal vectors that we want to keep (K)
    // and ip(q(v), R) is positive for the other minimal vectors of A
    // uses corrected algorithm described in Erratum (Schurmann)
    // A and R are symmetric matrices, K is list of symmetric matrices
    // (rank 1) coming from minimal vectors
    // assumes A is scaled so that minimum(A) = 1
    // M is minimal vectors of A
    m := 1;
    u := 1;
    l := 0;
    min := minimum(A + u*R);
    ///while not(ispositivedefinite(A + u*R)) or minimum(A + u*R) eq 1
    //do
    while  min in {0,1} do
	if min eq 0 then
	    u := (l + u)/2;
	else
	    l := u;
	    u := 2*u;
	end if;
	min := minimum(A + u*R);
    end while;
    qM := [q(v) : v in M];
    while Seqset([q(v) : v in minimal_vectors(A + l*R)]) subset Seqset(qM) do
	vprint Bianchi,2: "phase II.";
	gamma := (u + l)/2;
	if minimum(A + gamma*R) ge m then
	    vprint Bianchi,2: "phase IIA.";
	    l := gamma;
	else
	    vprint Bianchi,2: "phase IIB.";
	    S := [(m - ip(A, q(v)))/ip(R,q(v)): v in
		minimal_vectors(A + gamma*R)] cat [gamma];
	    u := Minimum(S);
	end if;
	if minimum(A + u*R) eq m then
	    vprint Bianchi,2: "phase IIC.";
	    l := u;
	end if;
    end while;
    return l;
end function;

function flip_form(A,R,M)
    // get next form using A, in direction R.  Assumes R is pointing
    // M is minimal vectors of A
    // in correct direction.
    // A and R are Hermitian matrices.
    rho := get_rho(A,R,M);
    return A + rho*R;
end function;

function perpendicular_to_vecs(D,L)
    // given a list of minimal vectors, computes the space
    // perpendicular to it in the conespace
    Q := Transpose(Matrix([hermitian_to_cone(q(v)): v in L]));
    return NullSpace(D`ipmat*Q);
end function;

function polytope(L)
    // given a collection of minimal vectors, compute the polytope in
    // C
    
    // the minimal vectors might by F-scalar multiples of each other.
    // These give rise to the same point in the cone space when the
    // scalar has norm one, and so should be removed.  Fixed the
    //minimal vectors command to account for this
    
    qvlist := [q(v): v in L];
    vertices := [hermitian_to_cone(qv): qv in qvlist];
    P := Polytope(vertices);
    assert [Eltseq(a): a in Vertices(P)] eq vertices;
    return P;
end function;

function first_form(D)
    // return an initial perfect form.
    
    F := D`basefield;
    A := Matrix(F,2,[1, -1/2, -1/2, 1]);
    M := minimal_vectors(A);
    perp := perpendicular_to_vecs(D,M);
    while Dimension(perp) ne 0 do
	R := cone_to_hermitian(D,perp.1);
	A := flip_form(A,R,M);
	M := minimal_vectors(A);
	perp := perpendicular_to_vecs(D,M);
    end while;
    return A;
end function;


function coneip(D,u,v)
    // given u, v in cone coordinates, return inner product
    U := Matrix(1,Eltseq(u));
    V := Matrix(1,Eltseq(v));
    return (U*D`ipmat*Transpose(V))[1,1];
end function;

function get_neighbor_form(D,A,M,ind)
    // given form A (hermitian matrix) with minimal vectors M compute 
    // the form that is  neighboring across face with indices ind
    // defining facet
    one := perpendicular_to_vecs(D,[M[i]: i in ind]);
    others := [q(M[i]): i in [1..#M] | not i in ind];
    assert Dimension(one) eq 1;
    R := cone_to_hermitian(D,one.1); // candidate extreme ray
    I := [ip(R,v) : v in others];
    if &and[i le 0: i in I] then 
	R := -R;
    else
	assert &and[i gt 0: i in I];
    end if;
    N :=  flip_form(A,R,M);
    return N;
end function;



function get_all_neighbors(D,A:M := minimal_vectors(A), modout :=
    true, polytope := polytope(M), face_ind := FacetIndices(polytope))
	// Given a form A, polytope P, and minimal vectors M, return a list of the
    // neighbors
    N := []; // neighbors.
    if modout then 
	Nind := []; // facets to consider.

	qM := [q(v) : v in M];
	bary := &+qM;
	stab := matrix_stabilizer(bary);
	done := {};
	vprint Bianchi,2: "Using stabilizer to organize facets.";
	todo := face_ind;
	while #todo ne 0 do
	    ind := todo[1];
	    Append(~Nind,ind);
	    for g in stab do
		gs := {Position(qM,g*qM[i]*star(g)) : i in ind};
		Exclude(~todo,gs);
	    end for;
	end while;

	vprint Bianchi,2: #Nind,"new neighbors to consider up to stabilizer.";    
    else
	Nind := face_ind;
    end if;
    
    for ind in Nind do
	Append(~N,get_neighbor_form(D,A,M,ind));
    end for;
    
    return N, face_ind;
end function;

function Qmat_to_Fmat(F,g)
    // given 2n x 2n rational matrix acts on (x,y), return the corresponding nxn
    // Hx = Ax + wCx matrix with coefficients in F.
    // used to take matrices which act on symmetric form to matrices
    // which act on the hermitian form
    n := 2;
    OF := Integers(F);
    w := F!(OF.2);
    cw := F`Conjugate(w);
    H := ZeroMatrix(F,2,2);
    for i,j in [1..n] do
	H[i][j]:=g[i][j]+g[i][j + n]*cw;
    end for;
    return H;
end function;

function is_isomorphic(A,B : getmover := false)
    RA,TA:=LLLGram(A[1] : Delta:=0.999); IA:=TA*A[2]*Transpose(TA);
    RB,TB:=LLLGram(B[1] : Delta:=0.999); IB:=TB*B[2]*Transpose(TB);
    tf,g0 := IsIsomorphic([RA,IA],[RB,IB]);
    if getmover then 
	if tf then
	    g := TB^-1*g0*TA;
	else
	    g := Parent(RA)!0;
	end if;
	return tf,g;
    else
	return tf;
    end if;
end function;


function matrix_is_GL_conj(A,B)
    // return Boolean and g such that gAg^* = B, if g exists.
    // Otherwise g = 0.
    F := Parent(A[1,1]);
    RA,IA := Explode(hermitian_to_fat(A));
    RB,IB := Explode(hermitian_to_fat(B));
    rA:=Lcm([Denominator(x) : x in Eltseq(RA)]);
    RA:=ChangeRing(RA*rA,Integers()); 
    iA:=Lcm([Denominator(x) : x in Eltseq(IA)]);
    IA:=ChangeRing(IA*iA,Integers());
    rB:=Lcm([Denominator(x) : x in Eltseq(RB)]);
    RB:=ChangeRing(RB*rB,Integers()); 
    iB:=Lcm([Denominator(x) : x in Eltseq(IB)]);
    IB:=ChangeRing(IB*iB,Integers());
    tf,g0 := is_isomorphic([RA,IA],[RB,IB]:getmover := true);
    if tf then
	g := Qmat_to_Fmat(F,g0);
	assert g*A*star(g) eq B;
        return tf,g;
    else
        return tf,_;
    end if;
end function;

celldata := recformat< init, polytope, Min, stabilizer, bary,
    perfectform, neighbors, facets, stabilizerplus, boundarymovers, fullstabilizer, mover>;


function get_perfect_forms(D:A := first_form(D))
    // Given initial data form, polyope, and minimal vectors, return
    // list of GL_n(OO)-classes of perfect forms

    todo := [A];
    sofar := [];
    sofarind := [];
    Msofar := [];
    sofarfat := [];
    dets := [];
    while #todo gt 0 do
	B := todo[1];
	RB,IB := Explode(hermitian_to_fat(B));
	rB:=Lcm([Denominator(x) : x in Eltseq(RB)]);
	RB:=ChangeRing(RB*rB,Integers()); 
	iB:=Lcm([Denominator(x) : x in Eltseq(IB)]);
	IB:=ChangeRing(IB*iB,Integers());
	Bfat := [RB,IB];
	Remove(~todo,1);
	det := Determinant(B);
	if not det in dets then
	    M := minimal_vectors(B);
	    P := polytope(M);
	    face_ind := FacetIndices(P);
	    Insert(~sofar, 1, B);
	    Insert(~Msofar,1,M);
	    Insert(~sofarind,1,face_ind);
	    Insert(~sofarfat,1,Bfat);
	    Insert(~dets,1,det);
	    for n in get_all_neighbors(D,B : M := M, polytope := P,
		face_ind := face_ind) do
		    if not n in todo then 
		    Append(~todo,n);
		end if;
	    end for;
	else
	    found := false;
	    for Af in sofarfat do
		if is_isomorphic(Bfat,Af) then 
		    found := true;
		    break Af;
		end if;
	    end for;
	    if not found then
		 M := minimal_vectors(B);
		 P := polytope(M);
		 face_ind := FacetIndices(P);
		 Insert(~sofar, 1, B);
		 Insert(~Msofar,1,M);
		 Insert(~sofarind,1,face_ind);
		 Insert(~sofarfat,1,Bfat);
		 for n in get_all_neighbors(D,B: M := M, polytope := P,
		     face_ind := face_ind) do
			 if not n in todo then 
			 Append(~todo,n);
		     end if;
		 end for;
	     end if;
	 end if;
     end while;
     return sofar,sofarind,Msofar;
 end function;


/**************************************************************************
Get Voronoi cell complex from perfect forms
**************************************************************************/

function make_cell(D, M)
    // create record for the cell
    cell := rec<celldata |
	init := D,
	polytope := polytope(M),
	Min := M,
	bary := &+[q(m) : m in M]
	>;
    return cell;
end function;

procedure set_stabilizer(~c)
    //  given cell c, if stabilizer is already set, do nothing.
    // otherwise, compute and set it.
    if not assigned c`stabilizer then
	vprint Bianchi,1: "Computing cell stabilizer.";
	s,fs := matrix_stabilizer(c`bary);
	c`stabilizer := s;
	c`fullstabilizer := fs;
	vprint Bianchi,1: "Done.";
    end if;
end procedure;

procedure set_facets(~c)
    //  given cell c, if facetind is already set, do nothing.
    // otherwise, compute and set it.
    if not assigned c`facets then
	c`facets := FacetIndices(c`polytope);
    end if;
end procedure;


function get_neighbor_data(c,pf)
    // given cell record for top cell and list of all perfect forms,
    // return neighbor data.
    D := c`init;
    neighborforms := get_all_neighbors(D, c`perfectform : M := c`Min,
	polytope := c`polytope, modout := false); // list of neighbor perfect
    // forms.
    neighbors := [];
    for N in neighborforms do
	minvecs := minimal_vectors(N);
	Ncell := rec<celldata| Min := minvecs, 
	    perfectform := N,
	    bary := &+[q(v):v in minvecs]>;
	// get mover.
	for A in pf do
	    tf,g := matrix_is_GL_conj(A,N);
	    // g sends pf A to pf N so star(g) sends minimal vectors
	    // of N to minimal vectors of A
	    if tf then
		Ncell`mover := star(g);
		break A;
	    end if;
	end for;
	assert assigned Ncell`mover;
	Append(~neighbors,Ncell);
    end for;
    return neighbors;
end function;

function get_top_cells(D : getstabilizers := true)
    // return the top dimensional cells as records.
    pf,faceind,min := get_perfect_forms(D); // perfect forms up to action of GL
    
    S := [];
    for i in [1..#pf] do
	c := rec<celldata |
	    init := D,
	    polytope := polytope(min[i]),
	    Min := min[i],
	    bary := &+[q(m) : m in min[i]],
	    facets := faceind[i],
	    perfectform := pf[i]
	    >;
	if getstabilizers then 
	    set_stabilizer(~c);
	end if;
	c`neighbors := get_neighbor_data(c,pf);
	
	Append(~S,c);
    end for;
    return S;
end function;

function boundary_of_cell(c)
    // given cell record, return the boundary cells as a sequence of
    // records.
    // only keep the ones that are new up to the stabilizer of the
    // c.
    D := c`init;
    P := c`polytope;
    M := c`Min;
    qM := [q(v) : v in M];
    boundary := [];
    baryboundary := [];
    set_facets(~c);
    FL := c`facets;
    set_stabilizer(~c);
    G := c`stabilizer;
    Nind := [];
    todo := FL;
    while #todo ne 0 do
	vprint Bianchi,2: #todo ,"left to check in boundary of cell.";
	ind := todo[1];
	if Rank(Matrix(D`n,&cat[M[i] : i in ind])) ne D`n then
	    vprint Bianchi,2: "cell is at infinity and so deleted.";
	else
	    Append(~Nind,ind);
	end if;
	for g in G do
	    gs := {Position(qM,g*qM[i]*star(g)) : i in ind};
	    Exclude(~todo,gs);
	end for;
    end while;
    
    for ind in Nind do
	BM := [M[i] : i in ind];
	Append(~boundary,make_cell(D,BM));
    end for;
	    
    vprint Bianchi,2: "Done.";
    return boundary,c;
end function;

function boundary(L)
    // given list of cell records, return a list of cell records for
    // the boundary up to GL
    if #L eq 0 then return [],[]; end if;
    D := L[1]`init;
    todo := L;
    bd := [];
    barybd :=[];
    cell := [];
    while #todo gt 0 do
	vprint Bianchi,2: #todo, "cells left to check.";
	c := todo[1];
	Remove(~todo,1);
	B,c := boundary_of_cell(c);
	Append(~cell,c);
	for b in B do
	    bary := b`bary;
	    isconj := exists(i){ i: i in [1..#barybd] |
		matrix_is_GL_conj(bary,barybd[i]) } ;
	    if not isconj then 
		Append(~bd, b);
		vprint Bianchi,1: #bd, "cells found so far.";
		Append(~barybd, bary);
	    end if;
	end for;
    end while;
    
    return bd,cell;
end function;


function voronoi_cells(D)
    n := D`n;
    total_time := Cputime();
    perfect_time := Cputime();
    face_time := perfect_time;
    aa := get_top_cells(D);
    vprint Bianchi,1: "The CPU time used to compute perfect forms is: ", Cputime(perfect_time), "seconds.";
    vprint Bianchi,1: "Perfect forms found:", #aa;
    vprint Bianchi,1: [c`perfectform : c in aa];
    V := [];
    for i in [1..n^2 - 1] do
	vprint Bianchi,1: "The CPU time used to compute dimension ", (n^2 - i), 
	    "face information  is: ", Cputime(face_time), "seconds. \n\n";
	face_time := Cputime();
	aa,a := boundary(aa);
	Append(~V,a);
	vprint Bianchi,1: "\n\nCell dimension:",n^2 - i;
	vprint Bianchi,1: "------------------";
	if #a ne 0 then
	    if assigned a[1]`facets then 
		vprint Bianchi,1: "Total # facets (with multiplicity):",
		    &+[#c`facets: c in a] ; 
	    end if;
	    vprint Bianchi,1: "Orbits:",#a;
	    if assigned a[1]`stabilizer then  
		vprint Bianchi,1: "Mass:",&+[1/#c`stabilizer : c in a];
		vprint Bianchi,1: "Primes dividing product of stabilizer sizes:",[t[1]: t in Factorization(&*[#c`stabilizer:c in
		    a])];
	    end if;
	end if;	
	
    
    end for;
    masslist := [&+[1/#c`stabilizer :c in S]: S in V[1..n^2 - n + 1]];
    vprint Bianchi,1: "Stabilizer mass list:",masslist;
    vprint Bianchi,1: "Alternating mass sum:",&+[(-1)^i*masslist[i] : i in [1..#masslist]];
    vprint Bianchi,1: "The total CPU time used is: ", Cputime(total_time), "seconds.";
    return Reverse(V);
end function;


function get_edges(p)
    //assumes p is 3 dimensional polytope.
    f:=Facets(p);
    V:=Vertices(p);
    edges:={};
    for face in f do
	e:=Facets(face);
	newedges:={Vertices(a):a in e};
	edges:=edges join newedges;
    end for;
    return {[Position(V,a[1]),Position(V,a[2])]:a in edges};
    
end function;

    
function graph_of_edges(p)
    edges:=get_edges(p);
    G:=Graph<#Vertices(p)|>;
    v:=Vertices(G);
    for e in edges do
	AddEdge(~G,v[e[1]],v[e[2]]);
    end for;
    return G;
end function;

function GLtype(bary,L)
    // given M, barycenter, and list of other barycenters, return
    // the type and mover matrix sending L std to bary.
    for type in [1..#L] do 
	tf, mover := matrix_is_GL_conj(L[type], bary);
	if tf then
	    return type, mover;
	end if;
    end for;
    // if it reaches here, then it is not conjugate to std
    return 0, _;
end function;


function oldcell_to_newcell(F,cell: std := [])
    // convert cell record to be compatible with BianchiCuspForm package
    newcell := rec<CellRec |
	O2_vertices := cell`Min,
	bary := cell`bary
	>;
    
    if assigned cell`neighbors then
	newcell`neighbors := [oldcell_to_newcell(F,a) : a in cell`neighbors];
	neighbors_mover := [];
	for N in cell`neighbors do
	    gamma := N`mover;
	    type := Position(std,gamma * N`bary * star(gamma));
	    assert type ne 0;
	    Append(~neighbors_mover, <type,gamma>);
	end for;
	newcell`neighbors_mover := neighbors_mover;
    end if;
    if assigned cell`polytope  then
	newcell`polytope := cell`polytope;
	newcell`cone_vertices := [Eltseq(a): a in Vertices(newcell`polytope)];
	if Dimension(newcell`polytope) eq 3 then 
	    newcell`graph := graph_of_edges(newcell`polytope);
	end if;
    end if;
    if assigned cell`stabilizer then
	newcell`stabilizer := cell`stabilizer;
	newcell`fullstabilizer := cell`fullstabilizer;
    end if;
    
    if assigned cell`stabilizerplus then
	newcell`stabilizer_plus := cell`stabilizerplus;
    end if;
    
    if assigned cell`perfectform then
	newcell`form := ToBianchiCone(F,cell`perfectform);
    end if;
			
    return newcell;
end function;

forward preserves_orientation;

function set_stabilizer_plus(M, c)
    // given cell c, set the orientation preserving subgroup of the
    // stabilizer of c
    vprint Bianchi,2: "Computing orientation preserving stabilizer for cell.";
    
    if not assigned c`stabilizerplus then 
	L := [ Position(M`ModFrmData`Qstandardorder, ToBianchiCone(BaseField(M),v)) : v in c`Min ];
	assert not 0 in L;
	G := [ g : g in c`fullstabilizer | preserves_orientation(M,L,
	    g) ];
	if #G eq #c`fullstabilizer then
	    GG := c`fullstabilizer;
	else
	    GG := MatrixGroup< 2, BaseField(M) | G>;
	    GG`Order := #c`fullstabilizer div 2;
	end if;
	c`stabilizerplus := GG;
    end if;
    return c;
end function;

forward relative_orientation;
forward standard_simplex_indices;

procedure FindCells(M)
    // M is BianchiCuspForm module.
    // Set data for Voronoi cells.
    // squarefree, negative
    F := M`Field;
    D := initialize(M);
    V := voronoi_cells(D);
    // Need to fix once and for all the standard ordering of vertices.
    standardorder := [];
    Qstandardorder := [];
    for cell in V[3] do 
	for v in cell`Min do 
	    qv := ToBianchiCone(M`Field, v);
	    if not qv in Qstandardorder then
		Append(~standardorder,v);
		Append(~Qstandardorder,qv);
	    end if;
	end for;
    end for;
    ParallelSort(~standardorder, ~Qstandardorder);
    M`ModFrmData`standardorder := standardorder;
    M`ModFrmData`Qstandardorder := Qstandardorder;    
    
    V[1] := [set_stabilizer_plus(M,a) : a in V[1]];
    V[2] := [set_stabilizer_plus(M,a) : a in V[2]];
    M`ModFrmData`three_poly := [ oldcell_to_newcell(F,a:std := [a`bary : a in V[3]]) : a in V[3] ];
    two_poly :=[ oldcell_to_newcell(F,a) : a in V[2] ];
    boundarybary := [a`bary : a in V[1]];

    // boundarybary is a list of the edges barycenters.
    new_two_poly := [];
    for t in [1..#two_poly] do 
	GL_facet_types := [];
	cell := two_poly[t];
	for f in V[2,t]`facets do
	    cellind := [Position(Qstandardorder,  ToBianchiCone(F,v) )
		: v in cell`O2_vertices];
	    bary := &+[q(v) : v in [cell`O2_vertices[k] : k in f]];
	    type, mover := GLtype(bary, boundarybary);
	    if type ne 0 then
		stdind := standard_simplex_indices(M, [Position(Qstandardorder, ToBianchiCone(F,v)) : v in V[1,type]`Min]);
		faceind := [Position(Qstandardorder, ToBianchiCone(F,
		    Eltseq(mover*Matrix(1,standardorder[k])))) : k in stdind ];
		sgn := relative_orientation(M, cellind, faceind);
	    else
		sgn := 0;
	    end if;
	    Append(~GL_facet_types,<type,sgn,mover>);
	end for;
	newcell := cell;
	newcell`GL_facet_types := GL_facet_types;
	Append(~new_two_poly, newcell);
    end for;
    
    M`ModFrmData`two_poly := new_two_poly;
    
    M`ModFrmData`one_poly :=[ oldcell_to_newcell(F,a) : a in V[1]];
    L:=&join{{e*Determinant(Matrix([a,b])):
	a,b in cell`O2_vertices,e in M`ModFrmData`torsion_units}:
	cell in M`ModFrmData`three_poly};
    M`ModFrmData`dets:=L;
    // Need to check if edge vertex order agrees or disagrees with O2_vertices ordering.	
    pos := [];
    for cell in M`ModFrmData`one_poly do 
	posL := [Position(M`ModFrmData`standardorder,v) : v in cell`O2_vertices];
	assert not 0 in posL;
	Append(~pos,posL);
    end for;
    reverse := [i : i in [1..#pos] | pos[i,1] gt pos[i,2]];
    M`ModFrmData`zero_reversers := reverse;
end procedure;


function standard_simplex_indices(M,L)
    // given a list L of indices, return the indices in the
    // standardorder that give the standard simplex (choose from left
    // to right, adding vertices that increase rank.
    Sort(~L);
    Qstandardorder := M`ModFrmData`Qstandardorder;
    ind := [L[1]];
    m := Rank(Matrix([ Qstandardorder[a] : a in L ]));
    counter := 2;
    A := Matrix([ Qstandardorder[a] : a in ind ]);
    n := Rank(A);
    while n lt m do
	while Rank( Matrix([ Qstandardorder[a] : a in ind cat
	    [L[counter]] ])) eq n do 
	    counter := counter + 1;
	end while;
	Append(~ind,L[counter]);
	A := Matrix([ Qstandardorder[a] : a in ind ]);
	n := Rank(A);
    end while;
    return ind;
end function;


function complement(M,L)
    // given indices L, return vectors that span a complement
    // of L
    Qstandardorder := M`ModFrmData`Qstandardorder;
    
    I := IdentityMatrix(Rationals(),#Qstandardorder[1]);
    RI := [Eltseq(a) : a in Rows(I)];
    A := Matrix([ Qstandardorder[i] : i in L]);
    n := Rank(A);
    ind := [];
    m := #Qstandardorder[1];
    counter := 1;    while n lt m do
	if Rank( Matrix([ Qstandardorder[a] : a in L] cat
	    [ RI[i] : i in ind cat [counter] ])) gt n then
	    Append(~ind,counter);
	end if;
	n := Rank( Matrix([ Qstandardorder[a] : a in L] cat
	    [ RI[i] : i in ind cat [counter] ]));
	counter := counter +1;
    end while;
    return [ RI[i] : i in ind ];
end function;


function preserves_orientation(M, L, g)
    // given list of indices, and a g in stabilizer group, return if g preserves
    // the orientation of the cell 
    ssi := standard_simplex_indices(M, L);
    ext := complement(M, ssi);
    Qstandardorder := M`ModFrmData`Qstandardorder;
    standardorder := M`ModFrmData`standardorder;
    
    A1 := Matrix([ Qstandardorder[i] : i in ssi] cat ext);
    newind :=
	[Position(Qstandardorder, ToBianchiCone(M`Field, Eltseq(g*Matrix(1,standardorder[i])))) : i in ssi];
    A2 := Matrix([ Qstandardorder[i] : i in newind] cat ext);
    det := Determinant(A1)*Determinant(A2);

    if det lt 0 then 
	return false;
    else
	assert det gt 0;
	// if it reaches here, then g preserves orientation
	return true;
    end if;
end function;

function relative_orientation(M, cell, face)
    // given list of indices, return relative orientation.
    // note: the face is gotten from the Herbert method of standard
    // simplex.
    // assumes cell is std. assumes face is simplicial and ordered.
    Qstandardorder := M`ModFrmData`Qstandardorder;
    std_cell := standard_simplex_indices(M,cell);
    extra := [Minimum([a : a in std_cell | not a in face])];
    
    ext := complement(M, std_cell);
    A1 := Matrix([ Qstandardorder[i] : i in face cat extra] cat
	ext);
    A2 := Matrix([ Qstandardorder[i] : i in std_cell ] cat ext);
    d := Determinant(A1)*Determinant(A2);
    assert d ne 0;
    s := Sign(d);
    return s;
end function;


