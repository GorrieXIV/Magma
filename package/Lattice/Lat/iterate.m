freeze;

// Original code: Bernd Souvignier, Jun 1997
// Modified for packages: Allan Steel, Dec 1997 -- Jan 1998

/*******************************************************************************
			    Group Attributes
*******************************************************************************/

declare attributes GrpMat: Nsforms, Naforms;
declare attributes GrpMat: Sforms, Aforms;
declare attributes GrpMat: Nends, Ncenends;
declare attributes GrpMat: EndomorphismRing, CentreOfEndomorphismRing;

/*******************************************************************************
				Consts, Check
*******************************************************************************/

Iterate := InternalIterate;
IterateForm := InternalIterateForm;

Z := IntegerRing();
Q := RationalField();

function MatrixZ(X)
    return ChangeRing(Parent(X), Z) ! X;
end function;

function SequenceZ(Q)
    return [MatrixZ(X): X in Q];
end function;

RingIsZ := func<G | BaseRing(G) cmpeq Z>;
RingIsQ := func<G | BaseRing(G) cmpeq Q>;
RingIsZQ := func<G | R cmpeq Z or R cmpeq Q where R is BaseRing(G)>;

/*******************************************************************************
				Auxiliary
*******************************************************************************/

//----------

Randhom := function(m, n)	// return a 'random' sparse mxn matrix with
				// m+n entries 1 and the rest 0
    f := RMatrixSpace(Q, m, n) ! 0;
    for k in [1..m+n] do
	    f[Random([1..m])][Random([1..n])] +:= 1;
    end for;
    return f;

end function;

//----------

Randbil := function(n)	// return a 'random' bilinear form with n copies of A_2
			// and n hyperbolic planes
    f := MatrixRing(Q, n) ! 0;
    for k in [1..n] do
	    i := Random([1..n]);
	    j := Random([1..n]);
	    f[i][i] +:= 2;
	    f[j][j] +:= 2;
	    f[i][j] +:= 1;
	    f[j][i] +:= 1;
	    i := Random([1..n]);
	    j := Random([1..n]);
	    f[i][j] +:= 1;
	    f[j][i] -:= 1;
    end for;
    return f;

end function;

/*******************************************************************************
			    Invariant Forms
*******************************************************************************/

Nforms := function(G)	// compute the number of independent invariant forms
			// first return value are symmetric,
			// second anti-symmetric forms

    if assigned G`Nsforms then
	return G`Nsforms, G`Naforms;
    end if;

    p := NextPrime(Degree(G)+2);	// p does not divide |G|
    K := GF(p);
    H := ChangeRing(G, K);
    M := GModule(H);
    CM := ConstituentsWithMultiplicities(M);
    sym := 0;
    anti := 0;
    for T in CM do
	C, m := Explode(T);
	D := Dual(C);
	forms := Basis(GHom(C, D));
	d := Dimension(C);
	M := MatrixRing(K, d);
	syms := Rank(
	    Matrix(
		K, #forms, d^2, &cat[Eltseq(M!f + Transpose(M!f)): f in forms]
	    )
	);
	antis := Rank(
	    Matrix(
		K, #forms, d^2, &cat[Eltseq(M!f - Transpose(M!f)): f in forms]
	    )
	);
	if syms gt 0 and antis eq 0 then
	    // constituent is of orthogonal type
	    sym +:= (m^2+m)/2 * syms;
	    anti +:= (m^2-m)/2 * syms;
	elif syms eq 0 and antis gt 0 then
	    // constituent is of symplectic type
	    sym +:= (m^2-m)/2 * antis;
	    anti +:= (m^2+m)/2 * antis;
	elif syms gt 0 and antis gt 0 then
	    // constituent is of unitary type and selfdual
	    sym +:= m^2 * syms;
	    anti +:= m^2 * antis;
	else
	    // constituent is of unitary type but not selfdual (fixes no form)
	    e := Dimension(EndomorphismRing(C));
	    sym +:= m^2 * e/2;	// other half comes from dual
	    anti +:= m^2 * e/2;
	end if;
    end for;

    G`Nsforms := Z!sym;
    G`Naforms := Z!anti;
    return G`Nsforms, G`Naforms;

end function;

function basis_over(F, K) if #F ge 0 then return F; end if;
//[KSpace(K,e)!RepresentationMatrix(b) : b in Basis(K)];
// d:=Degree(K); e:=Degree(Parent(F[1])) div d;
// B:=&cat[[BlockMatrix(f,1+(i-1)*d,1+(j-1)*d,d,d) : j in [1..e]] : i in [1..e]];
end function;


function Forms(H, sym, anti, any, OverField)
    // for sym, anti:
    // -1 => all
    // 0 => none
    // k > 0 => k

    OverDegree:=Degree(OverField); K:=OverField;
    n := Degree(H);
    M := MatrixRing(Q, n);
    MZ := MatrixRing(Z, n);

    vprint Iterate: "INVARIANT FORMS";
    if sym ge 0 then
	vprintf Iterate: "Number of symmetrics: %o\n", sym;
    end if;
    if anti ge 0 then
	vprintf Iterate: "Number of antisymmetrics: %o\n", anti;
    end if;
    if any ge 0 then
	vprintf Iterate: "Number of either: %o\n", any;
    end if;

    full_sym := sym lt 0;
    full_anti := anti lt 0;

    if sym lt 0 or anti lt 0 then
	true_sym, true_anti := Nforms(H);	// get the dimensions
	if sym lt 0 then
	    sym := true_sym;
	end if;
	if anti lt 0 then
	    anti := true_anti;
	end if;
    end if;

    if any ge 0 then
	L := [MZ|];

	if assigned H`Sforms then
	    L cat:= H`Sforms;
	end if;

	if assigned H`Aforms then
	    L cat:= H`Aforms;
	end if;

	if #L ge any then
	    return L[1 .. any], [MZ|];
	end if;
    else
	if assigned H`Sforms and anti eq 0 then
	    return H`Sforms[1 .. sym], [MZ|];
	end if;

	if assigned H`Aforms and sym eq 0 then
	    return [MZ|], H`Aforms[1 .. anti];
	end if;

	if assigned H`Sforms and assigned H`Aforms then
	    return H`Sforms[1 .. sym], H`Aforms[1 .. anti];
	end if;
    end if;

    G := [ M | h : h in Generators(H) ];
    Append(~G, &*[M | g : g in G ]);
    if OverDegree eq 1 then GT := [ Transpose(g) : g in G ];
    else GT:=[BlockTranspose(g,OverDegree) : g in G]; end if;

    if sym gt 0 then
	f := M!1;
        if OverDegree eq 1 then IterateForm(~G, ~GT, ~f);
	else Iterate(~G, ~GT, ~f, 1); end if;
	F := [ MZ!f ]; /* should now Clean group wrt this form */
        /* But F[1] need not be symmetric if OverDegree is bigger than 1 */
    else
	F := []; U:=Parent(G)!1; UI:=U; GC:=G; GTC:=GT;
    end if;
    S := [];
    while
	any ge 0 select
	    (#F + #S lt any) else
	    (#F lt sym or #S lt anti)
    do
	    f := Randbil(n);
	    // iterate over a form with symmetric and anti-symmetric part
            if OverDegree eq 1 then IterateForm(~G, ~GT, ~f);
	    else Iterate(~G, ~GT, ~f, 1); end if;
	    if any ge 0 or #F lt sym then
		    // symmetric part of invariant form
	            if OverDegree eq 1 then f1 := f + Transpose(f);
		    else f1:=f+BlockTranspose(f,OverDegree); end if;
                     // if space is more than 1-dim, this is insufficient!
		    if IsIndependent(F cat [f1]) then
			    gcd := Gcd([ Z!x : x in Eltseq(f1) ]);
			    f1 := f1/gcd;
			    Append(~F, MZ!f1);
			    vprint Iterate: "Found symmetric form";
		    end if;
	    end if;
	    if any ge 0 or #S lt anti then
		    // anti-symmetric part of invariant form
	            if OverDegree eq 1 then f2 := f - Transpose(f);
		    else f2:=f-BlockTranspose(f,OverDegree); end if;
                     // if space is more than 1-dim, this is insufficient!
		    if IsIndependent(S cat [f2]) then
			    gcd := Gcd([ Z!x : x in Eltseq(f2) ]);
			    f2 := f2/gcd;
			    Append(~S, MZ!f2);
			    vprint Iterate: "Found symplectic form";
		    end if;
	    end if;
    end while;
    if OverDegree gt 1 then S:=basis_over(S,K); F:=basis_over(F,K); end if;
    if full_sym then
	H`Sforms := F;
    end if;
    if full_anti then
	H`Aforms := S;
    end if;
    return F, S;
end function;

intrinsic NumberOfInvariantForms(G::GrpMat) -> []
{The number of invariant (both symmetric and anti-symmetric) forms of G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return s + a where s, a is Nforms(G);
end intrinsic;

intrinsic NumberOfSymmetricForms(G::GrpMat) -> []
{The number of symmetric invariant forms of G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return s where s is Nforms(G);
end intrinsic;

intrinsic NumberOfAntisymmetricForms(G::GrpMat) -> []
{The number of anti-symmetric invariant forms of G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return a where _, a is Nforms(G);
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic InvariantForms(G::GrpMat : OverField:=Rationals()) -> []
{The symmetric and anti-symmetric invariant forms of G
(the first symmetric form is positive definite)}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return S cat A where S, A is Forms(G, -1, -1, -1, OverField);
end intrinsic;

intrinsic SymmetricForms(G::GrpMat : OverField:=Rationals()) -> []
{The symmetric invariant forms of G
(the first symmetric form is positive definite)}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return s where s is Forms(G, -1, 0, -1, OverField);
end intrinsic;

intrinsic AntisymmetricForms(G::GrpMat : OverField:=Rationals()) -> []
{The anti-symmetric invariant forms of G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return a where _, a is Forms(G, 0, -1, -1, OverField);
end intrinsic;

intrinsic InvariantForms(G::GrpMat, n::RngIntElt) -> []
{n invariant forms of G (either symmetric or antisymmetric}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    requirerange n, 0, s + a where s, a is Nforms(G);
    return (S cat A)[1 .. n] where S, A is Forms(G, 0, 0, n, Rationals());
end intrinsic;

intrinsic SymmetricForms(G::GrpMat, n::RngIntElt) -> []
{n symmetric invariant forms of G
(the first symmetric form is positive definite if n is non-zero)}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    requirerange n, 0, Nforms(G);
    return s where s is Forms(G, n, 0, -1, Rationals());
end intrinsic;

intrinsic AntisymmetricForms(G::GrpMat, n::RngIntElt) -> []
{n anti-symmetric invariant forms of G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    requirerange n, 0, a where s, a is Nforms(G);
    return a where _, a is Forms(G, 0, n, -1, Rationals());
end intrinsic;

// Lattice versions

intrinsic NumberOfInvariantForms(L::Lat) -> []
{The number of invariant (both symmetric and anti-symmetric) forms of G}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return NumberOfInvariantForms(Group(L));
end intrinsic;

intrinsic NumberOfSymmetricForms(L::Lat) -> []
{The number of symmetric invariant forms of G}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return NumberOfSymmetricForms(Group(L));
end intrinsic;

intrinsic NumberOfAntisymmetricForms(L::Lat) -> []
{The number of anti-symmetric invariant forms of G}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return NumberOfAntisymmetricForms(Group(L));
end intrinsic;

intrinsic InvariantForms(L::Lat) -> []
{The symmetric and anti-symmetric invariant forms of G
(the first symmetric form is positive definite)}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return InvariantForms(Group(L));
end intrinsic;

intrinsic SymmetricForms(L::Lat) -> []
{The symmetric invariant forms of G
(the first symmetric form is positive definite)}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return SymmetricForms(Group(L));
end intrinsic;

intrinsic AntisymmetricForms(L::Lat) -> []
{The anti-symmetric invariant forms of G}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return AntisymmetricForms(Group(L));
end intrinsic;

intrinsic InvariantForms(L::Lat, n::RngIntElt) -> []
{n invariant forms of G (either symmetric or antisymmetric}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    requirerange n, 0, s + a where s, a is Nforms(Group(L));
    return InvariantForms(Group(L), n);
end intrinsic;

intrinsic SymmetricForms(L::Lat, n::RngIntElt) -> []
{n symmetric invariant forms of G
(the first symmetric form is positive definite if n is non-zero)}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    requirerange n, 0, Nforms(Group(L));
    return SymmetricForms(Group(L), n);
end intrinsic;

intrinsic AntisymmetricForms(L::Lat, n::RngIntElt) -> []
{n anti-symmetric invariant forms of G}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    requirerange n, 0, a where s, a is Nforms(Group(L));
    return AntisymmetricForms(Group(L), n);
end intrinsic;

////////////////////////////////////////////////////////////////////////

 // should just use GHom(M,HermitianDual(M))

/*
intrinsic SymmetricHermitianForms(G::GrpMat) -> []
{The symmetric Hermitian forms of G, for G over an imaginary quadratic field}
 K:=BaseRing(G);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
 "MatrixGroup must be over an imaginary quadratic field"; e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in SymmetricForms(S:OverField:=K)];
 end intrinsic;

intrinsic AntisymmetricHermitianForms(G::GrpMat) -> []
{The alternating Hermitian forms of G, for G over an imaginary quadratic field}
 K:=BaseRing(G);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
 "MatrixGroup must be over an imaginary quadratic field"; e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in AntisymmetricForms(S:OverField:=K)];
 end intrinsic;

intrinsic InvariantHermitianForms(G::GrpMat) -> []
{The invariant Hermitian forms of G, for G over an imaginary quadratic field}
 K:=BaseRing(G);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
 "MatrixGroup must be over an imaginary quadratic field"; e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in InvariantForms(S:OverField:=K)];
 end intrinsic;
*/

intrinsic SymmetricQuaternionicForms(G::GrpMat) -> []
{The symmetric quaternionic forms of G, for G over a quaternion algebra over Q}
 K:=BaseRing(G);
 require ISA(Type(K),AlgQuat): "Group must be over a quaternion algebra";
 require BaseRing(K) eq Rationals(): "Center of quaternions must be rationals";
 e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in SymmetricForms(S:OverField:=K)];
 end intrinsic;

intrinsic AntisymmetricQuaternionicForms(G::GrpMat) -> []
{The alternating quaternionic forms of G over a quaternion algebra over Q}
 K:=BaseRing(G);
 require ISA(Type(K),AlgQuat): "Group must be over a quaternion algebra";
 require BaseRing(K) eq Rationals(): "Center of quaternions must be rationals";
 e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in AntisymmetricForms(S:OverField:=K)];
 end intrinsic;

intrinsic InvariantQuaternionicForms(G::GrpMat) -> []
{The invariant quaternionic forms of G over a quaternion algebra over Q}
 K:=BaseRing(G);
 require ISA(Type(K),AlgQuat): "Group must be over a quaternion algebra";
 require BaseRing(K) eq Rationals(): "Center of quaternions must be rationals";
 e:=Degree(K);
 S:=sub<GL(e*Degree(G),Q)|[RepresentationMatrix(g) : g in Generators(G)]>;
 return [WriteOver(s,BaseRing(G)) : s in InvariantForms(S:OverField:=K)];
 end intrinsic;

/*******************************************************************************
				Bravais
*******************************************************************************/

intrinsic BravaisGroup(G::GrpMat[RngInt]) -> GrpMat
{The Bravais group of G}
    S := SequenceZ(SymmetricForms(G));
    B :=  AutomorphismGroup(LatticeWithGram(S[1]), S[2 .. #S]:
	Generators := [G.i:i in [1..Ngens(G)]]);
    return B;
end intrinsic;

/*******************************************************************************
			    Endomorphisms
*******************************************************************************/

//----------

Nends := function( G )	// compute the dimension of the endomorphism ring of G
    if assigned G`Nends then
	return G`Nends;
    end if;

    p := NextPrime(Degree(G)+2);	// p does not divide |G|
    H := ChangeRing( G, GF(p) );
    M := GModule(H);
    CM := ConstituentsWithMultiplicities(M);
    ends := 0;
    for C in CM do
	    e := Dimension(EndomorphismAlgebra(C[1]));
	    ends +:= C[2]^2 * e;
    end for;
    G`Nends := ends;
    return ends;

end function;

//----------

intrinsic Endomorphisms(G::GrpMat, N::RngIntElt) -> []
{N independent endomorphisms from
the endomorphism ring of the integral/rational matrix group G}

    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    requirerange N, 1, Nends(G);

    n := Degree(G);
    M := MatrixRing(BaseRing(G), n);
    p := NextPrime(n^2);
    Mp := MatrixRing(GF(p), n);
    G := [ M|h : h in Generators(G) ];
    Append(~G, &*[M| g : g in G ]);
    GI := [ g^-1 : g in G ];
    C := [ M!1 ];
    Cp := [ Mp!1 ];
    while #C lt N do
	    c := M!Randhom(n, n);
    // iterate over a random (sparse) nxn matrix
	    Iterate(~G, ~GI, ~c, 1);
    // check linear dependency modulo a reasonably large prime
	    if IsIndependent(Cp cat [Mp!c]) then
		    Append(~C, c);
		    Append(~Cp, Mp!c);
		    vprint Iterate: "Found endomorphism";//:", c;
		    cand := #C;
		    // form the algebra closure
		    while cand le #C and #C lt N do
			    nC := #C;
			    for i in [nC..2 by -1] do
				    cp := Cp[i] * Cp[cand];
				    if IsIndependent(Cp cat [cp]) then
					    Append(~C, C[i] * C[cand]);
					    Append(~Cp, cp);
					    vprint Iterate: "Found independent product";
					    if #C ge N then
						    break i;
					    end if;
				    end if;
				    cp := Cp[cand] * Cp[i];
				    if IsIndependent(Cp cat [cp]) then
					    Append(~C, C[cand] * C[i]);
					    Append(~Cp, cp);
					    vprint Iterate: "Found independent product";
					    if #C ge N then
						    break i;
					    end if;
				    end if;
			    end for;
			    cand +:= 1;
		    end while;
	    end if;
    end while;
    return C;

end intrinsic;

intrinsic EndomorphismRing(G::GrpMat) -> AlgMat
{The endomorphism ring of the integral/rational matrix group G}

return EndomorphismRing(GModule(G));

    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    if not assigned G`EndomorphismRing then
	n := Degree(G);
	M := MatrixRing(Q, n);
	G`EndomorphismRing := sub<M| Endomorphisms(G, Nends(G))>;
    end if;
    return G`EndomorphismRing;
end intrinsic;

intrinsic DimensionOfEndomorphismRing(G::GrpMat) -> AlgMat
{The dimension of the endomorphism ring of the integral/rational matrix
group G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return Nends(G);
end intrinsic;

// Lattice versions

intrinsic Endomorphisms(L::Lat, N::RngIntElt) -> []
{N independent endomorphisms from
the endomorphism ring of the G-lattice L}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    requirerange N, 1, Nends(Group(L));
    return Endomorphisms(Group(L), N);
end intrinsic;

intrinsic EndomorphismRing(L::Lat) -> AlgMat
{The endomorphism ring of the G-lattice L}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return EndomorphismRing(Group(L));
end intrinsic;

intrinsic DimensionOfEndomorphismRing(L::Lat) -> AlgMat
{The dimension of the endomorphism ring of the G-lattice L}
    G := Group(L);
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return DimensionOfEndomorphismRing(Group(L));
end intrinsic;

/*******************************************************************************
			    Central Endomorphisms
*******************************************************************************/

Ncenends := function( G )	// compute the dimension of the centre of the
				// endomorphism ring of G
    if assigned G`Ncenends then
	return G`Ncenends;
    end if;

    p := NextPrime(Degree(G)+2);	// p does not divide |G|
    H := ChangeRing( G, GF(p) );
    M := GModule(H);
    CM := Constituents(M);
    cenends := 0;
    for C in CM do
	    c := Dimension(Centre(EndomorphismAlgebra(C)));
	    cenends +:= c;
    end for;
    G`Ncenends := cenends;
    return cenends;

end function;


intrinsic CentralEndomorphisms(G::GrpMat, N::RngIntElt) -> []
{N independent central endomorphisms from
the endomorphism ring of the integral/rational matrix group G}

    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    requirerange N, 1, Ncenends(G);

    n := Degree(G);
    M := MatrixRing(BaseRing(G), n);
    p := NextPrime(n^2);

    Mp := MatrixRing(GF(p), n);
    G := [ M|h : h in Generators(G) ];
    Append(~G, &*[M| g : g in G ]);
    GI := [ g^-1 : g in G ];
    C := [ M!1 ];
    Cp := [ Mp!1 ];
    while #C lt N do
    // the centre of the endomorphism ring is the image of the representation of the
    // group ring under the averaging operator
	    c := &+[ g : g in G ];
    // iterate over the sum of the current generators
	    Iterate(~G, ~GI, ~c, 5);
    // check linear dependency modulo a reasonably large prime
	    if IsIndependent(Cp cat [Mp!c]) then
		    Append(~C, c);
		    Append(~Cp, Mp!c);
		    vprint Iterate: "Found central endomorphism";
		    cand := #C;
		    // form the algebra closure
		    while cand le #C and #C lt N do
			    nC := #C;
			    for i in [nC..2 by -1] do
				    cp := Cp[i] * Cp[cand];
				    if IsIndependent(Cp cat [cp]) then
					    Append(~C, C[i] * C[cand]);
					    Append(~Cp, cp);
					    vprint Iterate: "Found independent product";
					    if #C eq N then
						    break i;
					    end if;
				    end if;
				    cp := Cp[cand] * Cp[i];
				    if IsIndependent(Cp cat [cp]) then
					    Append(~C, C[cand] * C[i]);
					    Append(~Cp, cp);
					    vprint Iterate: "Found independent product";
					    if #C eq N then
						    break i;
					    end if;
				    end if;
			    end for;
			    cand +:= 1;
		    end while;
	    end if;
    end while;
    return C;

end intrinsic;

intrinsic CentreOfEndomorphismRing(G::GrpMat) -> AlgMat
{The centre of the endomorphism ring of the integral/rational matrix group G}

return CentreOfEndomorphismRing(GModule(G));

    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    if not assigned G`CentreOfEndomorphismRing then
	n := Degree(G);
	M := MatrixRing(Q, n);
	G`CentreOfEndomorphismRing :=
	    sub<M|CentralEndomorphisms(G, Ncenends(G))>;
    end if;
    return G`CentreOfEndomorphismRing;
end intrinsic;

intrinsic DimensionOfCentreOfEndomorphismRing(G::GrpMat) -> AlgMat
{The dimension of the centre of the endomorphism ring of the integral/rational
matrix group G}
    require RingIsZQ(G): "Base ring of argument 1 must be Z or Q";
    return Ncenends(G);
end intrinsic;

// Lattice versions

intrinsic CentralEndomorphisms(L::Lat, N::RngIntElt) -> []
{N independent central endomorphisms from the endomorphism ring of
the G-lattice L}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    requirerange N, 1, Ncenends(Group(L));
    return CentralEndomorphisms(Group(L), N);
end intrinsic;

intrinsic CentreOfEndomorphismRing(L::Lat) -> AlgMat
{The centre of the endomorphism ring of the G-lattice L}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return CentreOfEndomorphismRing(Group(L));
end intrinsic;

intrinsic DimensionOfCentreOfEndomorphismRing(L::Lat) -> AlgMat
{The dimension of the centre of the endomorphism ring of the G-lattice L}
    require IsGLattice(L): "Argument 1 must be a G-lattice";
    return DimensionOfCentreOfEndomorphismRing(Group(L));
end intrinsic;

/*******************************************************************************
			    Homomorphisms
*******************************************************************************/

Nhoms := function( G1, G2 )	// compute the number of independent 
				// homomorphism from G1 to G2
    p := NextPrime( Max(Degree(G1), Degree(G2)) + 2 );// p does not divide
							// |G1| or |G2|
    H1 := ChangeRing( G1, GF(p) );
    H2 := ChangeRing( G2, GF(p) );
    M1 := GModule(H1);
    M2 := GModule(H2);
    CM1 := ConstituentsWithMultiplicities(M1);
    CM2 := ConstituentsWithMultiplicities(M2);
    homs := 0;
    for C1 in CM1 do
	    for C2 in CM2 do
		    if IsIsomorphic(C1[1], C2[1]) then
			    e := Dimension(EndomorphismAlgebra(C1[1]));
			    homs +:= C1[2]*C2[2] * e;
			    break C2;
		    end if;
	    end for;
    end for;
    return homs;

end function;

intrinsic Homomorphism(G1::GrpMat, G2::GrpMat) -> ModMatRngElt
{A non-trivial homomorphism from G1 to G2, or zero if one does not exist}
						// H1 to H2
    require RingIsZQ(G1): "Base ring of argument 1 must be Z or Q";
    require RingIsZQ(G2): "Base ring of argument 2 must be Z or Q";
    require Ngens(G1) eq Ngens(G2):
	"Arguments must have equal numbers of generators";
    H1 := G1;
    H2 := G2;
    N := Nhoms(H1, H2);	// check whether there is a homomorphism at all
    n1 := Degree(H1);
    n2 := Degree(H2);
    H := RMatrixSpace(Q, n1, n2);
    if N eq 0 then
	    return H!0;
    end if;
    M1 := MatrixRing(Q, n1);
    G := [ M1!(H1.i) : i in [1..Ngens(H1)] ];
    Append(~G, &*[M1| g : g in G ]);
    M2 := MatrixRing(Q, n2);
    GI := [ M2!(H2.i^-1) : i in [1..Ngens(H2)] ];
    Append(~GI, &*[M1| g : g in Reverse(GI) ]);
    found := false;
    while not found do
	    h := H!Randhom(n1, n2);
	    Iterate(~G, ~GI, ~h, 1);
	    if not IsZero(h) then
		    found := true;
	    end if;
    end while;
    return h;

end intrinsic;

intrinsic DimensionOfHom(G1::GrpMat, G2::GrpMat) -> RngIntElt
{The dimension of the homomorphism module Hom(G1, G2)};
    require RingIsZQ(G1): "Base ring of argument 1 must be Z or Q";
    require RingIsZQ(G2): "Base ring of argument 2 must be Z or Q";
    require Ngens(G1) eq Ngens(G2):
	"Arguments must have equal numbers of generators";
    return Nhoms(G1, G2);
end intrinsic;
