//setup.m for Bianchi groups, Assumes F is entered as NumberField

freeze;

import "defs.m":ModFrmDataRec;

import "sharbly.m":unimodularize;

MaximalOrder := Integers; // faster calling sequence

// These should really be functions, not intrinsics
// (Don't document them!)

intrinsic PrincipalPrimesUpTo(N::RngIntElt,F::FldAlg:coprime_to:=1)->[]
    {A sequence containing the principal prime ideals in the number
    field F with norm less than or equal to N}
    L:=PrimesUpTo(N,F:coprime_to:=coprime_to);
    return [a:a in L|IsPrincipal(a)];
end intrinsic;

intrinsic NonPrincipalPrimesUpTo(N::RngIntElt,F::FldAlg:coprime_to:=1)->[]
    {A sequence containing the non-principal prime ideals in the
    number field F with norm less than or equal to N}
    L:=PrimesUpTo(N,F:coprime_to:=coprime_to);
    return [a:a in L|not IsPrincipal(a)];
end intrinsic;

intrinsic SPrimesUpTo(n::RngIntElt,F::FldNum:coprime_to:=1)->[]
    {Returns the primes up to norm n that are square in the class group.}
    primes:=PrimesUpTo(n,F:coprime_to:=coprime_to);
    C,f:=ClassGroup(F);
    two := 2*C;
    return [p:p in primes|p@@f in two];
end intrinsic;

procedure SetConeSpace(M)
    //sets cone_space as inner product space and cone_lattice as
    //lattice with inner product
    F:=BaseField(M);
    O:=MaximalOrder(F);
    E:=[];
    E[1]:=Matrix(O,2,[1,0,0,0]);
    
    E[2]:=Matrix(O,2,[0,O.1,F`Conjugate(O.1),0]);
    E[3]:=Matrix(O,2,[0,O.2,F`Conjugate(O.2),0]);
    E[4]:=Matrix(O,2,[0,0,0,1]);
    Q:=ZeroMatrix(RationalField(),4,4);
    for i, j in [1..#E] do 
	Q[i,j]:=RationalField()!(Trace(Trace(E[i]*E[j]))/2);
    end for;
    M`ModFrmData`cone_lattice:=
	LatticeWithBasis(IdentityMatrix(RationalField(),#E),Q);
    M`ModFrmData`cone_space:=VectorSpace(RationalField(),#E,Q);
end procedure;

intrinsic ToBianchiCone(F::FldNum,A::Mtrx)->[]
    {Given F and a Hermitian matrix A, returns the vector in cone_space}
    
    O:=Integers(F);
    B:=BasisMatrix(O);
    a:=A[1,1];
    b:=Vector(Eltseq(F!A[1,2]))*B^(-1);
    c:=A[2,2];
    return [RationalField()|a,b[1],b[2],c];
end intrinsic;

intrinsic ToBianchiCone(F::FldNum,v::[])->[]
    {Given F and a pair in F^2, returns the vector in cone_space}
    return ToBianchiCone(F,Vector(v));
end intrinsic;

intrinsic ToBianchiCone(F::FldNum,v::ModTupRngElt)->[]
    {Given F and vector in F^2, returns the vector in cone_space}

    O:=Integers(F);
    B:=BasisMatrix(O);
    a:=v[1]*F`Conjugate(v[1]);
    c:=v[2]*F`Conjugate(v[2]);
    b:=Vector(Eltseq(F!(v[1]*F`Conjugate(v[2]))) )*B^(-1);
    return [RationalField()|a,b[1],b[2],c];
end intrinsic;

procedure SetTorsionUnits(M)
    //Sets torsion units of BaseField(M)}
    G,f:=TorsionUnitGroup(BaseField(M));
    tor:=[f(g):g in G ];
    M`ModFrmData`torsion_units:=tor;
end procedure;

procedure SetInG(M)
    F:=BaseField(M);
    G:=M`ModFrmData`G;
    O:=MaximalOrder(F);
    M2O := MatrixRing(O,2);
    if G eq "GL" then
        function f(A);
	    tf:=IsCoercible(M2O, A) and Norm(Determinant(A)) eq 1;
            return tf;
        end function;
    elif G eq "SL" then
        function f(A)
	    tf:=IsCoercible(M2O, A) and Determinant(A) eq 1;
            return tf;
        end function;
    end if;
    M`ModFrmData`in_G:=f;
end procedure;


function getidealreps(M)
    F := BaseField(M);
    OF := Integers(F);
    C,f := ClassGroup(F);
    Js := [];
    for g in C do
	Append(~Js, CoprimeRepresentative(f(g),Level(M)) * f(g));
    end for;
    return Js;
end function;

procedure Preset(M)
    //Given M, precomputes the data needed for Voronoi cone
    F:=BaseField(M);
    F`Conjugate:=Automorphisms(F)[2];
    M`ModFrmData`ideal_reps := getidealreps(M);
    if not assigned M`ModFrmData`in_G then 
	SetInG(M);
    end if;
    
    if not assigned M`ModFrmData`cone_space then 
	SetConeSpace(M);
	O:=MaximalOrder(BaseField(M));
	e:=[Vector([a,0]): a in Basis(O)] cat [Vector([0,a]): a in Basis(O)] ;
	M`ModFrmData`O2_in_cone_space:=[ToBianchiCone(F,a):a in e];
	M`ModFrmData`O2_in_cone_space_ij:=[[ToBianchiCone(F,e[i]+e[j]):j in [1..4]]:i in [1..4]];
    end if;
    
    if not assigned M`ModFrmData`torsion_units then 
	SetTorsionUnits(M);
    end if;
end procedure;

/*

function act_on_cone(M, g, x)
    //Given gamma and cone vector x returns gamma acting on x
    F:=BaseField(M);
    O:=MaximalOrder(F);
    conj:=F`Conjugate;
    gg := Eltseq(g);
    //gstar := Transpose(Matrix(F, 2, [ Trace(x) - x : x in gg ]));
    gstar := Transpose(Matrix(F, 2, [ conj(x) : x in gg ]));
    B:=Basis(O);
    beta:=x[2]*B[1]+x[3]*B[2];
    mat:=Matrix(F,2,[x[1], beta, conj(beta), x[4]]);
    h:=g*mat*gstar;
    BM:=BasisMatrix(O);
    a:=h[1,1];
    b:=Vector(Eltseq(F!h[1,2]))*BM^(-1);
    c:=h[2,2];
    return [RationalField()|a,b[1],b[2],c];
end function;

function cone_mat(M,A)
    I:=IdentityMatrix(RationalField(),4);
    L:=[];
    for i in [1..4] do
	Append(~L,act_on_cone(M,A,I[i]));
    end for;
    return Transpose(Matrix(L));
end function;

*/

