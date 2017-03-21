//getdata.m 5/14/09

freeze;

VERB := false;

import "hecke.m":
    hecke_from_mats,
    hecke_mats,
    TpMatrix,
    Tab_mats,
    Tpp_mats;

import "cohomology.m":
    homologydata;

import "sharbly.m":
    unimodularize;

function is_square(p)
    //returns boolean true if p is a square in the class group. 
    C,f:=ClassGroup(Order(p));
    two:={2*g:g in C};
    return p@@f in two;
end function;


intrinsic NumberOfCusps(M:ModFrmBianchi)->RngIntElt
    {Given space of cusp forms, computes the number of cusps}
    level:=Level(M);
    K:=BaseField(M);
    h:=ClassNumber(K);
    D:=Divisors(level);
    MM:=[d + level*d^(-1):d in D];
    ans:=0;
    for m in MM do 
	R,mu:=quo<Integers(K)|m>;
	U:={mu(a):a in M`ModFrmData`torsion_units};
	Rs,mus:=UnitGroup(R);
	RsU:=quo<Rs|[a@@mus:a in U]>;
	ans:=ans + #RsU;
    end for;
    return h* ans;
end intrinsic;

	
function abmat(a1,a2,b)
    // given a1, a2 in OF and ideal B, find ab matrix.
    OF := Parent(a1);
    a := ideal<OF | a1,a2>;
    tf,g := IsPrincipal(a*b);
    assert tf;
    
    if a1*a2 eq 0 then
	assert b eq 1*OF;
	if a2 eq 0 then 
	    A:= Matrix(OF,2,[a1,0,0,1/a1]);
	else
	    A :=  Matrix(OF,2,[0,a2,-1/a2,0]);
	end if;
    else

	I := a1/g*b;
	J := a2/g*b;
	tf,i,j := Idempotents(I,J);
	assert i + j eq 1;
	// now i + j = 1.
	b2 := g*i/a1;
	b1 := -j*g/a2;
	
	assert ideal<OF | b1, b2> eq b;
	A :=  Matrix(OF,2,[a1,b1,a2,b2]);
    end if;
    assert ideal<OF| Determinant(A)> eq a*b;
    return A;
end function;


forward TaaTpMatrix;


function heckematrixprincipalprime(M,n)
    //Computes Hecke matrix Tn restricted to cuspidal space.  Assumes p is
    //principal, and either prime or the product of two primes.
    
    bool, T := IsDefined(M`Hecke, n);
    if bool then
        return T;
    end if;
    
    // TO DO: when possible, factor n as a product of coprime principal ideals,
    // and call recursively

    b:=M`basis_matrix;
    bi:=M`basis_matrix_inv;
    mats:=hecke_mats(M,n);

if VERB then
printf "#hecke_mats = %o, complexity %o\n", #mats,
Ceiling(Sqrt( &+[&+ [Norm(x) : x in Eltseq(t)] : t in mats] / #mats )); // average L2 norm
//for t in mats do printf "[ %o %o %o %o ]\n", t[1,1], t[1,2], t[2,1], t[2,2]; end for;
end if;

    T:=hecke_from_mats(M,mats,b) * bi;

    M`Hecke[n] := T;
    return T;
end function;

intrinsic HeckeMatrixBianchi(M::ModFrmBianchi,n::RngOrdIdl)->Mtrx
   {Computes Hecke matrix Tn (for n coprime to the level)
    restricted to cuspidal space. Assumes n is principal, and either prime
    or the product of two primes.  Alternatively, if n is prime and is a
    square in the class group, computes T_a,a*Tn for suitable a
    This will return T_n, since T_a,a is trivial on the space we
    are considering.}

    //homologydata(M);
    //d:=Dimension(M);
   
    error if GCD(n, Level(M)) ne 1*Order(n), 
	"The second argument must be an ideal coprime to the level of the space";
    if IsPrincipal(n) then
	T:=heckematrixprincipalprime(M,n);
    elif is_square(n) then
	T:=TaaTpMatrix(M,n);
    else
	error "Hecke matrix not implemented for this type of ideal: "*
              "ideal is not a square in the class group.";
    end if;
    
    return T;
end intrinsic;


intrinsic TppMatrix(M::ModFrmBianchi,p::RngOrdIdl)->Mtrx
    {Computes Hecke matrix Tp,p restricted to cuspidal space.  
    Assumes p is non-principal, and prime with p^2 principal.}
    //if we have computed a hecke matrix for the whole
    //cohomology space, use this instead.

    bool, T := IsDefined(M`Hecke_pp, p);
    if bool then
        return T;
    end if;

    require IsPrincipal(p*p) : 
            "The second argument must square to a principal ideal.";

    b:=M`basis_matrix;
    bi:=M`basis_matrix_inv;
    mats:=Tpp_mats(M,p);

if VERB then
printf "#Tpp_mats = %o, complexity %o\n", #mats,
Ceiling(Sqrt( &+[&+ [Norm(x) : x in Eltseq(t)] : t in mats] / #mats )); // average L2 norm
//for t in mats do printf "[ %o %o %o %o ]\n", t[1,1], t[1,2], t[2,1], t[2,2]; end for;
end if;

    T:=hecke_from_mats(M,mats,b) * bi;
    M`Hecke_pp[p] := T;
    return T;
end intrinsic;

function get_good_a(M,p)
    //Finds an ideal a, prime to the level such that a^2*p is principal.
    //Note: ClassGroup always returns the same map (which is stored).
    
    C,f:=ClassGroup(BaseField(M));
    g:=p@@f;
    bool, a := IsDefined(M`LevelData`good_a,Eltseq(g)); 
    if bool then
        return a;
    end if;
    bound:=100;
    N:=Level(M);
    while true do
	//cand_list := PrimesUpTo(bound, BaseField(M) : coprime_to:=N);
	cand_list := IdealsUpTo(bound, BaseField(M) : CoprimeTo:=N);
	for a in cand_list do
	    if IsId((a*a*p)@@f) then
		return a;
	    end if;
	end for;
	bound:=bound+100;
    end while;
end function;

function TaaTpMatrix(M,p)
    //TaaTpMatrix(M::ModFrmBianchi,p::RngOrdIdl)->Mtrx
    //{Computes Hecke matrix T_a,aT_p restricted to cuspidal space,
    // where a is chosen so that a^2*p is a principal ideal.}
    //This should give the eigenvalues for T_p, I think.  
    //Check Cremona preprint.

    bool, T := IsDefined(M`Hecke_ap, p);
    if bool then
        return T;
    end if;
    
    a:=get_good_a(M,p);
    mats:=Tab_mats(M,a*p,a);

if VERB then
printf "#Tab_mats = %o, complexity %o\n", #mats,
Ceiling(Sqrt( &+[&+ [Norm(x) : x in Eltseq(t)] : t in mats] / #mats )); // average L2 norm
//for t in mats do printf "[ %o %o %o %o ]\n", t[1,1], t[1,2], t[2,1], t[2,2]; end for;
end if;

    b:=M`basis_matrix;
    bi:=M`basis_matrix_inv;
    vprintf Bianchi,3: "matrices are %o.\n", mats;
    T:=hecke_from_mats(M,mats,b) * bi;
    M`Hecke_ap[p] := T;
    return T;
end function;


