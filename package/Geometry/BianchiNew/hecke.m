freeze;

import "sharbly.m":
    star,
    act_on_sharbly,
    FullReduce;
import "setlevel.m":
    brm;

import "compute.m": GLtype, q;

MaximalOrder := Integers; // faster calling sequence


function get_small_elt(q)
    //given an ideal q, returns a small nonzero element of q
    return Basis(LLL(q))[1];
end function;

function get_x(O,z,a)
    vprintf Bianchi,3:"get_x";
    L:=StandardLattice(2);
    r:=1;
    aB:=Basis(a);
    found_x:=false;
    while true do
	P:=ShortVectorsProcess(L,r,r);
	v,n:=NextVector(P);
	while n ne -1 do
	    x:=v[1]*aB[1]+v[2]*aB[2];
	    if a eq ideal<O|z> + ideal<O|x> then 
		found_x:=true;
		return x;
	    end if;
	    v,n:=NextVector(P);
	end while;
	r:=r+1;
    end while;
end function;


function Mab(M,a,b)
    //Given ideals a,b returns Mab from Lingham Lemma 1.2.5
    tf,mu:=IsPrincipal(a*b);
    assert tf;
    F:=BaseField(M);
    O:=MaximalOrder(F);
    z:=get_small_elt(Level(M) meet a);
    x:=get_x(O,z,a);
    I:=x/mu*b;
    J:=z/mu*b;
    _,i,j:=Idempotents(I,J);
    r:=i*mu/x;
    s:=j*mu/z;
    M:=Matrix(O,2,[x,-s,z,r]);
    assert ideal<O|r>+ideal<O|s> eq b;
    assert Determinant(M) eq mu;
    
    vprintf Bianchi,3:"Mab = %o.\n",M;
    return M; 
end function;

function get_d(O,c,d0,q);
    d:=d0;
    //Need to deal with the fact that d and c are not coprime
    //change d by adding elements of q
    B:=Basis(q);
    Lt:=StandardLattice(2);
    r:=1;
    found_d:=GCD(ideal<O|d>,ideal<O|c>) eq 1*O;
    while true do
	P:=ShortVectorsProcess(Lt,r,r);
	v,n:=NextVector(P);
	while n ne -1 do
	    d:=d0-v[1]*B[1]-v[2]*B[2];;
	    if GCD(ideal<O|d>,ideal<O|c>) eq 1*O then
		return d;
	    end if;
	    v,n:=NextVector(P);
	end while;
	r:=r+1;
    end while;
end function;

function std_mats(M,q)
    //find a list of g with bottom row that reduces mod q to give reps of P1
    //and bottom left lies in Gamma0(level);
    O:=MaximalOrder(BaseField(M));
    if q eq 1*O then return [Matrix(O,2,[1,0,0,1])]; end if;
    proj:=[v: v in ProjectiveLine(quo<O|q>)|v[1] ne 0];
    L:=[Matrix(O,2,[1,0,0,1])];
    for v in proj do
	c:=CRT(q,Level(M),O!v[1],O!0);
	d0:=v[2];
	d:=get_d(O,c,d0,q);
	_,i,j:=Idempotents(ideal<O|d>,ideal<O|c>);
	//i in d and j in c so that i+j = 1;
	a:=i/d;
	b:=-j/c;
	Append(~L,Matrix(O,2,[a,b,c,d]));
    end for;
    return L;
end function;

function Tp_mats(M,p);
    F:=BaseField(M);
    O:=MaximalOrder(F);
    _,beta:=IsPrincipal(p);
    R,mu:=ResidueClassField(p);
    return [Matrix(O,2,[beta,0,0,1])] cat
	[Matrix(O,2,[1,alpha@@mu,0,beta]):alpha in R];
end function;

function get_uv(level,beta)
    //gets u and v for proposition 199 in Bygott
    //Specifically, solves u*beta + v
    u:=InverseMod(beta,level);
    v:=1-u*beta;
    return u,v;
end function;

function Tp_squared_mats(M,p);
    //ideal ell=(beta) is p^2
    //p is non-principal prime with p^2 principal.
    F:=BaseField(M);
    O:=MaximalOrder(F);
    ell:=p*p;
    is_principal,beta:=IsPrincipal(ell);
    assert is_principal;
    u,v:=get_uv(Level(M),beta);
    R,mu:=quo<O|ell>;
    rF:={mu(a*O.1+b*O.2): a, b in [0..Norm(ell)]};
    //This should be the sequence of all the elements of R;
    assert #rF eq #R;
    L:=[Matrix([[O|beta, 0],[O|0,1]])] cat
	[Matrix([[O|1,a@@mu],[O|0,beta]]):a in rF] cat
	[Matrix([[O|beta,0],[O|v*alpha,1]]): a in rF|
	not alpha in ell and alpha in p where alpha:=a@@mu] cat 
	[Mab(M,p,p)];
    return L;
end function;

function Tpp_mats(M,ell)
    //T_p,p
    return [Mab(M,ell,ell)];
end function;

function Tab_mats(M,a,b);
    //returns part of a Hecke operator.  Used in Tm_mats.
    m:=Mab(M,a,b);
    return [m*V:V in std_mats(M,a div b)];
end function;

function Tm_mats(M,m)
    //Hecke operator for T_m, where m is composite and prncipal.
    //Probably faster to use Bygott when it Bygott applies since
    //nice matrices are chosen.
    //CHECK TIME
    L:=&cat [Tab_mats(M,a,b): a in Divisors(m)|
	b in Divisors(a) where b:=m div a];
    return L;
end function;


function Tpq_mats(M,p,q)
    //T_pq, assumes p*q is principal
    ell:=p*q;
    tf,beta:=IsPrincipal(ell);
    assert tf;
    F:=BaseField(M);
    O:=MaximalOrder(F);
    u,v:=get_uv(Level(M),beta);
    R,mu:=quo<O|ell>;
    //This should be the sequence of elements of R;
    rF:={mu(a*O.1+b*O.2): a, b in [0..Norm(ell)]};
    assert #rF eq #R;
    
    L:=[Matrix([[O|beta, 0],[O|0,1]])] cat
	[Matrix([[O|1,a@@mu],[O|0,beta]]):a in rF] cat
	[Matrix([[O|beta,0],[O|v*alpha,1]]):
	a in rF|not alpha in q and alpha in p where alpha:=a@@mu] cat 
	[Matrix([[O|beta,0],[O|v*alpha,1]]):
	a in rF|not alpha in p and alpha in q where alpha:=a@@mu] cat 
	[Mab(M,p,q),Mab(M,q,p)];
    return L;
end function;

function homology_to_sharbly(M,hvec)
    //given M (assumes everything is already computed), returns a list
    //of 0-sharblies corresponding to the nth basis vector of the homology;
    H:=M`LevelData`homology`H;
    ToH:=M`LevelData`homology`ToH;
    
    v:=(H!hvec)@@ToH;
    orbits:=M`LevelData`one_orbits;
    gammalist:=&cat[a`gamma_list:a in orbits];
    gltype:=&cat[[i:j in [1..orbits[i]`total_number]]:i in [1 .. #orbits]];
    //onepoly:=M`ModFrmData`one_poly;
    supp:=Support(v);
    osupp:=[<gltype[i], gammalist[i], v[i]>: i in supp];
    tot_sharbly:=[];
    std:= M`ModFrmData`standard_sharblies;
    for L in osupp do
	s:=std[L[1]];
	gs:=act_on_sharbly(M,L[2],s);
	//fix coeff to be v[i].
	gs`coefficient:=L[3];
	Append(~tot_sharbly,gs);
    end for;
    return tot_sharbly;
end function;

function sharbly_to_homology(M,S)
    //Given a list of sharblies, returns the image in H_1
    //Assumes all of the sharblies involved are reduced.
    vprint Bianchi,3:"Converting 0-sharblies to homology class."; 
    ToH:=M`LevelData`homology`ToH;
    V:=M`LevelData`homology`zero_sharbly_space;
    v:=Zero(V);
    barylist := [a`bary : a in M`ModFrmData`one_poly];
    for s in S do
	
	GL_type:=s`GL_type;
	std:=M`ModFrmData`standard_sharblies[GL_type];
	orbits:=M`LevelData`one_orbits[GL_type];
	//FIXME  	
	type, gamma := GLtype(s`bary, barylist);
	//L:=GLtype(M,[M`ModFrmData`standard_sharblies[GL_type]`O2_vertices],
	//    s`O2_vertices,s`vertices);
	//if this is slow, we can try to record it later.
	//gamma:=L[3];
	//The sign of gamma acting on cell.
	//i.e. is gamma * std equal to or opposite from s;
	// sgn:=L[2];
	if type ne 0 then
	    L := [gamma*q(v)*star(gamma) : v in std`O2_vertices];
	    pos := [Position(L,a) : a in [q(v) : v in s`O2_vertices]];
	    assert not 0 in pos;
	    if pos eq [1,2] then
		sgn := 1;
	    else
		sgn := -1;
	    end if;
	    ind:=brm(M,gamma);
	    Gamma0type:=orbits`orbit_type[ind];
	    sgno:=orbits`orbit_number_list[ind];
	    coeff:=s`coefficient*sgn*sgno;
	    //Use GLtype and Gamma0type to get correct entry
	    i:=orbits`entry[Gamma0type];
	    v[i]:=v[i] + coeff;
	end if;
    end for;
    vprintf Bianchi,4:"v which is to be sent to H is %o.\n",v;
    return ToH(v);
end function;

function HeckeOnVector(M,mats,v)
    //Returns the hecke vector associated to T_ell acting on vector
    //of H_1 of M`LevelData.  Assumes everything is already computed,
    //assumes ell is either principal prime, or (pq) principal, or
    //type is p,p
    //F:=BaseField(M);
    //H:=M`LevelData`homology`H;
    ss:=homology_to_sharbly(M,v);
//printf "%o : ", #ss;
    Tss:=[act_on_sharbly(M,g,s):s in ss,g in mats];
//printf "%o ", #Tss;
//time
    S:=&cat[FullReduce(M,s):s in Tss];
    S:=[s:s in S|s`GL_type ne 0];
    return sharbly_to_homology(M,S);
end function;

function TpOnVector(M,ell,v)
    //Returns the hecke vector associated to T_ell acting on vector
    //of H_1 of M`LevelData. Assumes everything is already computed,
    //assumes ell is principal prime.
    Tpmats:=Tp_mats(M,ell);
    return HeckeOnVector(M,Tpmats,v);
end function;


function hecke_from_mats(M,mats,b)
    //returns the hecke matrix acting on the rows of b, where
    //the Hecke operator is defined by mats
    L:=[];
    ker := VectorSpaceWithBasis(b);
    for i in [1..NumberOfRows(b)] do
	vprintf Bianchi,1: "Computing row %o of %o.\n",i,NumberOfRows(b);
	new_row_vector:=HeckeOnVector(M,mats,b[i]);
	assert Vector(new_row_vector) in ker;
	Append(~L,new_row_vector);
    end for;
    return Matrix(L);
end function;

function hecke_mats(M,n)
    //Factor n.  Return the set of matrices used to compute T_n.
    //Assumes n is principal.
    fact:=Factorization(n);
    powers:=[a[2]:a in fact];
	
    if powers eq [1] then
	mats:=Tp_mats(M,n);
    elif powers eq [2] then 
	mats:=Tp_squared_mats(M,fact[1,1]);
    elif powers eq [1,1] then
	mats:=Tpq_mats(M,fact[1,1],fact[2,1]);
    else
	mats:=Tm_mats(M,n);
    end if;
    return mats;
end function;

function TpMatrix(M,p)
    //Returns the hecke matrix associated to ideal ell acting on H_0
    //of M`LevelData.  Assumes everything is already computed,
    H:=M`LevelData`homology`H;
    mats:=hecke_mats(M,p);
    b:=BasisMatrix(H);
    T:=hecke_from_mats(M,mats,b);
    M`EHecke[p] := T;
    return T;
end function;


