/*
Computation of Primary Invariants.
Gregor Kemper <Gregor.Kemper@IWR.Uni-Heidelberg.De>
November 1996.
*/

freeze;

function poly_ring(R, n, S)
    /*
    if Type(S) eq RngInvarOld then
	return OPolynomialRing(R, n);
    else
	return PolynomialRing(R, n);
    end if;
    */
    return PolynomialRing(R, n);
end function;

function poly_ring1(R, n, s, S)
    /*
    if Type(S) eq RngInvarOld then
	return OPolynomialRing(R, n, s);
    else
	return PolynomialRing(R, n, s);
    end if;
    */
    return PolynomialRing(R, n, s);
end function;

function choose(S,k)
   if k eq 0 then
      return {{}};
   else
      return &join{{s join {x}: s in choose(S diff {x},k-1)}: x in S};
   end if;  
end function;

function mysum(Q)
    if #Q le 2 then
	return &+Q;
    end if;
    n := #Q div 2;
    return mysum(Q[1 .. n]) + mysum(Q[n + 1 .. #Q]);
end function;

function SelectBasis(M,I, invar)
// Select a subsequence of M which is linearly independent mod the ideal I
    local i,P,Pg,Ig,T,TP,f,g,eqn,V,W,Ws,v,res;
    
    if #M eq 0 then return M; end if;
    P:=Parent(M[1]);
    Pg:=poly_ring1(CoefficientRing(P),Rank(P),"grevlex", invar);
    g:=hom<P -> Pg | [Pg.i: i in [1..Rank(P)]]>;
    Ig:=ideal<Pg | [g(i): i in Basis(I)]>;
    T:=poly_ring(CoefficientRing(Pg),#M, invar);
    TP:=poly_ring(T,Rank(P), invar);
    f:=hom<Pg -> TP | [TP.i: i in [1..Rank(P)]]>;
//"#M:", #M;
    if 1 eq 1 then
	L1 := [g(M[i]): i in [1..#M]];
	L2 := GroebnerBasis(Ig);
	NF := NormalForm(L1, L2);
	if 0 eq 1 then
	    "OLD NF"; time
	    NF2 := [NormalForm(L1[i], Ig): i in [1..#M]];
	    if NF ne NF2 then
		    G := Generic(Universe(L1));
		    AssignNames(~G, [Sprintf("x%o", i): i in [1..Rank(G)]]);
		"L1:", L1;
		"L2:", L2;
		"Bad:", NF;
		"Good:", NF2;
		Set(NF) eq Set(NF2);
		"Diff:", [NF[i]-NF2[i]: i in [1..#NF]];
		error "";
	    end if;
	end if;
	//"Sum"; time
	eqn := Coefficients(mysum([T.i * f(NF[i]): i in [1..#M]]));
    else
	eqn:= Coefficients(&+[T.i * f(NormalForm(g(M[i]),Ig)): i in [1..#M]]);
    end if;

    res:=[];
    if 1 eq 1 then
	V:=VectorSpace(CoefficientRing(P),#eqn);

	//"mon set"; time
	eqnM := [{@ m: m in Monomials(e) @}: e in eqn];
	//"coeff set"; time
	eqnC := [Coefficients(e): e in eqn];
//eqnM;
//eqnC;

	//v:=[V![MonomialCoefficient(e,T.i): e in eqn]: i in [1..#M]];

	vprintf Invariants, 3: "Set up %o by %o matrix\n", #M, #eqn;
	v:=[
	    V![
		ind eq 0 select 0 else eqnC[e][ind] where
		    ind := Index(eqnM[e], Ti): e in [1 .. #eqn]
	    ] where Ti := T.i:
		i in [1..#M]
	];

	mat := Matrix(v);
	density := Density(mat);
	vprintf Invariants, 3: "Mat density: %.3o (%.3o/r)\n",
	    density, density*Ncols(mat);
	W_dim := Rank(mat);
	vprint Invariants, 3: "Mat rank:", Rank(mat);
	delete mat;
	Ws:=sub<V | >;
	for i:=1 to #M do
	    if not v[i] in Ws then
		Include(~Ws, v[i]);
		Include(~res,M[i]);
		if #res eq W_dim then
		    break;
		end if;
	    end if;
	end for;
    else
	V:=VectorSpace(CoefficientRing(P),#eqn);
	v:=[V![MonomialCoefficient(e,T.i): e in eqn]: i in [1..#M]];
	W:=sub<V|v>;
	Ws:=sub<V | []>;
	for i:=1 to #M do
	    if not v[i] in Ws then
		Ws:=sub<V | Ws,v[i]>;
		Include(~res,M[i]);
		if #res eq Dimension(W) then break; end if;
	    end if;
	end for;
    end if;

    function cmp(f, g)
	d := Length(f) - Length(g);
	if d ne 0 then return d; end if;
	if f lt g then return +1; end if;
	if f gt g then return -1; end if;
	return 0;
    end function;

    Sort(~res, cmp);

// Sort(~res);
// return Reverse(Sort(res));

    return res;
end function;

function AllVecs(s,n,q)
// All vectors in {0..q-1}^n (or N^n if q = 0) with coefficient sum s)
    local i,v,m;
    
    if n eq 0 then
	if s eq 0 then return [[]];
	else return [];
	end if;
    end if;
    m:=s;
    if q eq 0 then
	m:=s;
    else
	m:=Min(s,q-1);
    end if;
    return &cat[[[i] cat v: v in AllVecs(s-i,n-1,q)]: i in [0..m]];
end function;	 

function NextVector(v,q)
// The next vector after v when looping over a field of size q (q = 0 for
// char. = 0). Returned as a sequence of integers.
    local all,nz,i;
    
    if v eq [] then
	return [];
    end if;
    nz:=Position(v,1);
    if nz eq 0 then
	return [1] cat [0: i in [2..#v]];
    end if;

    SWAP_ORDER := true;
    SWAP_ORDER := false;

    k := #v;
    if 1 eq 1 then
	supp := [i: i in [nz + 1 .. k] | v[i] ne 0];
	// "nz:", nz, "supp:", supp;
	if #supp eq 0 then
	    if nz lt k then
		v[nz] := 0;
		v[nz + 1] := 1;
		return v;
	    elif k ge 2 then
		v[nz] := 0;
		v[1] := 1;
		if SWAP_ORDER then
		    v[2] := 1;
		else
		    v[k] := 1;
		end if;
		return v;
	    end if;
	elif #supp eq 1 then
	    i := supp[1];
	    if SWAP_ORDER then
		if i lt k then
		    v[i] := 0;
		    v[i + 1] := 1;
		    return v;
		elif nz + 2 le k then
		    v[i] := 0;
		    v[nz] := 0;
		    v[nz + 1] := 1;
		    v[nz + 2] := 1;
		    return v;
		end if;
		// Fall through to old case.
	    else
		if i gt nz + 1 then
		    v[i] := 0;
		    v[i - 1] := 1;
		    return v;
		end if;
	    end if;
	end if;
    end if;

    all:=[[0: i in [1..nz-1]] cat [1] cat a: a in AllVecs(&+v-1,#v-nz,q)];
    i:=Position(all,v);
    if i eq 0 then
	error "v not found";
    end if;
    if i lt #all then
	return all[i+1];
    end if;
    while nz lt #v do
	nz:=nz+1;
	all:=[[0: i in [1..nz-1]] cat [1] cat a: a in AllVecs(&+v-1,#v-nz,q)];
	if #all ne 0 then
	    return all[1];
	end if;
    end while;
    all:=[[1] cat a: a in AllVecs(&+v,#v-1,q)];
    if #all ne 0 then
	return all[1];
    else
	return [];
    end if;
end function;

/*
function MyDim(I)
    K := BaseRing(I);

    if K cmpeq RationalField() then
	K := GF(11863279);
	J := ChangeRing(I, K);
	return Dimension(J);
    end if;

    if Type(K) eq RationalField() then
	K := GF(11863279);

end function;
*/

SubDim:=procedure(I,L,degs,~res,~rem,~bas,~basI: invs:=[],HGB:=false)
// res is set to the dimension of the ideal generated by the homogeneous 
// components I_d, d in degs, and f_1,...,f_k, f_i in L.
// rem is a remember-table.
// If HGB is set = true, then in the case that degs is the empty list,
// a Hilbert-driven Buchberger is used which only checks if the dimension
// of the ideal (f_1,...,f_k) is equal to n-k. If this is true, n-k is
// returned. Otherwise, n-k+1 is returned, ALTHOUGH it is only known that
// the dimension is > n-k.
    local ls,i,J,f,F,P,Ps,phi;
    
    ls:=[f: f in L | not TotalDegree(f) in degs];
    for i:=1 to #rem`arg do
        if (rem`arg[i])`degrees eq degs and (rem`arg[i])`pols eq ls then
            res:=rem`val[i];
            return;
        end if;
    end for;
    
    P:=PolynomialRing(I);
    vprint Invariants, 3: "Calculate the dimension. Subset:",degs,"Polynomial degrees:",
        [TotalDegree(f): f in ls];
    for f in degs do
//        Include(~(rem`deg),f);
//      i:=case< #invs ge f | true: invs[f], default: InvariantsOfDegree(I,f)>;
//      Include(~(rem`dim),#i);
        i:=case< #invs ge f | true: invs[f], default: InvariantsOfDegree(I,f)>;
        if not f in rem`deg then
            Append(~(rem`deg),f);
            Append(~(rem`dim),#i);
        end if; // changed 26 May 1997
    end for;

    J:=ls cat &cat[case< #invs ge f |
            true: invs[f], default: InvariantsOfDegree(I,f)>: f in degs];

    HGB := Type(BaseRing(P)) notin {FldRat, FldFin, FldNum, FldCyc, FldQuad};

HGB := true;

    if HGB and #degs eq 0 then
        F:=PolynomialRing(IntegerRing());
        if #L eq 0 then res:=Rank(P);
        else
	    vprint Invariants, 3: "Using HGB!";//!!!
            Ps:=poly_ring1(CoefficientRing(P),Rank(P),"grevlex", I);
            phi:=hom<P->Ps | [Ps.i: i in [1..Rank(P)]]>;

            J := [phi(f): f in J];
	    U := Universe(J);
	    AssignNamesBase(~U, "x");
            HN := &*[1-F.1^TotalDegree(f): f in L];
//HN; J;
            b, J := HilbertGroebnerBasis(J, HN);
if 1 eq 1 and b then
    JJ:=Ideal(J);
    if HilbertNumerator(JJ) ne HN then
	"BAD";
	J;
	JJ;
	HN;
	HilbertNumerator(JJ);
	error "STOP";
    end if;
end if;

            if b then
                res:=Rank(P) - #L;
                bas:=J;
		basI := Ideal(bas);
		MarkGroebner(basI);
		basI := ChangeOrder(basI, P);
            else
		res:=Rank(P) - #L + 1;
		//if assigned bas then delete bas; end if;
            end if;
        end if;
    else
        basI:=ideal<P | J>;
	vprint Invariants, 3: "Get dim of", basI;
	vtime Invariants, 3: res:=Dimension(basI);
	vprint Invariants, 3: "Dim is", res;
	bas:=Basis(EasyIdeal(basI));
    end if;

    Append(~(rem`arg),rec<recformat<degrees,pols> | degrees:=degs,pols:=ls>);
    Append(~(rem`val),res);
    return;
end procedure;

function old_TaylorCoeffs(f,k)
// The Taylor coefficients of the rational function f up to t^k.
    local i,c,d,n,r;
    
    if k eq -1 then return []; end if;
    c:=old_TaylorCoeffs(f,k-1);
    n:=Numerator(f);
    d:=Denominator(f);
    r:=Coefficient(n-d*
	(&+([0] cat [c[i]*Name(Parent(d),1)^(i-1): i in [1..k]])),k);
    return c cat [r div Coefficient(d,0)];
end function;

function TaylorCoeffs(f,k)
// return old_TaylorCoeffs(f,k);
    S := PowerSeriesRing(BaseRing(Parent(f)), k + 1);
// "f:", f; "k:", k; "NEW"; time
    C := Coefficients(S!f);
    while #C le k do
	Append(~C, 0);
    end while;

    return C;

"OLD"; time
    CO := old_TaylorCoeffs(f, k);
C; CO;
    assert CO eq C;
    return C;
end function;

forward TryDegrees_intern;

TryDegrees:=function(I,degs: f:=[],k0:=0,invs:=[])
// Or have default k0 = -1 ??
 
// Try to find homog. f_1,...,f_m in I s.t. deg(f_i) = degs[i] and the
// dimension of (f_1,...,f_m) is n-m, where n = Rank(PolynomialRing(I)).
// If possible, return [f_1,...,f_m] and a grevlex Groebner basis of their
// ideal.
// If impossible: return a minimal k such that f_1,...,f_k don't exist.
// k0: Check subset-condition for k0 before trying an f_1.
// invs: List of bases of homogeneous invariants.
 
    local rem,res,gbas;
    
    rem:=rec<recformat<arg,val,deg,dim> | arg:=[], val:=[], deg:=[], dim:=[]>;
    TryDegrees_intern(I,degs,f,k0,~res,~rem,~gbas,~gbasI: invs:=invs);
    if assigned gbas then
        return res,gbas;
    else
        return res;
    end if;
end function;

TryDegrees_intern:=procedure(I,degs,f,k0,~res,~rem,~bas,~basI: invs:=[])
/*
Try to find homog. f_1,...,f_m in I s.t. deg(f_i) = degs[i] and the
dimension of (f,f_1,...,f_m) is n-#f-m, where n = Rank(PolynomialRing(I)).
Assign result to res.
If successful, assign a grevlex Groebner basis of (f_1...f_m) to bas and
ideal of that to basI.
If impossible: return a minimal k such that f_1,...,f_k don't exist.
k0: Check subset-condition for k0 before trying an f_1
invs: List of bases of homogeneous invariants.
*/

    local n,d,k,i,f1,M,dim,R,basis,vec,cnt,yet;
    
    vprint Invariants, 3: "Enter TryDegrees with degs =",degs,"and f =",f,"k0 =",k0;
    R:=k0-1;
    k:=-1;
    basis:=[I!0];
    yet:=I!0;
    n:=Rank(PolynomialRing(I));

    // Loop over invariants of degree degs[1] ...
    while true do
	
	if R ge k or #degs eq 0 then
	    k:=R+1;
	    vprint Invariants, 3: "The new k is",k,". Check if we can get further ...";
	    for d in [0] cat [k-i+1: i in [1..k]] do
		for M in choose({1..k},d) do
		    SubDim(I,f,{degs[i]: i in M},~dim,~rem,~gbas,~gbasI: HGB:=true);
		    if dim gt n-#f-#M then
			vprint Invariants, 3:
	"Can't go any further since the dim. of the old primaries and degrees",
			    [degs[i]: i in M],"is",dim,"instead of <=",
			    n-#f-#M;
			if d eq 0 then k:=0; end if;
			vprint Invariants, 3: "Exit TryDegrees with value",k;
			res:=k;
			return;
		    end if;
		end for;
	    end for;
	    if #degs eq 0 then
		vprint Invariants, 3: "Dimension of f_1..f_n is ",dim;
		vprint Invariants, 3: "Exit TryDegrees successfully";
		res:=f;
		if assigned gbas then bas:=gbas;basI:=gbasI; end if;
		return;
	    end if;
	    vprint Invariants, 3: "We should get further!";
	end if;
	
	f1:=I!0;
	if k lt 0 and (Type(Group(I)) eq GrpPerm or 
	    Characteristic(CoefficientRing(I)) eq 0 or 
	    #Group(I) mod Characteristic(CoefficientRing(I)) ne 0) then
	    // First try an element of InvariantsOfDegree(I,degs[1])
	    // which hasn't been used before
	    dim:=TaylorCoeffs(HilbertSeries(I),degs[1])[degs[1]+1];
	    d:=[TotalDegree(i): i in f];
	    for i:=#[i: i in d | i eq degs[1]]+1 to dim do
		poly:=case<#invs ge degs[1] | true: invs[degs[1]][i],
		    default: InvariantsOfDegree(I,degs[1],i)[i]>;
		if not poly in f then
		    f1:=poly;
		    yet:=f1;
		    break;
		end if;
	    end for;
	end if;

	if f1 eq I!0 then
	    if basis eq [I!0] then
//		Include(~(rem`deg),degs[1]);
		polys:=case<#invs ge degs[1] | true: invs[degs[1]],
		    default: InvariantsOfDegree(I,degs[1])>;
//		Include(~(rem`dim),#polys);
		if not degs[1] in rem`deg then
		    Append(~(rem`deg),degs[1]);
		    Append(~(rem`dim),#polys);
		end if; // changed 26 May 1997
		basis := SelectBasis(polys, ideal<PolynomialRing(I) | f>, I);
		vprint Invariants, 3: "Basis:", basis;
		vec:=[0: i in [1..#basis]];
	    end if;

	    if Characteristic(CoefficientRing(I)) eq 0 then
		q:=0;
	    else
		q:=#CoefficientRing(I);
	    end if;
	    vec := NextVector(vec,q);
	    if vec eq [] then break; end if;

	    vprint Invariants, 3: "Next vector is", vec;
	    supp := [i: i in [1..#vec] | vec[i] ne 0];
	    vprintf Invariants, 3: "vec (%o, %o) support: %o, %o\n",
		#f, #vec, Sprint(supp), forall{i: i in supp | vec[i] eq 1};

	    if Characteristic(CoefficientRing(I)) eq 0 then
		f1:=&+[I!vec[i]*basis[i]: i in [1..#basis]];
	    else
		c:=[CoefficientRing(I)!0] cat 
		    Exclude([i: i in CoefficientRing(I)],CoefficientRing(I)!0);
		f1:=&+[c[vec[i]+1]*basis[i]: i in [1..#basis]];
	    end if;
	    if f1 eq yet then continue; end if;
	end if;
	
	vprint Invariants, 3: "Try candidate",f1;
	if k gt 0 then
	    fail:=false;
	    for d:=k-1 to 0 by -1 do
		for M in choose({2..k},d) do
		    SubDim(I,f,{degs[i]: i in M},~dim,~rem,~gbas,~gbasI: HGB:=true);
		    if dim lt n-#f-#M then
			continue;
		    end if;
		    SubDim(I,f cat [f1],{degs[i]: i in M},~dim,~rem,~gbas,~gbasI:
			HGB:=true);
		    if dim gt n-#f-1-#M then
			vprint Invariants, 3:
	"The candidate won't do since dim. of old primaries and candidate and",
			    M,"is",dim,"instead of <=",n-#f-1-#M;
			fail:=true;
			break;
		    end if;
		end for;
		if fail then
		    break;
		end if;
	    end for;
	    if fail then
		continue;
	    end if;
	end if;
	
	if k le 0 then
	    k0:=k;
	else
	    k0:=k-1;
	end if;

	TryDegrees_intern(
	    I,[degs[i]: i in [2..#degs]],f cat [f1],k0,
	    ~R,~rem,~gbas,~gbasI: invs:=invs
	);
	
	if Type(R) ne RngIntElt then
	    vprint Invariants, 3: "Exit TryDegrees successfully!";
	    res:=R;
	    if assigned gbas then bas:=gbas;basI:=gbasI; end if;
	    return;
	end if;
	
    end while;
    
    vprint Invariants, 3: "No good vector could be found!";
    if k le 0 then
	SubDim(I,f,{},~dim,~rem,~gbas,~gbasI: HGB:=true);
	if dim gt n-#f then
	    vprint Invariants, 3:
		"The dim. of the input already was",dim,"instead of",n-#f;
	    k:=0;
	else
	    k:=1;
	end if;
    end if;
    vprint Invariants, 3: "Exit TryDegrees with value",k;
    res:=k;
end procedure;

/*******************************************************************************
				    MultPartitions
*******************************************************************************/

function InnerMultPartitions(n,k,m,H)
// All rising vectors from N^k having product n and first entry >= m.
// If H is a list, then all vectors v_1,...,v_k returned will have
// v_i >= H[i].
// If H is a rational function then prod_{i=1}^k (1-t^{v_i}) * H will have
// positive coefficients at t^{v_i}.
    local i,j,res,r;
    
    if k eq 1 then return [[n]];
    end if;
    
    //is_fraction := func<t | t eq FldFunRatUElt or t eq FldFunRatUEltOld>;
    is_fraction := func<t | t eq FldFunRatUElt>;
    res:=[];
    if is_fraction(Type(H)) then
	i:=m;
    else
	i:=Max(m,H[1]);
    end if;
    while i^k le n do
	if n mod i eq 0 then
	    if is_fraction(Type(H)) then
		if TaylorCoeffs(H,i)[i+1] gt 0 then
		    res:=res cat [[i] cat r: r in $$(n div i,
			k-1,i,(1-Name(Parent(H),1)^i)*H)];
		end if;
	    else
		if i * &*[H[j]: j in [2..#H]] gt n then break; end if;
		res:=res cat [[i] cat r: r in 
		    $$(n div i,k-1,i,[H[j]: j in [2..#H]])];
	    end if;
	end if;
	i:=i+1;
    end while;
    // Sort(~res,func<x,y | &+x - &+y>);
    return res;
end function;

function MultPartitions(n,k,m,H)
    P := InnerMultPartitions(n, k, m, H);
    Sort(~P, func<x,y | &+x - &+y>);
    return P;
end function;

/*******************************************************************************
				    Main algorithm
*******************************************************************************/

function InternalPrimaryInvariantsDirect(
    I: invs:=[], HGB := true, DegreeVectors := []
)

// Calculate optimal primary invariants.
// invs: List of bases of homogeneous invariants.
 
    local rem,blacklist,n,prod,degs,mindegs,molien,J,dim,d,i,j,k,H,P;

    vprint Invariants, 1: "PRIMARY INVARIANTS";
    vprint Invariants, 1: "DegreeVectors:", DegreeVectors;
    ZEIT := Cputime();

    P:=PolynomialRing(I);
    molien:=assigned I`HilbertSeries or (Type(Group(I)) eq GrpPerm or 
	Characteristic(CoefficientRing(I)) eq 0 or 
	#Group(I) mod Characteristic(CoefficientRing(I)) ne 0);
    rem:=rec<recformat<arg,val,deg,dim> | arg:=[], val:=[], deg:=[], dim:=[]>;
    n:=Rank(P);
    if not molien then
	J:=ideal<P | >;
	dim:=n;
	mindegs:=[];
	d:=1;
	while dim gt 0 do
	    vprint Invariants, 3: "Add invariants of degree",d,"to the ideal ...";
	    i:=case<#invs ge d | true: invs[d],
		 default: InvariantsOfDegree(I,d)>;
	    vprint Invariants, 3: "There are",#i,"linearly independent invariants of degree",d;
//	    Append(~(rem`deg),d);
//	    Append(~(rem`dim),#i);
	    if not d in rem`deg then
		Append(~(rem`deg),d);
		Append(~(rem`dim),#i);
	    end if; // changed 26 May 1997
	    J:=J + ideal<P | i>;
	    dim:=Dimension(J);
	    vprint Invariants, 3: "The dimension of the ideal is",dim;
	    vprint Invariants, 3: "";
	    mindegs:=mindegs cat [d: i in [1..n-dim-#mindegs]];
	    d:=d+1;
	end while;
    else
	H:=HilbertSeries(I);
    end if;
    
    blacklist:=[];
    prod:= #Group(I);
    
    while true do
	if molien then
	    i:=H;
	else
	    i:=mindegs;
	end if;

	if #DegreeVectors gt 0 then
	    degs_list := DegreeVectors;
	    DegreeVectors := [];
	else
	    degs_list := MultPartitions(prod,n,1,i);
	end if;

	for degs in degs_list do
	    k:=0;
	    for d in blacklist do
		dim:=true;
		for i:=1 to #d do
		    if degs[i] ne d[i] then
			if i eq #d and i gt k then k:=i; end if;
			dim:=false;
			break;
		    end if;
		end for;
		if dim then
		    vprint Invariants, 3: "Degree vector",degs,"rejected by blacklisted",d;
		    continue degs;
		end if;
	    end for;
	    
	    if molien then
		d:=&*[1-Name(Parent(H),1)^i: i in degs] * H;
		if Denominator(d) ne 1 then continue;
		end if;
		if (Characteristic(CoefficientRing(I)) eq 0 or 
		    #Group(I) mod Characteristic(CoefficientRing(I)) ne 0) and
		    not &and[i ge 0: i in Coefficients(Numerator(d))] then
		    continue;
		end if;
	    else
		dim:=0;
		for d:=1 to Max(rem`deg) do
		    i:=Position(rem`deg,d);
		    if i ne 0 then
			J:=PolynomialRing(IntegerRing());
			J:=TaylorCoeffs(elt<FunctionField(IntegerRing())|
			    case<dim ne 0 | true: 1+Name(J,1)^dim,
			    default: J!1>,
			    &*[1-Name(J,1)^degs[i]: i in [1..n]]>,d)[d+1];
			if (rem`dim)[i] lt J then
			    vprint Invariants, 3: "Degree vector",degs,
				"rejected since invariants of degree",d,
				"have dimension",(rem`dim)[i],
				"instead of >=",J;
			    continue degs;
			elif dim eq 0 and (rem`dim)[i] gt J then
			    dim:=d;
			end if;
		    end if;
		end for;
	    end if;
	    
	    vprintf Invariants, 1: "Try degree vector %o (time: %o)\n",
		degs, Cputime(ZEIT);

	    if molien and #blacklist eq 0 then k:=-1; end if;
	    if k gt 0 then
		SubDim(I,[],{degs[i]: i in [1..k]},~dim,~rem,~gbas,~gbasI: HGB:=HGB);
		if dim gt n-k then
		    vprint Invariants, 3: "Degree vector",degs,
			"rejected since the dimension of degrees",
			[degs[i]: i in [1..k]],"is",dim,"instead of",n-k;
		    Append(~blacklist,[degs[i]: i in [1..k]]);
		    if assigned gbasI then delete gbasI; end if;
		    continue degs;
		end if;
		k:=0;
	    end if;
//	    if k eq 0 and molien then k:=-1; end if;
	    TryDegrees_intern(I,degs,[],k,~k,~rem,~gbas,~gbasI: invs:=invs);
	    if Type(k) ne RngIntElt then
		vprint Invariants, 3: "";
		vprintf Invariants, 1: "Primaries of degrees %o found!\n", degs;
		//SetPrimaryInvariants(Group(I), k);
		if assigned gbas then
		    Ps:=PolynomialRing(I);
		    phi:=hom<P->Ps | [Ps.i: i in [1..Rank(P)]]>;
		    gbas := ideal<Generic(Universe(gbas)) | gbas>;
		else
		    gbas := false;
		end if;
		//return k, gbas;

		return k, gbasI;
	    end if;
	    Append(~blacklist,[degs[i]: i in [1..k]]);
	    vprint Invariants, 3: "";
	    vprint Invariants, 3: "Go to next degree vector ...";
	    
	end for;
	prod:=prod + #Group(I);
    end while;
    return degs, 0;
    //return degs, false, 0;
    
end function;

/*******************************************************************************
				    Main algorithm
*******************************************************************************/

intrinsic InternalPrimaryInvariantsHard(
    I::RngInvar: invs:=[], HGB := true, DegreeVectors := []
) -> []
{Internal function}

    return InternalPrimaryInvariantsDirect(
	I: invs := invs, HGB := HGB, DegreeVectors := DegreeVectors
    );

end intrinsic;

intrinsic PrimDecomp(
    I::RngInvar: invs:=[], HGB := true, DegreeVectors := []
) -> []
{Internal function}

    K := BaseRing(I);
    if 0 eq 1 or invs ne [] then
	return InternalPrimaryInvariantsDirect(I: invs := invs, HGB := HGB);
    end if;

    G := Group(I);
    if Type(G) eq GrpPerm then
	M := GModule(G, K);
    else
	M := GModule(G);
    end if;

    D := IndecomposableSummands(M);
    "Decomposition:", D;
    if #D eq 1 then
	return InternalPrimaryInvariantsDirect(I: invs := invs, HGB := HGB);
    end if;

    T := VerticalJoin(<Morphism(S, M): S in D>);
    "T:", T;

    P := PolynomialRing(I);
    L := [];
    pos := 0;
    for S in D do
	d := Dimension(S);
	IS := InvariantRing(MatrixGroup(S));
	SL := InternalPrimaryInvariantsDirect(IS);
	h := hom<PolynomialRing(IS) -> P | [P.(pos + i): i in [1 .. d]]>;

	"first SL:", SL;
	SL := [h(f): f in SL];
	"mapped SL:", SL;
	SL := [f^T: f in SL];
	"transformed SL:", SL;

	L cat:= SL;

	pos +:= d;
    end for;

    function cmp(f, g)
	d := TotalDegree(f) - TotalDegree(g);
	if d ne 0 then return d; end if;
	if f lt g then return +1; end if;
	if f gt g then return -1; end if;
	return 0;
    end function;

    Sort(~L, cmp);

    return L, Ideal(L);

end intrinsic;
