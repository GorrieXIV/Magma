freeze;

////////////////////////////////////////////////////////////////
//                                                            // 
//          Functions used in RepLoc package                  //
//                                                            // 
//             Jared Weinstein, May 2009                      //
//                                                            // 
////////////////////////////////////////////////////////////////

import "../ModSym/multichar.m": MC_MatrixActionOnSubspace;

ZZ:=IntegerRing();

////////////////////////////////////////
//LiftToChar0(mat,P,N)
//Given a matrix mat with integer entries with determinant = \pm 1 mod P,
//returns a matrix which is congruent to mat mod P and which is
// congruent to [\pm 1, *, 0, 1] mod N.
//P and N must be relatively prime.
////////////////////////////////////////

function LiftToChar0(mat,P,N)
	a,b,c,d:=Explode(Eltseq(mat));
	det:=a*d-b*c;
	if (det mod P ne 1) and (det mod P ne P-1) then
		print "Determinant must be 1 or -1 modulo the second argument."; 
		return false;
	end if;
	if det mod P eq 1 then
		eps:=1;
	end if;
	if det mod P eq P-1 then
		eps:=-1;
	end if;
	//Change entries to have appropriate congruence mod N:
	A:=CRT(P*ZZ,N*ZZ,a,eps);	
	B:=b;
	C:=CRT(P*ZZ,N*ZZ,c,0);
	D:=CRT(P*ZZ,N*ZZ,d,1);
	//Get B and D to be relatively prime, by adding multiples of P to B (if D =0, change it to D+PN)
	if D eq 0 then
		D:=D+P*N;
	end if;
	t:=0;
	while GCD(B,D) ne 1 do	
		B:=B+P*t;
		t:=t+1;
	end while;
		
	//Now solve appropriate Diophantine equation
	det:=A*D-B*C;
	if (eps - det) mod P*N ne 0 then return "error"; end if;
	T:=(eps - det) div (P*N);
	if B eq 0 then
		A:=eps*D;
		return [A,B,C,D];
	end if;
	x:=ZZ!(1/Integers(AbsoluteValue(B))!D);
	y:=(x*D-1) div B;
	//Thus xD-yB=1.
	A:=A+x*T*P*N;
	C:=C+y*T*P*N;
	return [A,B,C,D];
end function; 
	 

//////////////////////////////////////////////////////////////
// char_remove_p(chi,p):
// Given a Dirichlet character chi of conductor N0 p^o, gives
// the character of conductor N0 given by restriction.
/////////////////////////////////////////////////////////////

function char_remove_p(chi,p)
	N:=Conductor(chi);
	o:=Valuation(N,p);
	if o eq 0 then
		return chi;
	end if;
	D:=Decomposition(chi);
	chi_p:=[chi_test : chi_test in D | Conductor(chi_test) mod p eq 0][1];
	return chi/chi_p;
end function;


//////////////////////////////////////////////////////////////
// IsSteinberg(M,p):
// Returns true if M is a twist of the Steinberg representation
// at p.  This means exactly that M is a twist of a newform
// for Gamma_0(p) by a Dirichlet character.
////////////////////////////////////////////////////////////////
/*
function IsSteinberg(M,p)
	N:=Level(M);
	o:=Valuation(N,p);
	if o eq 0 then 
		return false;
	end if;
	if o eq 1 then 
		if IsMinimalTwist(M,p) then
			return true;
		end if;
		else return false;
	end if;
	if o gt 1 then
		k:=Weight(M);
		chi:=DirichletCharacter(M);
		chi0:=char_remove_p(chi,p);
		candidate_forms:=NewformDecomposition(CuspidalSubspace(ModularSymbols(chi0,k)));
		for f in candidate_forms do
			if IsTwist(M,f,p) then
				return true,f,chi0;
			end if;
		end for;
	end if;
	return false;
end function;
*/

/////////////////////////////////////////////////////////
// CI_space(f,p):
// Given a modular symbols space f and a prime p
// at which f is supercuspidal, determines a subspace W
// of a certain space of modular symbols M.  The subspace W
// represents f and its twists by Dirichlet characters of 
// p-power conductor.  W admits an action of a certain p-adic
// matrix group G, equal to SL_2(Z_p) if the p-conductor of f is
// even and an Iwahori subgroup of SL_2(Z_p) otherwise.
//
// The data of W together with the action of G forms
// a "cuspidal inducing datum" in the sense of Bushnell/Henniart.
// See the book "The Local Langlands Conjecture for GL(2)",p.110.
///////////////////////////////////////////////////////////////

// TO DO: this doesn't compute the right dimension 
// (the answer is unlikely to be incorrect though)

function CI_space(M,p)
	N:=Level(M);   
        K:=BaseRing(M);
        o:=Valuation(N,p);
        N0:=N div p^o;
	P:=p^(o div 2);
        G:=DirichletGroup(N,CyclotomicField(EulerPhi(N)));
        chars:=Elements(G);
        chi:=G!DirichletCharacter(M);
        chi_pprime := G!char_remove_p(chi,p);
        char_set:=[char : char in chars |  
		G!char_remove_p(char,p) eq chi_pprime and 
		Valuation(Conductor(char),p) le (o div 2)];

        M1:=ModularSymbols(char_set,Weight(M));
	V,m:=VectorSpace(M1);
        t:= (Sign(M) eq 0) select 1 else 2;
        dim:=t*EulerPhi(P)*Dimension(M);

	q:=2;
        vprintf RepLoc: "Constructing a space on which SL_2(Z/%o) acts:\n", P;
        vtime RepLoc:
	while Dimension(V) gt dim do
		if q eq p then 
			q:=NextPrime(q);
		end if;
                vprintf RepLoc: "    current dimension %o (target %o), using T_%o\n",
                                                                  Dimension(V),dim,q;
		c:=Order(Integers(P)!q);
                T:=HeckeOperator(M,q);
                f:=MinimalPolynomial(T^c);
                T1:=HeckeOperator(M1,q);
                sum := Evaluate(f, T1^c);
                V meet:= Kernel(sum);
		q:=NextPrime(q);
        end while;

	return V,m,M1;
end function;


////////////////////////////////////////////////////////////
// CI_rep(g,W,M,p)
// Given the output W,M of CI_space, and a matrix g
// (in the format of a sequence of four integers), returns the 
// action of g on W.  If the p-conductor is odd, then the SW
// entry of g must be divisible by p.
////////////////////////////////////////////////////////////
		
function CI_rep(g,V,m,M,p)
	K:=BaseRing(V);
	N:=Level(M);
	k:=Weight(M);
	o:=Valuation(N,p);
	P:=p^(o div 2);
	Q:=p^(Ceiling(o/2));
	N0:=N div p^o;
	gLift:=LiftToChar0(g,Q,N0);
	a,b,c,d:=Explode(gLift);
	gLiftConj:=[a*P,b,c*P^2,d*P];
	assert Codomain(m) eq M;
	assert IsAmbientSpace(M) and IsMultiChar(M);
	action:=Transpose(MC_MatrixActionOnSubspace(gLiftConj,V,m))^(-1);
	action*:=P^(k-2);
	return action;
end function;

///////////////////////////////////////////////////////////
// type_group(p,c)
// If f is a modular form which is supercuspidal at p, with 
// p conductor c, then the cuspidal inducing datum 
// corresponding to the p-component of f is a representation
// of a certain p-adic matrix group.  The representation factors
// through a finite matrix group, which is the output of type_group.
/////////////////////////////////////////////////////////////

function type_group(p,c)
	P:=p^(Ceiling(c/2));
	R:=Integers(P);
	U,m:=UnitGroup(R);
	G:=GL(2,R);
	n:={G!Matrix(2,[1,1,0,1])};
	t:={G!Matrix(2,[m(u),0,0,1/m(u)]) : u in Generators(U)};
 	if (c mod 2) eq 0 then
		w:={G!Matrix(2,[0,1,1,0])};
		else w:={G!Matrix(2,[1,0,p,1]),G!Matrix(2,[1,0,0,-1])};
	end if;
	gens:=&join[n,t,w];
	ans:=sub< G | gens>;
	return ans;
end function;
	
function Iwahori(p,c)
	P:=p^(Ceiling(c/2));
	R:=Integers(P);
	U,m:=UnitGroup(R);
	G:=GL(2,R);
	n:={G!Matrix(2,[1,1,0,1])};
	t:={G!Matrix(2,[m(u),0,0,1]):  u in Generators(U)};
	tm:={G!Matrix(2,[1,0,0,m(u)]) : u in Generators(U)};
	w:={G!Matrix(2,[1,0,p,1])};
	gens:=&join[n,t,tm,w];
	ans:=sub<G|gens>;
	return ans;
end function;

function find_f(f,M);
	K:=Parent(Coefficients(qEigenform(f,1))[1]);
	coeffs:=Coefficients(qEigenform(f,100));
	A:=ChangeRing(StarInvolution(M),K);
	V:=Eigenspace(A,1);
	p:=1;
        vprintf RepLoc: "Finding a new vector (over field of degree %o):\n", AbsoluteDegree(K);
        vtime RepLoc:
	while Dimension(V) gt 1 do
		p:=NextPrime(p);
                vprintf RepLoc: "    current dimension %o, using T_%o\n", Dimension(V), p;
		T:=HeckeOperator(M,p);
		TK:=ChangeRing(T,K);
		a_p:=coeffs[p];
		V meet:=Eigenspace(TK,a_p);
	end while;	
	return V.1;
end function;

function CI_datum_provisional(f,p)
	V,m,M:=CI_space(f,p);
	c:=Valuation(Level(f),p);
	G:=type_group(p,c);
	P:=p^(c div 2);
	n:=Ngens(G);
	gens:=[G.i: i in [1..n]];
	genslift:=[ChangeUniverse(Eltseq(g),ZZ) : g in gens];
	rep_values:=[];
	for i in [1..n] do
		g:=G.i;
		g_lift:=ChangeUniverse(Eltseq(g),ZZ);
		gmat:=G!Matrix(2,g_lift);
		rep_value:=CI_rep(g_lift,V,m,M,p);
		Append(~rep_values,rep_value);
	end for;
	W:=GModule(G,rep_values);
	w:=find_f(f,M);
	K:=Parent(w[1]);
	VK:=ChangeRing(V,K);
	WK:=ChangeRing(W,K);
	v:=WK!Coordinates(VK,w);
	rho:=Representation(WK);
	space,m:=sub<WK|[v]>;
	return space,v@@m;
end function;


function CI_datum(f,p)
	W:=CI_datum_provisional(f,p);
	d:=Dimension(W);
	chi:=DirichletCharacter(f);
	// need the p-part of chi
	if Conductor(chi) mod p ne 0 then
		chi_p:=DirichletGroup(1)!1;
		else 
		D:=Decomposition(chi);
		chi_p:=[chi_test : chi_test in D | Conductor(chi_test) mod p eq 0][1];
	end if;
	K:=BaseRing(W);
	N:=Level(f);
	c:=Valuation(N,p);
	rhoW:=Representation(W);
	G:=Group(W);	
	R:=Parent(Eltseq(G!1)[1]);
	Gl:=GL(2,R);
	Z:=Center(Gl);
	GZ:=sub<Gl|G,Z>;
	rep_values:=[];
	n:=Ngens(GZ);
	for i in [1..n] do
		g:=GZ.i;
		if g in Z then
			u:=g[1][1];
			if IsTrivial(DirichletCharacter(f)) then
				rep_value:=IdentityMatrix(K,d);
			else 
                                rep_value:=1/K!chi_p(u)*IdentityMatrix(K,d);
                                // MW, 9 Jun 2011: changed to 1/chi_p 
			end if;
		else 
			rep_value:=Matrix(rhoW(g));
		end if;
		Append(~rep_values,rep_value);		
	end for;	 	
	WZ:=GModule(GZ,rep_values);
	if c mod 2 eq 0 then
		WInd:=Induction(WZ,Gl);
	else 
                WInd:=Induction(WZ,Iwahori(p,c));
	end if;
        // TO DO
	if p eq 2 or p mod 4 eq 1 then
		WInd:=CompositionFactors(WInd)[1];
	end if;
	return WInd;
end function;
	
function HenniartTypeProvisional(M,p)
/* 
If M is minimal and principal series at p, returns the space of modular symbols on which the
corresponding principal representation of GL_2(Z_p) is realized.  This consists of M together
with its twists by Dirichlet characters of conductor no more than half the p-level of M.
*/
	N:=Level(M);   
        K:=BaseRing(M);
        o:=Valuation(N,p);
        assert o gt 0;
	c:=2*Ceiling(o/2);
        N0:=N div p^o;
	P:=p^c;
        G:=DirichletGroup(P*N0,CyclotomicField(EulerPhi(N)));
        chars:=Elements(G);
        chi:=G!DirichletCharacter(M);
        chi_pprime := G!char_remove_p(chi,p);
        char_set:=[char : char in chars |  
		G!char_remove_p(char,p) eq chi_pprime and 
		Valuation(Conductor(char),p) le (c div 2)];

        M1:=ModularSymbols(char_set,Weight(M));
	V,m:=VectorSpace(M1);
        t:= (Sign(M) eq 0) select 1 else 2;
        dim:=t*(p^((c div 2)-1)*(p+1))*Dimension(M);

	q:=2;
        vprintf RepLoc: "Constructing a space on which GL_2(Z_%o) acts:\n", p;
        vtime RepLoc:
	while Dimension(V) gt dim do
		if q eq p then
			q:=NextPrime(q);
		end if;
                vprintf RepLoc: "    current dimension %o (target %o), using T_%o\n",
                                                                  Dimension(V),dim,q;
		order:=Order(Integers(P)!q);
                T:=HeckeOperator(M,q);
                f:=MinimalPolynomial(T^order);
                T1:=HeckeOperator(M1,q);
                sum := Evaluate(f, T1^order);
                V meet:= Kernel(sum);
		q:=NextPrime(q);
        end while;
	R:=Integers(p^Ceiling(c/2));
	U,map:=UnitGroup(R);
	Gl:=GL(2,R);
	n:={Gl!Matrix(2,[1,1,0,1])};
	t:={Gl!Matrix(2,[map(u),0,0,1/map(u)]) : u in Generators(U)};
 	w:={Gl!Matrix(2,[0,1,1,0])};
        G:=sub<Gl | &join[n,t,w]>;
	n:=Ngens(G);
	gens:=[G.i: i in [1..n]];
	genslift:=[ChangeUniverse(Eltseq(g),ZZ) : g in gens];
	rep_values:=[];
	for i in [1..n] do
		g:=G.i;
		g_lift:=ChangeUniverse(Eltseq(g),ZZ);
		gmat:=G!Matrix(2,g_lift);
		rep_value:=CI_rep(g_lift,V,m,M1,p);
		Append(~rep_values,rep_value);
	end for;
	W:=GModule(G,rep_values);
	w:=find_f(M,M1);
	K:=Parent(w[1]);
	VK:=ChangeRing(V,K);
	WK:=ChangeRing(W,K);
	v:=WK!Coordinates(VK,w);
	rho:=Representation(WK);
	space,m:=sub<WK|[v]>;
	return space,v@@m;
end function;

function HenniartType(f,p)
	W:=HenniartTypeProvisional(f,p);
	d:=Dimension(W);
	chi:=DirichletCharacter(f);
	//we need the p-part of chi
	if Conductor(chi) mod p ne 0 then
		chi_p:=DirichletGroup(1)!1;
		else 
		D:=Decomposition(chi);
		chi_p:=[chi_test : chi_test in D | Conductor(chi_test) mod p eq 0][1];
	end if;
	K:=BaseRing(W);
	N:=Level(f);
	c:=Valuation(N,p);
	rhoW:=Representation(W);
	G:=Group(W);	
	R:=Parent(Eltseq(G!1)[1]);
	Gl:=GL(2,R);
	Z:=Center(Gl);
	GZ:=sub<Gl|G,Z>;
	rep_values:=[];
	n:=Ngens(GZ);
	for i in [1..n] do
		g:=GZ.i;
		if g in Z then
			u:=g[1][1];
			if IsTrivial(DirichletCharacter(f)) then
				rep_value:=IdentityMatrix(K,d);
			else rep_value:=1/K!chi_p(u)*IdentityMatrix(K,d);
                        // MW, 9 Jun 2011: changed to 1/chi 
			end if;
		else 
			rep_value:=Matrix(rhoW(g));
		end if;
		Append(~rep_values,rep_value);		
	end for;	 	
	WZ:=GModule(GZ,rep_values);
	WInd:=Induction(WZ,Gl);
	if p mod 4 eq 1 then
		WInd:=CompositionFactors(WInd)[1];
	end if;
	return WInd;
end function;

function EmbedQuadAlgInMatAlg(R, G)
	x:=R.1;
	M:=MatrixAlgebra(ZZ,2);
	f:=MinimalPolynomial(x);
	n,t:=Explode(Coefficients(f));
	mat:=Matrix(2,ChangeUniverse([t,1,-n,0],ZZ));
	iota:=hom< R -> M | y :-> (ZZ!Eltseq(y)[1])-(ZZ!Eltseq(y)[2])*mat >;
	U,m:=UnitGroup(R);
	gens:=[m(g) : g in Generators(U)];
	gens_embed:=[iota(r) : r in gens];
	torus:=sub< G | gens_embed>;
	return torus,iota;
end function;

function CIDatumToAdmissiblePair(W)
	d:=Dimension(W);
	G:=Group(W);
	rho:=Representation(W);
	K:=BaseRing(W);
	ZmodP:=Parent(Eltseq(G!1)[1]);
	Gl:=GL(2,ZmodP);
	P:=Characteristic(ZmodP);
	p:=Factorization(P)[1][1];
	c:=Valuation(P,p);
	prec:=10;
	PhiP:=EulerPhi(P);
	Qp:=pAdicField(p,prec);
	Zp:=Integers(Qp);
	w:=Gl!Matrix(2,[0,1,-1,0]);
	Z:=Center(G);

	if w in G and c eq 1 then

                vprint RepLoc : "Depth zero case";
                /*
                In this case, the cuspidal inducing type is associated to
                a character chi of the finite field of size p^2.  It is a cuspidal
                representation of GL_2(F_p) of dimension p-1 whose restriction to 
                the nonsplit torus contains each of the p+1 characters of that torus 
                with the correct restriction to the center of GL_2(F_p), less chi and
                its F_p-conjugate.  This suggests the following procedure:
                */
		error if d ne (p-1), "Representation has wrong dimension";

		E:=UnramifiedExtension(Qp,2);
		R:=Integers(E);
		torus,iota:=EmbedQuadAlgInMatAlg(R,G);
		gen:=torus.1;
		gen_center:=torus.1^(p+1);
		Evalues:=Eigenvalues(rho(gen_center));
		zeta:=SetToSequence(Evalues)[1][1];
		mat:=rho(gen);
		char_poly:=CharacteristicPolynomial(mat);
		poly_ring:=Parent(char_poly);
		X:=poly_ring.1;
		g:=(X^(p+1)-zeta)^(d div (p-1));
		if g mod char_poly ne 0 then
			error "This is not a cuspidal representation of GL_2";
		end if;
		quotient:=g div char_poly;
		K,root_list:=SplittingField(quotient);
		mu:=root_list[1];
		mu_order:=OrderOfRootOfUnity(mu,p^2-1);
		L:=CyclotomicField(mu_order); 
                z:=L.1;
		rep:=GModule(torus,[Matrix(1,[z])]);
		chi:=Character(rep);	

	elif w in G and c gt 1 then

                vprint RepLoc : "Unramified higher depth case";
                /*
                In this case, the cuspidal inducing type is associated to 
                a character chi of (R/p^cR)^*, where R/Z_p is unramified quadratic.
                When the type is retricted to the nonsplit torus (R/p^c)^* inside
                of GL_2(Z/p^cZ), all but two characters are trivial on the
                norm one subgroup of 1+p^(c-1)R.  The remaining two are chi and its Qp-conjugate.
                */
		R:=UnramifiedExtension(Zp,2);
		torus,iota:=EmbedQuadAlgInMatAlg(R,G);
		Wtorus:=Restriction(W,torus);
		n:=Ngens(torus);
		char_polys:=[CharacteristicPolynomial(rho(torus.i)):i in [1..n]];			
		L:=SplittingField(char_polys);
		WtorusL:=ChangeRing(Wtorus,L);
		D:=CompositionFactors(WtorusL);
		reps:=[Representation(x): x in D];
		if p ne 2 then
			test_elt:=iota(1+p^(c-1)*(R.1-Trace(R.1)/2));
			//this element has norm 1 in G
		else test_elt:=iota(1+p^(c-1)*R.1);
		end if;
		chars:=[rep : rep in reps | not(IsOne(rep(test_elt)))];
		chi:=Character(chars[1]);

	elif w notin G then

                vprint RepLoc : "Ramified case";
                /*
                In this case, the cuspidal inducing type W is a representation of GL_2(Z/p^cZ)
                of dimension p^(c-2)*(p-1).  It is associated to the data of a ramified
                quadratic extension R/Z_p and a character chi of that extension.  But (for p
                odd anyway) there are two possible ramified tori in GL_2(Z/p^cZ).  Experiments
                have shown that the restriction of W to the "correct" torus contains
                chi and its Q_p-conjugate with multiplicity one, and every other character with
                multiplicity two, whereas the restriction W to the "false" torus contains
                every character with multiplicity two.  
                */
		error if Dimension(W) ne p^(c-2)*(p-1), "Representation has wrong dimension";

                error if p eq 2, "Failed to compute an admissible pair";

                x:=PolynomialRing(Zp).1;
                chi := false;
		for l := 0 to 1 do
                        if l eq 0 then
		                R:=ext<Zp | x^2 - p >;
                        else
				R:=ext<Zp | x^2 - PrimitiveRoot(p)*p >;
			end if;
			torus,iota:=EmbedQuadAlgInMatAlg(R,G);
			Wtorus:=Restriction(W,torus);
                        T:=[torus.i : i in [1..Ngens(torus)]];
			char_polys:=[CharacteristicPolynomial(rho(t)) : t in T];
			L:=SplittingField(char_polys);
			WtorusL:=ChangeRing(Wtorus,L);
                        factors:=CompositionFactors(WtorusL);
                        assert forall{X: X in factors | Dimension(X) eq 1};
                        values:=[[rep(t) : t in T] where rep is Representation(X) : X in factors];
                        if exists(i){i : i in [1..#factors] | 
                               forall{j : j in [1..#factors] | i eq j or values[i] ne values[j]} }
                        then
			       chi:=Character(factors[i]);
                               break;
                        end if;
		end for;
                error if chi cmpeq false, "Failed to compute an admissible pair";

	end if;

	order:=Order(torus);
	order_LCM:=LCM([OrderOfRootOfUnity(chi(torus.i),order): i in [1..Ngens(torus)]]);
	L:=CyclotomicField(order_LCM);
	t,embed:=IsSubfield(L,BaseRing(chi));
	Embed(L,BaseRing(chi),embed(L.1));
	rep:=GModule(torus,[Matrix(1,[L!chi(torus.i)]):i in [1..Ngens(torus)]]);
	chi:=Character(rep);
	local_char:=map<R -> L | r :-> chi(iota(r))>;

	return R,local_char;	
end function;		


function HenniartTypeToPrincipalSeriesParameters(W)
	G:=Group(W);
	K:=NumberField(BaseRing(W));
	R:=Parent(Matrix(G!1)[1][1]);
	P:=Characteristic(R);
	L:=NumberField(CyclotomicField(EulerPhi(P)));
	K:=CompositeFields(L,K)[1];
	W:=ChangeRing(W,K);
	U,m:=UnitGroup(R);
	gens:=Generators(U);
	n:=Ngens(U);
	toric_gens1:={Matrix(2,[m(u),0,0,1]): u in gens};
	toric_gens2:={Matrix(2,[1,0,0,m(u)]): u in gens};
	borel_gens:=&join[toric_gens1,toric_gens2,{Matrix(2,[1,1,0,1])}];
	Borel:=sub<G | borel_gens>;
	WBorel:=Restriction(W,Borel);
	D:=CompositionFactors(WBorel);
	char:=[w: w in D|Dimension(w) eq 1][1];
	DrchGroup:=DirichletGroup(P,BaseRing(W));
	rho:=Representation(char);
	char1values:=[rho(x)[1][1]: x in toric_gens1];
	char2values:=[rho(x)[1][1]: x in toric_gens2];
	char1:=[chi : chi in Elements(DrchGroup) | forall{i:i in [1..n]|chi(m(U.i)) eq char1values[i]}][1];
	char2:=[chi : chi in Elements(DrchGroup) | forall{i:i in [1..n]|chi(m(U.i)) eq char2values[i]}][1];
	return char1,char2;
end function;

/*
function CheckGModule(W);
	G:=Group(W);
	n:=Ngens(G);
	FG,f:=FPGroup(G);
	rho:=Representation(W);
	mats:=[GL(Dimension(W),BaseRing(W))|FG.i@f@rho:i in [1..n]];
	B:=SLPGroup(n);
	words:=[B|LHS(r)*RHS(r)^-1: r in Relations(FG)];
	t:=forall{x:x in Evaluate(words,mats)|IsOne(x)};
	return t;
end function;
*/
