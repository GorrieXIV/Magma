freeze;

/********************************************************************************************************

June 20, 2013

2011/12: Implementation for linear and quadratic character (Alan Lauder)
2013: Optimisations and extension to characters of order dividing p-1 (Alan Lauder)

This is free software: it is made available in the hope that it will be useful, but without any warranty.

*********************************************************************************************************

Instructions:

OverconvergentHeckeSeries(p,eps,k,m: WeightBound) : ->

The characteristic series P(t) modulo p^m of the Atkin U_p operator acting upon the 
space of overconvergent p-adic modular forms of character eps and weight k. 
Here eps is a Dirichlet character of some level N.
The input eps may also be taken to be an integer N, in which case one considers
the trivial character in level Gamma_0(N). We require
p >= 5 to be a prime not dividing N, k an integer and m a positive integer. 
The algorithm requires that the field of values Q(eps) embeds in the field of p-adic numbers - that is,
the order of the character divides (p-1) - and has class number one. 
The output is given as a power series P modulo p^m, and an integer zeta_pm modulo p^m which
specifies the embedding of the cyclotomic field Q(eps) = Q(zeta) into the p-adic field Q_p
via zeta -> zeta_pm modulo p^m.

The optional parameter WeightBound gives a 
bound on the weight of the generators which are chosen for certain spaces of classical 
modular forms required at one point in the algorithm for level N>=2. This takes the default value 
6 for even characters and 3 for odd characters. However, for some levels the algorithm will terminate more quickly
with a smaller WeightBound.

The input k may also be taken to be a sequence kseq of weights all congruent modulo (p-1). In this
case the output is the corresponding sequence of characteristic series'. (This is faster than
computing for each weight separately.)

Provided m<=k-1 then P(t) is the reverse characteristic polynomial modulo p^m of the Atkin
U_p operator on the space of classical modular forms of level Gamma_0(pN) with character eps (trivial at
p) and weight k, by Coleman's theorem. In addition, for trivial character at least, 
provided m <= (k-2)/2 then P(t) is the reverse characteristic polynomial modulo p^m of the Hecke 
T_p operator on the space of classical modular forms of level Gamma_0(N) and weight k.

The algorithm gives a provably correct output but for level N>=2 uses randomisation and may not terminate
in certain exceptional cases.

The algorithm is based upon "Algorithms 1 and 2" in "Computations with classical and p-adic modular forms" 
by Alan Lauder, in LMS J. Comput. Math. 14 (2011), 214-231. We use suggestions of
David Loeffler and John Voight to generate certain spaces of classical modular forms for level N>=2. 
The algorithm has a running time which is linear in log(k), and is especially
fast for level N := 1.

OverconvergentHeckeSeriesDegreeBound(p,N,k,m) : ->

Gives a bound on the degree of the characteristic series P(t) modulo p^m of the Atkin U_p operator 
on the space of overconvergent p-adic modular forms of (even) weight k and level Gamma_0(N).
This bound is due to Daqing Wan and depends only upon k modulo (p-1) rather than k itself. 

Examples:

> time P:=OverconvergentHeckeSeries(5,11,10000,5);                                                           
Time: 0.300
> P;
625*t^8 + 375*t^7 + 1275*t^6 - 875*t^5 - 661*t^4 + 335*t^3 + 1189*t^2 + 861*t + 1
> time Pseq:=OverconvergentHeckeSeries(5,11,[10000,10004,10008],5);
Time: 0.340 // computing at a sequence of suitable weights is faster than doing each separately
> Pseq;
[
    625*t^8 + 375*t^7 + 1275*t^6 - 875*t^5 - 661*t^4 + 335*t^3 + 1189*t^2 + 861*t + 1,
    525*t^6 - 125*t^5 - 916*t^4 - 145*t^3 + 914*t^2 - 254*t + 1,
    625*t^8 - 1000*t^7 - 475*t^6 - 1225*t^5 + 879*t^4 - 1250*t^3 - 611*t^2 - 69*t + 1
]
> time OverconvergentHeckeSeriesDegreeBound(5,11,10000,5); 
15 // a bound on the degree, which depends only on the weight k modulo p-1 rather than k itself.
Time: 0.010

One can also compute with spaces of negative weight and/or non-trivial character.

> G:=FullDirichletGroup(13);
> eps:=G.1^4;
> Order(eps);
3
> eps(-1); // check parity of character                              
1
> time P,zeta:=OverconvergentHeckeSeries(7,eps,-4,5); // note 3 divides p-1 here
Time: 3.560
> P;
2401*t^14 - 2744*t^13 + 3234*t^12 + 5285*t^11 - 2693*t^10 - 6082*t^9 - 2966*t^8 + 4136*t^7 + 6288*t^6 - 1964*t^5 -
    122*t^4 - 8243*t^3 - 5157*t^2 - 8181*t + 1
> zeta;
34967 // this cube root of unity modulo 7^5 specifies the embedding of Z[eps] into Z_7/(7^5).

One can compute with spaces of very large weight ...

> time P:=OverconvergentHeckeSeries(31,1,12345678910,10);
Time: 1.440
> P;
139626516613325*t^6 - 381703165808925*t^5 + 57324452617590*t^4 + 252464307339952*t^3 - 256421361272967*t^2 + 
    188709250511024*t + 1

... and very small weight.

> G:=DirichletGroup(23);    
> eps:=G.1;
> time P:=OverconvergentHeckeSeries(13,eps,1,5);            
Time: 9.500
> P;
-85683*t^29 + 37349*t^28 + 1014*t^27 - 97630*t^26 - 11423*t^25 + 55440*t^24 + 27750*t^23 - 29240*t^22 + 
    146299*t^21 + 77097*t^20 + 175538*t^19 + 152712*t^18 - 178547*t^17 + 11789*t^16 - 75745*t^15 + 66542*t^14 - 
    137061*t^13 - 129353*t^12 + 171896*t^11 + 33129*t^10 - 117081*t^9 + 92744*t^8 - 127052*t^7 + 12355*t^6 - 
    87541*t^5 + 76885*t^4 - 45642*t^3 + 13372*t^2 - 29914*t + 1

**************************************************************************************************************/

declare verbose OverconvergentHeckeSeries, 3;

// **********************************************
// ****** OVERCONVERGENT HECKE SERIES CODE ******
// **********************************************

//  *** AUXILIARY CODE FOR GENERAL LEVEL ***

// Reverse characteristic polynomial.
// NOTE: it is important that the matrix is over IntegerRing() rather than pAdicRing(),
// otherwise it takes forever.

function ReverseCharacteristicPolynomial(A) // JAN 3, 2012
	
	P:=CharacteristicPolynomial(A);
	return ReciprocalPolynomial(P);

end function;

// Returns Eisenstein series E_k over given ring S modulo q^NN normalised
// to have constant term a_0 = 1.

function ESeries(k,NN,S)

	R<q> := PowerSeriesRing(S,NN);
	a1 := -S!(2*k/Bernoulli(k));
	Ek := 1 + a1*q;
	for n := 2 to NN-1 do
		coeffn := 0;
		divs := Divisors(n);
		for d in divs do
			coeffn := coeffn + d^(k-1);
		end for;
		Ek := Ek + a1*coeffn*q^n;
	end for;

	return Ek;

end function;

// Returns dimension of space of classical modular forms for char of weight k.
// NOTE: this computation is trivial *except* when the weight is one.

function DimensionMNk(char,k)

	if k gt 0 then
		M:=ModularForms(char,k); // space over Q, all conjugates
        deg:=Degree(Parent(char(1))); // number of conjugates
		return Integers()!(Dimension(M)/deg);
	elif ((k eq 0) and Order(char) eq 1) then // trivial character
		return 1;
	else // k < 0 or k = 0 with non-trivial character
		return 0;
	end if;

end function;

// Check kseq contains weights congruent modulo p-1.

function IsValidWeightSequence(kseq,p)

	len:=#kseq;
	if len eq 0 then
            return false, "must be nonempty";
	end if;
	
	k0:=kseq[1] mod (p-1);
	for i:=2 to len do
		if (kseq[i] mod (p-1)) ne k0 then
                    return false, "must be a sequence of integers " *
                                  "in a single congruence class mod (p-1)";
		end if;
	end for;

	return true, _;

end function;


// ******************************************
// ************** LEVEL N > 1 ***************
// ******************************************

// CLASSICAL MODULAR FORMS AND LINEAR ALGEBRA

// Converts a "modular form" (power series) with coefficients in a cyclotomic field
// Q(zeta) where Order(zeta)|(p-1) into a power series with coefficients in
// Z/(p^m), via a fixed choice zeta_pm of embedding of zeta in Zp.
// NOTE: this fails for trivial reasons when Q(zeta) = Q so is not used then. 

function qexpToPSinZpm(f,NN,degC,zeta_pm)

    Zpm:=Parent(zeta_pm);
    R<q>:=PowerSeriesRing(Zpm,NN);
    
    fPS:=R!0;
    for i:=0 to NN-1 do
        fi:=Coefficient(f,i);
        fi_pm:=&+[(Zpm!fi[j])*zeta_pm^(j-1): j in [1 .. degC]];
        fPS:=fPS + fi_pm*q^i;
    end for;

    return fPS;

end function;

// Computes a saturated basis for the space M_k(eps) of classical modular forms of
// weight k and level eps to precision q^qprec, assuming the class number of cyclotomic field
// Q(eps) is one.
// NOTE: the assumption on the class number is not that serious, but probably the rest of the
// code will be far too slow anyway in examples which are large enough for this not to be met.

function IntegralBasis(eps,k,qprec: is_cuspidal:=false)

    assert k ge 2;
    
    // When modular form space defined over Q
    if (2 mod Order(eps)) eq 0 then 
        // when R = Z the creation of ideals works differently
        // and it is simpler just to do the following ...
        if is_cuspidal eq false then
            M:=ModularForms(eps,k);
        else // cusp forms only
            M:=CuspForms(eps,k);
        end if;
        b:=Basis(M,qprec);
        C:=BaseRing(Parent(eps)); // cyclotomic field
        Cq:=PowerSeriesRing(C,qprec);
        return [Cq!f: f in b];
    end if;
    
    // Now consider case when space not over Q

    // Construct q-expansions of cuspidal space using modular symbols
    MM:=ModularSymbols(eps,k);
    SS:=CuspidalSubspace(MM);
    SSb:=qExpansionBasis(SS,qprec);
    
    // Directly compute eisenstein series
    M:=ModularForms(eps,k);
    if Dimension(M) eq 0 then
        return [];
    end if;
    sturm:=PrecisionBound(M);
    
    // Put coefficients in a matrix
    if is_cuspidal eq false then
        Es:=EisensteinSeries(M);
        dim:=#SSb + #Es;
    else // cusp forms only
        dim:=#SSb;
    end if;
    C:=BaseRing(Parent(eps)); // cyclotomic field
    
    A:=ZeroMatrix(C,dim,sturm);
    for i:=1 to #SSb do
        for j:=1 to sturm do
            A[i,j]:=Coefficient(SSb[i],j-1);
        end for;
    end for;
    if is_cuspidal eq false then
        for i:=#SSb + 1 to dim do
            for j:=1 to sturm do
                A[i,j]:=Coefficient(Es[i - #SSb],j-1);
            end for;
        end for;
    end if;
    
    // Create pseudomatrices for A and R^dim      
    R:=Integers(C);
    I1:=1*R;
    ps_A:=PseudoMatrix([I1: i in [1 .. dim]],A);
    ps_R:=PseudoMatrix(Module(R,sturm)); // R^sturm as pseudo matrix

    ps_Asat:=ps_A meet ps_R; // compute the intersection of the spaces
    // I believe one can also just saturate ps_A directly.

    assert ClassNumber(C) eq 1; // to ensure all ideals principal
    // NOTE: I think you should take second element in TwoElement(Is[i]) otherwise, and
    // this will be a local generator.
    
    Is:=CoefficientIdeals(ps_Asat);
    Is_gen:=[];
    for i:=1 to dim do // find generators for principal ideals
        _,gen:=IsPrincipal(Is[i]);
        Append(~Is_gen,gen);
    end for;
    Asat_vecs:=Matrix(ps_Asat);
    
    Asat:=ZeroMatrix(C,dim,sturm);
    for i:=1 to dim do
        for j:=1 to sturm do
            Asat[i,j]:=Is_gen[i]*Asat_vecs[i,j];
        end for;
    end for;
    
    // Find transformation matrix from A to Asat
    B:=Solution(A,Asat); // B*A eq Asat
    
    // Transform basis elements to full q-adic precision
    b:=[];
    Cq:=PowerSeriesRing(C,qprec);
    if is_cuspidal eq false then
        Mb:=[f: f in SSb] cat [PowerSeries(e,qprec): e in Es];
    else // cusp forms only
        Mb:=[f: f in SSb];
    end if;
    Mb_sat:=[**];
    for i:=1 to dim do
        f:=Cq!0;
        for j:=1 to dim do
            f:=f + B[i,j]*(Cq!Mb[j]);
        end for;
        Append(~Mb_sat,f);
    end for;
    
    return Mb_sat;
    
end function;

// Code for saturating the weight one basis output by ModularFormsBasis (from weight1 code).

// TO DO: saturation step also in ModularFormsBasis ?

function WeightOneSaturatedBasis(eps,qprec: is_cuspidal:=false)

    M2:=ModularForms(eps^2,2); 
    sturm:=PrecisionBound(M2);
    // this will be a sturm bound for weight one too
    qprec:=Maximum(qprec,sturm); // increase precision if too small

    Mb:=ModularFormsBasis(eps,1,qprec: Cuspidal:=is_cuspidal);
    
    if Mb eq [] then // saturation code gives segmentation fault with empty input.
        return [];
    end if;
    
    // Put coefficients in a matrix
    dim:=#Mb;
    C:=BaseRing(Parent(eps));
    
    A:=ZeroMatrix(C,dim,sturm);
    for i:=1 to #Mb do
        for j:=1 to sturm do
            A[i,j]:=Coefficient(Mb[i],j-1);
        end for;
    end for;
        
    if C eq Rationals() then
        Asat:=Saturation(A);
        B:=Solution(A,Parent(A)!Asat); // B*A eq Asat
    else
        R:=Integers(C);
        I1:=1*R;
        ps_A:=PseudoMatrix([I1: i in [1 .. dim]],A);
        ps_R:=PseudoMatrix(Module(R,sturm)); // R^sturm as pseudo matrix

        ps_Asat:=ps_A meet ps_R;

        assert ClassNumber(C) eq 1;
    
        Is:=CoefficientIdeals(ps_Asat);
        Is_gen:=[];
        for i:=1 to dim do // find generators for principal ideals
            _,gen:=IsPrincipal(Is[i]);
            Append(~Is_gen,gen);
        end for;
        Asat_vecs:=Matrix(ps_Asat);
    
        Asat:=ZeroMatrix(C,dim,sturm);
        for i:=1 to dim do
            for j:=1 to sturm do
                Asat[i,j]:=Is_gen[i]*Asat_vecs[i,j];
            end for;
        end for;
        B:=Solution(A,Asat); // B*A eq Asat
    end if;
    
    // constructed saturated code to full precision
    b:=[];
    Cq:=PowerSeriesRing(C,qprec);
    Mb_sat:=[**];
    for i:=1 to dim do
        f:=Cq!0;
        for j:=1 to dim do
            f:=f + B[i,j]*Mb[j];
        end for;
        Append(~Mb_sat,f);
    end for;
    
    return Mb_sat;

end function;

// Returns an integral (saturated) basis for the space of modular forms of weight 
// k and character eps, to q-expansion precision q^qprec. We assume here that
// the class number of Q(eps) is one.

function IntegralBasisAllWeights(eps,k,qprec: Cuspidal:=false)

    if k eq 1 then
        return WeightOneSaturatedBasis(eps,qprec: is_cuspidal:=Cuspidal);
    else    // k >= 2
        return IntegralBasis(eps,k,qprec: is_cuspidal:=Cuspidal);
    end if;
    
end function;   

// Constructs lists of integral bases in weight <= weightbound and characters powers of "char".
// These basis are saturated, but we require the class number of Q(char) to be one. 
// The output also includes a matching list of the characters, which are stored
// as their values on a set of generators for the multiplicative group modulo Modulus(char).
// (The characters will be multiplied later on, and this is a better way to store them.) A third
// output is a root of unity used to embed Z(char) into Z_p. Note that all modular forms 
// are thought of as power series having coefficients in Q(char), even if the coefficients really
// lie in a smaller field.

function LowWeightBasesWithCharEmbeddedInZp(eps,p,m,NN,weightbound) // m is really mdash here in the main function
	
	generators:=[];
	characters:=[];
    
    C:=Parent(eps(1)); // cyclotomic field or rationals
    degC:=Degree(C);
    if degC gt 1 then
        BasisC:=Basis(C);
        zeta:=BasisC[2];
        assert BasisC eq [zeta^i: i in [0 .. degC-1]];
        Zpm:=pAdicField(p,m);
        IntZpm:=IntegerRing(p^m);
        ZZ:=Integers();
        PolZpm:=PolynomialRing(Zpm);
        zeta_pm:=IntZpm!(ZZ!(Roots(PolZpm!MinimalPolynomial(zeta))[1][1])); // NOTE: chosen FIRST root here
    else // in this case zeta_pm is never used
        if Order(eps) eq 2 then
            zeta_pm:=-1;
        else
            zeta_pm:=1;
        end if;
    end if; 
    
    Cq:=PowerSeriesRing(C,NN);
    
    // February 19, 2013: speeding up multiplication of characters    
    ZZ:=Integers();
    Z_N:=Integers(Modulus(eps));
    U_N,m_N:=UnitGroup(Z_N);
    gens_N:=[ZZ!m_N(u): u in Generators(U_N)]; // generators
    
    S:=IntegerRing(p^m);
    Sq<q>:=PowerSeriesRing(S,NN);
    
	for k:=1 to weightbound do 
		basisweightk:=[];
		charsweightk:=[];
        for i:=0 to Order(eps)-1 do 
            b:=IntegralBasisAllWeights(eps^i,k,NN);
            randomb:=b;
			if #b gt 0 then // randomisation to remove echelon shape of basis.
				R:=Parent(b[1]);
				dimweightkchari:=#b;
				coeffsmat:=Random(GL(dimweightkchari,p));
				randomb:=[];
				for j:=1 to dimweightkchari do
					coeffsmatj:=coeffsmat[j];
					f:=R!0; 
					for l:=1 to dimweightkchari do
						f:=f + (Integers()!coeffsmatj[l])*b[l];
					end for;
					Append(~randomb,f);
				end for;
			else
				randomb:=b;
			end if;
            if degC eq 1 then
                for f in randomb do
                    Append(~basisweightk,Sq!f);
                    Append(~charsweightk,[(eps^i)(g): g in gens_N]); // represent character by value on generators
                end for;
            else // cyclotomic field
                for f in randomb do
                    Append(~basisweightk,qexpToPSinZpm(f,NN,degC,zeta_pm));
                    Append(~charsweightk,[(eps^i)(g): g in gens_N]); // represent character by value on generators
                end for;
            end if;
		end for;
		Append(~generators,basisweightk);
		Append(~characters,charsweightk);
        
	end for;
    
	return generators, characters, zeta_pm;

end function;

// Reduces the basis of low weight forms mod (p,q^elldash).

function LowWeightBasesModp(LWB,p,elldash)

	R:=PowerSeriesRing(GF(p),elldash);
	LWBModp:=[];	
	
	for i:=1 to #LWB do // weight k = i
		LWBModpWeightk:=[];
		for j:=1 to #LWB[i] do
			Append(~LWBModpWeightk,R!LWB[i][j]);
		end for;
		Append(~LWBModp,LWBModpWeightk);
	end for;
	
	return LWBModp;

end function;

// ***** CONSTRUCTION OF COMPLEMENTARY SPACES - VERSION B *****

/*

This is from March 2013. It is *very complicated* but seems significantly faster than the method "A" used in
the first magma distributed implementation. Here is a summary of how the complementary spaces are constructed.

(1) Given a character char, compute the q-expansions of all modular forms in spaces M_chi(k) for chi in <char> and
k <= weightbound, to suitable precision (p^mdash,q^elldashp). Coefficients are embedded in Z_p via the root of
unity zeta_pm. This is done using LowWeightBasesWithCharEmbeddedInZp and the output is LWB.

(2) Reduce these modular forms modulo (p,q^elldash), using LowWeightBasesModp. This list is LWBModp.

(3) Recursively construct the complementary spaces modulo (p,q^elldash) starting from LWBModp, and taking products
which have suitable weight and character. The *innovation in "B"* is that q-expansions in the complementary spaces
are appended to LWBModp, and used to construct later complementary spaces. This is done with ComplementarySpacesModp_B, and
the two preceding functions.

(4) The products of forms in LWBModp which give the elements in the complementary spaces are stored as "codes". These codes
are then used to construct the complementary spaces modulo (p^mdash,q^elldashp), using LWB and again updating this list
with the older complementary spaces to construct the newer ones. This is done in ComplementarySpaces_B

*/


// The output is a list [[a1,b1],....] where [ai,bi] is the bi character of
//      ** weight ai if ai <= Weightbound
//      ** weight k0 + (ai - weightbound)*(p-1) if ai > Weightbound
// and the product of the associated modular forms is a weight "weight" and character "char".
// 19/02/13: use new approach to handling characters where you store them as a list of
// their values on generators - this reduces MASSIVE overhead on multiplying characters.
// Note also that the input list of characters matches up with another list of modular forms
// and both are updated when computing the complementary spaces.

function RandomSolutionWithChar_B(characters,char_on_gens,char_on_gens_1,k0,j,p,weightbound)

    weight:=k0 + j*(p-1); // 08/04/03 - this is the target weight.
    // char_on_gens: this is just the characters "char" values on the generators of Z/N^* where N is the modulus. 
    // char_on_gens_1: this is just the value of the trivial character on these generators.
    
    if j eq 0 then
        B := weightbound; // problem is if j = 0 then taking B = weightbound - 1 we might not generate forms.
    else
        B := weightbound + (j-1); // start choosing from this position.
    end if;
     
	found := false;
    
	while found eq false do
		K := weight;
		sol := [];
        charprod:=char_on_gens_1; // just all ones vector of right length.
		a := [];
		// Choose elements in weights B,...,2.
		for i:=B to 2 by -1 do
            if #characters[i] gt 0 then // Nov 15: i.e. there are forms in that weight
                if i le weightbound then
                    ai := Random(0,Floor(K/i)); // pick ai elements of weight i
                    K := K - ai*i;
                else 
                    j_i:=i - weightbound; // so form in position i is weight k0 + j_i(p-1)
                    ai := Random(0,Floor(K/(k0 + j_i*(p-1))));
                    K := K - ai*(k0 + j_i*(p-1)); 
                end if; 
                for j:=1 to ai do
                    bij := Random(1,#characters[i]); // characters[i] = chars for weight i
                    charprod:=[charprod[l]*characters[i][bij][l]: l in [1 .. #charprod]]; // #charprod is 1 or 2.
                    Append(~sol,[i,bij]);
                end for;
            else
                ai:=0;
            end if;
		end for;
        // Feb 18, 2013: some code which will work even when nothing in weight one
        if #characters[1] gt 0 then // pick K elements in weight one
            for j:=1 to K do
                b1j := Random(1,#characters[1]);
                charprod:=[charprod[l]*characters[1][b1j][l]: l in [1 .. #charprod]]; // Feb 19, 2013
                Append(~sol,[1,b1j]);
            end for;
            if (charprod eq char_on_gens) then
                found := true;
            end if;
        else // nothing in weight one
            if (K eq 0) and (charprod eq char_on_gens) then
                found:=true;
            end if;
        end if;
	end while;
			
	sol:=Reverse(sol);
	
	return sol;

end function;


// Auxiliary function used in main loop of ComplementarySpacesModp

function RandomNewBasisModp_B(p,k0,j,LWBModp,OldBasisModp,weightbound,characters,char,char_on_gens,char_on_gens_1)
    
    k:=k0 + j*(p-1); // 08/04/13
    
    R:=Parent(LWBModp[2][1]);
    // this should be non-empty, since it is the space of weight two forms with trivial character.
    
    // Construct TotalBasisModp
	TotalBasisModp:=OldBasisModp; // Recall E_(p-1) = 1 mod p.
    elldash:=Degree(TotalBasisModp); // Steve 19/02/13: more efficient to use vector spaces than matrices.
	
	// Case k0 + i(p-1) = 0 + 0(p-1) = 0
	if ((k eq 0) and Order(char) eq 1) then // need trivial character and weight 0 to get anything  
        TotalBasisModp:=sub< V | V.1 > where V is VectorSpace(GF(p), Degree(TotalBasisModp)); // This is (1,0,0,...,0)
        return TotalBasisModp, [[]], LWBModp, characters; // June 18, 2013: we have not extended LWBModp here.
	elif k eq 0 then // non-trivial character in weight 0.
        // here [] should correspond to "nothing".
        return TotalBasisModp, [], LWBModp, characters; // June 18, 2013: we have not extended LWBModp here.
	end if;
	
	// Case k = k0 + i(p-1) > 0
	di:=DimensionMNk(char,k);
	diminus1:=DimensionMNk(char,k-(p-1)); 
    // NOTE: this wastes a little time when input weight k = 1 mod (p-1) since same dimension computed twice
    // and this computation is not trivial.
    
    mi:=di - diminus1;

    // Generate mi new forms in weight k.
	NewBasisCode:=[];
	rk:=diminus1;
	for i:=1 to mi do // extra forms
	    while (rk lt diminus1 + i) do
                        sol:=RandomSolutionWithChar_B(characters,char_on_gens,char_on_gens_1,k0,j,p,weightbound); // 19/02/13
			TotalBasisi:=R!1;
			TotalBasisiCode:=sol;
			for s in sol do
				TotalBasisi:=TotalBasisi*LWBModp[s[1]][s[2]];
			end for;
            // Steve 19/02/13: more efficient way of detecting when "new" modular form is found
            Include(~TotalBasisModp, Vector([Coefficient(TotalBasisi,j): j in [0 .. elldash-1]]), ~new);
            rk:=Dimension(TotalBasisModp);
	end while;
	Append(~NewBasisCode,TotalBasisiCode); // this one increased dimension.
        if j gt 0 then // this is case k0 + j(p-1) with j > 0
            Append(~LWBModp[weightbound + j],TotalBasisi); // add this new q-expansion to LWBModp
            Append(~characters[weightbound + j],char_on_gens); // add character "char" to list of characters
        end if;
	end for;
		
	return TotalBasisModp,NewBasisCode,LWBModp,characters;

end function;

// Finds complementary spaces modulo p and returns a list of "codes" describing
// what products of basis forms were chosen.

function ComplementarySpacesModp_B(p,k0,n,elldash,LWBModp,weightbound,characters,char)

    // 19/02/13: change to way characters are handled
    ZZ:=Integers();
    Z_N:=Integers(Modulus(char));
    U_N,m_N:=UnitGroup(Z_N);
    gens_N:=[ZZ!m_N(u): u in Generators(U_N)];
    char_on_gens:=[char(u): u in gens_N];
    char_on_gens_1:=[1: u in Generators(U_N)];  // trivial character

	CompSpacesCode:=[];
    ell:=DimensionMNk(char,k0 + n*(p-1)); 
    OldBasisModp:=sub< VectorSpace(GF(p),elldash) | >; // Steve 19/02/13
	for i:=0 to n do
        // Here we update both LWBModp and characters, appending the new q-expansions found.
        TotalBasisModp,NewBasisCodemi,LWBModp,characters:=RandomNewBasisModp_B(p,k0,i,LWBModp,OldBasisModp,weightbound,characters,char,char_on_gens,char_on_gens_1);
		Append(~CompSpacesCode,NewBasisCodemi);
		OldBasisModp:=TotalBasisModp; // basis for M_(k0 + i(p-1))
	end for;

	return CompSpacesCode;

end function;

// Constructs complementary spaces.

function ComplementarySpaces_B(p,k0,n,mdash,elldash,elldashp,weightbound,char,eps)

    // Find q-expansions for k <= weightbound mod (p^mdash,q^elldashp)
	LWB,characters,zeta_pm := LowWeightBasesWithCharEmbeddedInZp(eps,p,mdash,elldashp,weightbound);

    // Reduce modulo (p,q^elldash)
	LWBModp:=LowWeightBasesModp(LWB,p,elldash);
    
    // March 27, 2013: add extra lists to be filled in during the algorithm
    LWBModp:=LWBModp cat [[]: j in [1  .. n]];
    LWB:=LWB cat [[]: j in [1 .. n]];
    characters:=characters cat [[]: j in [1 .. n]];

	CompSpacesCode:=ComplementarySpacesModp_B(p,k0,n,elldash,LWBModp,weightbound,characters,char);

	// Reconstruct products mod (p^mdash,q^elldashp)
	
	W:=[];
	
	Epm1:=ESeries(p-1,elldashp,IntegerRing(p^mdash));

	
	OldBasis:=[];
	for i:=0 to n do
		CompSpacesCodemi:=CompSpacesCode[i+1];
		Wi:=[];
		for k:=1 to #CompSpacesCodemi do
			CompSpacesCodemik:=CompSpacesCodemi[k];	// this is a "sol"	
			Wik:=Parent(Epm1)!1;
			for j:=1 to #CompSpacesCodemik do 
                kminus1:=CompSpacesCodemik[j][1]; // 26/03/13: This is *not* k-1 any more, see immediately below.
				index:=CompSpacesCodemik[j][2];
                Wik:=Wik*LWB[kminus1,index];
                // In B the (k,a) in "code" will correspond to a form in weight k when 1 <= k <= weightbound
                // but otherwise in weight (k - weightbound)*(p-1) + k0.
                // In any case, the product of these forms will have the right weight and character.
			end for;
			Append(~Wi,Wik);
            if i gt 0 then // add new form to low weight basis.
                Append(~LWB[weightbound+i],Wik);
            end if;
		end for;
		Append(~W,Wi); 
	end for;

	return W, zeta_pm; // Nov 15, 2012: also return element used to embed cyclotomic ring in Zp.
    
end function;


// ***** AUXILIARY CODE: KATZ EXPANSIONS *****

// Returns basis of Katz Expansions modulo (p^mdash,q^elldashp) as a matrix
// of coefficients. These are (part of) a basis for the space of overconvergent
// modular forms of level N and weight k0.

function HigherLevelKatzExp(p,k0,m,mdash,n,elldash,elldashp,weightbound,char,eps)

	ordr:=1/(p+1); 
	S:=IntegerRing(p^mdash);
	Ep1:=ESeries(p-1,elldashp,S);
	R:=Parent(Ep1);
	q:=R.1;

	// construct basis as list of series

	W,zeta_pm:=ComplementarySpaces_B(p,k0,n,mdash,elldash,elldashp,weightbound,char,eps);
    
	KatzBasis:=[];
    Ep1minusj:=R!1; // 19/02/13 
    Ep1inv:=Ep1^(-1); // 19/02/13
	for j:=0 to n do
		Wj:=W[j+1];
		dimj:=#Wj;
		for i:=1 to dimj do
			wji:=Wj[i];
			b:=p^Floor(ordr*j)*wji*Ep1minusj;
			Append(~KatzBasis,b);
		end for;
        Ep1minusj:=Ep1minusj*Ep1inv; // 19/02/13 -  this is E_(p-1)^(-j) for next loop - very slightly faster
	end for;
   
	
	// extract basis as matrix
	
	ell:=#KatzBasis;
	M:=ZeroMatrix(S,ell,elldashp);
	for i:=1 to ell do
		for j:=1 to elldashp do
			M[i,j]:=Coefficient(KatzBasis[i],j-1);
		end for;
	end for;
	
	// M is only in echelon form modulo p: see comments below.
    return M,Ep1,zeta_pm;
    
    /*
    In the original magma distributed version we put M in echelon form - this is used only when we
    solve the triangular system T = AE. Here we do not - it is faster - and slightly modifiy
    the code for solving the triangular system to account for this.
    */

end function;

// Returns ldash, the Sturm bound for M_k(char).

function Computeelldash(p,char,k0,m)

	n:=Floor(((p+1)/(p-1))*(m+1));
	N:=Modulus(char);
	// From Page 173-174 Stein's book: Corollary 9.19 and 9.20
	ind:=Index(Gamma0(N));
	elldash:=Floor(((k0 + n*(p-1))*ind)/12) + 1;
	// This is a sturm bound for M(Gamma0(N),k), and hence also
	// for M(char,k) by Corollary 9.20 in Stein's book.

	return elldash;

end function;


// ***** MAIN FUNCTION FOR LEVEL N > 1 *****

// Returns matrix A modulo p^m in Step 5 of Algorithm 2 for each k in kseq.
// kseq has already been checked to have all weights congruent modulo (p-1).

function HigherLevelUpGj(p,kseq,m,weightbound,char)
    
    char:=MinimalBaseRingCharacter(char); // otherwise when order is 2 but domain not Q will crash.
    
    assert weightbound gt 1; // otherwise will crash for trivial reasons.
    
    eps:=char; 
    //  Here "char" is the character of the space of overconvergent modular forms and eps
    // can be taken to be *any other* character such that <eps> contains char. We just set eps:=char.
    
	// Step 1
	
	k0:=kseq[1] mod (p-1);
	
    elldash:=Computeelldash(p,char,k0,m);
	elldashp:=elldash*p;
	n:=Floor(((p+1)/(p-1))*(m+1));	 
	mdash:=m + Ceiling(n/(p+1));
	
	// Steps 2 and 3

	e,Ep1,zeta_pm:=HigherLevelKatzExp(p,k0,m,mdash,n,elldash,elldashp,weightbound,char,eps);

	ell:=Dimension(Parent(Transpose(e)[1]));
	S:=Parent(e[1,1]);

	// Step 4: March 24, 2012: changed to avoid doing anything when kdiv = 0.
    
    Aseq:=[];
    
    for k in kseq do
        kdiv:=k div (p-1);
        if kdiv eq 0 then
            u:=e;
        else;
            q := Parent(Ep1).1; 
            Ep1p := Evaluate(Ep1,q^p);
            Ep1pinv := Ep1p^-1;
            G := Ep1*Ep1pinv;
            Gkdiv := G^kdiv;
        
            u:=Parent(e)!0; // ell x elldashp zero matrix.
            for i:=1 to ell do 
                ei:=Parent(Gkdiv)![e[i][j]: j in [1 .. elldashp]]; // extract rows as q-expansions
                Gkdivei:=Gkdiv*ei; // act by G^kdiv
                for j:=1 to elldashp do // put back as rows of ak
                    u[i,j]:=Coefficient(Gkdivei,j-1);
                end for;
            end for;
        end if;

	// Step 5

        T:=ZeroMatrix(S,ell,elldash);
	
        for i:=1 to ell do
            for j:=1 to elldash do
                T[i,j]:=u[i,p*(j-1) + 1];
            end for;
        end for;
	
        // Step 6: Solve T = AE for A.

        A := ZeroMatrix(S,ell,ell);

        E := Parent(T)![[e[j,l]: l in [1 .. elldash]]: j in [1 .. ell]]; // March 25, 2012
        // NOTE: now E *not* in echelon form so code below is different.
        E,Q:=EchelonForm(E); // put smaller matrix E in echelon form.
        T:=Q*T; // apply same row operations to T
    
        E_leadingpos:=[Depth(E[j]): j in [1 .. ell]];
        // finding leading positions on each loop was wasting a lot of time.
        // NOTE: the function Depth(u) should give index of first non-zero entry.
    
        for i := 1 to ell do
            Ti := T[i];		
            for j := 1 to ell do
                ej := E[j]; // March 25, 2012.
                ejleadpos:=E_leadingpos[j];
                lj:=Integers()!ej[ejleadpos];
                A[i,j] := S!((Integers()!Ti[ejleadpos])/lj);
                Ti := Ti - A[i,j]*ej;
            end for;
        end for;
        
        Append(~Aseq,MatrixRing(IntegerRing(p^m),ell)!A);
		
    end for;
        
	return Aseq,zeta_pm;

end function;


// ********************************
// *********** LEVEL 1 ************
// ********************************

// Returns dimension of space of modular forms of weight k and level 1.

function DimensionMk(k)

	if ((k mod 2) eq 1) or (k lt 0) then
		return 0;
	end if;
	kmod12 := k mod 12;
	if (kmod12 eq 2) then
		return Floor(k/12);
	else
		return Floor(k/12) + 1;
	end if;

end function;

// Returns basis for W_i (those elements in the Miller basis of weight k which 
// are not in E_(p-1) x {weight (k - (p-1)) forms} and a power of delta
// which can be reused on the next call of function.

function ComputeWi(k,p,delta,deltaj,E4,E6)
	
	// Define a and b
	a := k mod 3;
	b := (k div 2) mod 2;
		
	// Compute dimensions required for Miller basis
	d := DimensionMk(k) - 1;
	e := DimensionMk(k - (p-1)) - 1;
	
	// Construct basis for Wi
	Wi := [];
	for j := e+1 to d do
		// compute aj = delta^j*E6^(2*(d-j) + b)*E4^a
		aj := deltaj*E6^(2*(d-j) + b)*E4^a;
		deltaj := deltaj*delta;
		Wi := Append(Wi,aj);
	end for;

	return Wi,deltaj;

end function;

// AUXILIARY CODE: KATZ EXPANSIONS

// Returns list e of Katz expansions e_(i,s) from Step 3 of Algorithm 1
// and E_(p-1) for use in Step 4.

function KatzExpansions(k0,p,ellp,mdash,n)
	
	S := IntegerRing(p^mdash); 
	Ep1 := ESeries(p-1,ellp,S);

	E4 := ESeries(4,ellp,S);
	E6 := ESeries(6,ellp,S);
	q := Parent(E4).1;
	delta := Delta(q);
	
	deltaj := Parent(delta)!1;
	e := [];	
	for i := 0 to n do
		Wi,deltaj := ComputeWi(k0 + i*(p-1),p,delta,deltaj,E4,E6);
		for bis in Wi do
			eis := p^Floor(i/(p+1))*Ep1^(-i)*bis;
			e := Append(e,eis);
		end for;
	end for;
	
	return e,Ep1;

end function;	

// ***** MAIN FUNCTION FOR LEVEL 1 *****

// Returns matrix A modulo p^m from Step 6 of Algorithm 1 for each k on kseq.
// kseq has weights congruent modulo (p-1).

// Notational change from paper: In Step 1 following Wan we defined j by
// k = k_0 + j(p-1) with 0 <= k_0 < p-1. Here we replace j by kdiv so that
// we may use j as a column index for matrices.

function Level1UpGj(p,kseq,m) 
 
	// Step 1

	k0 := kseq[1] mod (p-1);
	n := Floor(((p+1)/(p-1)) * (m+1));
	ell := DimensionMk(k0 + n*(p-1));
	ellp := ell*p;
	mdash := m + Ceiling(n/(p+1));

	// Steps 2 and 3

	e,Ep1 := KatzExpansions(k0,p,ellp,mdash,n);
	
	// Step 4

	q := Parent(Ep1).1; 
	Ep1p := Evaluate(Ep1,q^p);
	Ep1pinv := Ep1p^-1;
	G := Ep1*Ep1pinv;
	Aseq:=[];
	
	for k in kseq do
		kdiv := k div (p-1);
		Gkdiv := G^kdiv;
		u := [];
		for i := 1 to ell do
			ei := e[i];
			ui := Gkdiv*ei;
			u := Append(u,ui);
		end for;
	
		// Step 5 and computation of T in Step 6

		S := Parent(Coefficient(e[1],0));
		T := ZeroMatrix(S,ell,ell);
	
		for i := 1 to ell do
			for j := 1 to ell do
				T[i,j] := Coefficient(u[i],p*(j-1));
			end for;
		end for;
	
		// Step 6: solve T = AE using fact E is upper triangular.
		// Warning: assumes that T = AE (rather than pT = AE) has 
		// a solution over Z/(p^mdash). This has always been the case in 
		// examples computed by the author, see Note 3.1.

		A := ZeroMatrix(S,ell,ell);
	
		for i := 1 to ell do
			Ti := T[i];		
			for j := 1 to ell do
				ej := Parent(Ti)![Coefficient(e[j],l-1): l in [1 .. ell]];
				lj := Integers()!ej[j];
				A[i,j] := S!((Integers()!Ti[j])/lj);
				Ti := Ti - A[i,j]*ej;
			end for;
		end for;			

		// Append A mod p^m to Aseq.
		
		Append(~Aseq,MatrixRing(IntegerRing(p^m),ell)!A); // JAN 3, 2012

	end for;

	return Aseq,1;

end function;


// *******************************************
// ***** MAIN FUNCTION FOR GENERAL LEVEL *****
// *******************************************

intrinsic OverconvergentHeckeSeries(p::RngIntElt, char::GrpDrchElt, kseq::SeqEnum[RngIntElt], m::RngIntElt:
WeightBound:= IsOdd(char) select 3 else 6) -> SeqEnum, RngPadElt

{Returns the reverse characteristic series of the U_p operator on the 
space of p-adic overconvergent modular forms of character eps and weight k for each k in kseq, 
for each k in kseq, and a p-adic integer used to embed the cyclotomic field Q(char) in the p-adic field.  
Here kseq is a sequence of integer weights all congruent modulo (p-1). The result is correct modulo (p^m). 
They are returned as a sequence of polynomials over pAdicRing(p,m) and an element in pAdicRing(p,m).}

    require p ge 5 and IsPrime(p) : "The first argument must be a prime >= 5";
    require m ge 1 : "The fourth argument must be a positive integer";
    require ((Modulus(char) mod p) ne 0) : "The first argument must not divide the modulus of the second argument";
    bool, message := IsValidWeightSequence(kseq,p);
    require bool : "The third argument " * message;
    require ((p-1) mod Order(char)) eq 0 : "The order of second argument must divide p-1, where p is the first argument";
    require char(-1) eq (-1)^kseq[1]: "The space of overconvergent modular forms must be non-zero";
    require WeightBound ge 2: "The optional parameter WeightBound must be at least 2";
    
    Zp:=pAdicRing(p,m);
    PolZp<t> := PolynomialRing(Zp); // JAN 3, 2012: added variable name.
    
    if Modulus(char) eq 1 then
        Aseq,zetapm:=Level1UpGj(p,kseq,m);
    else
        Aseq,zetapm:=HigherLevelUpGj(p,kseq,m,WeightBound,char);
    end if; 
    
    Pseq:=[];
	for A in Aseq do
		P:=ReverseCharacteristicPolynomial(A); // P is over IntegerRing(p^m)
		Append(~Pseq,PolZp!P);
	end for;
	
    return Pseq,Zp!zetapm;
    
end intrinsic;

intrinsic OverconvergentHeckeSeries(p::RngIntElt, N::RngIntElt, kseq::SeqEnum[RngIntElt], m::RngIntElt: WeightBound:=6) -> SeqEnum

{Returns the reverse characteristic series of the U_p operator on the 
space of p-adic overconvergent modular forms of level N and weight k for each k in kseq.
Here kseq is a sequence of integer weights all congruent modulo (p-1).
The result is correct modulo (p^m).
It is returned as a sequence of polynomials over pAdicRing(p,m).}

    require p ge 5 and IsPrime(p) : "The first argument must be a prime >= 5";
    require N ge 1 : "The second argument must be a positive integer or Dirichlet character";
    bool, message := IsValidWeightSequence(kseq,p);
    require bool : "The third argument " * message;
    require m ge 1 : "The fourth argument must be a positive integer";
    require ((N mod p) ne 0) : "The first argument must not divide the second argument";
    require IsEven(N) eq false: "The space of modular forms must be non-zero";
    require WeightBound ge 2: "The optional parameter WeightBound must be at least 2";
    
        G:=DirichletGroup(N);
        char:=G!1;
	
        Pseq := OverconvergentHeckeSeries(p, char, kseq, m: WeightBound:=WeightBound);
        return Pseq;

end intrinsic;

intrinsic OverconvergentHeckeSeries(p::RngIntElt, N::RngIntElt, k::RngIntElt, m::RngIntElt: WeightBound:=6) -> RngUPolElt

{Returns the reverse characteristic series of the U_p operator on the 
space of p-adic overconvergent modular forms of level N and weight k. 
The result is correct modulo (p^m).
It is returned as a polynomial over pAdicRing(p,m).}

    require p ge 5 and IsPrime(p) : "The first argument must be a prime >= 5";
    require N ge 1 : "The second argument must be a positive integer";
    require m ge 1 : "The fourth argument must be a positive integer";
    require ((N mod p) ne 0) : "The first argument must not divide the second argument";
    require IsEven(N) eq false: "The space of overconvergent modular forms must be non-zero";
    require WeightBound ge 2: "The optional parameter WeightBound must be at least 2";
	
        G:=DirichletGroup(N);
        char:=G!1;
    
        Pseq := OverconvergentHeckeSeries(p, char, [k], m: WeightBound:=WeightBound);
        return Pseq[1];

end intrinsic;

intrinsic OverconvergentHeckeSeries(p::RngIntElt, char::GrpDrchElt, k::RngIntElt, m::RngIntElt: 
WeightBound:= IsOdd(char) select 3 else 6) -> RngUPolElt, RngPadElt

{Returns the reverse characteristic series of the U_p operator on the 
space of p-adic overconvergent modular forms of character char and weight k, and
a p-adic integer used to embed the cyclotomic field Q(char) in the p-adic field. 
The result is correct modulo (p^m).
They are returned as a polynomial over pAdicRing(p,m) and an element in pAdicRing(p,m).}

    require p ge 5 and IsPrime(p) : "The first argument must be a prime >= 5";
    require ((Modulus(char) mod p) ne 0) : "The first argument must not divide the modulus of the second argument";
    require m ge 1 : "The fourth argument must be a positive integer";
    require char(-1) eq (-1)^k: "The space of overconvergent modular forms must be non-zero";
    require WeightBound ge 2: "The optional parameter WeightBound must be at least 2";
	
        Pseq,zetapm := OverconvergentHeckeSeries(p,char, [k], m: WeightBound:=WeightBound);
        return Pseq[1],zetapm;

end intrinsic;

// Writing A := UpGj(p,N,k,m), the function returns d with deg(det(1 - At)) <= d.
// Uses Lemma 3.1. in D. Wan "Dimension variation of classical
// and p-adic modular forms", Invent. Math. 133, (1998) 449-463.

intrinsic OverconvergentHeckeSeriesDegreeBound(p::RngIntElt, N::RngIntElt, k::RngIntElt, m::RngIntElt) -> RngIntElt

{Returns a bound on the degree of the characteristic series P(t) modulo p^m of the Atkin U_p operator
on the space of overconvergent p-adic modular forms of (even) weight k and level Gamma_0(N).
(This bound is due to Daqing Wan.  The bound depends only on k modulo (p-1), not on k itself).}

    require p ge 5 and IsPrime(p) : "The first argument must be a prime >= 5";
    require N ge 1 : "The second argument must be a positive integer";
    require m ge 1 : "The fourth argument must be a positive integer";
    require ((N mod p) ne 0) : "The first argument must not divide the second argument";
    
    if IsOdd(k) eq true then
        return 0;
    end if;

        chi := DirichletGroup(N)! 1;

	k0:=k mod (p-1);
	ds:=[DimensionMNk(chi, k0)];
	ms:=[ds[1]];
	sum:=0;
	u:=1;
		
	repeat
		Append(~ds,DimensionMNk(chi, k0 + u*(p-1)));
		Append(~ms,ds[u+1] - ds[u]);
		sum:=sum + u*ms[u+1];
		ord:=Floor(((p-1)/(p+1))*sum - ds[u+1]);
		u:=u+1;
	until ord ge m;	

	return (ds[u]-1);	

end intrinsic;

