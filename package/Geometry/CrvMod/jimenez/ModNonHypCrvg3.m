freeze;
// 04/12/2011

/******************************************************
*                                                     *           
*          Enrique Gonzalez-Jimenez                   *         
*                                                     *   
*              FILE: ModNonHypCrvg3.m                 *                        
*   (Modular Non Hyperelliptic Curves of genus 3)     *                              
*                                                     *
******************************************************/

import "MAV.m": Chi,chi;

//  References:

//  [GJO]  Enrique Gonzalez-Jimenez, Roger Oyono "Non-hyperelliptic modular curves of genus 3". Journal of Number Theory 130, no. 4, 862-878 (2010). 

//////////////////////////////////////////////////////////////////////////////

//----------------------------------------------------------------------------

function Caseg3(F,verbose)
// Given F a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq for a modular abelian threefold B.
// This function determines if there exists a modular non-hyperelliptic  genus 3 curve C : P(x,y,z)=0  such that Jac( C) is Q-isogenous to B.
// In the affirmative case, it returns the degree 4 homogeneous polynomial P.
// cf. Proposition 2 [GJO]

  g:=#F; if g ne 3 then return false,"ERROR1: genus must be 3"; end if;
  m:=Max([Degree(f) : f in F]);
  Q:=Rationals();
  Qq<q>:=LaurentSeriesRing(Q);
  P<x,y,z> := ProjectiveSpace(Q,2);
  
  X:=F[1];
  Y:=F[2];
  Z:=F[3];

  S:=[Z^4,Y*Z^3,Y^2*Z^2,Y^3*Z,Y^4,X*Z^3,X*Y*Z^2,X*Y^2*Z,X*Y^3,X^2*Z^2,X^2*Y*Z,X^2*Y^2,X^3*Z,X^3*Y,X^4];
  s:=[z^4,y*z^3,y^2*z^2,y^3*z,y^4,x*z^3,x*y*z^2,x*y^2*z,x*y^3,x^2*z^2,x^2*y*z,x^2*y^2,x^3*z,x^3*y,x^4];

  A:=[[Coefficient(S[i],j) : j in [1..m-1]]:i in [1..15]];
  ss:=KernelMatrix(Matrix(A));

  if IsZero(ss) or NumberOfRows(ss) ne 15-14 then return false,"ERROR2: No Non-hyperelliptic curve of genus 3"; end if;

  Res:=&+[ss[1][i]*S[i] : i in [1..15]];

  if IsWeaklyZero(Res) then Ecuacion:=&+[ss[1][i]*s[i] : i in [1..15]];
	C:=Curve(P,Ecuacion); 
	if IsIrreducible(C) and IsNonSingular(C) then 
		ecu:=Ecuacion; 
	else return false,"ERROR3: Curve no irreducible or Singular";
	end if;
  else 
	return false,"ERROR2: No Non-hyperelliptic curve of genus 3"; 
  end if;

//----- Psi_F(q) -----//
  Fy:=Evaluate(Derivative(ecu,y),[X,Y,Z]);
  psi:=q*(Z*Derivative(X)-X*Derivative(Z))/Fy;
  
  if Degree(psi) ne 0 then return false,"ERROR6: Psi_F(q) not in Q!!!!"; 
    else 
	if verbose eq 1 then printf "Psi_F(q) = %o\n",psi; end if;
  end if;
//--------------------//  

return true, ecu;

end function;


function Caseg3new(F,verbose)
// Given F a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq for a NEW modular abelian threefold B.
// This function determines if there exists a NEW modular non-hyperelliptic genus 3 curve C : P(x,y,z)=0  such that Jac( C) is Q-isogenous to B.
// In the affirmative case, it returns the degree 4 homogeneous polynomial P.
// cf. Proposition 2 & Lemma 3 [GJO]

  g:=#F; if g ne 3 then return false,"ERROR1: genus must be 3"; end if;
  m:=Max([Degree(f) : f in F]);
  Q:=Rationals();
  Qq<q>:=LaurentSeriesRing(Q);
  P<x,y,z> := ProjectiveSpace(Q,2);
  
  A:=Matrix([[Q!Coefficient(F[1],i),Coefficient(F[2],i),Coefficient(F[3],i)] : i in [1..m]]);
  A:=Transpose(A);
  E,T:=EchelonForm(A);

  X:=&+[E[1][k]*q^k : k in [1..m]]+O(q^m);
  Y:=&+[E[2][k]*q^k : k in [1..m]]+O(q^m);
  Z:=&+[E[3][k]*q^k : k in [1..m]]+O(q^m);

  n:=Valuation(Z);

//  printf "Valuation(Z) = %o\n",n;
  
  case n:
     when 3:
        S:=[X^3*Z,X^2*Y^2,X^2*Y*Z,X*Y^3,X^2*Z^2,X*Y^2*Z,Y^4,X*Y*Z^2,Y^3*Z,X*Z^3,Y^2*Z^2,Y*Z^3,Z^4];
        s:=[x^3*z,x^2*y^2,x^2*y*z,x*y^3,x^2*z^2,x*y^2*z,y^4,x*y*z^2,y^3*z,x*z^3,y^2*z^2,y*z^3,z^4];
     when 4:
        S:=[X^3*Z,X*Y^3,X^2*Y*Z,Y^4,X*Y^2*Z,X^2*Z^2,Y^3*Z,X*Y*Z^2,Y^2*Z^2,X*Z^3,Y*Z^3,Z^4];
        s:=[x^3*z,x*y^3,x^2*y*z,y^4,x*y^2*z,x^2*z^2,y^3*z,x*y*z^2,y^2*z^2,x*z^3,y*z^3,z^4];
      when 5:
        S:=[X^3*Z,Y^4,X^2*Y*Z,X*Y^2*Z,Y^3*Z,X^2*Z^2,X*Y*Z^2,Y^2*Z^2,X*Z^3,Y*Z^3,Z^4];
        s:=[x^3*z,y^4,x^2*y*z,x*y^2*z,y^3*z,x^2*z^2,x*y*z^2,y^2*z^2,x*z^3,y*z^3,z^4];
      else
        return false, "ERROR2: Valuation(Z) must be in [3,4,5]";
 end case;

  A:=[[Coefficient(S[i],j) : j in [1..m-1]]:i in [1..#S]];
  ss:=KernelMatrix(Matrix(A));

  if IsZero(ss) or NumberOfRows(ss) ne 1 then return false,"ERROR3: NO Non-hyperelliptic modular curve of genus 3"; end if;

  Res:=&+[ss[1][i]*S[i] : i in [1..#S]];

  if IsWeaklyZero(Res) then Ecuacion:=&+[ss[1][i]*s[i] : i in [1..#s]];
	C:=Curve(P,Ecuacion); 
	if IsIrreducible(C) and IsNonSingular(C) then 
		ecu:=Ecuacion; 
	else return false,"ERROR4: Curve no irreducible or Singular";
	end if;
  else 
	return false,"ERROR5: NO Non-hyperelliptic modular curve of genus 3"; end if;

//----- Psi_F(q) -----//

  Fy:=Evaluate(Derivative(ecu,y),[X,Y,Z]);
  psi:=q*(Z*Derivative(X)-X*Derivative(Z))/Fy;
  
  if Degree(psi) ne 0 then return false,"ERROR6: Psi_F(q) not in Q!!!!"; 
   else 
	if verbose eq 1 then printf "Psi_F(q) = %o\n",psi; end if;
  end if;
//--------------------//  

return true, ecu;

end function;

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------

intrinsic NewModularNonHyperellipticCurveGenus3(F::[RngSerPowElt]) -> BoolElt, RngMPolElt
{
Returns whether a NEW modular non-hyperelliptic genus 3 curve exists attached to a NEW modular abelian threefold B, 
where F is a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq.
If so, also returns the quartic defining polynomial of the curve.
}
	verbose := GetVerbose("ModularCurve");
	boo,P :=  Caseg3new(F,verbose);
	if boo then return boo,P; else
	return false,_; end if;
	
end intrinsic;

//----------------------------------------------------------------------------

function Zbase(B,m)
// Given a NEW modular abelian variety B by a sequences of Q-simple NEW modular abelian varieties as Modular Symbols,
// this function computes a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq
        qQ:=[];     
	for A in B do 
		fs:=qIntegralBasis(A,m);
		for f in fs do
               		qQ:=Append(qQ,f);
		end for;
	end for;
        
	return qQ;

end function;

//----------------------------------------------------------------------------

intrinsic NewModularNonHyperellipticCurveGenus3(B::[ModSym]: prec:=100, check:=false, gamma:=1) -> BoolElt, RngMPolElt
{
Returns whether a NEW modular non-hyperelliptic genus 3 curve exists attached to a NEW modular abelian threefold B.
If so, also returns the quartic defining polynomial of the curve.
}
// It must be use check:=true if one wants to prove that the curve obtained C:P(x,y,z)=0 satisfies that C is NEW and Jac( C) is Q-isogenous to B.
// Otherwise (i.e. if one uses check:=false) it is just an approximation.
// (cf. Proposition 3 [GJO])

	verbose := GetVerbose("ModularCurve");        
	N:=Level(B[1]);                                            
	if check then 
		case gamma:
		   when 1: prec:=Ceiling(Index(Gamma1(N)))+30;
		   when 0: prec:=Ceiling(Index(Gamma0(N)))+30;
		end case;
	end if;
	F:=Zbase(B,prec);
	boo,P := Caseg3new(F,verbose);
	if boo then return boo,P; else
	return false,_; end if;
		
end intrinsic;

//----------------------------------------------------------------------------



//----------------------------------------------------------------------------

intrinsic ModularNonHyperellipticCurveGenus3(F::[RngSerPowElt]) -> RngMPolElt
{
Returns whether a modular non-hyperelliptic genus 3 curve exists attached to a modular abelian threefold B, 
where F is a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq.
If so, also returns the quartic defining polynomial of the curve.
}

	verbose := GetVerbose("ModularCurve");
	boo,P :=  Caseg3(F,verbose);
	if boo then return boo,P; else
	return false,_; end if;
	
end intrinsic;
//----------------------------------------------------------------------------


///////////////////////////////////////////////////////////////////////////
// All the NEW Non-hyperelliptic curves of genus 3 and a given level N
///////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////////
function BoundedESubspace(eps, range) 
//Returns the newform subspaces of weight 2 and Nebentypus character eps corresponding to
//newforms for which the field E=K_f has degree over Q in the given range

// Ripped from the function BoundedFSubspace from building_blocks.m

    eps := MinimalBaseRingCharacter(eps);
    N := Modulus(eps);
    k:=2;
    M := NewSubspace(CuspidalSubspace(ModularSymbols(eps,k,1)));
    P := []; p:=1;
    while #P lt 5 do
        p := NextPrime(p);
        if N mod p ne 0 then Append(~P,p); end if;
    end while;

    for p in P do
	if Dimension(M) eq 0 then return []; end if;
        hecke_f := HeckePolynomial(M,p);
        deg := 0; for f in Factorisation(hecke_f) do deg := deg + Degree(f[1])*f[2]; end for;
        if deg ne Degree(hecke_f) then
            print "!!!!! Bug in polynomial factorisation !!!!!";
        else;
        pol := Parent(hecke_f)!1;
        for f in [x[1] : x in Factorisation(hecke_f)] do
            ff := Factorisation(f)[1,1];
            deg := Max([Degree(MinimalPolynomial(x)) : x in Coefficients(ff)]);
            if deg*Degree(ff) le Max(range) then pol := pol*f; end if;
        end for;
        M := Kernel([<p,pol>],M); 	
        end if;
    end for;

    MM := NewformDecomposition(M);
    MM := [x : x in MM | Dimension(x)*Degree(BaseRing(x)) in range];
    MM := SortDecomposition(MM);
    return MM;
end function;
///////////////////////////////////////////////////////////////////////////

function ZXNonhyperGenus3(N,gamma,m)
// This function computes a sequence of sequences of q-expansions (up to precision:=m) of the elements of a rational basis of H^0(Af,Omega^1)q/dq 
// where the Af's are NEW modular abelian variety of level N and Dirichlet character of order 1,2,3,4 or 6 and Dimension(Af)=1 or Dimension(Af)=3 and 2 not dividing N; and Dimension(Af)=2 otherwise

  qQ:=[];
  G:=Chi(N);
  	
  G:=[seq : seq in G | Order(chi(N,seq)) in [1,2,3,4,6]]; // 1 <= [Q(eps):Q]=EulerPhi(Ord(eps)) <= 2
  seq0:=[seq : seq in G | Order(chi(N,seq)) eq 1][1]; // trivial character
 
  if gamma eq 1 then G:=G; else G:=[seq0]; end if;

  for seq in G do 
	eps:=chi(N,seq);
	A2:=BoundedESubspace(eps,[2]);
	for B in A2 do 
		f:=qIntegralBasis(B,m);
               	qQ:=Append(qQ,f);
	end for; 
  end for;


  if N le 130000 then 
	D:=CremonaDatabase();
  	isog:=NumberOfIsogenyClasses(D, N);
  	if isog eq 0 then A1:=[]; end if;
  	A1:=<ModularSymbols(EllipticCurve(D, N, k, 1),1) : k in [1..isog]>;
	for B in A1 do 
		f:=qIntegralBasis(B,m);
               	qQ:=Append(qQ,f);
	end for; 
    else
	A1:=BoundedESubspace(chi(N,seq0),[1]);
	for B in A1 do 
		f:=qIntegralBasis(B,m);
               	qQ:=Append(qQ,f);
	end for; 
  end if; 
 
if (N mod 2) ne 0 then // In the Q-simple case is not posible that 2 | N (cf. Prop 7.7(ii) and 7.8(i) [BGJGP])
  A3:=BoundedESubspace(chi(N,seq0),[3]);
  for B in A3 do 
	f:=qIntegralBasis(B,m);
        qQ:=Append(qQ,f);
  end for;
end if;

return qQ;

end function;

//----------------------------------------------------------------------------

function Dequal(d,g)
// Given d:=[d1,..,dn], this function returns all the subsequences S in [1..n] such that &+[dk : k in S] = g

	L:=[];
	S:={1..#d};
	P:=Subsets(S);
	P:=[set : set in P | set ne {}];
	for p in P do l:=[d[k] : k in p]; if &+l eq g then L:=Append(L,Setseq(p)); end if; end for;
	return L;
end function;

///////////////////////////////////////////////////////////////////////////


intrinsic NewModularNonHyperellipticCurvesGenus3(N::RngIntElt : check:=false, gamma:=1, prec:=100) -> SeqEnum
{
The defining equations of ALL the NEW Modular Non-Hyperelliptic Curves of Genus 3 parametrized by X_1(N).
}
// NEW Modular Non-Hyperelliptic Curves of genus 3 parametrized from X_gamma
// If gamma:=1 then X_gamma=X_1(N). If gamma:=0 then X_gamma=X_0(N). 

	verbose := GetVerbose("ModularCurve");

	QQ := PolynomialRing(RationalField()); x := QQ.1;
	if (Type(gamma) ne RngIntElt) or ((gamma ne 0) and (gamma ne 1)) then
	    error "Parameter gamma should be 0 or 1";
	end if;
	if check then 
		case gamma:
		   when 1: prec:=Ceiling(Index(Gamma1(N)))+30;
		   when 0: prec:=Ceiling(Index(Gamma0(N)))+30;
		end case;
	end if;
	B:=ZXNonhyperGenus3(N,gamma,prec);
	d:=[#b : b in B];
	L:=Dequal(d,3);

	//--------------
	if verbose ge 1 then
		printf "\n     Candidates:=%o\n",#L;
	end if;
	//--------------
	curves:=[];
        cont:=0;	
	for i in [1..#L] do a:=L[i]; if verbose eq 1 then cont:=cont+1; printf "%o ",cont; end if;
		LL:=[];
		for b in a do
			for c in B[b] do
				LL:=Append(LL,c);
			end for;
		end for; 
	        boo,P:=Caseg3new(LL,verbose);
		if boo then curves:=Append(curves,P); end if;
		//--------------
		if verbose eq 2 then
			if boo then 
				printf  "[(%o)]---------------> NewMNonHC[%o,%o]:=%o;\n", i,N,a,P;
			else 
				printf  "  %o  ---------------> NO NewMNonHC of level %o for : %o;\n",i,N,a;
			end if;
		end if;
		//--------------
		
		
	end for;
	if verbose eq 1 then  printf "%o\n\n"," "; end if;
	return curves;

end intrinsic;

//----------------------------------------------------------------------------

/////// NOT USED ////// In the Jo(N) case is not posible that 4 | N (cf. Prop 7.7(ii) [BGJGP])


