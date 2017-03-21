freeze;
// 04/12/2011

/**************************************************
*                                                 *                                                                    
*        Enrique Gonzalez-Jimenez                 *         
*                                                 *
*          FILE: NewModHypCrv.m                   *
*     (New Modular Hyperelliptic Curves)          *                              
*                                                 *
**************************************************/

import "MAV.m": Chi,chi;

//  References:
//  [GJG]  E. Gonzalez-Jimenez, J. Gonzalez, "Modular curves of genus 2". Math. Comp. 72, no. 241, 397-418, (2003). 
//  [BGJGP] M. H. Baker, E. Gonzalez-Jimenez, J. Gonzalez, B. Poonen, "Finiteness Results for modular curves of genus at least 2". Amer. J. Math. 127, no. 6, 1325-1387, (2005).

//----------------------------------------------------------------------------
// BOUNDS

function Bound(N,gamma,g)
// cf. Lemma 6.6 [BGJGP]
      case gamma:
        when 0: gg:=DimensionCuspFormsGamma0(N,2); 
        when 1: gg:=DimensionCuspFormsGamma1(N,2); 
        else return "ERROR: Wrong Input";
      end case;
      cN:=4*(g+1)*(gg-1)+1;
      return cN+100;

end function;

//----------------------------------------------------------------------------

function Case(F)
// Given F a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq for a NEW modular abelian variety B.
// This function determines if there exists a new modular hyperelliptic curve C : y^2=f(x) such that Jac( C) is Q-isogenous to B.
// In the affirmative case, it determines if degree(f) is even or odd.
// cf. Lemma 6.1 & Proposition 6.5 [BGJGP]
	g:=#F;
	Mg:=MatrixAlgebra(Rationals(),g);
	Q<q>:=LaurentSeriesRing(RationalField());
	QQ := PolynomialRing(RationalField()); x := QQ.1;
	MQg:=MatrixAlgebra(Q,g);
	MQg1:=KMatrixSpace(Q,g,1);

	mF:=Mg![Coefficient(F[j],i) : i in [1..g] , j in [1..g]];
	L,P,Q:=SmithForm(mF);
	FF:=(MQg!P)*(MQg1!F);	

	v:=[Valuation(FF[i][1]):i in [1..g]];

	if v eq [i : i in [1..g]] then
		Feven:=[FF[i][1] : i in [1..g]];
		return(<"even", Feven>);
	end if;

	mF:=Mg![Coefficient(F[j],2*i-1) : i in [1..g] , j in [1..g]];
	L,P,Q:=SmithForm(mF);
	FF:=(MQg!P)*(MQg1!F);	
	v:=[Valuation(FF[i][1]):i in [1..g]];

	if v eq [2*i-1 : i in [1..g]] then
		Fodd:=[FF[i][1] : i in [1..g]];
		return(<"odd", Fodd>);
	end if;
	
	return(["no","no"]);
end function; 
  
function CaseEven(F)
// Given F a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq for a NEW modular abelian variety B.
// Assuming that there exists a new modular hyperelliptic curve C : y^2=f(x) such that Jac( C) is Q-isogenous to B and degree(f) is EVEN,
// this function returns f(x).
// cf. Lemma 6.1 & Proposition 6.5 [BGJGP]

	g:=#F;
	Q<q>:=LaurentSeriesRing(RationalField());
	QQ := PolynomialRing(RationalField()); x := QQ.1;
	
	h1:=F[g-1];
 	h2:=F[g];
 	X:=h1/h2;
 	X:=X/Coefficient(X,Valuation(X));
 	X:=X-Coefficient(X,0);
 	Y:=q*Derivative(X)/h2;
 	Y:=Y/Coefficient(Y,Valuation(Y));
 	Mpar:=KMatrixSpace(RationalField(),1,2*g+2);
 	a:=Mpar![0: i in [0..2*g+1]];
 	for i in [0..2*g+1] do
 		a[1][2*g+2-i]:=Coefficient(Y^2-(X^(2*g+2)+&+[a[1][i+1]*X^i:i in [0..2*g+1]]),i-(2*g+1));
  	end for;
  	Res:=Y^2-(X^(2*g+2)+&+[a[1][i+1]*X^i: i in [0..2*g+1]]);
  	P:=x^(2*g+2)+&+[a[1][i+1]*x^i: i in [0..2*g+1]];

	if IsWeaklyZero(Res) then  
  		return P; 
	else 
  		return "ERROR: There is not a New Modular Hyperelliptic Curve"; 
	end if;

end function;

function CaseOdd(F)
// Given F a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq for a NEW modular abelian variety B.
// Assuming that there exists a new modular hyperelliptic curve C : y^2=f(x) such that Jac( C) is Q-isogenous to B and degree(f) is ODD,
// this function returns f(x).
// cf. Lemma 6.1 & Proposition 6.5 [BGJGP]

	g:=#F;
	Q<q>:=LaurentSeriesRing(RationalField());
	QQ := PolynomialRing(RationalField()); x := QQ.1;

	h1:=F[g-1];
 	h2:=F[g];
	X:=h1/h2;
	X:=X/Coefficient(X,Valuation(X));
	X:=X-Coefficient(X,0);
	Y:=q*Derivative(X)/h2;
	Y:=Y/Coefficient(Y,Valuation(Y));
	Mimpar:=KMatrixSpace(RationalField(),1,2*g+1);
	a:=Mimpar![0: i in [0..2*g]];
	for i in [0..2*g] do
		a[1][2*g+1-i]:=Coefficient(Y^2-(X^(2*g+1)+&+[a[1][i+1]*X^i:i in [0..2*g]]),2*(i-2*g));
	end for;
	Res:=Y^2-(X^(2*g+1)+&+[a[1][i+1]*X^i: i in [0..2*g]]);
	P:=x^(2*g+1)+&+[a[1][i+1]*x^i: i in [0..2*g]];

	if IsWeaklyZero(Res) then  
  		return P; 
	else 
  		return "ERROR: There is not a New Modular Hyperelliptic Curve"; 
	end if;

end function;


function NMHC(F,check,N,gamma)
// Defining polynomial of the NEW Modular Hyperelliptic Curve, if there exists, attached to a NEW modular abelian variety B, 
// where F is a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq.
//
// It must be use check:=true if one wants to prove that the curve obtained C:y^2=f(x) satisfies that C is NEW and Jac( C) is Q-isogenous to B.
// Otherwise (i.e. if one uses check:=false) it is just an approximation.
//
// If check := true, then it must be specify:
// * N = the level of B,
// * and gamma, where
//            * gamma:=1 if the Q-simple factors of B have different characters.
//            * gamma:=0 if the Q-simple factors of B have ALL trivial characters.
// NOTE: This function also works in the case when B=Jac(X) and X is a modular curve. cf. Lemma 2.5 [BGJGP]
  	
	g:=#F; if g lt 2 then return "ERROR: genus must be greater than 1"; end if;
	
	if check then  bound:=Bound(N,gamma,g);
	   vprintf ModularCurve: "Checking ...\n          ... bound =%o\n",bound;
	   if Type(bound) eq MonStgElt then 
		error "Illegal input for parameter gamma"; 
	   else
		if Degree(F[1]) lt bound then 
		  error "Need coefficients in q-expansions of basis of degree up to at least ",bound; 
		end if;
	   end if;
	end if;

	c:=Case(F);
	case c[1]:
		when "even": return(CaseEven(c[2]));
		when "odd":  return(CaseOdd(c[2])); 
		else return "ERROR: There is not a New Modular Hyperelliptic Curve";
	end case;
	
end function;
//----------------------------------------------------------------------------

intrinsic NewModularHyperellipticCurve(F::[RngSerPowElt]) -> BoolElt, RngUPolElt
{
Returns whether a NEW modular hyperelliptic curve exists attached to a NEW modular abelian variety B, 
where F is a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq.
If so, also returns a univariate polynomial f(x) such that y^2=f(x) is a Weierstrass equation for the curve.
}

	val := NMHC(F,false,1,1);
	if Type(val) eq MonStgElt then return false,_; else
	return true,val; end if;
	
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

intrinsic NewModularHyperellipticCurve(B::[ModSym]: prec:=100, check:=false, gamma:=1) -> BoolElt, RngUPolElt
{
Returns whether a NEW modular hyperelliptic curve exists attached to a NEW modular abelian variety B.
If so, also returns a univariate polynomial f(x) such that y^2=f(x) is a Weierstrass equation for the curve.
}
	N:=Level(B[1]);                                            
	if check then 
	  g:=#Zbase(B,50);
	  bound := Bound(N,gamma,g); 
	  if Type(bound) eq MonStgElt then 
		error "Illegal input for parameter gamma";
	  end if;	   
	  F:=Zbase(B,bound+10);
	else
	  F:=Zbase(B,prec);
	end if;
    	try
          val := NMHC(F,check,N,gamma);
	catch e
      	  error e`Object;
	end try;
	if Type(val) eq MonStgElt then return false,_; else
	return true,val; end if;
	
end intrinsic;

//----------------------------------------------------------------------------

function g1(N)
// cf. Theorem 1.9 [BGJGP]

//if ((N mod 2) ne 0) or ((N mod 3) ne 0) then return 10; 
//  else 
//    if ((N mod 5) ne 0) then return 14; 
//      else
        return 16;
//    end if;
//end if;
end function;

//----------------------------------------------------------------------------

function g0(N)
// cf. Proposition 7.7 [BGJGP]

	v2:=Valuation(N,2);
	v3:=Valuation(N,3);
	v5:=Valuation(N,5);
	v7:=Valuation(N,7);
	v11:=Valuation(N,11);
	v13:=Valuation(N,13);
	v17:=Valuation(N,17);
	v19:=Valuation(N,19);

case v2:
	when 1:	   g:=4;
	when 0:	
	       case v3:
  		  when 1:	g:=4;
		  when 0:
			case v5:	
	 			when 1:	  g:=4;
				when 0:
				    case v7:	
				       when 1:   g:=6;
				       when 0:   g:=10;
				       else      g:=6;
				    end case;
				else   g:=4;	    
			end case;
		  else       g:=2;
		end case;
	else 
	       case v3:
  		  when 1:	g:=4;
		  when 0:
			case v5:	
	 			when 1:	  g:=4;
				when 0:
				   case v7:	
				       when 1:   g:=4;
				       when 0:	 
				            case v11:	
				              when 1:   g:=5;
					      when 0:	 
					        case v13:	
				                  when 1:   g:=6;
					          when 0:
						    case v17:	
				                      when 1:   g:=8;
					              when 0:	 
						        case v19:	
				                           when 1:   g:=9;
					                   when 0:   g:=10;
							   else      g:=9;
							end case;
						      else   g:=8;
						    end case;
						  else  g:=6;
						end case; 
					      else     g:=5;
					    end case;
				       else      g:=4;
				   end case;
			        else      g:=2;	    
			end case;
		  else    g:=1;
		end case;
end case;
return g;
end function;


//----------------------------------------------------------------------------

function ZX1hyper(N,m)
// This function computes a sequence of sequences of q-expansions (up to precision:=m) of the elements of a rational basis of H^0(Af,Omega^1)q/dq 
// where the Af's are NEW modular abelian variety of level N, and the characters of Af's are of order 1,2,3,4 or 6.
// cf. Proposition 6.18 [BGJGP]

	G:=Chi(N);
	qQ:=[];
        for seq in G do g:=chi(N,seq); 
		if Order(g) in {1,2,3,4,6} then            
			A:=Af(g);
			A:=[B : B in A | Dimension(B)*Degree(BaseRing(g)) le g1(N)];
			for B in A do 
				f:=qIntegralBasis(B,m);
                    		qQ:=Append(qQ,f);
			end for;
                end if;
	end for;
	return qQ;

end function;

//----------------------------------------------------------------------------

function ZX0hyper(N,m)
// This function computes a sequence of sequences of q-expansions (up to precision:=m) of the elements of a rational basis of H^0(Af,Omega^1)q/dq 
// where the Af's are NEW modular abelian variety of level N and trivial character.
	qQ:=[];
        A:=Af(N);
	A:=[B : B in A | Dimension(B) le g0(N)];
	for B in A do 
		f:=qIntegralBasis(B,m);
               	qQ:=Append(qQ,f);
	end for;
                	
	return qQ;

end function;

//----------------------------------------------------------------------------

function D(d,g)
// Given d:=[d1,..,dn], this function returns all the subsequences S in [1..n] such that &+[dk : k in S] <= g

	L:=[];
	S:={1..#d};
	P:=Subsets(S);
	P:=[set : set in P | set ne {}];
	for p in P do l:=[d[k] : k in p]; if &+l le g then L:=Append(L,Setseq(p)); end if; end for;
	return L;
end function;

function Dequal(d,g)
// Given d:=[d1,..,dn], this function returns all the subsequences S in [1..n] such that &+[dk : k in S] = g

	L:=[];
	S:={1..#d};
	P:=Subsets(S);
	P:=[set : set in P | set ne {}];
	for p in P do l:=[d[k] : k in p]; if &+l eq g then L:=Append(L,Setseq(p)); end if; end for;
	return L;
end function;

//----------------------------------------------------------------------------

intrinsic NewModularHyperellipticCurves(N::RngIntElt, g::RngIntElt  :  check:=false, gamma:=1, prec:=100) -> SeqEnum
{
The defining equations of ALL the NEW Modular Hyperelliptic Curves parametrized from X_1(N) of genus=g (if g:=0 then all the curves for all the possible genera). 
}
// NEW Modular Hyperelliptic Curves parametrized from X_1(N) if gamma:=1 or from X_0(N) if gamma:=0. 

	verbose := GetVerbose("ModularCurve");

	QQ := PolynomialRing(RationalField()); x := QQ.1;

	if (Type(gamma) ne RngIntElt) or ((gamma ne 0) and (gamma ne 1)) then
	    error "Parameter gamma should be 0 or 1";
	end if;
	case gamma:
		when 1:
			B:=ZX1hyper(N,prec);
			d:=[#b : b in B];
			gg:=g1(N);
		when 0:
			B:=ZX0hyper(N,prec);
			d:=[#b : b in B];
			gg:=g0(N);
	end case;

	case g:
		when 0: L:=D(d,gg);
		else L:=Dequal(d,g);
	end case;

        if check then prec:=Bound(N,gamma,gg)+1; end if;

	//--------------
	if verbose ge 1 then
		printf "\n     Candidates:=%o\n",#L;
		case g:
			when 1:	printf "\n     Maximum g:=%o\n\n",g;
			when 0: printf "\n     %o\n\n","All the curves";  
			else printf "\n     Exact genus:=%o\n\n",g;
		end case;
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
	        P:=NMHC(LL,check,N,gamma);
		if Type(P) eq RngUPolElt then curves:=Append(curves,P); end if;
		//--------------
		if verbose eq 2 then
			if Type(P) eq RngUPolElt then 
				printf  "[(%o)]---------------> NewMHC[%o,%o]:=%o;\n", i,N,a,P;
			else 
				printf  "  %o  ---------------> NO NewMHC of level %o for : %o;\n",i,N,a;
			end if;
		end if;
		//--------------
		
		
	end for;
	if verbose eq 1 then  printf "%o\n\n"," "; end if;
	return curves;

end intrinsic;

//----------------------------------------------------------------------------

///////////////////////////////////////////////////////////////////////////////////////////////////////
// Non necessary NEW
///////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ModularHyperellipticCurve(F::[RngSerPowElt]) -> BoolElt, RngUPolElt
{ 
F is a sequence of q-expansions of the elements of a rational basis of H^0(B,Omega^1)q/dq attached
to a modular abelian subvariety B of J1(N) (or J0(N)).
Returns whether the differentials of this basis give a map from X1(N) (or X0(N)) to a hyperelliptic curve C.
If so, also returns a univariate polynomial f(x) such that y^2=f(x) is a Weierstrass equation for C.
NOTE: It is not guaranteed that Jac(C) is Q-isogenous to B.
}
	val := NMHC(F,false,1,0);
	if Type(val) eq MonStgElt then return false,_; else
	return true,val; end if;
	
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ModularHyperellipticCurve(B::[ModSym]: prec:=100) -> BoolElt, RngUPolElt
{
B is a modular abelian subvariety of J1(N) (or J0(N)).
Returns whether the differentials of this basis give a map from X1(N) (or X0(N)) to a hyperelliptic curve C.
If so, also returns a univariate polynomial f(x) such that y^2=f(x) is a Weierstrass equation for C.
NOTE: It is not guaranteed that Jac(C) is Q-isogenous to B.
}
        F:=Zbase(B,prec);
	val := NMHC(F,false,1,1);
	if Type(val) eq MonStgElt then return false,_; else
	return true,val; end if;
	
end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////////////////////
