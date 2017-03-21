freeze;

/*  
**   $Id: AlgCarTyp.m,v 1.1 2005/03/27 11:36:07 smurray Exp $
**
**   Sergei Haller <sergei@maths.usyd.edu.au>
**
**   (Non-classical) Cartan-type Lie algebras
**
**        - Witt:             W(m,n)
**        - Special:          S(m,n)
**             - Conformal:  CS(m,n)
**        - Hamiltonian:      H(m,n)
**             - Conformal:  CH(m,n)
**        - Contact:          K(m,n)
**
**
*/

/*
**
**   TODO:  we could set some flags like is_simple upon creation.
**          unfortunately, there is no write access to them from
**          magma level at the moment. maybe implement later.
**
*/

/*
**
**   Example:
**
**
**
**   F := GF(9);
**   WittLieAlgebra( F, 1, [1]     ); // the standard p-dim Witt-Algebra (p=char(F))
**   WittLieAlgebra( F, 3, [1,2,1] ); // dim = 3*p^{1+2+1} = 243
**   WittLieAlgebra( F, 2, [2,3]   ); // dim = 2*p^{2+3}   = 486
**
**   W := WittLieAlgebra( GF(3), 2, [2,3] );
**   Total time: 57.989 seconds, Total memory usage: 39.98MB
**   Total time:  9.470 seconds, Total memory usage: 11.58MB  // after some tuning ;^)
**
**
**   W := WittLieAlgebra( GF(5), 1, [1] );
**
**   time IsAbelian(W);
**   time IsSolvable(W);
**   time IsNilpotent(W);
**   time IsSimple(W);
**   time IsSemisimple(W);
**   time IsReductive(W);
**   time HasLeviSubalgebra(W);
**
**   time CartanSubalgebra(W);
**
**   time SemisimpleType(W);
**   time RootSystem(W);
**
**   time IsRestrictedLieAlgebra(W);
**
**
**   time CS,S,W := ConformalSpecialLieAlgebra( GF(25), 3, [1,1,1] );
**
**   time IsSimple(S);   // false
**   time IsSimple(S*S); // true
**
**   time CH,H,W := ConformalHamiltonianLieAlgebra( GF(25), 2, [1,1] );
**
**   time IsSimple(H);   // false
**   time IsSimple(H*H); // true
**
**   time K,W := ContactLieAlgebra( GF(25), 3, [1,1,1] );
**
**   time IsSimple(K);   // true (because m+3 = 6 \neq 0 mod 5)
**   time IsSimple(K*K); // true
**
**
*/

forward aux;
forward mpol_to_witt, mpol_to_witt_subalg;
forward inc, der;

/********************************************************************************* 
**                                                                              **
**   (Generalised) Witt-algebra  W(m,n)                                         **
**                                                                              **
*********************************************************************************/
function wittprodbrkt(F, m, n, tau, ndx2pos, pos2ndx)
	local prod, brkt;
	 
	function prod( ndx1, ndx2 )
	     al := ndx1[1];              i := ndx1[2];
	     be := ndx2[1]; be[i] -:= 1; j := ndx2[2];
	     // "be" is actually  \beta - \epsilon_i
	
	     if be[i] eq -1 or exists{ l : l in [1..m] | al[l]+be[l] gt tau[l] } then
	          return 0, ndx1;
	     else
	          c := F!1;
	          for l in [1..m] do
	               c *:= Binomial(al[l]+be[l],be[l]);
	               if c eq 0 then
	                    return 0, ndx1;
	               end if;
	          end for;
	
	          return c, << al[l]+be[l] : l in [1..m]>,j>;
	     end if;
	end function;

	function brkt( p1, p2 : sym := true)
	     ndx1 := pos2ndx(p1);
	     ndx2 := pos2ndx(p2);
	     c1,b1 := prod( ndx1, ndx2 );
	     c2,b2 := prod( ndx2, ndx1 );
	 	r := [];
	
	     if b1 eq b2 then
	          c1 -:= c2;
	          c2  := F!0;
	     end if;
	
	     if c2 eq 0 then
	          if c1 eq 0 then
	               return [];
	          else
	               pb1 := ndx2pos(b1);
	               if sym then 	return [ <p1,p2,pb1,c1>, <p2,p1,pb1,-c1> ];
				else			return [ <p1,p2, pb1,  c1> ];
				end if;
	          end if;
	     elif c1 eq 0 then
	          pb2 := ndx2pos(b2);
               if sym then 	return [ <p1,p2,pb2,-c2>, <p2,p1,pb2,c2> ];
			else			return [ <p1,p2,pb2,-c2> ];
			end if;
	     else
	          pb1 := ndx2pos(b1);
	          pb2 := ndx2pos(b2);
               if sym then 	return [ <p1,p2,pb1,c1>, <p1,p2,pb2,-c2>, <p2,p1,pb1,-c1>, <p2,p1,pb2,c2> ];
			else			return [ <p1,p2,pb1,c1>, <p1,p2,pb2,-c2> ];
			end if;
	     end if;
	end function;
return prod, brkt;
end function;
intrinsic WittLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, Map
{Witt-algebra W(m,n) over the finite field F.}

     require m gt 0 and #n eq m and forall{ x : x in n | x gt 0 }
          : "n must be a non-empty sequence of positive integers of length m";

     p := Characteristic(F);

     require p gt 0 : "Characteristic of the field must be positive";

     dim, 
     tau, 
     ndx2pos, 
     pos2ndx,
	ndzsO := aux(p,m,n);
	_, brkt := wittprodbrkt(F, m, n, tau, ndx2pos, pos2ndx);

// time T := &cat[ brkt(i,j) : i,j in [1..#ndzsW] | i lt j ];
// this is 20% faster:
     T := [];
     for  i,j in [1..dim] do;
          if i lt j then
               T cat:= brkt(i,j);
          end if;
     end for;

     rep := 4*#T lt dim^3 select "Sparse" else "Dense";

     W := LieAlgebra< F, dim | T : Rep:=rep , Check:=Check >;

     require Dimension(W) eq m*p^&+n : "check procedure: wrong dimension";

     return W, mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

end intrinsic;

 

/********************************************************************************* 
**                                                                              **
**   Special Lie algebra  S(m,n)                                                **
**                                                                              **
*********************************************************************************/
intrinsic SpecialLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, AlgLie, Map, Map
{Special Lie algebra S(m,n) over the finite field F.}

     require m gt 1 : "m must be an integer greater than 1";

     require #n eq m and forall{ x : x in n | x gt 0 }
          : "n must be a sequence of positive integers of length m";

     p := Characteristic(F);

     require p gt 0 : "Characteristic of the field must be positive";

     _, 
     tau, 
     ndx2pos,
 	pos2ndx, 
	ndzsO := aux(p,m,n);

     basement := [[0..tau[i]]: i in [1..m]];
     
     W := WittLieAlgebra( F, m, n : Check:=Check );
     B := Basis(W);

     // create a new generating set
     new_gens := [W| B[ndx2pos(< ndx, i >)] : ndx in CartesianProduct( Insert(Remove(basement,i),i,[0]) ),
                                                 i in [1..m] ];

     S := sub< W | new_gens >;

     require Dimension(S) eq (m-1)*p^&+n+1 : "check procedure: wrong dimension";

	phi := mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

     return S, W, mpol_to_witt_subalg(W, S, phi), phi;
end intrinsic;

/********************************************************************************* 
**                                                                              **
**   Conformal special Lie algebra  CS(m,n)                                     **
**                                                                              **
*********************************************************************************/
intrinsic ConformalSpecialLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, AlgLie, AlgLie, Map, Map, Map
{Conformal special Lie algebra CS(m,n) over the finite field F.}

     p := Characteristic(F);

     require p gt 0 : "Characteristic of the field must be positive";

     _, 
     _, 
     ndx2pos,
 	pos2ndx,
	ndzsO := aux(p,m,n);
     
     S,W := SpecialLieAlgebra( F, m, n : Check:=Check );

     b := Basis(W)[ndx2pos(< inc(<0:i in [1..m]>,1), 1 >)];

     // the following is actually a direct sum of S and sub<W|b>,
     // but we want S to be a subalgebra of CS
     CS := sub< W | Basis(S) cat [b] >;

     require Dimension(CS) eq (m-1)*p^&+n+2 : "check procedure: wrong dimension";

	phi := mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

     return CS,S,W,mpol_to_witt_subalg(W, CS, phi), mpol_to_witt_subalg(W, S, phi), phi;
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   Hamiltonian Lie algebra  H(m,n)                                            **
**                                                                              **
*********************************************************************************/
intrinsic HamiltonianLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, AlgLie, Map, Map
{Hamiltonian Lie algebra H(m,n) over the finite field F.}

     require IsEven(m) and m gt 1 : "m must be an even positive integer";

     require #n eq m and forall{ x : x in n | x gt 0 }
          : "n must be a sequence of positive integers of length m";

     p := Characteristic(F);
     require p gt 2 : "Characteristic of F must be at least 3";

     r := ExactQuotient(m,2);
     
     _, 
     _, 
     ndx2pos, 
     pos2ndx,
     ndzsO   := aux(p,m,n);

     W := WittLieAlgebra( F, m, n : Check:=Check );
     B := Basis(W);

     sig   := [1  :i in [1..r]] cat [-1:i in [1..r]];
     prime := [i+r:i in [1..r]] cat [ i:i in [1..r]];

     function D_H( al ) // only for x^(\alpha)
          return &+[W| sig[j] * B[ndx2pos( < der(al,j), prime[j]> )] : j in [1..2*r] | al[j] ne 0 ];
     end function;

     // create a new generating set
     new_gens := [W| D_H(al) : al in ndzsO ];

     H := sub< W | new_gens >;

     require Dimension(H) eq p^&+n-1 : "check procedure: wrong dimension";

	phi := mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

     return H,W, mpol_to_witt_subalg(W, H, phi), phi;
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Conformal Hamiltonian Lie algebra  CH(m,n)                                 **
**                                                                              **
*********************************************************************************/
intrinsic ConformalHamiltonianLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, AlgLie, AlgLie, Map, Map, Map
{Conformal Hamiltonian Lie algebra CH(m,n) over the finite field F.}

     p := Characteristic(F);
     require p gt 2 : "Characteristic of F must be at least 3";

     r := ExactQuotient(m,2);
     
     _, 
     _, 
     ndx2pos,
 	pos2ndx,
	ndzsO := aux(p,m,n);

     H,W := HamiltonianLieAlgebra( F, m, n : Check:=Check );
     B := Basis(W);

     al := <0:i in [1..m]>;
     b := &+[W| B[ndx2pos( < inc(al,j), j > )] : j in [1..m] ];

     // the following is actually a direct sum of H and sub<W|b>,
     // but we want H to be a subalgebra of CH
     CH := sub< W | Basis(H) cat [b] >;

     require Dimension(CH) eq p^&+n : "check procedure: wrong dimension";

	phi := mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

     return CH,H,W, mpol_to_witt_subalg(W, CH, phi), mpol_to_witt_subalg(W, H, phi), phi;
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   Contact Lie algebra  K(m,n)                                                **
**                                                                              **
*********************************************************************************/
intrinsic ContactLieAlgebra( F::Fld, m::RngIntElt, n::SeqEnum[RngIntElt] : Check:=false ) -> AlgLie, AlgLie, Map, Map
{Contact Lie algebra K(m,n) over the finite field F.}

     require IsOdd(m) and m gt 1 : "m must be an odd positive integer at least 3";

     require #n eq m and forall{ x : x in n | x gt 0 }
          : "n must be a sequence of positive integers of length m";

     p := Characteristic(F);
     require p gt 2 : "Characteristic of F must be at least 3";

     r := ExactQuotient(m-1,2);
     
     _, 
     tau, 
     ndx2pos, 
     pos2ndx,
     ndzsO   := aux(p,m,n);

     W := WittLieAlgebra( F, m, n : Check:=Check );
     B := Basis(W);

     sig   := [1  :i in [1..r]] cat [-1:i in [1..r]]; // no sig and
     prime := [i+r:i in [1..r]] cat [ i:i in [1..r]]; // no prime for i = m = 2r+1

     function D_H( al ) // only for x^(\alpha)
          return &+[W| sig[j] * B[ndx2pos( < der(al,j), prime[j]> )] : j in [1..2*r] | al[j] ne 0 ];
     end function;

     function D_K( al ) // only for x^(\alpha)
          return     D_H(al) 
                 +   (al[m] eq 0 
                         select W!0 
                           else &+[W| (al[prime[j]] + 1) 
                                      * B[ndx2pos( < inc(der(al,m),prime[j]), prime[j]> )] 
                                    : j in [1..2*r] | al[prime[j]] lt tau[prime[j]]])
                 +   (2 - &+[ al[i] : i in [1..2*r] ]) * B[ndx2pos( < al, m > )];
     end function;

     // create a new generating set
     new_gens := [W| D_K(al) : al in ndzsO ];

     K := sub< W | new_gens >;

	phi := mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO);

     require Dimension(K) eq p^&+n : "check procedure: wrong dimension";

     return K,W, mpol_to_witt_subalg(W, K, phi), phi;
end intrinsic;






/********************************************************************************* 
**                                                                              **
**   AUXILIARY FUNCTIONS                                                        **
**                                                                              **
*********************************************************************************/
/*
**   This one was just extracted to avoid code duplication.
*/
function aux( p, m, n )
	local tau, basement, ndzsO, ndzsW;
	
     tau := < p^n_i-1 : n_i in n >;

     basement := [[0..tau[i]]: i in [1..m]];
     ndzsO := CartesianProduct( basement );
     ndzsW := [ <ndx, delta_i> :  delta_i in [1..m], ndx in ndzsO ];
     /*
     **   actually, ndzsW is built in a way that it is sorted,
     **   but KNOWING that it is sorted, is essential for
     **   the function Position. (speeds up to quasi-zero-time)
     **
     */
     Sort(~ndzsW); 

     return #ndzsW,                             // dim
            tau,                                // tau
            func< ndx | Position(ndzsW,ndx) >,  // ndx2pos
            func< pos | ndzsW[pos] >,           // pos2ndx
            ndzsO;                              // ndzsO
end function;

/*
**   Increase alpha at component i by 1.
**   Derive alpha in direction i. That is, decrease alpha at component i by 1.
**
**   Beware that NO argument checking is done.
*/
function inc( al, i ) al[i] +:= 1; return al; end function;
function der( al, i ) al[i] -:= 1; return al; end function;

/*
** A map assisting the end user in identifying the basis elements of a Witt lie algebra
*/
function mpol_to_witt(W, m, n, ndx2pos, pos2ndx, ndzsO)
	local F, p, P, trmtoW, PtoW, bastoP, WtoP;
	
	F := BaseRing(W);
	P := PolynomialRing(F, 2*m);
	AssignNames(~P, [ Sprintf("x%o",i) : i in [1..m] ] cat [ Sprintf("d%o",i) : i in [1..m]]);
	p := Characteristic(F);
	
	trmtoW := function(trm)
		local i, delta, t, deltaok;
		
		t := Rep(ndzsO);
		for i in [1..m] do
			if Degree(trm, P.i) gt p^(n[i])-1 then error Sprintf("trmtoW: Degree of x%o must be between 0 and %o", i, p^(n[i]) -1); end if;
			t[i] := Degree(trm, P.i);
		end for;
		delta := 0; deltaok := true;
		for i in [1..m] do
			if Degree(trm, P.(i+m)) eq 0 then continue; end if;
			if Degree(trm, P.(i+m)) ne 1 then deltaok := false; break; end if;
			if delta ne 0 then deltaok := false; break; end if;
			delta := i;
		end for;
		deltaok := deltaok and delta ne 0;
		if not deltaok then error Sprintf("trmtoW: Precisely one of the d's must occur with degree one"); end if;
		
		i := ndx2pos(<t, delta>);
		return LeadingCoefficient(trm)*W.i;
	end function;
	PtoW := function(p)
		return &+[ trmtoW(t) : t in Terms(p) ];
	end function;
	
	bastoP := function(i)
		local t, r;
		assert i ge 1 and i le Dimension(W);
		t := pos2ndx(i);
		return &*[ (P.j)^(t[1][j]) : j in [1..m] ]*P.(m+t[2]);
	end function;
	WtoP := function(w)
		return &+[ w[i]*bastoP(i) : i in [1..Dimension(W) ] ];
	end function;

	return map<P -> W | p :-> PtoW(p), w :-> WtoP(w) >;
end function;

function mpol_to_witt_subalg(W, S, phi)
	return map<Domain(phi) -> S | p :-> S!(phi(p)), s :-> ((W!(S!s)) @@ phi)>;
end function;
 
 
 
