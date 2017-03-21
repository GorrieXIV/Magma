freeze;

///////////////////////////////////////////////////////////////////////////
//
//  chevbas.m
//
//  By Willem de Graaf
//  Modified by Scott H. Murray
//
//  A Chevalley basis consists of three lists, x, y, h, that together form a 
//  Chevalley basis of L.
//
//  This file currently contains two algorithms:  one due to Willem and one due
//  to Scott and Arjeh Cohen.

declare attributes AlgLie : StandardBasis;

import "rootsystem.m" : integerConvert;
import "stsa.m":DR_IsSTSA;

intrinsic CanonicalGenerators( L::AlgLie ) -> SeqEnum, SeqEnum, SeqEnum
{} // grab description from other intrinsic
// A set of canonical generators of the classical-type Lie algebra L
// ie. one generator from each root space

    R, Rv, fund, C:= RootSystem( L );
    rank:= #fund;
    n:= IntegerRing()!( #R/2 );
    x:= Rv[[1..rank]];
    y:= Rv[[n+1..n+rank]];
    for i in [1..rank] do
        V:= VectorSpaceWithBasis( Matrix( [ x[i] ]  ));
        c:= Coordinates( V, V!( (x[i]*y[i])*x[i] ) )[1];
        y[i]:= y[i]*2/c;
    end for;
    
    return x, y, [ x[i]*y[i] : i in [1..rank] ];
    
end intrinsic;

//
// THIS IS NOT USING H CORRECTLY  
//
WdG_ChevBasis := function( L, H )

    // We first calculate an automorphism `f' of `L' such that 
    // F(L_{\alpha}) = L_{-\alpha}, and f(H)=H, and f acts as multiplication
    // by -1 on H. For this we take the canonical generators of `L',
    // map its `x'-part onto its `y' part (and vice versa), and map
    // the `h'-part on minus itself. The automorphism is determined by this.

    if assigned L`ChevalleyBasis then
       cc := L`ChevalleyBasis;
	   if H eq sub<L|cc[3]> then
         return cc[1], cc[2], cc[3];
       end if;
    end if;

    F:= BaseField( L );

    if IsAbelian( L ) then
      return [L|], [L|], Basis( L );
    elif not IsSemisimple( L ) then
      derL := L*L;
      pos, neg, cart := $$( derL, H meet derL );
      return ChangeUniverse( pos, L ), ChangeUniverse( neg, L ),
        ChangeUniverse( cart, L ) cat ChangeUniverse( Basis(Centre(L)), L );
    end if;

    R,Rv,fund,C:= RootSystem( L, H );
    n:= IntegerRing()!(#R/2);
    rank:= #fund;
    dim:= Dimension( L );
    n:= IntegerRing()!( #R/2 );
    
    // construct the canonical generators
    x:= Rv[[1..rank]];
    y:= Rv[[n+1..n+rank]];
    for i in [1..rank] do
        V:= VectorSpaceWithBasis( Matrix( [ x[i] ]  ));
        c:= Coordinates( V, V!( (x[i]*y[i])*x[i] ) )[1];
        y[i]:= y[i]*2/c;
    end for;
    h := [ x[i]*y[i] : i in [1..rank] ];

    // extend to a basis
    b1p:= x; b1m:= y;
    b2p:= y; b2m:= x;
   
    k:= 1;
    while k le n do
        r:= R[k];
        for i in [1..rank] do
            r1:= r + fund[i];
            pos:= Index( R, r1 );
            if pos ne 0 and not IsDefined( b1p, pos ) then 
                
                b1p[pos]:= x[i]*b1p[k];
                b1m[pos]:= y[i]*b1m[k];
                b2p[pos]:= y[i]*b2p[k];
                b2m[pos]:= x[i]*b2m[k];
            end if;
        end for;
        k:= k+1;
    end while;
    
    b1:= b1p cat b1m cat h; 
    b2:= b2p cat b2m cat [ -h[i] : i in [1..rank] ]; 

    f:= hom< L -> L | [ b1[i] -> b2[i] : i in [1..2*n+rank] ] >;
    
    // Now for every positive root vector `x' we set `y= -f( x )'.
    // We compute a scalar `cf' such that `[x,y]=h', where `h' is the
    // canonical Cartan element corresponding to the root (unquely determined).
    // Then we have to multiply `x' and `y' by Sqrt( 2/cf ), in order to get
    // elements of a Chevalley basis.

    cfs:= [ ];
    bHa:= [ ];
    posRV:= [ ];
    negRV:= [ ];

    //F:= RationalField();  Z := Integers();
    for i in [1..n] do
        a:= Rv[i];
        b:= -f(a);
        ha:= a*b;
        V:= VectorSpaceWithBasis( Matrix( [ a ] ) );
        cf:= Coordinates( V, V!( ha*a ) )[1];
        if i le rank then Append( ~bHa, (2/cf)*ha ); end if;
        
        P:= PolynomialRing( F, 1 );
        g:= UnivariatePolynomial( P.1^2-F!(2/cf) );
        if IsIrreducible( g ) then
           // extend the field...
           F := ext< F | g >;
        end if;
        Append( ~cfs, Sqrt( F!( 2/cf ) ) );
        posRV[i]:= a; negRV[i]:= b;
    end for;

    // The `cfs' will lie in a field extension of the ground field.
    // We construct the Lie algebra over that field with the same structure 
    // constants as `L'. Then we map the Chevalley basis elements into
    // this new Lie algebra. Then we take the structure constants table of
    // this new Lie algebra with respect to the Chevalley basis, and
    // form a new Lie algebra over the same field as `L' with this table.
    
    T:= BasisProducts( L );
    T:= [ [ Eltseq( T[i][j] ) : j in [1..dim] ] : i in [1..dim] ]; 
    K:= LieAlgebra< F, dim | T >;

    B:= [ ];
    for i in [1..n] do
        B[i]:= cfs[i]*( K!( Eltseq( posRV[i] ) ) );
        B[n+i]:= cfs[i]*( K!( Eltseq( negRV[i] ) ) );
    end for;
    for i in [1..#bHa] do
        B[2*n+i]:= K!( Eltseq( bHa[i] ) );
    end for;
    
    T:= [ ];
    V:= VectorSpaceWithBasis( Matrix( B ) );
    for i in [1..dim] do
        T[i]:= [ ];
        for j in [1..dim] do
            T[i][j]:= Coordinates( V, V!( B[i]*B[j] ) );
        end for;
    end for;

    K:= LieAlgebra< BaseField( L ), dim | T >;
    
    // Now the basis elements of `K' form a Chevalley basis. Furthermore,
    // `K' is isomorphic to `L'. We construct the isomorphism, and map
    // the basis elements of `K' into `L', thus getting a Chevalley basis
    // in `L'.
    
    b1p:= [ K.i : i in [1..rank] ]; 
    b1m:= [ K.(n+i) : i in [1..rank] ];
    b2p:= x; b2m:= y;
   
    k:= 1;
    while k le n do
        r:= R[k];
        for i in [1..rank] do
            r1:= r + fund[i];
            pos:= Index( R, r1 );
            if pos ne 0 and not IsDefined( b1p, pos ) then 
                
                b1p[pos]:= b1p[i]*b1p[k];
                b1m[pos]:= b1m[i]*b1m[k];
                b2p[pos]:= b2p[i]*b2p[k];
                b2m[pos]:= b2m[i]*b2m[k];
            end if;
        end for;
        k:= k+1;
    end while;
    
    b1:= b1p cat b1m cat [ K.(2*n+i) : i in [1..rank] ]; 
    b2:= b2p cat b2m cat h;
    f:= hom< K -> L | [ b1[i] -> b2[i] : i in [1..dim] ] >; 

    return [ L | f( K.i ) : i in [1..n] ],
           [ L | f( K.(n+i) ) : i in [1..n] ],
           [ L | -f( K.(2*n+i) ) : i in [1..rank] ];

end function;

/*
--this function wasn't used anyway--
SHM_ChevBasis := function( L, H )

    k := BaseRing( L );
    p := Characteristic( k );
    
    R := RootDatum( L );  
    n := Rank( R );  d := Dimension( R );  N := NumPosRoots( R );
    if n eq 0 then  return [L|], [L|], Basis(L);  end if;
    rts, rvs, simples, C := RootSystem( L, H );

    // reorder rts/rvs to agree with the root datum
    _, perm := IsCartanEquivalent( CartanMatrix(R), C );
    perminv := Eltseq( ( Sym(#perm)!perm )^-1 );
    newrts := rts[perm];  newrvs := rvs[perm];
    for r in [n+1..2*N] do
        v := Root( R, r : Basis:="Root" );
        rt := &+[ v[i]*newrts[i] : i in [1..n] ];
        if rt notin rts then
          error "Error: This should not happen.  Please mail entire run to magma-bugs@maths.usyd.edu.au";
        end if;
        Append( ~newrts, rt );  Append( ~newrvs, rvs[Position(rts,rt)] );
    end for;
    rts := newrts;  rvs := newrvs;
    
    // normalise the simple root vectors
    pos := [];  neg := [];  cart := [];
    for r in [1..n] do
        e := rvs[r];  f := rvs[r+N];
        _ := exists(i){i : i in [1..Dimension(L)] | e[i] ne 0 };
        a := (e*(f*e))[i] / (2*e[i]);
        Append( ~pos, e );  Append( ~neg, f/a );  
        Append( ~cart, f*e/a );
    end for;
    
    // compute the nonsimple root vectors
    for pair in ExtraspecialPairs( R ) do
        i := pair[1];  j := pair[2];
        Append( ~pos, pos[i]*pos[j]/LieConstant_N(R,i,j) );
        Append( ~neg, neg[i]*neg[j]/LieConstant_N(R,i+N,j+N) );
    end for;

    return pos, neg, cart;

end function;
*/

DR_ChevBasis := function( L, H : AssumeAlmostSimple := false)
/* Uses ReductiveType to compute a Chevalley basis */
	R, _, _, infos := ReductiveType(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
	assert #infos gt 0;
	pos := &cat[ i`ChevBasData`BasisPos : i in infos ];
	neg := &cat[ i`ChevBasData`BasisNeg : i in infos ];
	cart := &cat[ i`ChevBasData`BasisCart : i in infos ];
	return pos, neg, cart;
end function;

ChevBasis := function( L, H : AssumeAlmostSimple := false)
  if IsFinite(BaseRing(L)) then
    return DR_ChevBasis( L, H : AssumeAlmostSimple := AssumeAlmostSimple);
  else
    return WdG_ChevBasis( L, H );
  end if;
end function;

intrinsic ChevalleyBasis( L::AlgLie, H::AlgLie : AssumeAlmostSimple := false) -> SeqEnum, SeqEnum, SeqEnum
{A Chevalley basis of L with respect to H}

	/* Cached? */
	if assigned L`ChevalleyBasis then
		cc := L`ChevalleyBasis;
		if H eq sub<L | cc[3]> then
			return cc[1], cc[2], cc[3];  
		else
			delete L`ChevalleyBasis;
		end if;
	end if;

	/* Check prerequisites */
	k := BaseRing(L);
	if Characteristic(k) eq 0 then
		require IsSplittingCartanSubalgebra( L, H ) : "Not a splitting Cartan subalgebra";
		if not assigned L`CartanSubalgebra then
			L`CartanSubalgebra := H;
		end if;
	else
		require DR_IsSTSA( L, H ) : "Not a split Toral subalgebra";
	end if;
	
	/* Do the hard work. */
	pos, neg, cart := ChevBasis( L, H );
	L`ChevalleyBasis := [* pos, neg, cart *];
	return pos, neg, cart;
end intrinsic;

intrinsic ChevalleyBasis( L::AlgLie : AssumeAlmostSimple := false ) -> SeqEnum, SeqEnum, SeqEnum
{A Chevalley basis of L}
	
	/* Cached? */
	if assigned L`ChevalleyBasis then
		cc := L`ChevalleyBasis;
		return cc[1], cc[2], cc[3];  
	end if;
	
	/* No. Compute Split(Cartan|Toral)Subalgebra and call the above intrinsic */
	k := BaseRing( L );
	if Characteristic(k) eq 0 then
		H := SplittingCartanSubalgebra(L);
	else
		H := SplitMaximalToralSubalgebra(L);
	end if;
	
	return ChevalleyBasis(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
end intrinsic;

intrinsic ChevalleyBasisOld( L::AlgLie ) -> SeqEnum, SeqEnum, SeqEnum
{ Deprecated. Is as ChevalleyBasis, but the third return value (Cartan elements) is
  different. IsChevalleyBasis on the result probably returns false. }

	require Characteristic(BaseRing(L)) eq 0 : "Only for Lie algebras over char. 0";

	e, f, h := ChevalleyBasis(L);
	tmpH := sub<L|>;
	for i in [1..#h] do
		t := e[i]*f[i];
		if t in tmpH then break; end if;
		h[i] := t;
		tmpH := sub<L|tmpH, t>;
	end for;
	
	return e, f, h;
end intrinsic;




// We default to SC isogeny here because it means that the 
// Chevalley and standard bases will be the same.
//
// NB:  This will fail for some modular algebras
intrinsic RootDatum( L::AlgLie ) -> RootDtm
{The root datum of the Lie algebra L}
  if not assigned L`RootDatum then
    _,_,_,C := RootSystem( L );
    type := CartanName( C );
    R := RootDatum( type : Isogeny:="SC" );
    Ldim := Dimension(L);
    ssdim := Rank(R) + 2*NumPosRoots(R);
    L`RootDatum := (ssdim eq Ldim) select R else
      DirectSum( R, ToralRootDatum(Ldim-ssdim) );
  end if;
  return L`RootDatum;
end intrinsic;


intrinsic WeylGroup( L::AlgLie ) -> GrpPermCox
{The Weyl group of L}
  return CoxeterGroup( RootDatum(L) );
end intrinsic;


intrinsic WeylGroup( `GrpFPCox, L::AlgLie ) -> GrpFPCox
{The Weyl group of L as a finitely presented group}
  return CoxeterGroup( GrpFPCox, RootDatum( L ) );
end intrinsic;

intrinsic WeylGroup( `GrpPermCox, L::AlgLie ) -> GrpPermCox
{The Weyl group of L as a permutation group}
  return WeylGroup( L );
end intrinsic;

intrinsic WeylGroup( `GrpMat, L::AlgLie ) -> GrpMat
{The Weyl group of L as a matrix group}
  return CoxeterGroup( GrpMat, RootDatum( L ) );
end intrinsic;



intrinsic StandardBasis( L::AlgLie, H::AlgLie : R := false ) -> SeqEnum, SeqEnum, SeqEnum
{A standard basis of L with respect to split Cartan subalgebra H}

    require IsSplittingCartanSubalgebra( L, H ):
      "Not a splitting Cartan subalgebra";

    pos, neg, cart := ChevBasis( L, H );

    // change Cartan generators to agree with root datum
	if R cmpeq false then
	    R := RootDatum( L );
	end if;
    d := Dimension( R );  n := Rank( R );
    V := VectorSpace( BaseRing(L), d);
    A := SimpleCoroots( R );
    simplesR := [ V | Vector(A[i]) : i in [1..n] ];
    simplesH := [ V | Vector(H!v) : v in cart ];
    if n lt d then
      simplesR := ExtendBasis( simplesR, V );
      simplesH := ExtendBasis( simplesH, V );
    end if;  
    simplesR := Matrix( simplesR );
    simplesH := Matrix( simplesH );
    cart := simplesH * simplesR^-1;
    cart := [ L!(H!cart[i]) : i in [1..d] ];

    return pos, neg, cart;
end intrinsic;


intrinsic StandardBasis( L::AlgLie : R := false ) -> SeqEnum, SeqEnum, SeqEnum
{A standard basis of L}

    if R cmpne false or not assigned L`StandardBasis then
      p := Characteristic( BaseRing(L) );
      require p notin {2,3} : 
        "Not implemented for fields of characteristic 2 or 3";
      H := SplittingCartanSubalgebra( L );
      // NB: since L has a splitting Cartan subalgebra, it must be
      // classical-type
      pos, neg, cart := StandardBasis( L, H : R := R );
      L`StandardBasis := [* pos, neg, cart *];
    end if;

    list := L`StandardBasis;
    return list[1], list[2], list[3];
  
end intrinsic;


// Testing function

checkStandardBasis:= function( L, R, pos, neg, cart )
  N := NumPosRoots(R);  n := Dimension( R );
  rts := pos cat neg;
  if N ne #pos or N ne #neg then
    return false, "wrong number of rts",_;
  elif n ne #cart then
    return false, "wrong basis",_;
  elif not forall(s){ <h1,h2> : h1 in cart, h2 in cart | h1*h2 eq 0 } then
    return false, "nonabelian Cartan", s;
  elif not forall(s){ <r,i> : r in [1..N], i in [1..n] | pos[r]*cart[i] eq
  Root(R,r)[i]*pos[r] } then
    return false, "wrong pos rt on Cartan", s;
  elif not forall(s){ <r,i> : r in [1..N], i in [1..n] | neg[r]*cart[i] eq
  Root(R,r+N)[i]*neg[r] } then
    return false, "wrong neg rt on Cartan", s;
  elif not forall(u){ <r,s> : r in [1..2*N], s in [1..2*N] |
  ( r eq s and rts[r]*rts[s] eq 0 ) or
  ( r eq s+N and rts[r]*rts[s] eq &+[ Coroot(R,s)[i]*cart[i] : i in [1..n]] ) or
  ( r+N eq s and rts[r]*rts[s] eq &+[-Coroot(R,r)[i]*cart[i] : i in [1..n]] ) or
  ( (r notin {s,s+N,s-N}) and (rts[r]*rts[s] eq LieConstant_N(R,r,s)*
    ((t eq 0) select 0 else rts[t] ) where t is Sum(R,r,s)) ) } then
    return false, "wrong rt prod", s;
  else return true;
  end if;
end function;


