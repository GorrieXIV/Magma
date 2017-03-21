freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes RootDtm: LongWords, LongestWeylWord, PosRootsWeightBasis;


intrinsic ExchangeElement( posR::SetIndx, w::SeqEnum, k::RngIntElt ) -> SeqEnum
{ We assume that ws_k has length l(w)-1; we return a reduced expression for 
ws_k, that is obtained from w by erasing one element; here posR are the 
positive roots in the weight basis.}

    n:= #w;

    alph:= posR[ k ];
    while n ge 1 do
        alph:= alph - alph[w[n]]*posR[ w[n] ];
        if not alph in posR then
            break;
        end if;
        n:= n-1;
    end while;
    u:= w;
    Remove( ~u, n );
    return u;

end intrinsic;

intrinsic GetBraidRelations( posR::SetIndx, C::AlgMatElt, w1::SeqEnum, 
          w2::SeqEnum ) -> SeqEnum
{ w1, w2 are two words (reduced expressions) in the Weyl group of R, 
  representing the same element. The output is a list of elementary 
  moves, moving w1 into w2. posR: positive roots in weight basis,
  C: Cartan matrix }
    

    if w1 eq w2 then return []; end if;

    n:= #w1;
    i:= w1[ n ];
    j:= w2[ n ];
    
    if i eq j then
        return $$( posR, C, [ w1[s] : s in [1..n-1] ], 
                      [ w2[s] : s in [1..n-1] ] );
    end if;

    ipij:= C[i][j];
    ipji:= C[j][i];
    
    if ipij eq 0 then
        
        u:= ExchangeElement( posR, w1, j );
        Append( ~u, j );
        
        // u is now a third rep of the same elt, but ending with i,j
        
        st2:= $$( posR, C, [u[s]: s in [1..n-1]], [w2[s] : s in [1..n-1]] );
        u[n]:=i; u[n-1]:= j;
        st1:= $$( posR, C, [w1[s] : s in [1..n-1]], [u[s]: s in [1..n-1]] );
        Append( ~st1, [n-1, i, n, j] );
        for mo in st2 do
            Append( ~st1, mo );
        end for;
        return st1;
    elif ipij eq -1 and ipji eq -1 then
        
        u:= ExchangeElement( posR, w1, j );
        Append( ~u, j );
        u:= ExchangeElement( posR, u, i );  
        Append( ~u, i );
        
        // now u is a third rep of the same elt, but ending with i,j,i
        
        st1:= $$( posR, C, [w1[s] : s in [1..n-1]], [u[s] : s in [1..n-1]] );
        Append( ~st1, [ n-2, j, n-1, i, n, j ] );
        
        u[n-2]:= j; u[n-1]:= i; u[n]:= j;
        
        st2:= $$( posR, C, [u[s] : s in [1..n-1]], [ w2[s] : s in [1..n-1]] );
        for mo in st2 do
            Append( ~st1, mo );
        end for;
        return st1;

    elif ipij eq -2 or ipji eq -2 then

        u:= ExchangeElement( posR, w1, j );
        Append( ~u, j );
        u:= ExchangeElement( posR, u, i );  
        Append( ~u, i );
        u:= ExchangeElement( posR, u, j );
        Append( ~u, j );
        
        // now u is a third rep of the same elt, but ending with i,j,i,j

        up:= u;
        up[n-3]:= j; up[n-2]:= i; up[n-1]:= j; up[n]:= i;

        st1:= $$( posR, C, [w1[s] : s in [1..n-1]], [up[s]: s in [1..n-1]] );
        Append( ~st1, [ n-3, i, n-2, j, n-1, i, n, j ] );
        st2:= $$( posR, C, [u[s] : s in [1..n-1]], [w2[s] : s in [1..n-1]] );
        for mo in st2 do
            Append( ~st1, mo );
        end for;
        return st1;
        
    elif ipij eq -3 or ipji eq -3 then

        u:= ExchangeElement( posR, w1, j );
        Append( ~u, j );
        u:= ExchangeElement( posR, u, i );  
        Append( ~u, i );
        u:= ExchangeElement( posR, u, j );
        Append( ~u, j );
        u:= ExchangeElement( posR, u, i );  
        Append( ~u, i );
        u:= ExchangeElement( posR, u, j );
        Append( ~u, j );
        
        // now u is a third rep of the same elt, but ending with i,j,i,j,i,j

        up:= u;
        up[n-5]:=j; up[n-4]:= i;
        up[n-3]:= j; up[n-2]:= i; up[n-1]:= j; up[n]:= i;

        st1:= $$( posR, C, [w1[s] : s in [1..n-1]], [up[s] : s in [1..n-1]] );
        Append( ~st1, [ n-5, i, n-4, j, n-3, i, n-2, j, n-1, i, n, j ] );
        
        st2:= $$( posR, C, [u[s] : s in [1..n-1]], [w2[s] : s in [1..n-1]] );

        for mo in st2 do
            Append( ~st1, mo );
        end for;
        return st1;

    end if;
end intrinsic;

intrinsic ApplyWeylElement( posR::SetIndx, w::SeqEnum, lam::ModTupFldElt ) ->
ModTupFldElt
{ returns w( lam ), where lam is a weight. }

    for k in [1..#w] do
        u:= w[#w-k+1];
        lam:= lam - lam[u]*posR[u];
    end for;
    return lam;
end intrinsic;

intrinsic LongestWeylWord( R::RootDtm ) -> SeqEnum
{The longest word in the Weyl group of R}

    if not assigned R`LongestWeylWord then
      R`LongestWeylWord:= Eltseq( LongestElement( CoxeterGroup( GrpFPCox, R ) ) );
    end if;
    return R`LongestWeylWord;

end intrinsic;


intrinsic LongWords( R::RootDtm ) -> SeqEnum
{list of longest elements in the Weyl group, the i-th element starting with 
the i-th simple reflection}

    if assigned R`LongWords then
       return R`LongWords;
    end if;
    
    w0:= LongestWeylWord( R );
    w0rev:= Reverse( w0 );
    wds:= [ ];
    posR:= PositiveRoots( R : Basis:= "Weight" );
    for i in [1..Rank(R)] do
        v:= ExchangeElement( posR, w0rev, i );
        Append( ~v, i );
        v:= Reverse( v );
        Append( ~wds, [* v, GetBraidRelations( posR, CartanMatrix(R), w0, v ),
                GetBraidRelations( posR, CartanMatrix(R), v, w0 ) *] );
    end for;
    R`LongWords:= wds;
    return wds;

end intrinsic;


intrinsic PosRootsWeightBasis( R::RootDtm ) -> SetIndx
{positive roots in weight basis}

    if not assigned R`PosRootsWeightBasis then
       posR:= {@ Vector( Integers(), u ) : u in 
	       PositiveRoots( R : Basis:= "Weight" ) @};
       R`PosRootsWeightBasis:= posR;
    end if;

    return R`PosRootsWeightBasis;

end intrinsic;
