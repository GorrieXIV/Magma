freeze;

declare type PathLS;

declare attributes PathLS : WeightSequence, RationalSequence, Shape, 
			    EndpointWeight, WeylWord, RootDatum;

intrinsic Print(P::PathLS, level::MonStgElt)
 {}

    if #P`WeightSequence eq 0 then
       printf "Zero LS-path";
    else
       printf "LS-path of shape %o ending in %o", P`Shape, P`EndpointWeight;
    end if;

end intrinsic;

intrinsic IsCoercible(x::PathLS, y::.) -> BoolElt, Any
{};
    return false;
end intrinsic;

intrinsic 'in'(x::Any, y::PathLS) -> BoolElt
{};
    require false : "Nothing should use this";
    return false;
end intrinsic;

intrinsic InternalPathLSCreate(W::[ModTupRngElt[RngInt]], R::[FldRatElt], S::ModTupRngElt[RngInt], E::ModTupRngElt[RngInt], wrd::[RngIntElt], Rdat::RootDtm ) -> PathLS
{};
    require #W eq #R - 1 : "Wrong sequence lengths";
    P := New(PathLS);
    P`WeightSequence := W;
    P`RationalSequence := R;
    P`Shape := S;
    P`EndpointWeight := E;

    P`WeylWord:= wrd;
    P`RootDatum:= Rdat;

    return P;
end intrinsic;

intrinsic WeightSequence(P::PathLS) -> SeqEnum
{The weight sequence of the path P};
    return P`WeightSequence;
end intrinsic;

intrinsic RationalSequence(P::PathLS) -> SeqEnum
{The rational sequence of the path P};
    return P`RationalSequence;
end intrinsic;

intrinsic Shape(P::PathLS) -> ModTupRngElt
{The shape of the path P};
    return P`Shape;
end intrinsic;

intrinsic EndpointWeight(P::PathLS) -> ModTupRngElt
{The endpoint weight of the path P};
    return P`EndpointWeight;
end intrinsic;

intrinsic 'eq'( p1::PathLS, p2::PathLS ) -> BoolElt
{True if the paths p1 and p2 are equal, false otherwise}

     return p1`WeightSequence eq p2`WeightSequence and
            p1`RationalSequence eq p2`RationalSequence and
            p1`Shape eq p2`Shape;

end intrinsic;

intrinsic DominantLSPath( R::RootDtm, hw::[RngIntElt] ) -> PathLS
{ The path that is the straight line from the origin to hw }

    require #hw eq Rank(R) : "the weight is not of the correct length.";
    require &and[ IsIntegral(x) and x ge 0 : x in hw ] : "The weight does not consist of non-negative integers."; 

    v:= Vector( Integers(), hw );
    return InternalPathLSCreate( [v], [ Rationals() | 0,1 ], v, v, [Integers()|], R );

end intrinsic; 

intrinsic IsZero( p::PathLS ) -> BoolElt
{ True if p is the zero path, false otherwise }

return #p`WeightSequence eq 0;

end intrinsic;

intrinsic Falpha( p::PathLS, alpha::RngIntElt ) -> PathLS
{The root operator f_alpha applied to the LS-path p}

    // Here `p' is an L-S path, represented as 
    // [ [w1, w2,..., ws], [a0=0, a1, a2, ..., as=1] ]
    // We apply the root operator f_{\alpha}.
    // `alpha' is represented by the index in which it occurs
    // in the list of simple roots.

    R:= p`RootDatum;
    require alpha ge 1 and alpha le Rank(R) : "the index of the root does not correspond to a simple root.";

    require not IsZero( p ) : "The path operators cannot be applied to the zero path.";
    
    weights:= p`WeightSequence;
    rats:= p`RationalSequence;
    sim_rt:= PosRootsWeightBasis(R)[alpha];

    s:= #weights;
    h:= [ Rationals() | 0 ];
    for i in [1..s] do
        Append( ~h, h[i] + (rats[i+1]-rats[i])*weights[i][alpha] );
    end for;

    m_a:= Minimum( h );
    j:= #h;
    while h[j] ne m_a do j:= j-1; end while;
    
    k:= j+1;
    while k le #h do

        if h[k] lt m_a + 1 then
           k:= k+1;
        else
           break;
        end if;
    end while;

    if k gt #h then 

       v:= 0*p`Shape;
       return  InternalPathLSCreate( [], [ Rationals() | 0 ], p`Shape, 
                             v, [], R );
    end if;
    
    if h[k] eq h[j] + 1 then
        eta:= weights;
        aa:= rats;
        for i in [j..k-1] do    
            // apply s_{alpha} to eta[i]:
            eta[i]:= eta[i] - eta[i][alpha]*sim_rt;
        end for;
    else
        x:= rats[k-1] + (1/weights[k-1][alpha])*(h[j]+1-h[k-1]);
        eta:= [ ];
        aa:= [ Rationals() | ];
        for i in [1..j-1] do 
            Append( ~eta, weights[i] );
            Append( ~aa, rats[i] );
        end for;
        for i in [j..k-1] do
            w:= weights[i];
            w:= w - w[alpha]*sim_rt;
            Append( ~eta, w );
            Append( ~aa, rats[i] );
        end for;
        Append( ~eta, weights[k-1] );
        Append( ~aa, x );
        for i in [k..s] do
            Append( ~eta, weights[i] );
            Append( ~aa, rats[i] );
        end for;
        Append( ~aa, rats[s+1] );
    end if;

    i:= 1;
    while i le #eta-1 do
        if eta[i] eq eta[i+1] then
            Remove( ~eta, i );
            Remove( ~aa, i+1 );
        else
            i:= i+1;
        end if;
    end while;
    
    if j eq 1 then 
        word:= [ Integers() | alpha ];
        word cat:= p`WeylWord;
    else
        word:= p`WeylWord;
    end if;
    
    return InternalPathLSCreate( eta, aa, p`Shape, p`EndpointWeight-sim_rt,
                         word, R );
    
end intrinsic;


intrinsic Ealpha( p::PathLS, alpha::RngIntElt ) -> PathLS
{The root operator e_alpha applied to the LS-path p}
    
    // Here path is an L-S path, represented as 
    // [ [w1, w2,..., ws], [a0=0, a1, a2, ..., as=1] ]
    // We apply the root operator f_{\alpha}.
    // alpha is represented by the index in which it occurs
    // in the list of simple roots.

    R:= p`RootDatum;
    require alpha ge 1 and alpha le Rank(R) : "the index of the root does not correspond to a simple root.";

    require not IsZero( p ) : "The path operators cannot be applied to the zero path.";

    weights:= p`WeightSequence;
    rats:= p`RationalSequence;
    sim_rt:= PosRootsWeightBasis(R)[alpha];

    s:= #weights;
    h:= [ Rationals() | 0 ];
    for i in [1..s] do
        Append( ~h, h[i] + (rats[i+1]-rats[i])*weights[i][alpha] );
    end for;

    m_a:= Minimum( h );
    j:= 1;
    while h[j] ne m_a do j:= j+1; end while;
    
    k:= j-1;
    while k gt 0 do
        if h[k] lt m_a+1 then
           k:= k-1;
        else
           break;
        end if;
    end while;

    if k eq 0 then 

       v:= 0*p`Shape;
       return  InternalPathLSCreate( [], [ Rationals() | 0 ], p`Shape, 
                             v, [], R );
    end if;
    
    if h[k] eq h[j] + 1 then
        eta:= weights;
        aa:= rats;
        for i in [k..j-1] do
            // apply s_{alpha} to eta[i]:
            eta[i]:= eta[i] - eta[i][alpha]*sim_rt;
        end for;
    else
        x:= rats[k] + (1/weights[k][alpha])*(h[j]+1-h[k]);
        eta:= [ ]; 
        aa:= [Rationals() |  0 ];
        for i in [1..k-1] do 
            Append( ~eta, weights[i] );
            Append( ~aa, rats[i+1] );
        end for;
        Append( ~eta, weights[k] );
        Append( ~aa, x );
        for i in [k..j-1] do
            w:= weights[i];
            w:= w - w[alpha]*sim_rt;
            Append( ~eta, w );
            Append( ~aa, rats[i+1] );
        end for;
        for i in [j..s] do
            Append( ~eta, weights[i] );
            Append( ~aa, rats[i+1] );
        end for;
    end if;
    
    i:= 1;
    while i le #eta-1 do
        if eta[i] eq eta[i+1] then
            Remove( ~eta, i );
            Remove( ~aa, i+1 );
        else
            i:= i+1;
        end if;
    end while;

    if k eq 1 and h[k] eq m_a + 1 then
        word:= Reverse( p`WeylWord );
        word:= ExchangeElement( PosRootsWeightBasis(R), word, alpha );
        word:= Reverse( word );
    else
        word:= p`WeylWord;
    end if;


    return InternalPathLSCreate( eta, aa, p`Shape, p`EndpointWeight+sim_rt,
                         word, R );

end intrinsic;


intrinsic CrystalGraph( R::RootDtm, hw::SeqEnum ) -> GrphDir, SeqEnum
{ The crystal graph of the representation of the quantum group corresponding to the root datum R with highest weight hw }

    require #hw eq Rank(R) : "the weight is not of the correct length.";
    require &and[ IsIntegral(x) and x ge 0 : x in hw ] : "The weight does not consist of non-negative integers."; 

    oldpoints:= [ DominantLSPath( R, hw ) ];
    oldinds:= [ 1 ];
    edges:= [ ];
    done:= false;

    rank:= Rank( R );

    count:= 1;

    points:= oldpoints;
    while not done do
          newpoints:= [ ];
          newinds:= [ ];
          for i in [1..#oldpoints] do
              p:= oldpoints[i];
              for j in [1..rank] do
                  r:= Falpha( p, j );
                  if not IsZero( r ) then

                     // check whether we have already seen it
                     pos:= 0;
                     for k in [1..#newpoints] do
                         if newpoints[k]`WeightSequence eq r`WeightSequence and
                     newpoints[k]`RationalSequence eq r`RationalSequence then
                            pos:= k;
                            break;
                         end if;
                     end for;
                     if pos gt 0 then
                        Append( ~edges, [* [oldinds[i], newinds[pos]], j *] );
                     else
                        Append( ~newpoints, r );
                        count:= count+1;
                        Append( ~newinds, count );
                        Append( ~edges, [* [oldinds[i], count], j *] );
                     end if;
                  end if;
              end for;
          end for;

          done:= #newpoints eq 0;
          points cat:= newpoints;
          oldpoints:= newpoints;
          oldinds:= newinds;

    end while;

    // construct the graph

    S:= {};
    for e in edges do
        Include( ~S, e[1] );
    end for;
    G:= Digraph< count | S >;

    for e in edges do
        AssignLabel( G, e[1][1], e[1][2], e[2] );
    end for;

    return G,points;

end intrinsic;


intrinsic WeylWord( p::PathLS ) -> SeqEnum
{ The Weyl word of the LS-path p}

     return p`WeylWord;

end intrinsic;


