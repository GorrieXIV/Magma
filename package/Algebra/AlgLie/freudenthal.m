freeze;

///////////////////////////////////////////////////////////////////////////

intrinsic DominantCharacter( R::RootDtm, hw::ModTupFldElt ) -> SeqEnum, SeqEnum
   {The dominant weights of the representation with highest weight hw and their multiplicities}
   return DominantCharacter( R, Eltseq(hw) );
end intrinsic;

intrinsic DominantCharacter( R::RootDtm, hw::ModTupRngElt ) -> SeqEnum, SeqEnum
   {The dominant weights of the representation with highest weight hw and their multiplicities}
   return DominantCharacter( R, Eltseq(hw) );
end intrinsic;

intrinsic DominantCharacter( R::RootDtm, hw::SeqEnum ) -> SeqEnum, SeqEnum
   {The dominant weights of the representation with highest weight hw and their multiplicities}

   // Here R is a root datum corresponding to a semisimple Lie algebra L,
   // and hw is a dominant weight. Let V be the highest-weight module 
   // over L with highest weight hw. This function returns two lists:
   // the first list consists of the dominant weights of V, and the second
   // one contains their multiplicities. A complete list of weights is 
   // obtained by letting the Weyl group act on the dominant ones, 
   // weights in the same orbit have the same multiplicity.
   // This is a straightforward implementation of Freudenthal's formula.

    require IsCrystallographic( R ): 
       "This function only works for crystallographic root data";

    rank:= Rank( R );

    require #hw eq rank: "The weight is not of the correct length";

    require &and[ IsIntegral( hw[i] ) and hw[i] ge 0 : i in [1..rank] ]:
       "The weight must be dominant integral";

   posR:= PositiveRoots( R : Basis:= "Weight" );
   pp:= PositiveRoots( R : Basis:= "Root" );
   // heights:= [ &+Eltseq( pp[i] ) : i in [1..#pp] ];
   heights:= [ &+Eltseq(v) : v in pp ];

   Bil:= Matrix( RationalField(), CoxeterForm( R : Basis:= "Weight" ) );
   
   inprod_wts:= function( a, b )

       vv:= Eltseq( Vector( RationalField(), a )*Bil );
       br:= Eltseq( b );
       return &+[ vv[i]*br[i] : i in [1..rank] ];

   end function;

   // First we get the dominant weights.

   // Now `dom' will be the list of dominant weights; `levels' will be a list
   // (in bijection with `dom') of the levels of the weights in `dom'.

   dom:= [ hw ];
   levels:= [ 0 ];

   ww:= [ hw ];

   // `ww' is the list of weights found in the last round. We subtract the
   // positive roots from the elements of `ww'; algorithm as in
   // R. V. Moody and J. Patera, "Fast recursion formula for weight
   // multiplicities", Bull. Amer. math. Soc., 7:237--242.

   while #ww gt 0 do

       newdom:= [ ];
       for mu in ww do
           for k in [1..#posR] do
               nu:= [ IntegerRing()!(mu[i]-posR[k][i]) : i in [1..rank] ];
               if &and[ nu[i] ge 0 : i in [1..rank ] ] and 
                  not( nu in dom ) then
                  Append( ~newdom, nu );
                  Append( ~dom, nu );
                  pos:= Index( dom, mu );
                  Append( ~levels, levels[Index(dom,mu)]+heights[k] );
               end if;
           end for;
       end for;
       ww:= newdom;

   end while;

   // we have to sort the elements in dom according to level...
   f:= function( a, b )
       if a lt b then return -1; end if;    
       if a eq b then return 0; end if;
       return 1;
   end function;

   Sort( ~levels, f, ~p );
   dom1:= [ ];
   for i in [1..#dom] do
      j:= i^p;
      dom1[i]:= dom[j];
   end for;
   dom:= [ Vector( dom1[i] ) : i in [1..#dom1] ];   

   ww:= [ hw[i]+1 : i in [1..rank] ];
   iplam:=  inprod_wts( ww, ww );

   noposR:= #pp;
   
   G:= ReflectionGroup( R );
   g:= SimpleReflectionPermutations( G );
   Sn:= Sym( 2*noposR );

   mults:= [ 1 ];
   for i in [2..#dom] do
       sum:= 0;

       mu:= dom[i];
       h:= [Sn| ];
       inds:= [ ];
       for j in [1..rank] do
           if mu[j] eq 0 then 
              Append( ~h, g[j] ); 
              Append( ~inds, j ); 
           end if;
       end for;

       H:= sub< Sn | h >;

       // get orbit representatives of H on the root system
       reps:= [ ];
       sizes:= [ ];  // will contain the orbit sizes

       O:= Orbits( H );
       for o in O do
           kk:= Sort( SetToSequence( o ) );
           if kk[1] le noposR then
              Append( ~reps, pp[ kk[1] ] );
              if kk[#kk] le noposR then
   	         // whole orbit contained in the positive roots, so the
                 // "real" orbit (i.e., under the group with -1 added)
                 // has twice the size. 
	         Append( ~sizes, 2*#kk );
              else
    	         Append( ~sizes, #kk );
              end if;
           end if;
       end for;

       for j in [1..#reps] do
           a:= posR[ Index( pp, reps[j] ) ];
           nu := [ dom[i][k] + a[k] : k in [1..rank] ];
           eta:= DominantWeight( R, nu : Basis:= "Weight" );

           sum1:= 0;
           while eta in dom do
               sum1 +:= inprod_wts( nu, a )*mults[ Index( dom, eta ) ];
               nu := [ nu[k] + a[k] : k in [1..rank] ];
               eta:= DominantWeight( R, nu : Basis:= "Weight" );
           end while;
           sum:= sum + sizes[j]*sum1;
       end for;
       ww:= [ dom[i][k]+1 : k in [1..rank] ];

       Append( ~mults, sum/(iplam - inprod_wts( ww, ww ) ) );
   end for;

   return dom, mults;

end intrinsic;



intrinsic DimensionOfHighestWeightModule( R::RootDtm, w::ModTupFldElt ) 
-> RngIntElt
   {Dimension of the highest weight module with highest weight w}
   return DimensionOfHighestWeightModule( R, Eltseq(w) );
end intrinsic;

intrinsic DimensionOfHighestWeightModule( R::RootDtm, w::ModTupRngElt )
-> RngIntElt
   {Dimension of the highest weight module with highest weight w}
   return DimensionOfHighestWeightModule( R, Eltseq(w) );
end intrinsic;

intrinsic DimensionOfHighestWeightModule( R::RootDtm, w::SeqEnum ) -> RngIntElt
   {Dimension of the highest weight module with highest weight w}

    // Here R is a root datum corresponding to a semisimple Lie algebra
    // L. This function calculates the dimension of the highest weight
    // module over L with highest weight w.
    // The algorithm is a straightforward implementation of Weyl's
    // dimension formula.

    w:= Eltseq( w );

    require IsCrystallographic( R ):
       "This function only works for crystallographic root data";

    l:= Rank( R );

    require #w eq l: "The weight is not of the correct length";

    require &and[ IsIntegral( w[i] ) and w[i] ge 0 : i in [1..l] ]:
       "The weight must be dominant integral";

    posR:= PositiveRoots( R : Basis:= "Root" );
    M:= CoxeterForm( R : Basis:= "Root" );
    p:= 1;
    for r in posR do
        den:= 0;
        num:= 0;
        for i in [1..l] do
            num:= num + r[i]*(w[i]+1)*M[i][i];
            den:= den + r[i]*M[i][i];
        end for;
        p:= p*(num/den);
    end for;

    return IntegerRing()!( p );

end intrinsic


intrinsic DecomposeTensorProduct( R::RootDtm, w1, w2 ) ->
                                            SeqEnum
    {The decomposition of the tensor product of two highest weight
      modules with highest weight w1 an w2} 

   // Here R is a root datum corresponding to a semisimple Lie algebra L,
   // and w1,w2 are dominant weights. Let V1,V2 be the respective highest
   // weight modules. Then the tensor product V1\otimes V2 splits as a 
   // direct sum of highest weight modules. This function returns two lists;
   // one list contains the highest weights that occur in this decomposition,
   // the other contains the multiplicities.
   // This is a straightforward implementation of Klymik's formula.

    w1:= Eltseq( w1 ); w2:= Eltseq( w2 );

    require IsCrystallographic( R ):
       "This function only works for crystallographic root data";

    rank:= Rank( R );

    require #w1 eq rank and #w2 eq rank:
                      "The weights are not of the correct length";

    require &and[ IsIntegral( w1[i] ) and w1[i] ge 0 : i in [1..rank] ] and
            &and[ IsIntegral( w2[i] ) and w2[i] ge 0 : i in [1..rank] ]:
       "The weights must be dominant integral";

    if DimensionOfHighestWeightModule( R, w1 ) gt 
       DimensionOfHighestWeightModule( R, w2 )   then
       // interchange...
       store:= w1;
       w1:= w2;
       w2:= store;
    end if;

    W:= CoxeterGroup( R );
    ch1,mm1:= DominantCharacter( R, w1 );
    wts:= [ ]; mlts:= [ ];
    rho:= Vector( RationalField(), [ 1 : i in [1..rank] ] );

    wvec2:= Vector( RationalField(), w2 );
    for i in [1..#ch1] do

        // We loop through all weights of the irrep wih highest weight w1.
        // We get these by taking the orbits of the dominant ones under the
        // Weyl group.

        orb:= WeightOrbit( W, ch1[i] : Basis:= "Weight" );
        for wt in orb do

            ww:= wt+wvec2+rho;
            mu, word := DominantWeight( W, ww : Basis := "Weight" );

            if not ( 0 in Eltseq( mu ) ) then

              // The stabilizer of `ww' is trivial; so `ww' contributes to the
              // formula. `nu' will be the highest weight of the direct
              // summand gotten from `ww'.

                nu:= mu-rho;
                mult:= mm1[i]*( (-1)^#word );
                p:= Index( wts, nu );
                if p eq 0 then
                    Append( ~wts, nu );
                    Append( ~mlts, mult );
                else
                    mlts[p]:= mlts[p]+mult;
                    if mlts[p] eq 0 then
                        Remove( ~mlts, p );
                        Remove( ~wts, p );
                    end if;

                end if;
            end if;
        end for;
    end for;
    return wts, mlts;

end intrinsic;




formal_dec:= function( R, wts, mults )

    // Here wts is a sequence of dominant characters, and mults a
    // sequence of multiplicities, which are allowed to be negative.
    // We suppose that there is a module over the semisimple Lie algebra
    // with root datum L, with this as dominant character. 
    // This function will return a sequence of dominant weights along
    // with a sequence of multiplicities, which give the decomposition
    // of the character into a sum of irreducible ones.
    // If some of the multiplicities given are negative, then there is 
    // no module with that character. However, the decomposition is still
    // correct.

    // first we get the levels of the weights

    pos:= PositiveRoots( R : Basis:= "Weight" );
    sim:= [ Vector( Rationals(), pos[i] ) : i in [1..Rank(R)] ];
    V:= VectorSpaceWithBasis( sim );

    levels:= [ &+Coordinates( V, V!w ) : w in wts ];

    // now we sort

    f:= function( a, b )

        if a lt b then return 1; end if;    
        if a eq b then return 0; end if;
        return -1;
    end function;

    Sort( ~levels, f, ~p );
    w1:= [ ]; m1:= [ ];
    for i in [1..#wts] do
       j:= i^p;
       w1[i]:= wts[j];
       m1[i]:= mults[j];
    end for;
    wts:= w1;
    mults:= m1;

    w:= [ ]; m := [ ];

    while #wts gt 0 do

       Append( ~w, wts[1] );
       Append( ~m, mults[1] );

       w1,m1:= DominantCharacter( R, Eltseq( wts[1] ) );

       l1:= [ &+Coordinates( V, V!wt ) : wt in w1 ];

       mult1:= mults[1];

       for i in [1..#w1] do
           ind:= Index( wts, w1[i] );
           if ind gt 0 then
              mults[ ind ] -:= mult1*m1[i];
           else
              Append( ~wts, w1[i] );
              Append( ~mults, -mult1*m1[i] );
              Append( ~levels, l1[i] );
           end if;
       end for; 

       // get rid of the ones with zero multiplicity

       i:= 1;
       while i le #wts do
           if mults[i] eq 0 then
              Remove( ~wts, i );
              Remove( ~mults, i );
              Remove( ~levels, i );
           else
              i:= i+1;
           end if;
       end while;

       // sort again... 

       Sort( ~levels, f, ~p );
       w1:= [ ]; m1:= [ ];
       for i in [1..#wts] do
          j:= i^p;
          w1[i]:= wts[j];
          m1[i]:= mults[j];
       end for;
       wts:= w1;
       mults:= m1;

    end while;
        
    return w,m;

end function;


adams:= function( R, k, lam )

   
     // Here R is a root datum, k an integer, and lam a
     // weight (sequence of non-negative integers). This 
     // function returns the formal decomposition of the 
     // character wihc is k times the character of lam.

     w,m:= DominantCharacter( R, lam );
     for i in [1..#w] do
         w[i]:= k*w[i];
     end for;
     return formal_dec( R, w, m );

end function;


sym_alt_dec:= function( R, n, lam, alt )

     // alt = 1 if it is an alternating power, symmteric
     // power otherwise. This function returns the highest weights
     // and their multiplicities that occur in a direct sum decomposition
     // of the symmetric (alternating) power of the irreducible module 
     // with highest weight lam. 

     www:= [ ]; mmm:= [ ];
     
     for k in [1..n-1] do

         if alt eq 1 then
            sign:= (-1)^(k-1);
         else
            sign:= 1;
         end if;

         w1, m1:= $$( R, n-k, lam, alt );
         w2, m2:= adams( R, k, lam );

         for i in [1..#w1] do
             for j in [1..#w2] do
                 w,m:= DecomposeTensorProduct( R, Eltseq( w1[i] ),
                                                  Eltseq( w2[j] ) );
                 mu:= m1[i]*m2[j];
                 for s in [1..#w] do
                     ind:= Index( www, w[s] );
                     if ind gt 0 then
                        mmm[ind] +:= sign*mu*m[s];
                     else
                        Append( ~www, w[s] );
                        Append( ~mmm, sign*mu*m[s] );
                     end if;
                 end for;

             end for;

         end for;
     end for;


     // Have to add the n-th term
     w, m:= adams( R, n, lam );
     if alt eq 1 then
        sign:= (-1)^(n-1);
     else
        sign:= 1;
     end if;
     for s in [1..#w] do
         ind:= Index( www, w[s] );
         if ind gt 0 then
            mmm[ind] +:= sign*m[s];
         else
            Append( ~www, w[s] );
            Append( ~mmm, sign*m[s] );
         end if;
     end for;

     i:= 1;
     while i le #mmm do
           if mmm[i] eq 0 then
              Remove( ~www, i );
              Remove( ~mmm, i );
           else
              i:= i+1;
           end if;
     end while;


     for i in [1..#mmm] do
         mmm[i]:= Integers()!( mmm[i]/n );
     end for;

     return www, mmm;

end function;

intrinsic DecomposeSymmetricPower( R::RootDtm, n::RngIntElt, w ) -> 
                                                       SeqEnum
    {The decomposition of the symmetric power of the highest weight
      module with highest weight w} 

   // Here R is a root datum corresponding to a semisimple Lie algebra L,
   // n is a positive integer, and w is a dominant weight. Let V be the 
   // highest weight modules with highest weight w. Then the symmetric
   // power S^n(V) splits as a 
   // direct sum of highest weight modules. This function returns two lists;
   // one list contains the highest weights that occur in this decomposition,
   // the other contains the multiplicities.

    w:= Eltseq( w );

    require IsCrystallographic( R ):
       "This function only works for crystallographic root data";

    rank:= Rank( R );

    require #w eq rank : "The weight is not of the correct length";

    require &and[ IsIntegral( w[i] ) and w[i] ge 0 : i in [1..rank] ] :
       "The weight must be dominant integral";

    w,m:= sym_alt_dec( R, n, w, 0 );

    return w, m;


end intrinsic;


intrinsic DecomposeExteriorPower( R::RootDtm, n::RngIntElt, w ) -> 
                                                       SeqEnum
    {The decomposition of the exterior power of the highest weight
      module with highest weight w} 

   // Here R is a root datum corresponding to a semisimple Lie algebra L,
   // n is a positive integer, and w is a dominant weight. Let V be the 
   // highest weight modules with highest weight w. Then the exterior
   // power /\^n(V) splits as a 
   // direct sum of highest weight modules. This function returns two lists;
   // one list contains the highest weights that occur in this decomposition,
   // the other contains the multiplicities.

    w:= Eltseq( w );

    require IsCrystallographic( R ):
       "This function only works for crystallographic root data";

    rank:= Rank( R );

    require #w eq rank : "The weight is not of the correct length";

    require &and[ IsIntegral( w[i] ) and w[i] ge 0 : i in [1..rank] ] : 
       "The weight must be dominant integral";

    w,m:= sym_alt_dec( R, n, w, 1 );

    return w, m;


end intrinsic;



