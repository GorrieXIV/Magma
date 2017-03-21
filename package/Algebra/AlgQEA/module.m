freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes ModAlg: WeightsAndVectors, HighestWeightsAndVectors;


// This file contaisn functions for constructing irreducible modules
// over a quantized enveloping algebra.

import "qea.m" : in_p;
    

rev_lex_ord:= function( novar, m1, m2 )

    // m1 < m2? -1 if yes, 1 if no, 0 if equal.

    for k in [novar..1 by -1] do
        if Degree( m1, k ) lt Degree( m2, k ) then
           return -1;
        elif Degree( m1, k ) gt Degree( m2, k ) then
           return 1;
        end if;
    end for;
  
    return 0;

end function;


LM:= function( e )

    // The leading monomial of e...
    // Reverse lexicographical ordering...

    novar:= #PositiveRoots( Parent( e )`RootDatum );

    mns:= Monomials( e );
    cfs:= Coefficients( e );

    max:= mns[1];
    ind:= 1;
    cf:= cfs[1];

    m:= [ Degree( max, i ) : i in [1..novar] ];

    for k in [2..#mns] do

        // we look for the last nonzero position in the list that
        // is the difference between the exponent list of mns[k] and m.
        // dif will be the value of this difference at that position.

        dif:= 0;
        j:= novar;
     
        while j ge 1 and dif eq 0 do
              dif:= Degree( mns[k], j ) - m[j];
              j:= j-1;
        end while;

        if dif gt 0 then
            max:= mns[k];
            ind := k;
            cf:= cfs[k];
            m:= [ Degree( max, i ) : i in [1..novar] ];
        end if;
    end for;

    return [* max, m, cf, ind *];

end function;


LeftRed:= function( G, lms, DL, P, p )

    // We left-reduce the QUEA element `p' modulo the elements in `G'.
    // Here `lms' is a list of leading monomials of the elts of `G'
    // (i.e., the outputs of the previous function). 
    // DL is a monomial division list, corr to the poly ring P.

    U:= Parent( p );

    reduced:= false;
    res:= Zero( U );

    while p ne 0 do

        mmm:= LM( p );

        // look for a factor...
        mn:= One( P );
        for j in [1..#mmm[2]] do
            mn:= mn*(P.j)^mmm[2][j];
        end for;
        ind:= Divisor( DL, mn );
      
        if ind eq 0 then

           // there is no factor, move lm to res
           res:= res + mmm[3]*mmm[1];
           p:= p - mmm[3]*mmm[1];

        else            

           // reduce...
           fac:= [ mmm[2][i] - lms[ind][2][i] : i in [1..#mmm[2]] ];
           mn:= One( U );
           for i in [1..#fac] do
              if fac[i] ne 0 then
                 for j in [1..fac[i]] do
                     mn:= mn*U.i;
                 end for; 
                 mn:= Monomials( mn )[1];
              end if;
           end for;
           h:= mn*G[ind];

           // look for the coefficient of the leading mon of p in h;
           // then subtract the correct multiple of h from p
           // (note that this coeffcient is not necessarily 1, as 
           // e.g., x*x = [2]_q x^2...).
           mns:= Monomials( h );
           cfs:= Coefficients( h );
           i:= Position( mns, mmm[1] );
           p:= p - mmm[3]/cfs[i]*h;

        end if;
                  
    end while;

    return res;

end function;

     
append_div_list:= procedure( ~DL, P, mon )

    // Here `mon' is a monomial in F's;
    // we append it to the division list DL.

    novar:= #PositiveRoots( Parent( mon )`RootDatum );
    m:= One( P );
    for j in [1..novar] do
        m:= m*( P.j )^Degree( mon, j );
    end for;
    Append( ~DL, m );
     
end procedure;



////////////////////////////////////////////////////////////////////////////
//
//  And now the functions that construct the representation.
//  ModuleData computes a list of data that defines the module;
//  this is then used by HighestWeightRepresentation to 
//  construct the representation matrices.
//
//
Module_Dat:= function( U, hw )

     // Compute a big list of data needed to be able to compute
     // representation matrices.

     find_factor:= function( novar, mon, P, MDL )

        // Here `mon' is a monomialin F's
        // `MDL' is a monomial division list; we establish
        // whether there is a leading monomial that is a factor of mon.
        // P is the polynomial ring corresponding to lms. 

        m:= One( P );
        for j in [1..novar] do
            m:= m*( P.j )^Degree( mon, j );
        end for;

        i:= Divisor( MDL, m );
        if i gt 0 then 
           return true;
        end if; 
        return false;

     end function;

     // first we make a list of all weights, along with multiplicities.

     R:= U`RootDatum;
     q:= CoefficientRing( U ).1;
     ch,mm:= DominantCharacter( R, hw );
     www:= {@@};
     mults:= [ ];
     W:= CoxeterGroup( R );

     for i in [1..#ch] do
         o:= [ Eltseq( x ) : x in WeightOrbit( W, ch[i] : Basis:="Weight" ) ];
         for j in o do Include( ~www, j ); end for;
         mults:= mults cat [ mm[i] : k in [1..#o] ];
     end for;

     // `levels' will be a list of lists, and `levels[k]' is the list of
     // weights of level `k-1'.
     // `weights' will be the list of all weights, sorted according to level.
     // `wd' will be the list of the weights of the extended weight diagram,
     // also sorted according to level.
     // `levwd' will be the list of the levels of the elements of `wd'.

     rank:= Rank( R );
     levels:= [ {@ hw @} ];
     weights:= {@@};
     k:=1;
     wd:= [ hw ];
     levwd:= [ 0 ];
     posR:= U`Roots[2];   // i.e., positive roots in weight basis
     novar:= #posR;
     posR:= [ Eltseq( posR[i] ) : i in [1..novar] ];
     lcombs:= U`Roots[1];  // i.e., positive roots in root basis
     lcombs:= [ Eltseq( lcombs[i] ) : i in [1..novar] ];
     hts:= [ &+lcombs[i] : i in [1..novar] ];

     // We need to shuffle things around to get the roots into
     // convex order, (since later on we multiply things in the quea,
     // it is of paramount importance to attach the correct root to each 
     // generator of the uea).

     conv:= U`Perm;
     posR:= [ posR[conv[i]] : i in [1..novar] ];
     lcombs:= [ lcombs[ conv[i] ] : i in [1..novar] ];
     hts:= [ hts[conv[i]] : i in [1..novar] ];

     while k le #levels do
         for i in [1..#levels[k]] do
             w:= levels[k][i];
             for j in [1..#posR] do
                 w1:= [ w[u] - posR[j][u] : u in [1..rank] ];
                 lev:= IntegerRing()!(k + hts[j]);
                 if w1 in www then
                     if IsDefined( levels, lev ) then
                         if not w1 in levels[lev] then
                             Include( ~levels[lev], w1 );
                         end if;
                     else
                         levels[lev]:= {@ w1 @};
                     end if;
                 end if;
                 if not w1 in wd then
                     Append( ~wd, w1 );
                     Append( ~levwd, lev-1 );
                 end if;
 
             end for;
         end for;
         k:= k+1;
     end while;

     // we have to sort the elements in wd according to level...
     f:= function( a, b )
 
         if a lt b then return -1; end if;    
         if a eq b then return 0; end if;
         return 1;
     end function;

     Sort( ~levwd, f, ~p );
     wd1:= [ ];
     for i in [1..#wd] do
        j:= i^p;
        wd1[i]:= wd[j];
     end for;
     wd:= wd1;

     for k in levels do
         for u in k do
             Include( ~weights, u );
         end for;
     end for;

     // `lents' is a list of the lengths of the elements of `levels'; this is
     // used to calculate the position of an element of the list `weights'
     // efficiently.

     lents:=[ #x : x in levels];
     maxlev:= #levels;

     // `wcfs' will be a list of coefficient-lists. The k-th element of `cfs'
     // are the coefficients $k_i$ in the expression `wd[k] = hw - \sum_i k_i
     // \alpha_i', where the \alpha_i are the fundamental roots.

     fund:= [ U`Roots[2][u] : u in [1..rank ] ];  
                // i.e., simple roots in weight basis

     V:= KSpace( RationalField(), rank );
     vecs:= [ V!fund[i] : i in [1..rank] ];
     W:= sub<V|vecs>;
     mat:= Matrix( [ Coordinates( W, vecs[i] ) : i in [1..rank] ] );
     mat:= mat^-1;
     wcfs:= [ Eltseq( Vector( Coordinates( W, W!(Vector( hw ) - Vector( x )) 
                         ))*mat ) : x in wd ]; 

     // `paths' is the list of normal monomials of each weight in `weights'.
     // `GB' is the Groebner basis, as a flat list, `lms' are the
     // corresponding leading monomials.

     paths:= [ [ One(U) ] ];
     GB:= [ ];
     lms:= [ ];

     P:= PolynomialRing( IntegerRing(), novar );
     DL:= MonomialDivisionList(P);

     k:= 2;

     while k le #wd do

        // We take all weights of level equal to the level of `wd[k]'
        // together, and construct the corresponding parts of the Groebner
        // basis simultaneously.

        w:= [ ]; curlev:= levwd[k];
        ccc:= {@@};
        while k le #wd and levwd[k] eq curlev do
            Append( ~w, wd[k] );
            Include( ~ccc, wcfs[k] );
            k:= k+1;
        end while;

        // `mons' will be a list of sets of monomials of the QUAE.
        // They are candidates for the normal monomials of the weights in `w'.

        mons:= [ ];
        for j in [1..#w] do
            mons[j]:= [ ];
            for i in [1..#posR] do

                //We construct all weights of lower levels (that already have
                //been taken care of), connected to the weight `w'.

                w1:= [ w[j][u] + posR[i][u] : u in [1..rank] ];
                lev:= IntegerRing()!(curlev - hts[i]+1);

                if lev gt 0 and lev le maxlev then
                    pos:= Index( levels[lev], w1 );
                else
                    pos:= 0;
                end if;

                if pos ne 0 then // `w1' is a weight of the representation.

                  //`pos' will be the position of `w1' in the list `weights'.

                    pos:= pos + &+lents[ [1..lev-1] ];

                    for m in paths[pos] do

                        // fit F_i in m (commutatively)
                        mn:= One( U );
                        for v in [1..novar] do
                            if v eq i then
                               di:= Degree( m, v ) +1;
                            else
                               di:= Degree( m, v );
                            end if;
                            for r in [1..di] do
                                mn:= mn*U.v;
                            end for;
                            mn:= Monomials( mn )[1];
                        end for;

                        if not mn in mons[j] then
                           Append( ~mons[j], mn );
                        end if;
                    end for;
                end if;
            end for;
        end for;

        // `Gk' will contain the part of the Groebner basis corresponding
        // to the weights in `w'. `Glmsk' are the corresponding leading
        // monomials. The list `isdone' keeps track of the positions
        // with a complete part of the GB. `mmm' are the corresponding
        // normal monomials.

        Gk:= [* *];
        isdone:= [ false : i in [1..#w] ];
        mmm:= [ ];  // normal monomials...

        for j in [1..#w] do

            i:= 1;
            while i le #mons[j] do
                if find_factor( novar, mons[j][i], P, DL ) then
                   // the monomial reduces; get rid of it. 
                   Remove( ~mons[j], i );
                else
                   i+:= 1;
                end if;
            end while;        

            // Sort the monomials, biggest first:
            Sort( ~mons[j], function( a, b ) 
               return -rev_lex_ord( novar, a, b ); end function );

            Gk[ j ]:= [ ];

            if curlev+1 gt maxlev or not w[j] in levels[ curlev+1 ] then

            // `w[j]' is not a weight of the representation; this means that
            // there are no normal monomials of weight `w[j]'. Hence we can
            // add all candidates in `mons' to the Groebner basis.
                  
                Gk[j]:= mons[j];
                isdone[j]:= true;
                // normal monomials are empty here...
                mmm[j]:= [ ];
            else
                mmm[j]:= mons[j];
            end if;
        end for;

        // For all remaining weights we know the dimension
        // of the corresponding weight space, and we calculate Groebner
        // basis elements of weight `w' until we can reduce all monomials
        // except a number equal to this dimension.
        // `mmm' will contain the lists of normal monomials, from which we
        // erase elements if they are reducible.

        multiplicity:= [ ];
        for j in [1..#w] do
            if not isdone[j] then
               // w[j] is a weight of the rep, we get its mult

               pos:= Index( www, w[j] );
               Append( ~multiplicity, mults[pos] );
               //if the number of candidate monomials is equal to the 
               //multiplicity, then isdone will be true, and we add the 
               //monomials to paths:
               if #mons[j] eq mults[pos] then
                  paths[ Index( weights, w[j] ) ]:= mons[j];
                  isdone[j]:= true;
               end if;

            else
               Append( ~multiplicity, 0 );
            end if;
        end for;

        we_had_enough:= &and( isdone );
        lent:= #GB;

        for i in [1..lent] do
            if we_had_enough then break i; end if;
            f:= GB[i];

            // `prelcm' will be the leading monomial of `f', represented 
            // in the `long' form (i.e., as a monomial, rather than in
            // ind-exp form).
            prelcm:= lms[i][2];

            for j in [1..i] do

                if we_had_enough then break j ; end if;
                g:= GB[j];

                // `lcm' will be the least common multiple of the LM of `f'
                // and the LM of `g', represented as a list of length novar.
                m2a:= lms[j][2];
                lcm:= prelcm;
                for l in [1..novar] do
                    lcm[l]:= Maximum(lcm[l],m2a[l]);
                end for;

                // We check whether `lcm' is of the correct
                // weight; only in that case we form the S-element.
                lc:= [ 0 : u in [1..rank] ];
                for l in [1..#lcm] do
                    if lcm[l] ne 0*lcm[l] then
                       lc:= [ lc[u]+lcm[l]*lcombs[l][u] : u in [1..rank] ];
                    end if;
                end for;

                pp:= Index( ccc, lc );

                if pp ne 0 and not isdone[pp] then

                    // w1*f-w2*g will be the S-element of `f' and `g'.
                    w1:= [ lcm[u]-prelcm[u] : u in [1..novar] ];
                    w2:= lcm;
                    for l in [1..novar] do
                        w2[l]:= w2[l]-m2a[l];
                    end for;

                    // We make `w1' and `w2' into QUEA elements,
                    // `fac1' and `fac2' respectively.
                    fac1:= One(U); fac2:= One(U);
                    for l in [1..novar] do
                        for v in [1..w1[l]] do
                            fac1:= fac1*U.l;
                        end for;                        
                        for v in [1..w2[l]] do
                            fac2:= fac2*U.l;
                        end for;
                        fac1:= Monomials( fac1 )[1];
                        fac2:= Monomials( fac2 )[1];
                    end for;

                    fac1:= fac1*f;
                    fac2:= fac2*g; 

                    // `comp' will be the S-element of `f' and `g'.
                    // We reduce it modulo the elements we already have,
                    // and if it does not reduce to 0 we add it, and remove
                    // its leading monomial from the list of normal
                    // monomials.

                    comp:= LM( fac2 )[3]*fac1-LM( fac1 )[3]*fac2;
                    comp:= LeftRed( GB, lms, DL, P, comp );

                    if comp ne 0 then

                        vv:= [ 0*q : l in [1..#mons[pp]] ];
                        mns:= Monomials( comp );
                        cfs:= Coefficients( comp );
                        for l in [1..#mns] do
                           vv[ Index( mons[pp], mns[l])]:= cfs[l];
                        end for;
                        Append( ~Gk[pp], vv );

                        if #mons[pp] - #Gk[pp] eq multiplicity[pp] then
                           M:= EchelonForm( Matrix( Gk[pp] ) );
                           B:= [ ];
                           for l in [1..#Gk[pp]] do
                               if not IsZero( M[l] ) then
                                  Append( ~B, Eltseq( M[l] ) );
                               end if;
                           end for;

                           Gk[pp]:= B;
                           if #mons[pp] - #Gk[pp] eq multiplicity[pp] then

                              B:= [ ];
                              for u in [1..#Gk[pp]] do
                                  // First we rebuild the elements of Gk[pp]
                                  // into elms of the quea.
                                  vv:= Zero( U );
                                  lm:= Zero( U );
                                  for l in [1..#Gk[pp][u]] do
                                      if Gk[pp][u][l] ne 0 then
                                         vv:= vv + Gk[pp][u][l]*mons[pp][l];
                                         if lm eq 0 then
                                            lm:= mons[pp][l];
                                         end if;
                                      end if;
                                  end for;
                                  Append( ~B, vv );

                                  // erase the leading monomial (stored in lm)
                                  for l in [1..#mmm[pp]] do
                                      if mmm[pp][l] eq lm then
                                         Remove( ~mmm[pp], l );
                                         break l;
                                      end if;
                                  end for;
                              end for;
                              Gk[pp]:= B;
                              isdone[pp]:= true;

                              // the monomials in mmm[pp] are all normal;
                              // we add them to paths:
                              pos:= Index( weights, w[pp] );
                              paths[pos]:= mmm[pp];
                              we_had_enough:= &and( isdone );
                           end if;
                        end if;
                    end if;                    
                end if;   // done processing this S-element.

            end for;   // loop over j
        end for;     // loop over i

        for j in [1..#w] do

            if #Gk[j] gt 0 then
               GB:= GB cat Gk[j];
               for i in [1..#Gk[j]] do
                   lm:= LM( Gk[j][i] );
                   append_div_list( ~DL, P, lm[1] );
                   Append( ~lms, lm );
               end for;

            end if;
       
        end for;

    end while; //loop over k, we now looped through the entire 
               //extended weight diagram.

    mons:= {@@};
    wts:= [ ];
    for i in [1..#paths] do
        for j in [1..#paths[i]] do
            Include( ~mons, paths[i][j] );
            Append( ~wts, weights[i] );
        end for;
    end for;

    // `mats' will contain the matrices of the F's and the E's; first
    // there will be `novar' F-matrices, then `rank' holes, then `novar'
    // E-matrices.
    posR:= U`Roots[1];  // positive roots in root basis
    conv:= U`Perm;
    CF:= U`NormalizedCoxeterForm;    // normalized bilinear form.
    mats:= [ ];

    for j in [1..novar] do
        // compute the matrix of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // we do it the `hard' way
           mat:= [ ];
           for m in mons do
               u:= U.pos*m;
               mns:= Monomials( u );
               cfs:= Coefficients( u );
               f:= Zero( U );
               mm:= {@@};
               for k in [1..#mns] do
                   mon:= mns[k];
                   cf:= cfs[k];
                   ends_with_e:= false;
                   for i in [1..novar] do
                       if Degree( mon, novar + rank + i ) gt 0 then
                          ends_with_e:= true;
                          break i;
                       end if;
                   end for;
                   if not ends_with_e then

                      for i in [1..rank] do
                          kd:= KDegree( mon, i );
                          // multiply by the right constant
                          qp:= q^( Integers()!( CF[i][i]/2 ));
                          cf:= cf*GaussianBinomial(hw[i],kd[2],qp);
                          cf:= cf*qp^(hw[i]*kd[1]);
                      end for;

                      // get the f-bit:
                      fmon:= One( U );
                      for i in [1..novar] do
                          di:= Degree( mon, i );
                          for v in [1..di] do
                              fmon:= fmon*U.i;
                          end for;
                          fmon:= Monomials( fmon )[1];
                      end for;
                      f:= f + cf*fmon;
                   end if;
               end for;

               f:= LeftRed( GB, lms, DL, P, f );
 
               v:= [ 0*q : i in [1..#mons] ];
               mns:= Monomials( f );
               cfs:= Coefficients( f );
               for k in [1..#mns] do
                   v[ Position( mons, mns[k] ) ]:= cfs[k];
               end for;
          
               Append( ~mat, v );
           end for;
           mats[pos]:= SparseMatrix( Transpose( Matrix( mat ) ) );

        else // i.e., j > rank

           for k in [1..rank] do
                // We find a simple root r such that posR[j]-r is also a root.

                k1:= Position( posR, posR[j] - posR[k] );
                if k1 gt 0 then
                   k1:= Position( conv, k1 );
                   k2:= Position( conv, k );

                   if k1 gt k2 then
                      pair:= [ k1, k2 ];
                   else
                      pair:= [ k2, k1 ];
                   end if;

                   rel:= U.pair[1]*U.pair[2];

                   // we establish whether F_j is in there
                   mns:= Monomials( rel );
                   cfs:= Coefficients( rel );
                   pp:= Position( mns, U.pos );
                   if pp gt 0 then break k; end if;
                end if;
           end for;
                
           cf:= cfs[ pp ];
           rel:= rel - cf*mns[pp];
           rel:= (-1/cf)*rel; 

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
            
           mat:= (1/cf)*Matrix( mats[ pair[1] ] )*Matrix( mats[ pair[2] ] );
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               A:= ScalarMatrix( #mons, 1 );
               for l in [1..novar] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                           -in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      A *:= Matrix( mats[ l ] )^dl/cf;
                   end if; 
               end for;
               mat +:= cfs[k]*A;
           end for;
           
           mats[pos]:= SparseMatrix( mat );
          
        end if;
    end for;

    // same thing for the E-s

    for j in [1..novar] do
        // compute the matrix of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j )+rank+novar;
        if j le rank then  // we do it the `hard' way
           mat:= [ ];

           for m in mons do

               u:= U.pos*m;
               mns:= Monomials( u );
               cfs:= Coefficients( u );
               f:= Zero( U );
               mm:= {@@};

               for k in [1..#mns] do
                   mon:= mns[k];
                   cf:= cfs[k];
                   ends_with_e:= false;
                   for i in [1..novar] do
                       if Degree( mon, novar + rank + i ) gt 0 then
                          ends_with_e:= true;
                          break i;
                       end if;
                   end for;
                   if not ends_with_e then

                      for i in [1..rank] do
                          kd:= KDegree( mon, i );

                          // multiply by the right constant
                          qp:= q^( Integers()!( CF[i][i]/2 ));
                          cf:= cf*GaussianBinomial(hw[i],kd[2],qp);
                          cf:= cf*qp^(hw[i]*kd[1]);
                      end for;

                      // get the f-bit:
                      fmon:= One( U );
                      for i in [1..novar] do
                          di:= Degree( mon, i );
                          for v in [1..di] do
                              fmon:= fmon*U.i;
                          end for;
                          fmon:= Monomials( fmon )[1];
                      end for;
                      f:= f + cf*fmon;

                   end if;
               end for;

               f:= LeftRed( GB, lms, DL, P, f );

               v:= [ 0*q : i in [1..#mons] ];
               mns:= Monomials( f );
               cfs:= Coefficients( f );

               for k in [1..#mns] do
                   v[ Position( mons, mns[k] ) ]:= cfs[k];
               end for;
 
               Append( ~mat, v );
           end for;              

           mats[pos]:= SparseMatrix( Transpose( Matrix( mat ) ) );

        else // i.e., j > rank

           for k in [1..rank] do
                // We find a simple root r such that posR[j]-r is also a root.

                k1:= Position( posR, posR[j] - posR[k] );
                if k1 gt 0 then
                   k1:= Position( conv, k1 )+novar+rank;
                   k2:= Position( conv, k )+novar+rank;

                   if k1 gt k2 then
                      pair:= [ k1, k2 ];
                   else
                      pair:= [ k2, k1 ];
                   end if;

                   rel:= U.pair[1]*U.pair[2];

                   // we establish whether E_j is in there
                   mns:= Monomials( rel );
                   cfs:= Coefficients( rel );
                   pp:= Position( mns, U.pos );
                   if pp gt 0 then break k; end if;
                end if;

           end for;

           cf:= cfs[ pp ];
           rel:= rel - cf*mns[pp];
           rel:= (-1/cf)*rel; 

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
            
           mat:= (1/cf)*Matrix( mats[ pair[1] ] )*Matrix( mats[ pair[2] ] );
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );

           for k in [1..#mns] do
               A:= ScalarMatrix( #mons, 1 );
               for l in [1..novar] do
                   dl:= Degree( mns[k], l+novar+rank );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                           -in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      A:= A*Matrix( mats[ novar+rank+l ] )^dl/cf;
                   end if; 
               end for;
               mat +:= cfs[k]*A;
           end for;
           
           mats[pos]:= SparseMatrix( mat );

        end if;
    end for;
    delete DL;	// AKS: delete first before P

    return mats, wts;

end function;


intrinsic HighestWeightRepresentation( U::AlgQUE, hw::SeqEnum ) -> UserProgram
   {The highest weight representation of the quantized enveloping algebra
     U with highest weight hw }

    rank:= Rank( U`RootDatum );
    require #hw eq rank: "The weight is not of the correct length";
    require &and[ IsIntegral( hw[i] ) and hw[i] ge 0 : i in [1..rank] ]:
       "The weight must be dominant integral";

    mats, wts:= Module_Dat( U, hw );
  
    rho:= function( x )

          R:= U`RootDatum;
          q:= CoefficientRing(U).1;
          conv:= U`Perm;
          CF:= U`NormalizedCoxeterForm;
          rank:= Rank( R );
          posR:= U`Roots[1];
          s:= #posR;
          dim:= #wts;
          F:= CoefficientRing(U);
          mat:= ScalarMatrix( F, dim, 0*q );

          mx:= Monomials( x );
          cx:= Coefficients( x );

          for i in [1..#mx] do

               A:= SparseMatrix( ScalarMatrix( F, dim, q^0 ) );
               for l in [s..1 by -1] do
                   // see whether there is an E; starting with the
                   // highest one...
                   deg:= Degree( mx[i], s+rank+l);
                   if deg gt 0 then
                      qa:= q^( Integers()!(
                         in_p( CF, posR[ conv[l] ], posR[ conv[l] ] )/2 ) );
                      A := (Matrix( mats[ s+rank+l ] )^deg)*A;
                      A:= A/GaussianFactorial( deg, qa );
                   end if;
               end for;

               for l in [rank..1 by -1] do
                   // loop over the K's...
                   deg:= KDegree( mx[i], l );
                   tt:= [ ];
                   qa:= q^( Integers()!( CF[l][l]/2 ) );
                   for j in [1..dim] do
                       cf:= GaussianBinomial( wts[j][l], deg[2], qa );
                       cf:= cf*qa^( wts[j][l]*deg[1] );
                       if not IsZero( cf ) then
                          Append( ~tt, <j,j,cf> );
                      end if;
                   end for; 
                   A := Matrix( F, dim, dim, tt )*A;
                   A:= SparseMatrix( A );
               end for;

               for l in [s..1 by -1] do
                   // see whether there is an F; starting with the
                   // highest one...
                   deg:= Degree( mx[i], l);
                   if deg gt 0 then
                      qa:= q^( Integers()!(
                         in_p( CF, posR[ conv[l] ], posR[ conv[l] ] )/2 ) );
                      A := (Matrix( mats[ l ] )^deg)*A;
                      A:= A/GaussianFactorial( deg, qa );
                   end if;
               end for;

               mat +:= cx[i]*Matrix( A );
          end for;

          return mat;

    end function;

    return rho;

end intrinsic;


intrinsic HighestWeightModule( U::AlgQUE, hw::SeqEnum ) -> ModAlg
   {The highest weight module of the quantized enveloping algebra
     U with highest weight hw }

    rank:= Rank( U`RootDatum );
    require #hw eq rank: "The weight is not of the correct length";
    require &and[ IsIntegral( hw[i] ) and hw[i] ge 0 : i in [1..rank] ]:
       "The weight must be dominant integral";

    mats, wts:= Module_Dat( U, hw );

    // We take transposes of the matrices, because we are acting from
    // the right on vectors (it is a left module though).

    for i in [1..#mats] do
        if IsDefined( mats, i ) then
           mats[i]:= Transpose( mats[i] );
        end if;
    end for;

    V:= RModule( CoefficientRing( U ), #wts );

    rho:= function( x, v )

          R:= U`RootDatum;
          q:= CoefficientRing(U).1;
          conv:= U`Perm;
          CF:= U`NormalizedCoxeterForm;
          rank:= Rank( R );
          posR:= U`Roots[1];
          s:= #posR;
          dim:= #wts;
          F:= CoefficientRing(U);

          mx:= Monomials( x );
          cx:= Coefficients( x );

          u:= 0*v;

          for i in [1..#mx] do

	       w:= v;

               for l in [s..1 by -1] do
                   // see whether there is an E; 
                   deg:= Degree( mx[i], l+rank+s );
                   if deg gt 0 then
                      qa:= q^( Integers()!(
                         in_p( CF, posR[ conv[l] ], posR[ conv[l] ] )/2 ) );
                      for k in [1..deg] do
                          w := w*mats[ l+rank+s ];
                      end for;
                      w:= w/GaussianFactorial( deg, qa );
                   end if;
               end for;
               w:= V!Eltseq(w); 

               for l in [1..rank] do
                   // loop over the K's...
                   deg:= KDegree( mx[i], l );
                   qa:= q^( Integers()!( CF[l][l]/2 ) );
                   for j in [1..dim] do

           	       if not IsZero( Eltseq(w)[j] ) then
                          cf:= GaussianBinomial( wts[j][l], deg[2], qa );
                          cf:= cf*qa^( wts[j][l]*deg[1] );
                          w[j]:= w[j]*cf;
                      end if;
                   end for; 
               end for;

               for l in [s..1 by -1] do
                   // see whether there is an F; 
                   deg:= Degree( mx[i], l );
                   if deg gt 0 then
                      qa:= q^( Integers()!(
                         in_p( CF, posR[ conv[l] ], posR[ conv[l] ] )/2 ) );
                      for k in [1..deg] do
                          w:= w*mats[ l ];
                      end for;
                      w:= w/GaussianFactorial( deg, qa );
                   end if;
               end for;
               w:= V!Eltseq(w); 
               u:= u + cx[i]*w;

          end for;

          return u;

    end function;

    M:= Module( U, 
         map< CartesianProduct( U, V ) -> V | t :-> rho( t[1], t[2] ) > );

    // Add the weights and vectors as an attribute...
    ww:= [ ]; vv:= [ ];
    for i in [1..#wts] do
        pos:= Position( ww, wts[i] );
        if pos gt 0 then
           Append( ~vv[pos], M.i );
        else
           Append( ~vv, [ M.i ] );
           Append( ~ww, Vector( Integers(), wts[i] ) );
        end if;
    end for;
    M`WeightsAndVectors:= [* ww, vv *];
    return M;

end intrinsic;


WtsAndVecsOfQEAModule:= function( V )

     // Here V is a module over a quantized enveloping algebra;
     // the output of this function is formed by two sequences:
     // the first is a sequence of weights,
     // the second a sequence of sequences of basis vectors of V
     // the basis elements in the i-th sequence are of the i-th weight.

     // We assume that all basis vectors are weight vectors.

     U:= Algebra( V );

     q:= CoefficientRing( U ).1;
     R:= RootDatum( U );
     s:= #PositiveRoots( R );
     rank:= Rank(R);
     CF:= U`NormalizedCoxeterForm;
     wts:= [ ];
     vecs:= [ ];

     sp:= RModule( CoefficientRing(V), Dimension(V) );

     for v in Basis(V) do
         wt:= [ ];
         W:= sub< sp | [ sp!Coordinates( V, v ) ] >;
         for i in [s+1..s+rank] do
             w:= sp!Coordinates( V, U.i^v );
             error if not w in W, "The basis of V does not consist of weight vectors"; 
             a:= Evaluate( Derivative( Coordinates( W, w )[1] ), 1 );
             a:= Integers()!( a*2/CF[i-s][i-s] );
             Append( ~wt, a );
         end for;
         wt:= Vector( Integers(), wt );
         pos:= Position( wts, wt );
         if pos eq 0 then
            Append( ~wts, wt );
            Append( ~vecs, [ v ] );
         else
            Append( ~vecs[pos], v );
         end if;
     end for;

     
     return wts,vecs;

end function;
             
             
  
HighWtsAndVecsOfQEAModule:= function( V )

     // same as previous function, but in this case we only
     // return the highest weights; this is effectively computing the
     // direct sum decomposition....

     U:= Algebra( V );

     R:= RootDatum( U );
     W:= CoxeterGroup( R );

     s:= #PositiveRoots( R );
     rank:= Rank(R);

     wts, vecs:= WeightsAndVectors( V );

     // decompose the character...

     hwts:= [ ];
     posR:= PosRootsWeightBasis( R );
     sim_rts:= [ posR[k] : k in [1..rank] ];
     char:= wts;
     mults:= [ #vv : vv in vecs ];

     while #char gt 0 do

        // Find a dominant weight wt such that wt+a is not a weight, for 
        // simple roots a.
        found:= false;
        k:= 1;
        while not found do
            wt:= char[k];
            if &and[ z ge 0 : z in Eltseq(wt) ] then
               found:= &and[ not wt+a in char : a in sim_rts ];
            end if;
            k:= k+1;
        end while;
        k:= k-1;
        Append( ~hwts, wt );

        // compute the character of this highest weight:
        c,m:= DominantCharacter( R, Eltseq( wt ) );
        ch:= [ ]; 
        mm:= [ ];
        for i in [1..#c] do
            o:= WeightOrbit( W, c[i] : Basis:="Weight" );
            ch cat:= IndexedSetToSequence( o );
            mm cat:= [ m[i] : j in [1..#o] ];
        end for;

        // subtract this character
        mult:= mults[k];

        for i in [1..#ch] do
            pos:= Position( char, ch[i] );
            mults[pos]:= mults[pos] - mult*mm[i];
            if mults[pos] eq 0 then
               Remove( ~char, pos );
               Remove( ~mults, pos );
            end if;
        end for;            
     end while;

     // compute the corresponding highest weight vectors...
     hwvecs:= [ ];
     n:= Dimension( V );
     for s in [1..#hwts] do
         pos:= Position( wts, hwts[s] );
         vv:= vecs[pos];
         eqs:= ZeroMatrix( CoefficientRing(U), #vv, n*rank );
         for i in [1..rank] do
             u:= U.( #posR+rank+Position( U`Perm, i ) );
             for j in [1..#vv] do
                 cc:= Coordinates( V, u^vv[j] );
                 for k in [1..n] do
                     eqs[j][(i-1)*n+k]:= cc[k];
                 end for;
             end for;
         end for;

         sp:= Nullspace( eqs );
         Append( ~hwvecs, [ &+[ b[i]*vv[i] : i in [1..#Eltseq(b)] ] : 
                                b in Basis(sp) ] );
         
     end for;

     return hwts, hwvecs;

end function;


TPOfQUAModules:= function( modules ) 

     U:= Algebra( modules[1] );

     dims:= [ Dimension( M ) : M in modules ];

     // inds will be a sequence of seqneces of indices, if the r-th 
     // sequence is e.g., [ 2, 1, 5 ], then the r-th basis vector of the
     // module that we are producing is V1.2\tensor V2.1\tensor V3.5
     // (where modules = [ V1, V2, V3 ]).
 
     inds:= {@ [] @};
     for i in [1..#dims] do
         inds1:= {@@};
         for j in [1..dims[i]] do
             for k in [1..#inds] do
                 Include( ~inds1, inds[k] cat [j] );
             end for;
         end for;
         inds:= inds1;
     end for;

     Sort( ~inds );

     M:= RModule( CoefficientRing(U), #inds );
     D:= Comultiplication( U, #modules );

     ten_vec:= function( tt, v )

           // Here tt is a tensor (something produced by the coproduct),
           // v is an element of M; we compute tt^v.

           cc:= Coordinates( M, v );
           w:= Zero(M);
           for i in [1..#cc] do
               if not IsZero( cc[i] ) then
                  ii:= inds[i];
                  for j in [1..#tt-1 by 2] do
                
                      crds:= [* tt[j][r]^modules[r].ii[r] : 
                                            r in [1..#modules] *];
                      if not &or[ IsZero( u ) : u in crds ] then
                      
                         crds:= [ Coordinates( modules[r], crds[r] ) : 
                                     r in [1..#modules] ];

                         vec_inds:= [ [] ];
                         cfs:= [ tt[j+1]*cc[i] ];
                         for k in [1..#crds] do
                             inds1:= [ ];
                             cfs1:= [ ];
                             for r in [1..#crds[k]] do
                                 if not IsZero( crds[k][r] ) then
                                    for t in [1..#vec_inds] do
                                        Append( ~inds1, vec_inds[t] cat [r] );
                                        Append( ~cfs1, cfs[t]*crds[k][r] );
                                    end for;
                                 end if;
                             end for;
                             vec_inds:= inds1;
                             cfs:= cfs1;
                         end for;
                                           
                         u:= Eltseq( Zero(M) );
                         for k in [1..#vec_inds] do 
                             u[ Index( inds, vec_inds[k] ) ]:= cfs[k];
                         end for;
                         w:= w + M!u;
                      end if;
                  end for;
               end if;
           end for;

           return w;
     end function;


     R:= RootDatum(U);
     s:= #PositiveRoots(R);
     rank:= Rank(R);
     CF:= U`NormalizedCoxeterForm;
     conv:= U`Perm;
     posR:= U`Roots[1];
     q:= CoefficientRing( U ).1;

     act:= function( x, v )

           mx:= Monomials( x );
           cx:= Coefficients( x );

           res:= Zero(M);
           for i in [1..#mx] do

               w:= v;

               // see whether there are E's:
               for k in [s..1 by -1] do
                   exp:= Degree( mx[i], s+rank+k );
                   if exp gt 0 then
                      ten:= D( U.(s+rank+k) );
                      for j in [1..exp] do
                          w:= ten_vec( ten, w );
                      end for;
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[k] ], 
                                      posR[ conv[k] ] )/2 ) );
                      w:= w/GaussianFactorial( exp, qa );   
                   end if;
               end for;

               // see whether there are K's:
               for k in [1..rank] do
                   exp:= KDegree( mx[i], k );
                   KK:= One(U);
                   if exp[1] gt 0 then
                      KK:= KK*U.(s+k);
                   end if;
                   if exp[2] gt 0 then
                      KK:= KK*KBinomial( U, k, exp[2] );
                   end if;
                   if not IsOne( KK ) then
                      ten:= D(KK);
                      w:= ten_vec( ten, w );
                   end if;
               end for;

               // see whether there are F's:
               for k in [s..1 by -1] do
                   exp:= Degree( mx[i], k );
                   if exp gt 0 then
                      ten:= D( U.k );
                      for j in [1..exp] do
                          w:= ten_vec( ten, w );
                      end for;
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[k] ], 
                                      posR[ conv[k] ] )/2 ) );
                      w:= w/GaussianFactorial( exp, qa );   
                   end if;
               end for;

               res:= res + cx[i]*w;

           end for;
           return res;

     end function;

     W:= Module( U, 
          map< CartesianProduct( U, M ) -> M | t :-> act( t[1], t[2] ) > );

     f:= function( tuple )


         cc:= [ ];
         for i in [1..#tuple] do
             Append( ~cc, Coordinates( modules[i], tuple[i] ) );
         end for;

         vec_inds:= [ [] ];
         cfs:= [ 1 ];
         for k in [1..#cc] do
             inds1:= [ ];
             cfs1:= [ ];
             for r in [1..#cc[k]] do
                 if not IsZero( cc[k][r] ) then
                    for t in [1..#vec_inds] do
                        Append( ~inds1, vec_inds[t] cat [r] );
                        Append( ~cfs1, cfs[t]*cc[k][r] );
                    end for;
                 end if;
             end for;
             vec_inds:= inds1;
             cfs:= cfs1;
         end for;
                                           
         u:= Eltseq( Zero(W) );
         for k in [1..#vec_inds] do 
             u[ Index( inds, vec_inds[k] ) ]:= cfs[k];
         end for;
         return W!u;

     end function;         

     return W, map< CartesianProduct( modules ) -> W | t :-> f(t) >;


end function;
