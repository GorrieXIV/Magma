freeze;

declare attributes AlgIUE: RootDatum, LieEmbedding;
declare attributes AlgLie: IntegralUEA;
import "chevbas.m" : WdG_ChevBasis;

/////////////////////////////////////////////////////////////////////////////
//
//  This file contains a function for constructing a highest weight module 
//  over a semisimple Lie algebra with a split Cartan subalgebra.
//
//  First there are some functions that allow us to work inside the 
//  universal enveloping algebra of such a Lie algebra.
//
//  Also there is a function for constructing the integral (Kostant Z-form)
//  universal enveloping algebra.
//


GetUEADescription:= function( L )

      // This returns a list of 
      //  rts : roots, first the negative, then the positive
      //   C  : Cartan matrix
      //   n  : number of positive roots
      //  rank: rank of the root system
      //  Ntab: if i, j are two root indices, then Ntab[i][j] is the number 
      //        N such that x_i*x_j = Nx_k, for some k,
      // hlist: hlist[i] is the list of coordinates of y_i*x_i as elt of the
      //        CSA.
      //  emb : a function embedding L in the universal enveloping algebra.
      //
      //
      //  Root coordinates work as follows: the y's (negative root vecs)
      //  are numbered 1..n, the x's (positive root vecs) are numbered
      //  n+rank+1..2*n+rank. So in Ntab there are a lot of undef's.

      // This data is used to compute products in the uea of a semisimple
      // Lie algebra.

      if assigned L`UEADescription then return L`UEADescription; end if;

      R,Rv,sim,C:= RootSystem( L );
      n:= IntegerRing()!(#R/2);
      rank:= #sim;
      x,y,h:= WdG_ChevBasis( L, CartanSubalgebra(L) );
      
      /* Fix h, because WdG_ChevBasis sometimes doesn't quite return a Chev. basis */
      if #h eq rank then
	    h := [ x[i]*y[i] : i in [1..rank] ];
	  else
		h := [ x[i]*y[i] : i in [1..rank] ] cat [ L!b : b in Basis(Centre(L)) ];
	  end if;

      rootspaces:= [ VectorSpaceWithBasis(Matrix([ x[i] ])) : i in [1..n] ]
              cat [ VectorSpaceWithBasis(Matrix([ y[i] ])) : i in [1..n] ];
      cartan:= VectorSpaceWithBasis( Matrix( [ h[i] : 
                                         i in [1..rank] ] ) ); 

      Ntab:= [ ];
      hlist:= [ ];
      for i in [1..2*n] do

         if i le n then 
            // it is the index of a y
            l1:= i;
            a:= y[i];
         else
            // index of an x
            l1:= i+rank;
            a:= x[i-n];
         end if;

         Ntab[l1]:= [ ];
         for j in [1..2*n] do

             if j le n then 
                // it is the index of a y
                l2:= j;
                b:= y[j];
             else
                // index of an x
                l2:= j+rank;
                b:= x[j-n];
             end if;

             if i ne j-n and j ne i-n then 
                // get N st [a,b] = N*xk
                c:= a*b;

                if c eq 0*c then
                   Ntab[l1][l2]:= 0;
                else
                   // find the root vector to which c is proportional:
                   k:=1;
                   pos:= 0;
                   while k le 2*n and pos eq 0 do
                      if c in rootspaces[k] then
                         pos:= k;
                      end if;
                      k:= k+1;
                   end while;
                      
                   Ntab[l1][l2]:= Coordinates( rootspaces[pos], 
                                                  rootspaces[pos]!c )[1];
                end if;
             else
                u:= Minimum( i, j );
                if not IsDefined( hlist, u ) then
                   vec:= [ ];
                   c:= x[u]*y[u];
                   hlist[u]:= ChangeUniverse(Coordinates( cartan, cartan!c ), Integers());
                end if;
             end if;

         end for;
      end for;

      // We must also represent the roots in the form (a1...al), where
      // ai is such that [ h[i]*x[j] ] = aj*x[j]....

      posRts:= [ ];
      for i in [1..n] do
          V:= rootspaces[i];
          posRts[i]:= [ Coordinates( V, V!( h[j]*x[i] ) )[1] : 
                                                  j in [1..rank] ];
      end for;
      rts:= [ ];
      for i in [1..n] do
          rts[i]:= Vector( [ -posRts[i][j] : j in [1..rank]] );
          rts[ n+i ]:= Vector( posRts[i] );
      end for;

      goodBas:= y cat h cat x;
      V:= VectorSpaceWithBasis( Matrix( goodBas ) );

      emb:= function( U, x )

         // embeds the element x\in L in the universal enveloping algebra U,
         // using the convention: negative root vecs, then Cartan elems,
         // then positive root vecs...

         cfs:= Coordinates( V, V!x );
         elm:= Zero( U );
         for i in [1..#cfs] do
             if not IsZero( cfs[i] ) then
                elm:= elm + cfs[i]*U.i;
             end if;
         end for;
         return elm;
      end function;

      L`UEADescription:= [* rts, ChangeRing(C, Integers()), n, rank, Ntab, hlist, emb *];
      return L`UEADescription;

end function;



////////////////////////////////////////////////////////////////////////////
//
//  Some functions for reducing elements, modulo others:

lex_ord:= function( m1, m2 )

    // m1 < m2? -1 if yes, 1 if no, 0 if equal.
    // For a description of the ordering see below (in the comments
    // to LeadingUEAMon).

    deg1:= TotalDegree( m1 );
    deg2:= TotalDegree( m2 );

    if deg1 lt deg2 then
       return -1;
    end if;

    if deg1 gt deg2 then
       return 1;
    end if;

    if m1 lt m2 then
       return 1;
    elif m2 lt m1 then
       return -1;
    else
       return 0;
    end if;
    
end function;

LeadingUEAMon:= function( novar, f )

    // The leading monomial of `f'; novar is the number of generators
    // of U^( N^- ). The following ordering seems to lead to the fastest
    // algorithm:
    //
    // * monomials of higher degree are bigger,
    // * monomials of equal degree are ordered anti-lex, i.e., 
    //   if a < b in the lex ordering then a is bigger than b in 
    //   our ordering.
    //
    // since in Magma the deglex ordering is used, the leading monomial
    // of an element (in our ordering) is simply the last monomial
    // that has degree equal to the first monomial.

    mns:= Monomials( f );
    cfs:= Coefficients( f );

    d:= TotalDegree( mns[1] );
    ind:= 2;
    while ind le #mns do
          if TotalDegree( mns[ind] ) lt d then
             break;
          end if;
          ind:= ind+1;
    end while;

    ind:= ind-1;

    mon:= mns[ind];
    m:= [ ];
    for k in [1..novar] do
        m[k]:= Degree( mon, k );
    end for;

    return [* mon, m, cfs[ind] *];

end function;


LeftReduce:= function( f, G, lms, DL, P )

   // reduce f by the elements of G (left reduction only).
   // DL is a monomial division list, corr to the poly ring P.
   // lms is a list of leading monomials.

   U:= Parent( f );
   novar:= Rank( P );

   g:= f;
   red:= Zero(U);

   while g ne 0 do

      mmm:= LeadingUEAMon( novar, g );

      // look for a factor...
      mn:= One( P );
      for j in [1..novar] do
            mn:= mn*P.j^mmm[2][j];
      end for;
      ind:= Divisor( DL, mn );
      
      if ind eq 0 then

         // there is no factor, move lm to red
         red:= red + mmm[3]*mmm[1];
         g:= g - mmm[3]*mmm[1];

      else

         // reduce...
         fac:= [ mmm[2][i] - lms[ind][i] : i in [1..novar] ];
         mn:= One(U);
         for i in [1..novar] do
            if fac[i] ne 0 then
               mn:= mn*U.i^fac[i]; 
            end if;
         end for;
         h:= Monomials( mn )[1]*G[ ind ];
         // look for the coefficient of the leading mon of g in h;
         // then subtract the correct multiple of h from g
         // (note that this coeffcient is not necessarily 1, as 
         // e.g., x*x = 2x^2...).
         mns:= Monomials( h );
         cfs:= Coefficients( h );
         for i in [1..#mns] do
            if mns[i] eq mmm[1] then
               g:= g -mmm[3]/cfs[i]*h;
               break i;
            end if;
         end for;

      end if;
   end while;   

   return red;
end function;


////////////////////////////////////////////////////////////////////////////
//
//  And now the functions that construct the representation.
//  ModuleData computes a list of data that defines the module;
//  this is then used by HighestWeightRepresentation to 
//  construct the representation matrices.
//
ModuleData:= function( U, hw )

     // Compute a big list of data needed to be able to compute
     // representation matrices.

     find_factor:= function( mon, P, MDL )

        // Here `mon' is a monomial, in the UEA
        // `MDL' is a monomial division list; we establish
        // whether there is a leading monomial that is a factor of mon.
        // P is the polynomial ring corresponding to MDL.

        m:= One( P );
        for j in [1..Rank(P)] do
            m:= m*P.j^Degree( mon, j );
        end for;

        i:= Divisor( MDL, m );
        if i gt 0 then 
           return true;
        end if; 
        return false;

     end function;

     append_div_list:= procedure( ~DL, P, mon )

         // Here `mon' is a monomial in the UEA (list of exponents)
         // we append it to the division list DL.

         m:= One( P );
         for j in [1..Rank(P)] do
             if mon[j] gt 0 then
                m:= m*P.j^mon[j];
             end if;
         end for;
         Append( ~DL, m );
     end procedure;

     // first we make a list of all weights, along with multiplicities.

     R:= U`RootDatum;
     ch,mm:= DominantCharacter( R, hw );

     www:= [ ];
     mults:= [ ];
     W:= CoxeterGroup( R );

     for i in [1..#ch] do
         o:= [ Eltseq( x ) : x in WeightOrbit( W, ch[i] : Basis:="Weight" ) ];
         www:= www cat o;
         mults:= mults cat [ mm[i] : k in [1..#o] ];
     end for;

     www:= {@ wt : wt in www @};

     // `levels' will be a list of lists, and `levels[k]' is the list of
     // weights of level `k-1'.
     // `weights' will be the list of all weights, sorted according to level.
     // `wd' will be the list of the weights of the extended weight diagram,
     // also sorted according to level.
     // `levwd' will be the list of the levels of the elements of `wd'.

     rank:= Rank( R );
     levels:= [ [ hw ] ];
     weights:= [ ];
     k:=1;
     wd:= [ hw ];
     levwd:= [ 0 ];
     posR:= PositiveRoots( R : Basis:= "Weight" );
     novar:= #posR;
     posR:= [ Eltseq( posR[i] ) : i in [1..novar] ];
     lcombs:= PositiveRoots( R : Basis:= "Root" );
     lcombs:= [ Eltseq( lcombs[i] ) : i in [1..novar] ];
     hts:= [ &+lcombs[i] : i in [1..novar] ];

     while k le #levels do
         for i in [1..#levels[k]] do
             w:= levels[k][i];
             for j in [1..#posR] do
                 w1:= [ w[q] - posR[j][q] : q in [1..rank] ];
                 lev:= IntegerRing()!(k + hts[j]);
                 if w1 in www then
                     if IsDefined( levels, lev ) then
                         if not w1 in levels[lev] then
                             Append( ~levels[lev], w1 );
                         end if;
                     else
                         levels[lev]:= [ w1 ];
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

     // we have to sort the elements in dom according to level...
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
         weights:= weights cat k;
     end for;

     weights:= {@ wt : wt in weights @};

     // `lents' is a list of the lengths of the elements of `levels'; this is
     // used to calculate the position of an element of the list `weights'
     // efficiently.

     lents:=[ #x : x in levels];
     maxlev:= #levels;

     // `cfs' will be a list of coefficient-lists. The k-th element of `cfs'
     // are the coefficients $k_i$ in the expression `wd[k] = hw - \sum_i k_i
     // \alpha_i', where the \alpha_i are the fundamental roots.

     fund:= posR[ [1..rank ] ];

     V:= KSpace( RationalField(), rank );
     vecs:= [ V!fund[i] : i in [1..rank] ];
     W:= sub<V|vecs>;
     mat:= Matrix( [ Coordinates( W, vecs[i] ) : i in [1..rank] ] );
     mat:= mat^-1;
     cfs:= [ Eltseq( Vector( Coordinates( W, W!(Vector( hw ) - Vector( x )) 
                         ))*mat ) : x in wd ]; 

     // `paths' is the list of normal monomials of each weight in `weights'.
     // `GB' is the Groebner basis, as a flat list, `lms' are the
     // corresponding leading monomials.

     paths:= [ [ One( U ) ] ];
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
            Include( ~ccc, cfs[k] );
            k:= k+1;
        end while;

        // `mons' will be a list of sets of monomials of the UAE.
        // They are candidates for the normal monomials of the weights in `w'.

        mons:= [ ];
        for j in [1..#w] do
            mons[j]:= [ ];
            for i in [1..novar] do

                //We construct all weights of lower levels (that already have
                //been taken care of), connected to the weight `w'.

                w1:= [ w[j][q] + posR[i][q] : q in [1..rank] ];
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

                        // fit y_i in m (commutatively)

                        mn:= One( U );
                        for v in [1..novar] do

                            if v ne i then
                               mn:= mn*U.v^Degree( m, v );
                            else
                               mn:= mn*U.v^( Degree( m, v ) +1 );
                            end if;
                        end for;

                        mn:= Monomials( mn )[1];
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

        Glmsk:= [ ];
        Gk:= [ ];
        DLk:= [ ];

        isdone:= [ false : i in [1..#w] ];
        mmm:= [ ];  // normal monomials...

        for j in [1..#w] do

            i:= 1;
            while i le #mons[j] do
                if find_factor( mons[j][i], P, DL ) then
                   // the monomial reduces; get rid of it. 
                   Remove( ~mons[j], i );
                else
                   i+:= 1;
                end if;
            end while;        

            Glmsk[j]:= [ ];
            Gk[ j ]:= [ ];
            DLk[ j ]:= MonomialDivisionList( P );
            if curlev+1 gt maxlev or not w[j] in levels[ curlev+1 ] then

            // `w[j]' is not a weight of the representation; this means that
            // there are no normal monomials of weight `w[j]'. Hence we can
            // add all candidates in `mons' to the Groebner basis.
                  
                Gk[j]:= mons[j];
                Glmsk[j]:= [ LeadingUEAMon( novar, g )[2] : g in Gk[j] ];
                for i in [1..#Glmsk[j]] do
                    append_div_list( ~DLk[j], P, Glmsk[j][i] );
                end for;           
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
            // in the `long' form (i.e., as an exponent vector).
            prelcm:= lms[i];

            for j in [1..i] do

                if we_had_enough then break j ; end if;
                g:= GB[j];
                // `lcm' will be the least common multiple of the LM of `f'
                // and the LM of `g', represented as a list of length novar.
                m2a:= lms[j];
                lcm:= prelcm;
                for l in [1..novar] do
                    lcm[l]:= Maximum(lcm[l],m2a[l]);
                end for;

                // We check whether `lcm' is of the correct
                // weight; only in that case we form the S-element.
                lc:= [ 0 : v in [1..rank] ];
                for l in [1..#lcm] do
                    if lcm[l] ne 0*lcm[l] then
                       lc:= [ lc[v]+lcm[l]*lcombs[l][v] : v in [1..rank] ];
                    end if;
                end for;
                pp:= Index( ccc, lc );

                if pp ne 0 and not isdone[pp] then

                    // w1*f-w2*g will be the S-element of `f' and `g'.
                    w1:= [ lcm[v]-prelcm[v] : v in [1..novar] ];
                    w2:= lcm;
                    for l in [1..#m2a] do
                        w2[l]:= w2[l]-m2a[l];
                    end for;

                    // We make `w1' and `w2' into UEA elements,
                    // `fac1' and `fac2' respectively.

                    fac1:= One( U ); fac2:= One( U );
                    for l in [1..novar] do
                        fac1:= fac1*U.l^w1[l];
                        fac2:= fac2*U.l^w2[l];
                    end for;
                    fac1:= Monomials( fac1 )[1];
                    fac2:= Monomials( fac2 )[1];

                    // `comp' will be the S-element of `f' and `g'.
                    // We reduce it modulo the elements we already have,
                    // and if it does not reduce to 0 we add it, and remove
                    // its leading monomial from the list of normal
                    // monomials.
   
                    a1:= fac1*f;
                    a2:= fac2*g;

                    cf1:= LeadingUEAMon( novar, a2 )[3];
                    cf2:= LeadingUEAMon( novar, a1 )[3];
                    comp:= cf1*a1 - cf2*a2;

                    comp:= LeftReduce( comp, GB, lms, DL, P );
                    // We also reduce modulo the elements of its own weight:
                    comp:= LeftReduce( comp, Gk[pp], Glmsk[pp], 
                                              DLk[pp], P );

                    if comp ne 0 then

                        // add it...
                        lm:= LeadingUEAMon( novar, comp );
                        Append( ~Gk[pp], 1/lm[3]*comp  );
                        Append( ~Glmsk[pp], lm[2] );
                        append_div_list( ~DLk[pp], P, lm[2] );

                        // Erase the lm from the list of normal monomials...
                        for l in [1..#mons[pp]] do
                            if mmm[pp][l] eq lm[1] then
                               Remove( ~mmm[pp], l );
                               break l;
                            end if;
                        end for;
                        isdone[pp]:=  multiplicity[pp] eq #mmm[pp];

                        if isdone[pp] then

                            // the monomials in mmm[pp] are all normal;
                            // we add them to paths:
                            pos:= Index( weights, w[pp] );
                            paths[pos]:= mmm[pp];
                            we_had_enough:= &and( isdone );
                        end if;
                    end if;
                end if;   // done processing this S-element.

            end for;   // loop over j
        end for;     // loop over i

        for j in [1..#w] do

            // first we make the piece Gk[j] self reduced...
            // we order the monomials of this weight, and view each as a basis
            // element of a vector space. Then we calculate a triangular basis
            // of the subspace spanned by the polynomials of the Grobner basis.
            // So first we have to order the monomials in *decreasing* order...

            mns:= {@ mm : mm in mons[j] @};

            Sort( ~mns, function( a, b ) 
                            return -lex_ord( a, b ); end function );

            V:= KSpace( RationalField(), #mns );
            vecs:= [ ];
            n:= #mns;
            dim:= #Gk[j];
            for i in [1..dim] do
                vv:= [ RationalField()!0 : l in [1..n] ];
                mG:= Monomials( Gk[j][i] );
                cG:= Coefficients( Gk[j][i] );
                for l in [1..#mG] do
                    vv[ Index( mns, mG[l] ) ]:= cG[l];
                end for;
                Append( ~vecs, V!vv );
            end for;
            B:= Basis( sub<V|vecs> );
            B:= [ Eltseq( B[l] ) : l in [1..dim] ];

            elts:= [ ];
            lmlist:= [ ];
            for i in [1..dim] do
                f:= Zero( U );
                lm_found:= false;
                for l in [1..#B[i]] do
                    // the first nonzero cft has the leading mon
                    if not IsZero( B[i][l] ) then
                       if not lm_found then
                          lm_found:= true;
                          Append( ~lmlist, 
                               [ Degree( mns[l], v ) : v in [1..novar] ] );
                       end if;
                       f:= f + B[i][l]*mns[l];
                    end if;
                end for;
                Append( ~elts, f );
            end for;

            GB:= GB cat elts;
            lms:= lms cat lmlist; 
            for i in [1..#lmlist] do
                append_div_list( ~DL, P, lmlist[i] );
            end for;
                
        end for;

    end while; //loop over k, we now looped through the entire 
               //extended weight diagram.

    mons:= [ ];
    for i in [1..#paths] do
        mons:= mons cat paths[i];
    end for;

    return GB, lms, DL, P, mons;

end function;


intrinsic IntegralUEA( L::AlgLie ) -> AlgIUE
{ The integral (Kostant Z-form) of the universal enveloping algebra of L}

     require IsSemisimple( L ) and 
             IsZero( Characteristic( CoefficientRing(L) ) ):
	       "The integral UEA only exists for semisimple Lie algebras of characteristic 0";

     if assigned L`IntegralUEA then
        return L`IntegralUEA;
     end if;

     d := GetUEADescription(L);
     U := InternalIUEA(L, d[3], d[4], d[1], d[2], [d[5], d[6]]);

     U`RootDatum:= RootDatum( L );
     U`LieEmbedding:= d[7];

     L`IntegralUEA:= U;

     return U;

end intrinsic;

basisChange := function( R, Basis, v )
  case Basis:
  when "Root":
    return v * CartanMatrix(R);
  when "Standard":
    return R`RootSpace ! (Vector(v) * R`SimpleRoots * CartanMatrix(R));
  when "Weight":
    return RSpace( Integers(), Rank(R) )!v;
  else
    error "Invalid Basis parameter";
  end case;
end function;


intrinsic HighestWeightRepresentation( L::AlgLie, hw::. : Basis:="Weight" ) 
  -> Map
   {The highest weight representation of L with highest weight hw }

   // Dealing with positive characteristics
   k := BaseRing( L );  
   if Category( k ) ne FldRat then
     R := RootDatum( L );  LQ := LieAlgebra( R, Rationals() );
     rhoQ := HighestWeightRepresentation( LQ, hw );
     gens := [ rhoQ( LQ.i ) : i in [1..Dimension(L)] ];
     M := MatrixLieAlgebra( k, Degree(Universe(gens)) );
     ok, gens := CanChangeUniverse( gens, M );
     require ok : "Cannot compute this representation in characteristic ", Characteristic( k );
     f := func< l | &+[ l[i]*gens[i] : i in [1..Dimension(L)] ] >;
     return map< L -> M | x :-> f(x) >;
   end if;

   hw := Eltseq( basisChange( RootDatum( L ), Basis, hw ) );
   require &and[ IsIntegral( hw[i] ) and hw[i] ge 0 : i in [1..#hw] ]:
      "The weight is not dominant integral";

   if forall{ a : a in hw | a eq 0 } then
     M := MatrixLieAlgebra(BaseRing(L),1);
     return map< L -> M | x :-> 1 >;
   end if;
   U:= IntegralUEA( L );
   emb:= U`LieEmbedding;
   G, lms, DL, P, mons := ModuleData( U, hw );

   rep:= function( x )

       R:= RootDatum( L );
       rank:= Rank( R );
       n:= #PositiveRoots(R);
       ux:= emb( U, x );

       mat:= [ ];
       for i in [1..#mons] do

           elt:= ux*mons[i];
           mns:= Monomials( elt );
           cfs:= Coefficients( elt );

           felt:= Zero( U );
           for j in [1..#mns] do
               mn:= mns[j];

               edeg:= 0;
               k:= 1;
               while k le n and edeg eq 0 do
                     edeg:= Degree( mn, n+rank+k );
                     k:= k+1;
               end while;

               if edeg eq 0 then
                  // otherwise the monomial reduces to 0...
                  // for each `h' at the end of the monomial
                  // we multiply by the appropriate scalar...
                  // we put the rest into fbit

                  cf:= cfs[j];
                  for k in [1..rank] do
                      hdeg:= Degree( mn, n+k );
                      if hdeg gt 0 then
                         cf:= cf*Binomial( hw[k], hdeg );
                      end if;
                  end for;

                  fbit:= One( U );
                  for k in [1..n] do
                      fdeg:= Degree( mn, k );
                      if fdeg gt 0 then
                         fbit:= fbit*U.k^fdeg/Factorial( fdeg );
                      end if;
                  end for;

                  felt:= felt + cf*fbit;
               end if;
           end for;

           felt:= LeftReduce( felt, G, lms, DL, P );
           mns:= Monomials( felt );
           cfs:= Coefficients( felt );
           vec:= [ Rationals()!0 : k in [1..#mons] ];
           
           for j in [1..#mns] do
               pos:= Index( mons, mns[j] );
               vec[pos] := cfs[j];
           end for;
           Append( ~mat, vec );
       end for;
   
       return Transpose( Matrix( mat ) );
   end function;

   M := MatrixLieAlgebra( BaseRing(L), #mons );
   return hom< L -> M | x :-> M!rep(x) >;

end intrinsic;



intrinsic HighestWeightModule( L::AlgLie, hw::. : Basis:="Weight" )->ModAlg

   {The highest weight module of L with highest weight hw }

   // This is the module version of HighestWeightRepresentation

   require Characteristic( BaseRing(L) ) eq 0 : "This function is only implemented for Lie algebras of characteristic 0.";
  
   hw := Eltseq( basisChange( RootDatum( L ), Basis, hw ) );
   require &and[ IsIntegral( hw[i] ) and hw[i] ge 0 : i in [1..#hw] ]:
      "The weight is not dominant integral";

   
   U:= IntegralUEA( L );
   emb:= U`LieEmbedding;
   G, lms, DL, P, mons := ModuleData( U, hw );

   M:= RModule( CoefficientRing(L), #mons );

   rho:= function( x, v )

       R:= RootDatum( L );
       rank:= Rank( R );
       n:= #PositiveRoots(R);
       ux:= emb( U, x );

       cfs:= Coordinates( M, v );
       uv:= Zero( U );
       for i in [1..#cfs] do
           uv:= uv+cfs[i]*mons[i];
       end for;

       elt:= ux*uv;

       mns:= Monomials( elt );
       cfs:= Coefficients( elt );

       felt:= Zero( U );
       for j in [1..#mns] do
           mn:= mns[j];

           edeg:= 0;
           k:= 1;
           while k le n and edeg eq 0 do
                 edeg:= Degree( mn, n+rank+k );
                 k:= k+1;
           end while;

           if edeg eq 0 then
              // otherwise the monomial reduces to 0...
              // for each `h' at the end of the monomial
              // we multiply by the appropriate scalar...
              // we put the rest into fbit

              cf:= cfs[j];
              for k in [1..rank] do
                  hdeg:= Degree( mn, n+k );
                  if hdeg gt 0 then
                     cf:= cf*Binomial( hw[k], hdeg );
                  end if;
              end for;

              fbit:= One( U );
              for k in [1..n] do
                  fdeg:= Degree( mn, k );
                  if fdeg gt 0 then
                     fbit:= fbit*U.k^fdeg/Factorial( fdeg );
                  end if;
              end for;

              felt:= felt + cf*fbit;
           end if;
       end for;

       felt:= LeftReduce( felt, G, lms, DL, P );

       mns:= Monomials( felt );
       cfs:= Coefficients( felt );
       vec:= [ Rationals()!0 : k in [1..#mons] ];
           
       for j in [1..#mns] do
           pos:= Index( mons, mns[j] );
           vec[pos] := cfs[j];
       end for;

       return M!vec;
   end function;

   return Module( L, 
            map< CartesianProduct( L, M ) -> M | t :-> rho( t[1], t[2] ) > );

end intrinsic;


TPOfLieAlgebraModules:= function( modules )

     L:= Algebra( modules[1] );

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

     M:= RModule( CoefficientRing(L), #inds );

     act:= function( x, v )

           // Here x is an element of L
           // v is an element of M; we compute x^v.

           cc:= Coordinates( M, v );
           w:= Zero(M);
           for i in [1..#cc] do
               if not IsZero( cc[i] ) then
                  for j in [1..#modules] do
                      ii:= inds[i];
                      crds:= [* modules[r].ii[r] : r in [1..#modules] *];
                      crds[j]:= x^crds[j];
                      if not &or[ IsZero( u ) : u in crds ] then
                      
                         crds:= [ Coordinates( modules[r], crds[r] ) : 
                                        r in [1..#modules] ];

                         vec_inds:= [ [] ];
                         cfs:= [ cc[i] ];
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


     W:= Module( L, 
          map< CartesianProduct( L, M ) -> M | t :-> act( t[1], t[2] ) > );

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

SymPowOfLieAlgebraModules:= function( V, n )

     L:= Algebra( V );

     dim := Dimension( V );

     // inds will be a sequence of seqneces of indices, if the r-th 
     // sequence is e.g., [ 1,3,3 ], then the r-th basis vector of the
     // module that we are producing is V.1 * V.3 * V.3
 
     inds:= {@  @};
     for i in [1..dim] do
         Include( ~inds, [i] );
     end for;
     for i in [2..n] do
         inds1:= {@@};
         for j in [1..dim] do
             for k in [1..#inds] do
                 if j ge inds[k][i-1] then
                    Include( ~inds1, inds[k] cat [j] );
                 end if;
             end for;
         end for;
         inds:= inds1;
     end for;

     Sort( ~inds );

     M:= RModule( CoefficientRing(L), #inds );

     act:= function( x, v )

           // Here x is an element of L
           // v is an element of M; we compute x^v.

           cc:= Coordinates( M, v );
           w:= Zero(M);
           for i in [1..#cc] do
               if not IsZero( cc[i] ) then
                  for j in [1..n] do
                      ii:= inds[i];
                      crds:= [* V.ii[r] : r in [1..n] *];
                      crds[j]:= x^crds[j];
                      if not &or[ IsZero( u ) : u in crds ] then
                      
                         crds:= [ Coordinates( V, crds[r] ) : 
                                        r in [1..n] ];

                         vec_inds:= [ [] ];
                         cfs:= [ cc[i] ];
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
                             Sort( ~vec_inds[k] );
                             u[ Index( inds, vec_inds[k] ) ] +:= cfs[k];
                         end for;
                         w:= w + M!u;
                      end if;
                  end for;
               end if;
           end for;

           return w;
     end function;


     W:= Module( L, 
          map< CartesianProduct( L, M ) -> M | t :-> act( t[1], t[2] ) > );

     f:= function( tuple )


         cc:= [ ];
         for i in [1..#tuple] do
             Append( ~cc, Coordinates( V, tuple[i] ) );
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
             Sort( ~vec_inds[k] );
             u[ Index( inds, vec_inds[k] ) ] +:= cfs[k];
         end for;
         return W!u;

     end function;         

     return W, map< CartesianProduct( [ V : i in [1..n] ] ) -> W | t :-> f(t) >;

end function;


ExtPowOfLieAlgebraModules:= function( V, n )

     no_doubles:= function( list )

          // true if in the incresing list of integers `list'
          // there are no two consecutive entries the same

          for i in [1..#list-1] do
              if list[i] eq list[i+1] then return false; end if;
          end for;
          return true;

     end function;

     L:= Algebra( V );

     dim := Dimension( V );

     // inds will be a sequence of seqneces of indices, if the r-th 
     // sequence is e.g., [ 1,3,3 ], then the r-th basis vector of the
     // module that we are producing is V.1 * V.3 * V.3
 
     inds:= {@  @};
     for i in [1..dim] do
         Include( ~inds, [i] );
     end for;
     for i in [2..n] do
         inds1:= {@@};
         for j in [1..dim] do
             for k in [1..#inds] do
                 if j gt inds[k][i-1] then
                    Include( ~inds1, inds[k] cat [j] );
                 end if;
             end for;
         end for;
         inds:= inds1;
     end for;

     Sort( ~inds );

     M:= RModule( CoefficientRing(L), #inds );

     act:= function( x, v )

           // Here x is an element of L
           // v is an element of M; we compute x^v.

           cc:= Coordinates( M, v );
           w:= Zero(M);
           for i in [1..#cc] do
               if not IsZero( cc[i] ) then
                  for j in [1..n] do
                      ii:= inds[i];
                      crds:= [* V.ii[r] : r in [1..n] *];
                      crds[j]:= x^crds[j];
                      if not &or[ IsZero( u ) : u in crds ] then
                      
                         crds:= [ Coordinates( V, crds[r] ) : 
                                        r in [1..n] ];

                         vec_inds:= [ [] ];
                         cfs:= [ cc[i] ];
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
                             Sort( ~vec_inds[k], ~perm );
                             if no_doubles( vec_inds[k] ) then
                                u[ Index( inds, vec_inds[k] ) ] +:= 
                                                          Sign(perm)*cfs[k];
                             end if;
                         end for;
                         w:= w + M!u;
                      end if;
                  end for;
               end if;
           end for;

           return w;
     end function;


     W:= Module( L, 
          map< CartesianProduct( L, M ) -> M | t :-> act( t[1], t[2] ) > );

     f:= function( tuple )


         cc:= [ ];
         for i in [1..#tuple] do
             Append( ~cc, Coordinates( V, tuple[i] ) );
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
             Sort( ~vec_inds[k], ~perm );
             if no_doubles( vec_inds[k] ) then
                u[ Index( inds, vec_inds[k] ) ] +:= Sign(perm)*cfs[k];
             end if;
         end for;
         return W!u;

     end function;         

     return W, map< CartesianProduct( [ V : i in [1..n] ] ) -> W | t :-> f(t) >;

end function;


WtsAndVecsOfLieAlgebraModule:= function( V )

     // Here V is a module over a split semisimple Lie algebra;
     // the output of this function is formed by two sequences:
     // the first is a sequence of weights,
     // the second a sequence of sequences of basis vectors of V
     // the basis elements in the i-th sequence are of the i-th weight.

     // We assume that all basis vectors are weight vectors.

     L:= Algebra( V );
     x,y,h:= WdG_ChevBasis( L, CartanSubalgebra(L) );
     /* Fix h, because WdG_ChevBasis sometimes doesn't quite return a Chev. basis */
     h := [ x[i]*y[i] : i in [1..#h] ];

     wts:= [ ];
     vecs:= [ ];

     sp:= RModule( CoefficientRing(V), Dimension(V) );

     for v in Basis(V) do
         wt:= [ ];
         W:= sub< sp | [ sp!Coordinates( V, v ) ] >;
         for i in [1..#h] do
	     w := IsLeftModule(V) select h[i]^v else v^h[i];
             w:= sp!Coordinates( V, w );
             error if not w in W, "The basis of V does not consist of weight vectors"; 
             a:= Coordinates( W, w )[1];
             Append( ~wt, Integers()!a );
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
             
             
  
HighWtsAndVecsOfLieAlgebraModule:= function( V )

     // same as previous function, but in this case we only
     // return the highest weights; this is effectively computing the
     // direct sum decomposition....

     L:= Algebra( V );
     R:= RootDatum( L );
     W:= CoxeterGroup( R );
     rank:= Rank(R);
     x,y,h:= WdG_ChevBasis(L,CartanSubalgebra(L));
     /* Fix h, because WdG_ChevBasis sometimes doesn't quite return a Chev. basis */
     if #h eq rank then
          h := [ x[i]*y[i] : i in [1..rank] ];
     else
          h := [ x[i]*y[i] : i in [1..rank] ] cat [ L!b : b in Basis(Centre(L)) ];
     end if;

     wts, vecs:= WeightsAndVectors( V );

     // decompose the character...

     hwts:= [ ];
     posR:= PositiveRoots( R : Basis:= "Weight" );
     sim_rts:= [ Vector( Integers(), posR[k] ) : k in [1..rank] ];
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
         eqs:= ZeroMatrix( CoefficientRing(L), #vv, n*rank );
         for i in [1..rank] do
             for j in [1..#vv] do
	         im := IsLeftModule(V) select x[i]^vv[j] else vv[j]^x[i];
                 cc:= Coordinates( V, im );
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

intrinsic DirectSum( rho1::Map[AlgLie,AlgMatLie], rho2::Map[AlgLie,AlgMatLie] ) 
  -> Map[AlgLie,AlgMatLie]
{The direct sum of rho1 and rho2}
  G := CoveringStructure( Domain(rho1), Domain(rho2) );
  k := CoveringStructure( BaseRing(Codomain(rho1)), BaseRing(Codomain(rho2)) );
  d := Degree( Codomain(rho1)) + Degree( Codomain(rho2) );
  return hom< G -> MatrixLieAlgebra(k,d) | 
    g :-> DiagonalJoin( rho1(g), rho2(g) ) >;
end intrinsic;

intrinsic DirectSumDecomposition( rho::Map[AlgLie,AlgMatLie] ) -> SeqEnum
{Direct sum decomposition of a representation rho over a semisimple Lie algebra}
  L := Domain( rho );
  V := BaseModule( Codomain( rho ) );
  K := BaseRing(V);
  restrict := function( U )
    d := Dimension( U );
    return hom< L -> MatrixLieAlgebra(K,d) | g :->
      [ Coordinates( U, u*rho(g) ) : u in Basis(U) ] >;
  end function;
  
  M := Module( rho );
  decM := DirectSumDecomposition( M );
  return [ restrict( sub< V | [V!M!b : b in Basis(U) ] > ) : U in decM ];
end intrinsic;   
  
intrinsic IndecomposableSummands( rho::Map[AlgLie,AlgMatLie] ) -> SeqEnum
{Direct sum decomposition of a representation rho over a semisimple Lie algebra}
  return DirectSumDecomposition(rho);
end intrinsic;   

/* This can now be done with Allan's char 0 meataxe.

intrinsic DirectSumDecomposition( V::ModAlg ) -> SeqEnum
{Direct sum decomposition of a module over a semisimple Lie algebra}


     L:= Algebra( V );

     require ISA( Type(L), AlgLie ) : "V must be a module over a Lie algebra.";

     require IsSemisimple( L ) : "The algebra of V must be semisimple.";

     wt, vv:= HighestWeightsAndVectors( V );
     
     mods:= [ ];
     for i in [1..#vv] do
         for j in [1..#Eltseq(vv[i])] do
             Append( ~mods, sub< V | [ vv[i][j] ] > );
         end for;
     end for;

     return mods;


end intrinsic;*/
