freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes AlgQUE: BarAutomorphism, AutomorphismOmega, 
                           AntiAutomorphismTau;

import "qea.m" : in_p;


FindDef_F:= function( U, pos, j, posR, rank, conv )

       // Here pos is an integer between 1 and the number of positive roots;
       // we find a definition of F_pos. 
       // this function returns three things, cf, pair, rel, such that
       // F_pos = (1/cf)*U.pair[1]*U.pair[2] + rel.

       // It is assumed that pos is not the position of a simple root
       // (in the list of convex roots).

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
       return cf, pair, rel;

end function;

FindDef_E:= function( U, pos, j, posR, rank, conv )

       // Here pos is an integer between 1 and the number of positive roots;
       // we find a definition of E_pos. 
       // this function returns three things, cf, pair, rel, such that
       // E_pos = (1/cf)*U.pair[1]*U.pair[2] + rel.

       // It is assumed that pos is not the position of a simple root
       // (in the list of convex roots).

       s:= #posR;

       for k in [1..rank] do
           // We find a simple root r such that posR[j]-r is also a root.

           k1:= Position( posR, posR[j] - posR[k] );
           if k1 gt 0 then
              k1:= Position( conv, k1 )+s+rank;
              k2:= Position( conv, k )+s+rank;

              if k1 gt k2 then
                 pair:= [ k1, k2 ];
              else
                 pair:= [ k2, k1 ];
              end if;
              rel:= U.pair[1]*U.pair[2];

              // we establish whether E_j is in there
              mns:= Monomials( rel );
              cfs:= Coefficients( rel );
              pp:= Position( mns, U.(s+rank+pos) );
              if pp gt 0 then break k; end if;
           end if;
       end for;
    
       cf:= cfs[ pp ];
       rel:= rel - cf*mns[pp];
       rel:= (-1/cf)*rel; 

       // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.

       return cf, pair, rel;

end function;


bar:= function( f, q )

    // here f is a rat. func. in q, we compute the polyomial obtained
    // from f by setting q --> q^-1.

    if f in BaseRing( Parent( q ) ) then return f; end if; 

    n:= Numerator( f );
    d:= Denominator( f );
    mn:= Monomials( n );
    cf:= Coefficients( n );
    n1:= 0*f;
    for i in [1..#mn] do
        n1:= n1+cf[i]*q^( -Degree( mn[i] ) );
    end for;

    mn:= Monomials( d );
    cf:= Coefficients( d );
    d1:= 0*f;
    for i in [1..#mn] do
        d1:= d1+cf[i]*q^( -Degree( mn[i] ) );
    end for;

    return n1/d1;

end function;


intrinsic BarAutomorphism( U::AlgQUE ) -> Map
{The automorphism of the quantized enveloping algebra U that sends
   q to q^-1}

    if assigned U`BarAutomorphism then 
       return U`BarAutomorphism;
    end if;

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // the image is just the element itself

           imgs[pos]:= U.pos;

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= bar( (1/cf), q )*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= a*bar( cfs[k], q );

               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;


    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // the image is just the element itself

           imgs[s+rank+pos]:= U.(s+rank+pos);
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= bar( 1/cf, q)*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= a*bar( cfs[k], q ); 
               im:= im + a;
           end for;
           
           imgs[s+rank+pos]:= im;
          
        end if;
    end for;


    br:= function( x )


          a:= Zero( U );
          mx:= Monomials( x );
          cx:= Coefficients( x );
          for k in [1..#mx] do
        
              b:= One( U );
              // first we see whether the monomial contains F's...
              for l in [1..s] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ l ]^dl;
                     b:= b/cf;
                  end if;
              end for;

              // look for K's...
              for l in [1..rank] do
                  dl:= KDegree( mx[k], l );
                  if dl ne <0,0> then
 
                     if dl[1] eq 0 then // it is fixed under bar
                        b:= b*KBinomial( U, l, dl[2] );
                     else
                        b:= b*U.(s+l)^-1;
                        if dl[2] ne 0 then
                           b:= b*KBinomial( U, l, dl[2] );
                        end if;
                     end if;
                  end if;
              end for;

              // look for E's...
              for l in [1..s] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ s+rank+l ]^dl;
                     b:= b/cf;
                  end if;
              end for;
              a:= a + bar( cx[k], q )*b;

          end for;

          return a;
    end function;

    br_map:= map< U -> U | x :-> br(x), y :-> br(y) >;

    U`BarAutomorphism:= br_map;

    return br_map;

end intrinsic;


automorphism:= function( U, imgs )

     // Here imgs is a list of images of the E and F generators of U
     // (so a list of length 2*s+2*rank; 2*rank because of the images 
     // of the K^-1's. First there are s F's, then K_1, K_1^-1, K_2, K_2^-1,
     // and so on. Finally, there are the images of the s E's.
     // We create the corresponding automorphism.

     posR:= U`Roots[1]; // positive roots in root basis
     q:= CoefficientRing( U ).1;
     R:= U`RootDatum;
     conv:= U`Perm;
     rank:= Rank( R );
     s:= #posR;
     CF:= U`NormalizedCoxeterForm;

     aut:= function( x )

          a:= Zero( U );
          mx:= Monomials( x );
          cx:= Coefficients( x );
          for k in [1..#mx] do
        
              b:= One( U );
              // first we see whether the monomial contains F's...
              for l in [1..s] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ l ]^dl;
                     b:= b/cf;
                  end if;
              end for;

              // look for K's...
              for l in [1..rank] do
                  dl:= KDegree( mx[k], l );
                  if dl ne <0,0> then
 
                     if dl[1] gt 0 then
                        b:= b*imgs[ s+2*l-1 ];
                     end if;
                     if dl[2] gt 0 then
                        qa:= q^( Integers()!(CF[l][l]/2) );
                        x:= imgs[ s+2*l-1 ];
                        y:= imgs[ s+2*l ];
                        for i in [1..dl[2]] do
                            b:= b*(qa^(-i+1)*x-qa^(i-1)*y)/(qa^i-qa^-i);
                        end for;		         
                     end if;
                  end if;
              end for;

              // look for E's...
              for l in [1..s] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ s+2*rank+l ]^dl;
                     b:= b/cf;
                  end if;
              end for;
              a:= a + cx[k]*b;

          end for;

          return a;
     end function;

     return aut;

end function;

intrinsic AutomorphismOmega( U::AlgQUE ) -> Map
{Automorphism of the quantized enveloping algebra U}

    if assigned U`AutomorphismOmega then 
       return U`AutomorphismOmega;
    end if;

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // the image is the j-th E:

           imgs[pos]:= U.(s+rank+pos);

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        Append( ~imgs, U.(s+j)^-1 );
        Append( ~imgs, U.(s+j) );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // the image is just the j-th F

           imgs[s+2*rank+pos]:= U.pos;
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1]+rank ]*imgs[ pair[2]+rank ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;

    om:= automorphism( U, imgs );
    w:= map< U -> U | x :-> om(x), y :-> om(y) >; 
    U`AutomorphismOmega:= w;
    return w;

end intrinsic;


anti_automorphism:= function( U, imgs )

    // same as for automorphism, but this time it is an antiautomorphism...

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    a_aut:= function( x )

          a:= Zero( U );
          mx:= Monomials( x );
          cx:= Coefficients( x );
          for k in [1..#mx] do
        
              b:= One( U );
              // first we see whether the monomial contains E's...
              for l in [s..1 by -1] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ s+2*rank+l ]^dl;
                     b:= b/cf;
                  end if;
              end for;

              // look for K's...
              for l in [rank..1 by -1] do
                  dl:= KDegree( mx[k], l );
                  if dl ne <0,0> then
 
                     if dl[1] gt 0 then // i.e., it is 1
		        b:= b*imgs[s+2*l-1];
                     end if;

                     if dl[2] gt 0 then
                        qa:= q^( Integers()!(CF[l][l]/2) );
                        K:= imgs[s+2*l-1];
                        Ki:= imgs[s+2*l];
                        for i in [1..dl[2]] do
                            b:= b*(qa^(-i+1)*K-qa^(i-1)*Ki)/(qa^i-qa^-i);
                        end for;
                     end if;

                  end if;
              end for;

              // look for F's...
              for l in [s..1 by -1] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then  
                     qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                     cf:= GaussianFactorial( dl, qa );
                     b:= b*imgs[ l ]^dl;
                     b:= b/cf;
                  end if;
              end for;
              a:= a + cx[k]*b;

          end for;

          return a;
    end function;

    return a_aut;

end function;

 
intrinsic AntiAutomorphismTau( U::AlgQUE ) -> Map
{Anti-automorphism of the quantized enveloping algebra U}

    if assigned U`AntiAutomorphismTau then 
       return U`AntiAutomorphismTau;
    end if;

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // the image is the j-th F:

           imgs[pos]:= U.pos;

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[2] ]*imgs[ pair[1] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        Append( ~imgs, U.(s+j)^-1 ); 
        Append( ~imgs, U.(s+j) );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[s+2*rank+pos]:= U.(s+rank+pos);
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[2]+rank ]*imgs[ pair[1]+rank ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [s..1 by -1] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;


    tau:= anti_automorphism( U, imgs );
    t:= map< U -> U | x :-> tau(x), y :-> tau(y) >; 
    U`AntiAutomorphismTau:= t;
    return t;

end intrinsic;

make_T_aut:= function( U, r, inv )

    // if inv is true we make the inverse; otherwise we make the
    // automorphism T_r

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;
    C:= CartanMatrix( R );

    r_pos:= Position( conv, r );

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  
           
           if inv then
              if j eq r then
                 imgs[pos]:= -q^(-Integers()!CF[r][r])*U.(s+j)*U.(s+rank+pos);
              else
                 m:= Integers()!(-C[j][r]);
                 im:= Zero( U );
                 qa:= q^( Integers()!( CF[r][r]/2 ) );
                 for k in [0..m] do
                     a:= (-1)^k*qa^k*U.(r_pos)^(m-k)*U.pos*U.(r_pos)^k;
                     a:= a/(GaussianFactorial(k,qa)*GaussianFactorial(m-k,qa));
                     im:= im +a;
                 end for;
                 imgs[pos]:= im;
              end if;

           else
              if j eq r then
                 imgs[pos]:= -U.(s+j)^-1*U.(s+rank+pos);
              else
                 m:= Integers()!(-C[j][r]);
                 im:= Zero( U );
                 qa:= q^( Integers()!( CF[r][r]/2 ) );
                 for k in [0..m] do
                     a:= (-1)^k*qa^k*U.(r_pos)^k*U.pos*U.(r_pos)^(m-k);
                     a:= a/(GaussianFactorial(k,qa)*GaussianFactorial(m-k,qa));
                     im:= im +a;
                 end for;
                 imgs[pos]:= im;
              end if;
           end if;

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        m:= Integers()!(-C[j][r]);
        Append( ~imgs, U.(s+r)^m*U.(s+j) );
        Append( ~imgs, U.(s+r)^-m*U.(s+j)^-1 );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           if inv then

              if j eq r then
                 imgs[s+2*rank+pos]:= -q^(Integers()!CF[r][r])*U.pos*U.(s+j)^-1;
              else
                 m:= Integers()!(-C[j][r]);
                 im:= Zero( U );
                 qa:= q^( Integers()!( CF[r][r]/2 ) );
                 for k in [0..m] do
                     a:= (-1)^k*qa^-k*U.(s+rank+r_pos)^k*U.(s+rank+pos)*
                                      U.(s+rank+r_pos)^(m-k);
                     a:= a/(GaussianFactorial(k,qa)*GaussianFactorial(m-k,qa));
                     im:= im +a;
                 end for;
                 imgs[s+2*rank+pos]:= im;
              end if;

           else

              if j eq r then
                 imgs[s+2*rank+pos]:= -U.pos*U.(s+j);
              else
                 m:= Integers()!(-C[j][r]);
                 im:= Zero( U );
                 qa:= q^( Integers()!( CF[r][r]/2 ) );
                 for k in [0..m] do
                     a:= (-1)^k*qa^-k*U.(s+rank+r_pos)^(m-k)*U.(s+rank+pos)*
                                      U.(s+rank+r_pos)^k;
                     a:= a/(GaussianFactorial(k,qa)*GaussianFactorial(m-k,qa));
                     im:= im +a;
                 end for;
                 imgs[s+2*rank+pos]:= im;
              end if;

           end if;
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1]+rank ]*imgs[ pair[2]+rank ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;

    return automorphism( U, imgs );

end function;


intrinsic AutomorphismTalpha( U::AlgQUE, r::RngIntElt ) -> Map
{Automorphism T_r of the quantized enveloping algebra U}

    T:= make_T_aut( U, r, false );
    Ti:= make_T_aut( U, r, true );
    return map< U -> U | x :-> T(x), y :-> Ti(y) >;

end intrinsic;


intrinsic QUAToIntegralUEAMap( U::AlgQUE ) -> Map
{The map from a quantized enveloping algebra to the integral form of the universal enveloping algebra of the corresponding Lie algebra}


    // Basically we map q to 1, and K to 1, and [ K ; n ] to 
    // ( h ; n ).
    
    R:= RootDatum( U );
    L:= LieAlgebra( R, Rationals() );
    x,y,h:= ChevalleyBasis( L );
    A:= IntegralUEA( L );
    emb:= A`LieEmbedding;
     
    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the imaga of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[pos]:= emb( A, y[j] );

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= Evaluate( (1/cf), 1 )*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do

               a:= One( A );
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      a:= a*imgs[l]^dl;
                      a := a/Factorial( dl );
                   end if;
               end for;
               a:= a*Evaluate( cfs[k], 1 );

               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;


    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  

           imgs[s+rank+pos]:= emb( A, x[j] );
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= Evaluate( 1/cf, 1 )*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( A );
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      a:= a*imgs[ s+rank+l ]^dl;
                      a:= a/Factorial( dl );
                   end if;
               end for;
               a:= a*Evaluate( cfs[k], 1 ); 
               im:= im + a;
           end for;
           
           imgs[s+rank+pos]:= im;
          
        end if;
    end for;


    mp:= function( x )


          a:= Zero( A );
          mx:= Monomials( x );
          cx:= Coefficients( x );

          // check whether the coefficients do not have denominators
          // that evaluate to zero.
          xx:= [ Evaluate( Denominator( f ), 1 ) : f in cx ];
          //error if 0 in xx, "The coefficients cannot be evaluated at 1";
            
          assert not 0 in xx; 

          for k in [1..#mx] do
        
              b:= One( A );
              // first we see whether the monomial contains F's...
              for l in [1..s] do
                  dl:= Degree( mx[k], l );                  
                  if dl gt 0 then
                     b:= b*imgs[ l ]^dl;  
                     b:= b/Factorial( dl );
                  end if;
              end for;

              // look for K's...
              for l in [1..rank] do
                  dl:= KDegree( mx[k], l );
                  if dl[2] gt 0 then
                     b:= b*HBinomial( A, l, dl[2] );
                  end if;
              end for;

              // look for E's...
              for l in [1..s] do
                  dl:= Degree( mx[k], s+rank+l );                  
                  if dl gt 0 then  
                     b:= b*imgs[ s+rank+l ]^dl;
                     b:= b/Factorial( dl );
                  end if;
              end for;
              a:= a + Evaluate( cx[k], 1 )*b;

          end for;

          return a;
    end function;

    eval_map:= map< U -> A | x :-> mp(x) >;

    return eval_map;

end intrinsic;


diag_aut:= function( U, perm )

    imgs:= [ ];

    posR:= U`Roots[1]; // positive roots in root basis
    q:= CoefficientRing( U ).1;
    R:= RootDatum( U );
    conv:= PositiveRootsPerm( U );
    rank:= Rank( R );
    s:= #posR;
    CF:= U`NormalizedCoxeterForm;

    for j in [1..#posR] do
        // compute the image of the j-th F, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // apply perm

           imgs[pos]:= U.( Position( conv, j^perm ) );

        else // i.e., j > rank

           cf, pair, rel:= FindDef_F( U, pos, j, posR, rank, conv );

           // Now U.pos = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1] ]*imgs[ pair[2] ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );

           for k in [1..#mns] do

               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[l]^dl;
                      a := a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[pos]:= im;
          
        end if;
    end for;

    for j in [1..rank] do
        K:= U.( s + j^perm );
        Append( ~imgs, K );
        Append( ~imgs, K^-1 );
    end for;

    for j in [1..#posR] do
        // compute the image of the j-th E, where j is the j-th positive
        // root, as it appears in posR

        pos:= Position( conv, j );
        if j le rank then  // apply perm

           imgs[s+2*rank+pos]:= U.( s+rank+Position( conv, j^perm ) ) ;
   
        else

           cf, pair, rel:= FindDef_E( U, pos, j, posR, rank, conv );

           // Now U.(pos+s+rank) = 1/cf*U.pair[1]*U.pair[2] + rel.
           // We compute the image of U.pos:

           im:= (1/cf)*imgs[ pair[1]+rank ]*imgs[ pair[2]+rank ];
           mns:= Monomials( rel );
           cfs:= Coefficients( rel );
           for k in [1..#mns] do
               a:= One( U );
               for l in [1..s] do
                   dl:= Degree( mns[k], s+rank+l );
                   if dl gt 0 then
                      qa:= q^( Integers()!(
                            in_p( CF, posR[ conv[l] ], 
                                      posR[ conv[l] ] )/2 ) );
                      cf:= GaussianFactorial( dl, qa );
                      a:= a*imgs[ s+2*rank+l ]^dl;
                      a:= a/cf;
                   end if;
               end for;
               a:= cfs[k]*a;
               im:= im + a;
           end for;
           
           imgs[s+2*rank+pos]:= im;
          
        end if;
    end for;

    return automorphism( U, imgs );

end function;


intrinsic DiagramAutomorphism( U::AlgQUE, perm::GrpPermElt ) -> Map
{The diagram automorphism of U induced by the permutation perm}

    // check whether perm is indeed a diagram automorphism:
    R:= RootDatum( U );
    C:= CartanMatrix( R );
    r:= Rank( R );
    for i in [1..r] do
        for j in [1..r] do
            require C[i][j] eq C[i^perm][j^perm] : "The permutation does not represent a diagram automorphism";
        end for;
    end for;

    d:= diag_aut( U, perm );
    di:= diag_aut( U, perm );
    return map< U -> U | x :-> d(x), y :-> di(y) >;

end intrinsic;

// This synonym introduced for agreement with the corresponding functions
// for AlgLie and GrpLie -- Scott.
intrinsic GraphAutomorphism( U::AlgQUE, perm::GrpPermElt ) -> Map
{The diagram automorphism of U induced by the permutation perm}
  return DiagramAutomorphism(U,perm);
end intrinsic;
