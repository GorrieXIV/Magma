freeze;

///////////////////////////////////////////////////////////////////////////

declare attributes ModAlg : CanonicalBasis;

poly_part:= function( f, q )

     // Here f is a rational function in q  of the form pol/q^k,
     // and such that bar(f) = -f. This function returns a polynomial
     // h in q such that f = h - bar(h).

     n:= Numerator( f );
     d:= Denominator( f );

     val:= Degree( d );
     m:= Monomials( n );
     cf:= Coefficients( n );
     degs:= [ Degree( x ) - val : x in m ];

     r:= 0*q;
     for k in [1..#degs] do
         if degs[k] gt 0 then  
            r:= r+cf[k]*q^( degs[k] );
         end if;
     end for;

     return r;

end function;


MoveExpVector:= function( m, B, moves )
    
    // Here `m' is the exponent vector of a PBW monomial relative to 
    // the reduced word w1,
    // `moves' is a list of elementary moves, moving w1 to the word w2;
    // `B' is the matrix of the bilinear form, in the root basis.
    // We have that `m' is equivalent to a monomial expression relative
    // to w2, modulo q. This function calculates that monomial.
    
    exp:= m;
    for move in moves do

        if #move eq 4 then
            
            // just interchange the corresponding exponents.
            
            l:= move[1];
            store:= exp[l+1];
            exp[l+1]:= exp[l];
            exp[l]:= store;
            
        elif #move eq 6 then
            
            // here (a,b,c) - > ( b+c-min, min, a+b-min ), where
            // a,b,c are the three exponents, and min = Min( a, c ).
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2];
            min:= Minimum( a, c );
            exp[l]:= b+c-min;
            exp[l+1]:= min;
            exp[l+2]:= a+b-min;
            
        elif #move eq 8 then
            
            // This case is rather complicated. Roughly it works as 
            // follows. Suppose that F_1^a F_2^b F_3^c F_4^d is the 
            // PBW-monomial in the qea of type B2. Then we calculate
            // exponents p1,p2,p3,p4 belonging to an adapted string
            // corresponding to the word where we move to. Finally
            // we calculate the exponents of the PBW-monomial corresponding
            // to this adapted string.
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2]; d:= exp[l+3];
            min:= Minimum( b, d );
            max:= Maximum( b, d );
            
            if B[ move[2] ][ move[2] ] eq 2 then
                
                // i.e., the move is s_a s_b s_a s_b -> s_b s_a s_b s_a,
                // where b is short.
                
                p1:= Maximum( b, max+2*c-2*a );
                p2:= Maximum( b+c, a+b );
                p3:= Minimum( 2*c+d, min+2*a );
                p4:= Minimum( a, c );
                
                if p3 le p2+p4 then
                    exp[l]:= p1;
                    exp[l+1]:= p4;
                    exp[l+2]:= p3-2*p4;
                    exp[l+3]:= p2-p3+2*p4;
                else
                    exp[l]:= p1;
                    exp[l+1]:= p3-p2;
                    exp[l+2]:= 2*p2-p3;
                    exp[l+3]:= p4;
                end if;
                
            else
                
                // i.e., the move is s_a s_b s_a s_b -> s_b s_a s_b s_a,
                // where b is long.
                
                p1:= Maximum( b, max+c-a );
                p2:= Maximum( a, c ) + 2*b;
                p3:= Minimum( c+d, a+min );
                p4:= Minimum( a, c );

                if p2+p4 le 2*p3 then
                    exp[l]:= p1;
                    exp[l+1]:=2*p3-p2;
                    exp[l+2]:= p2-p3;
                    exp[l+3]:= p4;
                else
                    exp[l]:= p1;
                    exp[l+1]:= p4;
                    exp[l+2]:= p3-p4;
                    exp[l+3]:= p2+2*p4-2*p3;
                end if;
                
            end if;
            
        elif #move eq 12 then
            
            // We are in the G2 case. We map to the case D4, and back.
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2]; d:= exp[l+3];
            e:= exp[l+4]; f:= exp[l+5];
            B2:= [ [ 2, -1, 0, 0 ], [ -1, 2, -1, -1 ], [ 0, -1, 2, 0 ], 
                   [ 0, -1, 0, 2 ] ];
            
            if B[ move[2] ][ move[2] ] eq 6 then
                
                // i.e., the move is s_a s_b ... -> s_b s_a ..
                // where b is long.
                
                moves2:= [ [ 6, 3, 7, 1 ], [ 7, 4, 8, 1 ], 
                           [ 8, 2, 9, 1, 10, 2 ], [ 6, 4, 7, 3 ], 
                           [ 4, 2, 5, 4, 6, 2 ], [ 6, 3, 7, 2, 8, 3 ], 
                           [ 5, 3, 6, 4 ], [ 8, 1, 9, 3 ], 
                           [ 9, 2, 10, 3, 11, 2 ], [ 3, 2, 4, 3, 5, 2 ], 
                           [ 5, 4, 6, 2, 7, 4 ], [ 7, 1, 8, 4 ], 
                           [ 1, 1, 2, 2, 3, 1 ], [ 3, 3, 4, 1 ], 
                           [ 4, 4, 5, 1 ], [ 5, 2, 6, 1, 7, 2 ], 
                           [ 7, 4, 8, 2, 9, 4 ], [ 6, 4, 7, 1 ], 
                           [ 4, 2, 5, 4, 6, 2 ], [ 2, 3, 3, 2, 4, 3 ], 
                           [ 9, 3, 10, 4 ], [ 6, 1, 7, 2, 8, 1 ], 
                           [ 5, 1, 6, 4 ], [ 4, 1, 5, 3 ], 
                           [ 10, 2, 11, 4, 12, 2 ], [ 4, 3, 5, 1 ], 
                           [ 5, 4, 6, 1 ], [ 6, 2, 7, 1, 8, 2 ], 
                           [ 8, 3, 9, 2, 10, 3 ], [ 7, 3, 8, 1 ], 
                           [ 4, 4, 5, 3 ], [ 5, 2, 6, 3, 7, 2 ], 
                           [ 7, 1, 8, 2, 9, 1 ], [ 3, 4, 4, 2, 5, 4 ], 
                           [ 5, 3, 6, 4 ], [ 6, 1, 7, 4 ], [ 5, 1, 6, 3 ] ];

                exp2:= [ a, b,b,b, c, d,d,d, e, f,f,f ];
                exp2:= $$( exp2, B2, moves2 );
                exp[l]:= exp2[1]; exp[l+1]:= exp2[4];
                exp[l+2]:= exp2[5]; exp[l+3]:= exp2[8];
                exp[l+4]:= exp2[9]; exp[l+5]:= exp2[12];
                
            else
                
                // i.e., the move is s_a s_b ... -> s_b s_a ..
                // where b is short.
                
                moves2:= [ [ 5, 3, 6, 1 ], [ 6, 4, 7, 1 ], 
                           [ 7, 2, 8, 1, 9, 2 ], [ 5, 4, 6, 3 ], 
                           [ 3, 2, 4, 4, 5, 2 ], [ 5, 3, 6, 2, 7, 3 ], 
                           [ 4, 3, 5, 4 ], [ 7, 1, 8, 3 ], 
                           [ 8, 2, 9, 3, 10, 2 ], [ 6, 1, 7, 2, 8, 1 ], 
                           [ 5, 1, 6, 4 ], [ 4, 1, 5, 3 ], 
                           [ 10, 4, 11, 2, 12, 4 ], [ 9, 4, 10, 3 ], 
                           [ 4, 3, 5, 1 ], [ 5, 4, 6, 1 ], 
                           [ 6, 2, 7, 1, 8, 2 ], [ 2, 2, 3, 3, 4, 2 ], 
                           [ 4, 4, 5, 2, 6, 4 ], [ 6, 1, 7, 4 ], 
                           [ 7, 2, 8, 4, 9, 2 ], [ 5, 1, 6, 2, 7, 1 ], 
                           [ 4, 1, 5, 4 ], [ 3, 1, 4, 3 ], 
                           [ 9, 3, 10, 2, 11, 3 ], [ 7, 4, 8, 1 ], 
                           [ 8, 3, 9, 1 ], [ 5, 2, 6, 4, 7, 2 ], 
                           [ 1, 2, 2, 1, 3, 2 ], [ 3, 3, 4, 2, 5, 3 ], 
                           [ 5, 4, 6, 3 ], [ 6, 2, 7, 3, 8, 2 ], 
                           [ 4, 4, 5, 2, 6, 4 ], [ 8, 1, 9, 2, 10, 1 ], 
                           [ 6, 3, 7, 4 ], [ 7, 1, 8, 4 ], [ 6, 1, 7, 3 ] ];
                
                exp2:= [ a,a,a, b, c,c,c, d, e,e,e, f ];
                exp2:= $$( exp2, B2, moves2 );
                exp[l]:= exp2[1]; exp[l+1]:= exp2[4];
                exp[l+2]:= exp2[5]; exp[l+3]:= exp2[8];
                exp[l+4]:= exp2[9]; exp[l+5]:= exp2[12];
            end if;
            
        end if;
    end for;

    return exp;
    
end function;
   
            
intrinsic Falpha( u::AlgQUEElt, k::RngIntElt ) -> AlgQUEElt 
{Here u is a monomial in the negative part of a quantized enveloping 
   algebra, and k an integer between 1 and the rank of the root datum.
   This function returns the result of acting with the k-th Kashiwara
   operator F_\alpha_k on u.}
     
    // here u is a monomial in U_q^- and k in integer (1 <= k <=rank);
    // We compute the element that is obtained from u by acting with the
    // k-th Kashiwara operator \tilde{F}_k.

    require #Monomials( u ) eq 1: "u is not a monomial";

    U:= Parent( u );
    R:= U`RootDatum;

    rank:= Rank( R );
    s:= #PositiveRoots( R );

    require &and[ KDegree( u, i ) eq <0,0> : i in [1..rank] ]: "u does not
    belong to the negative part of the quantized enveloping algebra";

    require &and[ Degree( u, i ) eq 0 : i in [s+rank+1..2*s+rank] ]: 
    "u does not
    belong to the negative part of the quantized enveloping algebra";

    CF:= U`NormalizedCoxeterForm;
    w0:= LongestWeylWord( R );
    v:= LongWords( R )[k];

    mon:= Monomials( u )[1];
    
    // construct the exponent vector.
    exp:= [ ];
    for i in [1..#w0] do
        Append( ~exp, Degree( mon, i ) );
    end for;
    
    // Move it to an exponent vector relative to a reduced
    // expression of w0, starting with `k'.

    exp:= MoveExpVector( exp, CF, v[2] );

    // Increase first exponent by 1:
    exp[1]:= exp[1]+1;
    // Move back:
    exp:= MoveExpVector( exp, CF, v[3] );
    
    // Produce the PBW-monomial:
    mon:= One( U );
    for i in [1..#exp] do
        for j in [1..exp[i]] do
            mon:= mon*U.i;
        end for;
    end for;
    return Monomials( mon )[1];

end intrinsic;


intrinsic Ealpha( u::AlgQUEElt, k::RngIntElt ) -> AlgQUEElt 
{Here u is a monomial in the negative part of a quantized enveloping 
   algebra, and k an integer between 1 and the rank of the root datum.
   This function returns the result of acting with the k-th Kashiwara
   operator E_\alpha_k on u. The result is 0 of the operator cannot be
   applied.}
    
    // here u is a monomial in U_q^- and k in integer (1 <= k <=rank);
    // We compute the element that is obtained from u by acting with the
    // k-th Kashiwara operator \tilde{E}_k.
    // The result is 0 if the operator cannot be applied.

    require #Monomials( u ) eq 1: "u is not a monomial";

    U:= Parent( u );
    R:= U`RootDatum;

    rank:= Rank( R );
    s:= #PositiveRoots( R );
    require &and[ KDegree( u, i ) eq <0,0> : i in [1..rank] ]: "u does not
    belong to the negative part of the quantized enveloping algebra";

    require &and[ Degree( u, i ) eq 0 : i in [s+rank+1..2*s+rank] ]: 
    "u does not
    belong to the negative part of the quantized enveloping algebra";

    CF:= U`NormalizedCoxeterForm;
    w0:= LongestWeylWord( R );
    v:= LongWords( R )[k];

    mon:= Monomials( u )[1];
    
    // construct the exponent vector.
    exp:= [ ];
    for i in [1..#w0] do
        Append( ~exp, Degree( mon, i ) );
    end for;
    
    // Move it to an exponent vector relative to a reduced
    // expression of w0, starting with `k'.

    exp:= MoveExpVector( exp, CF, v[2] );

    if exp[1] eq 0 then 
       return Zero(U);
    end if;

    // Decrease first exponent by 1:
    exp[1]:= exp[1]-1;
    // Move back:
    exp:= MoveExpVector( exp, CF, v[3] );
    
    // Produce the PBW-monomial:
    mon:= One( U );
    for i in [1..#exp] do
        for j in [1..exp[i]] do
            mon:= mon*U.i;
        end for;
    end for;
    return Monomials( mon )[1];

end intrinsic;

lexord:= function( s1, s2 )
    
   // lex ordering for adapted strings:
   // [2,0,3,0,1] < [2,0,4,0,1] etc.

   // returns -1 if s1 < s2, 1 if s1 > s2, 0 if s1=s2.        
    
   for k in [1..#s1] do
       if s1[k] lt s2[k] then
          return -1;
       elif s1[k] gt s2[k] then
            return 1;
       end if;
   end for;
   // they are equal...
   return 0;
   
end function;

    
lex:= function( m1, m2 )
    
   // lex for monomials 
   // x_1x_2^3x_3^2... < x_1x_2^3x_3^3 etc.

   // returns -1 if m1 < m2, 1 if m1 > m2, 0 if m1=m2. 

   novar:= #PositiveRoots( Parent( m1 )`RootDatum );

   for i in [1..novar] do

       d1:= Degree( m1, i );
       d2:= Degree( m2, i );
       if d1 ne d2 then
          if d1 lt d2 then 
             return -1;
          else
             return 1;
          end if;
       end if;

   end for;
   
   return 0;

end function;
    

CBElements_HR:= function( U, rt )

    // Here `U' is a QEA, rt a linear combination
    // of simple roots (i.e., rt is the sequence of coeffcients).
    // We return the elements of the canonical basis of weight `rt'.
     // This function works best when the rank is >4.

    posR:= U`Roots[1];
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;

    // Now we calculate the adapted strings of weight `rt'.
    // An adapted string is represented as a
    // list of the same length as w0, with on the i-th position, the 
    // exponent of the w0[i]-th path operator. 
    
    // First we calculate all monomials of weight `rt'. The algorithm
    // is as follows: the monomial of the highest degree consists of
    // F_a only, where a is a simple root. If m is a monomial of degree
    // r, then we construct monomials of degree r+1 as follows. We write
    // down all positive roots involved in the generators that constitute 
    // m. We see which pairs sum to a root, and we decrease the exponents
    // corresponding to such a pair, while increasing the exponent
    // corresponding to their sum (all by 1).
    // The sequence `mlist' will consist of the exponent vectors of the
    // monomials.

    nu:= [ 0 : x in [1..s] ];
    for i in [1..rank] do
        nu[ Position( conv, i ) ]:= rt[i];
    end for;
    oldlev:= [ nu ];
    mlist:= [ nu ];
    deg:= &+rt -1;
    while deg ge 1 do
        newlev:= [ ];
        for mon in oldlev do
            rts:= [ ];
            for i in [1..#mon] do
                if mon[i] ne 0 then
                    Append( ~rts, [* i, posR[conv[i]] *] );
                end if;
            end for;
            for i in [1..#rts] do
                for j in [i+1..#rts] do
                    rr:= rts[i][2]+rts[j][2];
                    pos := Position( conv, Position( posR, rr ) );
                    if pos gt 0 then
                        mn1:= mon;
                        mn1[rts[i][1]]:= mn1[rts[i][1]]-1;
                        mn1[rts[j][1]]:= mn1[rts[j][1]]-1;
                        mn1[pos]:= mn1[pos]+1;
                        if not mn1 in newlev then
                            Append( ~newlev, mn1 );
                        end if;
                    end if;
                end for;
            end for;
        end for;
        oldlev:= newlev;
        mlist cat:= newlev;
        deg:= deg-1;
    end while;

    mons:= [ ];

    for m in mlist do

        mon:= One( U );
        for i in [1..#m] do
            for j in [1..m[i]] do
                mon:= mon*U.i;
            end for;
        end for;
        Append( ~mons, Monomials(mon)[1] );

    end for;

    w0:= LongestWeylWord( R );
    strings:= [ ];
    
    // Now for each monomial we calculate the corresponding string,
    // by acting with the Kashiwara operators.

    for m in mons do

        b:= m;
        st:= [ 0 : i in [1..s] ];
        for i in [1..s] do
            j:= 0;
            while b ne 0 do
                a:= b;
                b:= Ealpha( b, w0[i] );
                j:= j+1;
            end while;
            j:= j-1;
            b:= a;
            st[i]:= j;
        end for;
        Append( ~strings, st );
    end for;

    // Sort the strings; biggest one first:
    Sort( ~strings, function(x,y) return lexord(y,x); end function);

    // `stringMon' will be the list of monomials corresponding to the 
    // strings; as linear combinations of PBW elements.

    stringMon:= [ ];
    outStr:= [ ];
    for st in strings do
        m:= One(U);
        est:= [ ];
        for i in [1..s] do
            if st[i] ne 0 then
               ind:= Position( conv, w0[i] );
               f:= One( U );
               for j in [1..st[i]] do
                   f:= f*U.ind;
               end for;
               m:= m*Monomials(f)[1];
               Append( ~est, w0[i] );
               Append( ~est, st[i] );
            end if;
        end for;
        Append( ~stringMon, m );
        Append( ~outStr, est );
    end for;

    celms:= [ ];
    len:= 0;
        
    // `celms' will be a list of lists of length two;
    // let l be such a list, then l[1] is an element of the canonical
    // basis, and l[2] is the index of its principal vector, i.e., 
    // index as element of `mons'
    // `celms' is ordered from small to big (ordering on principal 
    // monomials).

    strs:= [ ];
    
    for i in [1..#stringMon] do

        g:= stringMon[i];
        mg:= Monomials( g );
        cg:= Coefficients( g );            
        // If the coefficients of `g' are all elements from 
        // qZ[q], then we are happy: it is a canonical element.
        // If not, we use the previous canonical elements to repair the 
        // situation.

        for j in [1..len] do

            // look in g for the principal monomial of the j-th canonical
            // element.
            pos:= 0;
            for k in [1..#mg] do
                if mg[k] eq mons[ celms[j][2] ] then
                   pos:= k;
                   break k;
                end if;
            end for;

            if pos gt 0 then
                pol:= cg[pos];
                val:= Degree( Denominator( pol ) );

                // if this has non-positive powers of q, then we repair this
                // situation by adding a bar-invariant multiple of the 
                // appropriate canonical element.

                if val eq 0 then
                   // it is a polynomial in q; we see if it has a 
                   // constant coefficient...
                   mns:= Monomials( Numerator( pol ) );
                   pp:= Position( mns, 1 );
                   fac:= Coefficients(  Numerator( pol ) )[pp];
                   if fac ne 0 then
                      g:= g - fac*celms[j][1];
                      mg:= Monomials( g );
                      cg:= Coefficients( g ); 
                   end if;
               
                elif val gt 0 then
                   k:= 1;
                   c:= Coefficients( Numerator( pol ) );
                   mns:= Monomials( Numerator( pol ) );

                   fac:= 0*pol;
                   done:= false;
                   while k le #c and not done do
                       deg:= Degree( mns[k] ); 
                       if deg gt val then
                          done:= true;
                       else
                          if deg lt val then
                             fac:= fac + c[k]*q^(deg-val) + c[k]*q^(-deg+val);
                          else // a constant; we only subtract it once...
                             fac:= fac+c[k];
                          end if;
                          k:= k+1;
                       end if;
                   end while;

                   g:= g - fac*celms[j][1];
                   mg:= Monomials( g );
                   cg:= Coefficients( g );    
                end if;       
            end if;
        end for;
        
        // Now g is a canonical element.            
        // look for correct position
        // lexicographic ordering of principal monomials
        pp:= 0;
        j:= len;

        for k in [1..#cg] do
            if IsOne( cg[k] ) then
               pmn:= mg[k];
               break;
            end if;
        end for;

        while pp eq 0 and j gt 0 do
              if lex( mons[ celms[j][2] ], pmn ) eq -1 then
                 pp:= j+1;
              else
                 j:= j-1;
              end if;
        end while;
                    
        if pp eq 0 then
           pp:= 1;
        end if;

        // Insert on the correct position:
        Insert( ~celms, pp, [* g, Position( mons, pmn ) *] );
        len:= len+1;

        Insert( ~strs, pp, outStr[  Position( mons, pmn ) ] );

    end for;

    return [ x[1] : x in celms ];

end function;    


CBElements_LR:= function( U, rt )

    // Here `U' is a QEA, rt a linear combination
    // of simple roots (i.e., rt is the sequence of coeffcients).
    // We return the elements of the canonical basis of weight `rt'.
    // This version of the function works well if the rank of the root
    // system is <= 4.

    posR:= U`Roots[1];
    q:= CoefficientRing( U ).1;
    R:= U`RootDatum;
    conv:= U`Perm;
    rank:= Rank( R );
    s:= #posR;


    // Now we calculate the adapted strings of weight `rt'.
    // An adapted string is represented as a
    // list of the same length as w0, with on the i-th position, the 
    // exponent of the w0[i]-th path operator. 
    
    // First we calculate all monomials of weight `rt'. The algorithm
    // is as follows: the monomial of the highest degree consists of
    // F_a only, where a is a simple root. If m is a monomial of degree
    // r, then we construct monomials of degree r-1 as follows. We write
    // down all positive roots involved in the generators that constitute 
    // m. We see which pairs sum to a root, and we decrease the exponents
    // corresponding to such a pair, while increasing the exponent
    // corresponding to their sum (all by 1).

    nu:= [ 0 : x in [1..s] ];
    for i in [1..rank] do
        nu[ Position( conv, i ) ]:= rt[i];
    end for;
    oldlev:= [ nu ];
    mlist:= [ nu ];
    deg:= &+rt -1;
    while deg ge 1 do
        newlev:= [ ];
        for mon in oldlev do
            rts:= [ ];
            for i in [1..#mon] do
                if mon[i] ne 0 then
                    Append( ~rts, [* i, posR[conv[i]] *] );
                end if;
            end for;
            for i in [1..#rts] do
                for j in [i+1..#rts] do
                    rr:= rts[i][2]+rts[j][2];
                    pos := Position( conv, Position( posR, rr ) );
                    if pos gt 0 then
                        mn1:= mon;
                        mn1[rts[i][1]]:= mn1[rts[i][1]]-1;
                        mn1[rts[j][1]]:= mn1[rts[j][1]]-1;
                        mn1[pos]:= mn1[pos]+1;
                        if not mn1 in newlev then
                            Append( ~newlev, mn1 );
                        end if;
                    end if;
                end for;
            end for;
        end for;
        oldlev:= newlev;
        mlist cat:= newlev;
        deg:= deg-1;
    end while;

    mons:= [ ];

    for m in mlist do

        mon:= One( U );
        for i in [1..#m] do
            for j in [1..m[i]] do
                mon:= mon*U.i;
            end for;
        end for;
        Append( ~mons, Monomials(mon)[1] );

    end for;

    Sort( ~mons, function(x,y) return lex(y,x); end function);

    b:= BarAutomorphism( U );

    canelms:= [ ];
    for i in [1..#mons] do

        // we let g be bar(x_i)-x_i:
        g:= b(mons[i])-mons[i];

        len:= #canelms;
        // we write g as a liner combination of canonical elements that
        // we already found:
        cfs:= [ ];
        mg:= Monomials( g );
        cg:= Coefficients( g );
        for j in [len..1 by -1] do

            // Look in g for the principal monomial of the j-th canonical
            // element.

            pos:= 0;
            for k in [1..#mg] do
                if mg[k] eq mons[ j ] then
                   pos:= k;
                   break k;
                end if;
            end for;
            
            if pos gt 0 then
                Append( ~cfs, cg[pos] );
                g:= g - cg[pos]*canelms[j];
                mg:= Monomials( g );
                cg:= Coefficients( g );
            else
                Append( ~cfs, 0*q );
            end if;

        end for;

        cfs:= Reverse( cfs );

        // for every coefficient in cfs we find a c such that 
        // c - bar(c) equals that coefficient.
        for j in [1..#cfs] do
            cfs[j]:= poly_part( cfs[j], q );        
        end for;

        // finally we make the linear combination cfs*canelms, and add 
        // the principal monomial:
        g:= mons[i];
        for j in [1..#cfs] do
            g:= g + cfs[j]*canelms[j];
        end for;

        Append( ~canelms, g );
         
    end for;

    return canelms;

end function;


intrinsic CanonicalElements( U::AlgQUE, rt::SeqEnum ) -> SeqEnum
{Here rt is a sequence of non-negative integers, of length equal to
the rank of the root datum of U. This function returns the elements 
of the canonical basis of weight equal to the linear combination of
simple roots specified by rt.}
    
    R:= U`RootDatum;

    require #rt eq Rank(R): "The weight is not of the correct length";

    require &and[ IsIntegral( rt[i] ) and rt[i] ge 0 : i in [1..Rank(R)] ]:
       "rt must have non-negative integral coefficients";

    if Rank( R ) le 4 then
       return CBElements_LR( U, rt );
    else
       return CBElements_HR( U, rt );
    end if;

end intrinsic;


intrinsic CanonicalBasis( V::ModAlg ) -> SeqEnum
{The canonical basis of V}

    // Here V is an irred hw module over a quantum uea; we compute 
    // its canonical basis.

    if assigned V`CanonicalBasis then 
       return V`CanonicalBasis;
    end if;
   
    U:= Algebra( V );

    require Type(U) eq AlgQUE : "This function is only defined for modules over a quantized universal enveloping algebra";

    hw, hwv := HighestWeightsAndVectors( V );

    wts:= [ ];
    vvv:= [ ];
    for i in [1..#hw] do
        for j in [1..#hwv[i]] do
            Append( ~wts, hw[i] );
            Append( ~vvv, hwv[i][j] );
        end for;
    end for;

    R:= RootDatum( U );
    q:= CoefficientRing(U).1;
    w0:= LongestWeylWord( R );
    lenw0:= #w0;
    
    rts:= U`Perm;
    rank:= Rank( R );
    pos:= [ Position( rts, i ) : i in [1..rank] ];

    CF:= U`NormalizedCoxeterForm;

    CC:= [ ];

    for t in [1..#wts] do

       // `cbas' will be a list of canonical basis elements spanning
       // L(\lambda) over Z[q]. The algorithm is a module version of 
       // the algorithm for calculating canonical basis elements in the
       // negative part of a quantized uea.
   
        cbas:= [ ];    
        _,paths:= CrystalGraph( R, Eltseq( wts[t] ) );       

        // For every path we compute its adapted string.    
        strings:= [ ];    
        for p in paths do
            b:= p;
            st:= [ 0 : i in [1..#w0] ];
            for i in [1..lenw0] do
                j:= 0;
                while not IsZero( b ) do
                      a:= b;
                      b:= Ealpha( b, w0[i] );
                      j:= j+1;
                end while;
                j:= j-1;
                b:= a;
                st[i]:= j; 
            end for;
            Append( ~strings, st );            
        end for;

        while #paths gt 0 do
        
            celms:= [ ];
            len:= 0;
        
            // `celms' will be a list of lists of length two;
            // let l be such a list, then l[1] is an element of the canonical
            // basis, and l[2] is the index of its principal vector, i.e., 
            // index as element of `vv' (to be constructed).
            // `celms' is ordered from small to big (ordering on principal 
            // vectors).

            // `len' is the length of `celms'.
        
            // We take all paths of the same weight as the first path 
            // together, and erase them from the list.
        
            p:= paths[1];
            st:= [ strings[1] ];
            Remove( ~paths, 1 );
            Remove( ~strings, 1 );
            i:= 1;
            while i le #paths do
                  if EndpointWeight( paths[i] ) eq EndpointWeight( p ) then 
                     Append( ~st, strings[i] );
                     Remove( ~paths, i );
                     Remove( ~strings, i );
                  else
                     i:= i+1;
                  end if;
            end while;

            // Sort according to lexicographical order; biggest one first.
        
            Sort( ~st, function(x,y) return lexord(y,x); end function );

            // `mons' will contain the PBW-monomials corresponding to the
            // strings in `st';
            // `vv' is the list of m^hwvec, where m is from `mons';
            // the elements from `vv' span the lattice L(\lambda) over Z[q];
            // `ww' is the list `m^v0', where `m' is the monomial in 
            // the generators corresponding to a string.
        
            mons:= [ ]; ww:=[ ]; vv:= [ ];
            for s in st do
                u:= One( U );
                for i in [lenw0..1 by -1] do
                    for k in [1..s[i]] do
                        u:= Falpha( u, w0[i] );
                    end for;
                end for;

                Append( ~mons, u );                    
                Append( ~vv, Vector( u^vvv[t] ) );
                    
                vec:= vvv[t];
                for i in [lenw0..1 by -1] do
                    for k in [1..s[i]] do
                        vec:= U.pos[ w0[i] ]^vec;
                    end for;
                    qa:= q^( Integers()!(CF[w0[i]][w0[i]]/2) );
                    vec:= vec/GaussianFactorial( s[i], qa );
                end for;

                Append( ~ww, vec );
            end for;     

            b:= VectorSpaceWithBasis( vv );
                
            for i in [1..#ww] do
                    
                // We write ww[i] as a linear combination of elements 
                // from `vv'. If the coefficients are all elements from 
                // qZ[q], then we are happy: then the element is 
                // bar-invariant, and it lies in L(\lambda). If not, we 
                // use the previous canonical elements to repair the 
                // situation.
                    
                w:= ww[i];
                cf:= Coordinates( b, Vector( w ) );

                for j in [1..len] do
                    pol:= cf[ celms[j][2] ]; 
                    val:= Degree( Denominator( pol ) ); 

                   // if this has non-positive powers of q, then we repair this
                   // situation by adding a bar-invariant multiple of the 
                   // appropriate canonical element.
                        
                   if val eq 0 then
                      // it is a polynomial in q; we see if it has a 
                      // constant coefficient...
                      if not IsZero(pol) then
                         mns:= Monomials( Numerator( pol ) );
                         pp:= Position( mns, 1 );
                         fac:= Coefficients(  Numerator( pol ) )[pp];
                         if fac ne 0 then
                            w:= w-fac*celms[j][1];
                            cf:= Coordinates( b, Vector( w ) );
                         end if;
                      end if;
               

                    elif val gt 0 then
                       k:= 1;
                       c:= Reverse( Coefficients( Numerator( pol ) ) );
                       mns:= Reverse( Monomials( Numerator( pol ) ) );
                       fac:= 0*pol;
                       done:= false;
                       while k le #c and not done do
                            deg:= Degree( mns[k] ); 
                            if deg gt val then
                               done:= true;
                            else
                               if deg lt val then
                                  fac:= fac + c[k]*q^(deg-val) + 
                                              c[k]*q^(-deg+val);
                               else // a constant; we only subtract it once...
                                  fac:= fac+c[k];
                               end if;
                               k:= k+1;
                            end if;
                       end while;                            
                       w:= w-fac*celms[j][1];
                       cf:= Coordinates( b, Vector( w ) );
                    end if;       
                end for;
                    
                // look for correct position
                // lexicographic ordering of principal monomials
                pp:= 0;
                j:= len;
                    
                while pp eq 0 and j gt 0 do
                    if lex( mons[ celms[j][2] ], mons[i] ) eq -1 then
                       pp:= j+1;
                    else
                       j:= j-1;
                    end if;
                end while;
                    
                if pp eq 0 then
                   pp:= 1;
                end if;
                    
                // Insert on the correct position:
                Insert( ~celms, pp, [* w, i *] );
                len:= len+1;

            end for;

            cbas cat:= [ x[1] : x in celms ];

       end while;
       CC cat:= cbas;

    end for;

    V`CanonicalBasis:= CC;
   
    return CC;
    
end intrinsic;

