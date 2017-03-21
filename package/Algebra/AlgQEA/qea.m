freeze;

///////////////////////////////////////////////////////////////////////////

include_mon:= procedure( ~res, ~mons, mon, cf )

    if #mon eq 0 then mon:= [ Integers() | ]; end if;

    if cf ne 0 then
        
       pos:= Position( mons, mon );
       if pos gt 0 then
          pos:= 2*pos-1;
          res[pos+1]+:= cf;
          if res[pos+1] eq 0 then
             Remove( ~res, pos );
             Remove( ~res, pos );
             mons:= {@@};
             for u in [1..#res-1 by 2 ] do
                 Include( ~mons, res[u] );
             end for;
          end if;
       else
          Append( ~res, mon );
          Append( ~res, cf );
          Include( ~mons, mon ); 
       end if;
    end if;

end procedure;

//
//  This file contains the basic code for computing the multiplication table 
//  of (PBW-type basis of) a quantized enveloping algebra.
//
//  This file roughly consists of four parts:
// 
//       * code for moving a w-expression into a u-expression,
//       * code for getting comm rels between two E's and between two F's,
//       * code for getting comm rels between an F and an E,
//       * code to create the quantized enveloping algebra.
//
//


//
//
//  Part one
//
//  Let w be a reduced word in the Weyl group and write w=s1s2..st.
//  Set Ek = T1..T{k-1}(E{k}) for k=1..t. Then any polynomial expression
//  in the Ek is called a w-expression. It is said to be in normal form 
//  if all monomials are of the form E{i1}...E{ir} with i1<i2<...<ir.
//  Let u be a reduced word in the Weyl group representing the same element
//  of the Weyl group as w. Let p be a w-expression in normal form. Then
//  p is equal to a u-expression in normal form. This first part contains 
//  code for finding this u-expression, given p, w, u. We reduce to the rank
//  2 case, where u is constructed from w by one elementary move. 
//  Furthermore, we assume that there is no component of type G2. 
//  The rewriting in the rank 2 cases is handled by the functions
//  `A2_rewrite', `B2_rewrite_1', `B2_rewrite_2'. The rewriting of an
//  expression "relative" to only one elementary move is handled by
//  `EltMove'. Finally everything is put together in `MoveIt'.


A2_rewrite:= function( expr, qa )
    
    // Let a and b be two roots spanning a root system of type A2, set
    // X1 = Ea, X2 = Ta(Eb), X3 = Eb, Y1 = Eb, Y2 = Tb(Ea), Y3=Ea. 
    // This functions rewrites an expression in the Xi to an expression in 
    // the Yi. Here expr is of the form [* [i1, e1, ...], cf, [... etc ]..*], 
    // where the indices ik are 1,2,3 (indicating whether it is X1,X2,X3). 
    
    // `todo' will contain the `expr' with the Yi substituted for the
    // Xi. We use the following substitutions:
    //
    //  X1 = Y3, X3 = Y1,
    //  X2 = (qa-qa^-1)Y1Y3-qaY2
    //
    // Also we "stretch" the monomials, i.e., [1,3,2,2] will be represented
    // as [ 1, 1, 1, 2, 2 ]. 
    

    todo:= [* *];
    for i in [1..#expr-1 by 2 ] do
        mns:= [* [], expr[i+1] *];
        for j in [1..#expr[i]-1 by 2] do
            if expr[i][j] eq 1 then
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 3 : m in [1..expr[i][j+1]] ];
                end for;

            elif expr[i][j] eq 2 then
                b:= expr[i][j+1];
                mns1:= [* [1,3], qa-qa^-1, [2], -qa *];
                for k in [1..b-1] do
                    mns2:= [* *];
                    for l in [1..#mns1-1 by 2 ] do
                        m:= mns1[l];
                        m cat:= [ 1,3];
                        Append( ~mns2, m ); 
                        Append( ~mns2, mns1[l+1]*(qa-qa^-1) );
                        m:= mns1[l];
                        Append( ~m, 2 );
                        Append( ~mns2, m ); 
                        Append( ~mns2, mns1[l+1]*(-qa) );
                    end for;
                    mns1:= mns2;
                end for;
                
                mns2:= [* *];
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    for l in [1..#mns1-1 by 2 ] do
                        m:= mns[k];
                        m cat:= mns1[l];
                        Append( ~mns2, m ); 
                        Append( ~mns2, mns[k+1]*mns1[l+1] );
                    end for;
                end for;
                mns:= mns2;
            elif expr[i][j] eq 3 then
                
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 1 : u in [1..expr[i][j+1]] ];
                end for;
            end if;
            
        end for;
        todo cat:= mns;
        
    end for;

    // Now we "straighten" the elements of `todo'. We use the following 
    // relations:
    //
    //  Y2Y1 = qa^(-1)Y1Y2
    //  Y3Y1 = qaY1Y3 - qaY2
    //  Y3Y2 = qa^(-1)Y2Y3
    //
    // `res' will contain the result (in normal form).
    // `mons' will be a list of monomials (only used for fast searching
    // for the position of a monomial in `res').

    res:= [* *];
    mons:= {@@};
    while #todo gt 0 do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        i:= 1;
        while i lt #m do
            if m[i] gt m[i+1] then
                found:= true;
                break;
            end if;
            i:= i+1;
        end while;
        if not found then
            
            // The monomial `m' is in normal form; we add it to `res'.
            // First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            // will become [1,3,2,2]). 
            
            mon:= [ ];
            s:= 1;
            while s le #m do
                ex:= 1;
                while s lt #m and m[s+1] eq m[s] do
                    s:= s+1;
                    ex:= ex+1;
                end while;
                Append( ~mon, m[s] );
                Append( ~mon, ex );
                s:= s+1;
            end while;

            include_mon( ~res, ~mons, mon, cf );

            Remove( ~todo, 1 );
            Remove( ~todo, 1 );

        else
            
            // we apply a commutation relation.
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            
            // note: now the order in m has changed so we test on this 
            // changed order.
            
            if [ m[i+1], m[i] ] eq [ 2, 1 ] then
                
                todo[2]:= todo[2]*qa^-1;
                
            elif [ m[i+1], m[i] ] eq [ 3, 2 ] then
                
                todo[2]:= todo[2]*qa^-1;
                
            else
                todo[2]:= todo[2]*qa;
                start:= [ m[k] : k in [1..i-1] ];
                Append( ~start, 2 );
                start cat:= [ m[k]: k in [i+2..#m] ];
                Append( ~todo, start ); Append( ~todo, cf*(-qa) );
            end if;
            
            
        end if;
    end while;
    
    return res;        
    
end function;

B2_rewrite_1:= function( expr, q )
    

    // Let a,b be two roots spanning a root system of type B2, where b is a
    // long root. Set X1 = Ea, X2 = Ta(Eb), X3 = TaTb(Ea), X4 = TaTbTa(Eb)=Eb, 
    // and Y1 = Eb, Y2 = Tb(Ea), Y3 = TbTa(Eb), Y4 = TbTaTb(Ea). 
    // Here `expr' is an expression on the Xi, which we transform into an
    // expression in the Yi (in normal form).
    
    // First we substitute expressions with Yi's for Xi's. We use the following 
    // substitutions:
    //
    //   X1 = Y4, X4 = Y1,
    //   X2 = q^2Y3 - (q^3-q)Y2Y4+(q^3-2q+q^-1)Y1Y4^2
    //   X3 = -q^2Y2 + (q^2-q^-2)Y1Y4
    //
    // `todo' will contain the result, in streched form 
    // (e.g., [1,1,1,2,2] instead of [1,3,2,2]).

    if #expr eq 0 then return expr; end if;
    
    todo:= [* *];
    for i in [1..#expr-1 by 2 ] do
        mns:= [* [], expr[i+1] *];
        for j in [1..#expr[i]-1 by 2] do
            if expr[i][j] eq 1 then
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 4 : m in [1..expr[i][j+1]] ];
                end for;

            elif expr[i][j] eq 2 then
                b:= expr[i][j+1];
                mns1:= [* [3], q^2, [2,4], -(q^3-q), [1,4,4], q^3-2*q+q^-1 *];
                for k in [1..b-1] do
                    mns2:= [* *];
                    for l in [1..#mns1-1 by 2] do
                        m:= mns1[l];
                        Append( ~m, 3 );
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*q^2 );
                        m:= mns1[l];
                        m cat:= [2,4];
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(-q^3+q) );
                        m:= mns1[l];
                        m cat:= [1,4,4];
                        Append( ~mns2, m ); 
                        Append( ~mns2, mns1[l+1]*(q^3-2*q+q^-1) );
                    end for;
                    mns1:= mns2;
                end for;
                
                mns2:= [* *];
                for k in [1..#mns-1 by 2] do
                    for l in [1..#mns1-1 by 2] do
                        m:= mns[k];
                        m cat:= mns1[l];
                        Append( ~mns2, m ); Append( ~mns2, mns[k+1]*mns1[l+1] );
                    end for;
                end for;
                mns:= mns2;
                
            elif expr[i][j] eq 3 then
                
                b:= expr[i][j+1];
                mns1:= [* [2], -q^2, [1,4], q^2-q^-2 *];
                for k in [1..b-1] do
                    mns2:= [* *];
                    for l in [1..#mns1-1 by 2] do
                        m:= mns1[l];
                        Append( ~m, 2 );
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(-q^2) );
                        m:= mns1[l];
                        m cat:= [1,4];
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(q^2-q^-2) );
                    end for;
                    mns1:= mns2;
                end for;
                
                mns2:= [* *];
                for k in [1..#mns-1 by 2] do
                    for l in [1..#mns1-1 by 2] do
                        m:= mns[k];
                        m cat:= mns1[l];
                        Append( ~mns2, m ); Append( ~mns2, mns[k+1]*mns1[l+1] );
                    end for;
                end for;
                mns:= mns2;

            elif expr[i][j] eq 4 then
                
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 1 : u in [1..expr[i][j+1]] ];
                end for;
            end if;
            
        end for;
        todo cat:= mns;
        
    end for;

    // Now we "straighten" the elements of `todo' using the following 
    // commutation relations:
    //
    //  Y2Y1 = q^(-2)Y1Y2
    //  Y3Y1 = Y1Y3 - (q^2-1)/(q+q^-1)Y2^2
    //  Y4Y1 = q^2Y1Y4 -q^2Y2
    //  Y3Y2 = q^(-2)Y2Y3 
    //  Y4Y2 = Y2Y4 - (q+q^-1)Y3
    //  Y4Y3 = q^(-2)Y3Y4

    res:= [* *];
    mons:= {@@};
    while #todo gt 0 do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        i:= 1;
        while i lt #m do
            if m[i] gt m[i+1] then
                found:= true;
                break;
            end if;
            i:= i+1;
        end while;
        if not found then
            
            // The monomial `m' is in normal form; we add it to `res'.
            // First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            // will become [1,3,2,2]). 
            
            mon:= [ ];
            s:= 1;
            while s le #m do
                ex:= 1;
                while s lt #m and m[s+1] eq m[s] do
                    s:= s+1;
                    ex:= ex+1;
                end while;
                Append( ~mon, m[s] );
                Append( ~mon, ex );
                s:= s+1;
            end while;

            include_mon( ~res, ~mons, mon, cf );

            Remove( ~todo, 1 );
            Remove( ~todo, 1 );

        else
            
            // we apply a commutation relation.
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            
            // note: now the order in m has changed so we test on this 
            // changed order.

            if [ m[i+1], m[i] ] eq [ 2, 1 ] then
                
                todo[2]:= todo[2]*q^-2;
                
            elif [ m[i+1], m[i] ] eq [ 3, 1 ] then
                
                start:= [ m[s] : s in [1..i-1]];
                start cat:= [2,2];
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-(q^2-1)/(q+q^-1)) );
                
            elif [ m[i+1], m[i] ] eq [ 4, 1 ] then
                
                todo[2]:= todo[2]*q^2;
                start:= [ m[s] : s in [1..i-1]];
                Append( ~start, 2 );
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-q^2) );
                
            elif [ m[i+1], m[i] ] eq [ 3, 2 ] then
                
                todo[2]:= todo[2]*q^-2;
                
            elif [ m[i+1], m[i] ] eq [ 4, 2 ] then
                
                start:= [ m[s] : s in [1..i-1]];
                Append( ~start, 3 );
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-(q+q^-1)) );
                
            else
                
                todo[2]:= todo[2]*q^-2;
                
            end if;
            
        end if;
    end while;
    
    return res;        
    
end function;    

B2_rewrite_2:= function( expr, q )

    // Let a,b be two roots spanning a root system of type B2, where b is a
    // long root. Set X1 = Ea, X2 = Ta(Eb), X3 = TaTb(Ea), X4 = TaTbTa(Eb)=Eb, 
    // and Y1 = Eb, Y2 = Tb(Ea), Y3 = TbTa(Eb), Y4 = TbTaTb(Ea). 
    // Here `expr' is an expression on the Yi, which we transform into an
    // expression in the Xi (in normal form).
    
    // First we substitute expressions with Xi's for Yi's. We use the following 
    // substitutions:
    //
    //   Y1 = X4, Y4 = X1,
    //   Y2 = -q^2X3 + (q^2-q^-2)X1X4
    //   Y3 = q^2X2 - (q^3-q)X1X3 + (q^3-2q+q^-1)X1^2X4
    //
    // `todo' will contain the result, in streched form 
    // (e.g., [1,1,1,2,2] instead of [1,3,2,2]).

    if #expr eq 0 then return expr; end if;

    todo:= [* *];
    for i in [1..#expr-1 by 2 ] do
        mns:= [* [], expr[i+1] *];
        for j in [1..#expr[i]-1 by 2] do
            if expr[i][j] eq 1 then
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 4 : m in [1..expr[i][j+1]] ];
                end for;

            elif expr[i][j] eq 3 then
                b:= expr[i][j+1];
                mns1:= [* [2], q^2, [1,3], -(q^3-q), [1,1,4], q^3-2*q+q^-1 *];
                for k in [1..b-1] do
                    mns2:= [* *];
                    for l in [1..#mns1-1 by 2] do
                        m:= mns1[l];
                        Append( ~m, 2 );
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*q^2 );
                        m:= mns1[l];
                        m cat:= [1,3];
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(-q^3+q) );
                        m:= mns1[l];
                        m cat:= [1,1,4];
                        Append( ~mns2, m ); 
                        Append( ~mns2, mns1[l+1]*(q^3-2*q+q^-1) );
                    end for;
                    mns1:= mns2;
                end for;
                
                mns2:= [* *];
                for k in [1..#mns-1 by 2] do
                    for l in [1..#mns1-1 by 2] do
                        m:= mns[k];
                        m cat:= mns1[l];
                        Append( ~mns2, m ); Append( ~mns2, mns[k+1]*mns1[l+1] );
                    end for;
                end for;
                mns:= mns2;
                
            elif expr[i][j] eq 2 then
                
                b:= expr[i][j+1];
                mns1:= [* [3], -q^2, [1,4], q^2-q^-2 *];
                for k in [1..b-1] do
                    mns2:= [* *];
                    for l in [1..#mns1-1 by 2] do
                        m:= mns1[l];
                        Append( ~m, 3 );
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(-q^2) );
                        m:= mns1[l];
                        m cat:= [1,4];
                        Append( ~mns2, m ); Append( ~mns2, mns1[l+1]*(q^2-q^-2) );
                    end for;
                    mns1:= mns2;
                end for;
                
                mns2:= [* *];
                for k in [1..#mns-1 by 2] do
                    for l in [1..#mns1-1 by 2] do
                        m:= mns[k];
                        m cat:= mns1[l];
                        Append( ~mns2, m ); Append( ~mns2, mns[k+1]*mns1[l+1] );
                    end for;
                end for;
                mns:= mns2;

            elif expr[i][j] eq 4 then
                
                k:= 1;
                for k in [1..#mns-1 by 2 ] do
                    mns[k] cat:= [ 1 : u in [1..expr[i][j+1]] ];
                end for;
            end if;
            
        end for;
        todo cat:= mns;
        
    end for;

    // Now we "straighten" the elements of `todo'. We use the following 
    // commutation relations:
    //
    //   X2X1 = q^(-2)X1X2
    //   X3X1 = X1X3 - (q+q^-1)X2
    //   X4X1 = q^2X1X4 - q^2X3
    //   X3X2 = q^(-2)X2X3
    //   X4X2 = X2X4 - (q^2-1)/(q+q^-1)X3^2
    //   X4X3 = q^(-2)X3X4
    

    res:= [* *];
    mons:= {@@};
    while #todo gt 0 do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        i:= 1;
        while i lt #m do
            if m[i] gt m[i+1] then
                found:= true;
                break;
            end if;
            i:= i+1;
        end while;
        if not found then
            
            // The monomial `m' is in normal form; we add it to `res'.
            // First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            // will become [1,3,2,2]). 
            
            mon:= [ ];
            s:= 1;
            while s le #m do
                ex:= 1;
                while s lt #m and m[s+1] eq m[s] do
                    s:= s+1;
                    ex:= ex+1;
                end while;
                Append( ~mon, m[s] );
                Append( ~mon, ex );
                s:= s+1;
            end while;

            include_mon( ~res, ~mons, mon, cf );

            Remove( ~todo, 1 );
            Remove( ~todo, 1 );

        else
            
            // we apply a commutation relation.
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            
            // note: now the order in m has changed so we test on this 
            // changed order.

            if [ m[i+1], m[i] ] eq [ 2, 1 ] then
                
                todo[2]:= todo[2]*q^-2;
                
            elif [ m[i+1], m[i] ] eq [ 3, 1 ] then
                
                start:= [ m[s] : s in [1..i-1]];
                start cat:= [2];
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-q-q^-1) );
                
            elif [ m[i+1], m[i] ] eq [ 4, 1 ] then
                
                todo[2]:= todo[2]*q^2;
                start:= [ m[s] : s in [1..i-1]];
                Append( ~start, 3 );
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-q^2) );
                
            elif [ m[i+1], m[i] ] eq [ 3, 2 ] then
                
                todo[2]:= todo[2]*q^-2;
                
            elif [ m[i+1], m[i] ] eq [ 4, 2 ] then
                
                start:= [ m[s] : s in [1..i-1]];
                start cat:=  [3,3];
                start cat:= [ m[s] : s in [i+2..#m]];
                Append( ~todo, start ); Append( ~todo, cf*(-(q^2-1)/(q+q^-1)) );
                
            else
                
                todo[2]:= todo[2]*q^-2;
                
            end if;
            
        end if;
    end while;
    
    return res;        
    
end function;   


EltMove:= function( move, expr, Bil, q )

    // Let w1 and w2 be two words in the Weyl group, such that 
    // w1 is moved into w2 by the elementary move `move'. 
    // `move' is a list of the form 
    // [ p1, im1, p2, im2, ...] which means that after the move, 
    // on position p1, there will be im1 etc.
    // So moves can be of lengths 4, 6, 8, 12. The last case only occurs 
    // if there is a component of type G2, which is excluded here (for these 
    // components commutation relations are found directly). 
    // `expr' is a w1-expression.
    // the output will be a w2-expression, which is equal to `expr'.
    // Bil is the matrix of the bilinear form.

    // An example in the case of a A1+A1 (should also clarify the rest).
    // Suppose that w1 = x(s_a)(s_b)y, and w2 = x(s_b)(s_a)y, where
    // s_a, s_b commute. The move maps their product to (s_b)(s_a), so the 
    // move reads [ s+1, b', s+2, a' ] (where a', b' denote the index in 
    // the list of simple roots).  This means that
    // the sub-monomial T_{x}(E_a)^m T_{xs_a}(E_b)^n is mapped to
    // T_{x}(E_b)^n T_{xs_b}(E_a)^m. Now the index of T_{x}(E_a) is
    // s+1, i.e., the `k' below. So we interchange the exponents of the
    // elements with indices k, k+1.
    

    k:= move[1]-1;
    if #move eq 4 then
        
        // Here we are in the case of A1+A1; the two elements with indices 
        // k and k+1 respectively commute. We interchange their exponents.
        
        res:= [* *];
        for i in [1..#expr-1 by 2 ] do
            mon:= expr[i];
            for j in [1..#mon-1 by 2 ] do         
                if mon[j] eq k+1 then
 
                    // See whether the next element has index k+2.
                    
                    if j+2 lt #mon and mon[j+2] eq k+2 then
                        // interchange the exponents
                        store:= mon[j+1];
                        mon[j+1]:= mon[j+3];
                        mon[j+3]:= store;
                        break j;
                    else
                        mon[j]:= k+2;
                        break j;
                    end if;
                elif mon[j] eq k+2 then
                    mon[j]:= k+1;
                    break j;
                end if;
            end for;
            Append( ~res, mon );
            Append( ~res, expr[i+1] );
        end for;
        return res;
        
    elif #move ge 6 then
        
        // a2, b2 are booleans signalling whether we are in the A2, or B2 case.
        // `set' will be the set of indices that need to be treated.
        // `up' is the biggest element of this set. 
        
        a2:= false; b2:= false; 
        if #move eq 6 then
            // case (alpha,beta)=-1
            a2:= true;
            set:= [k+1,k+2,k+3];
            up:= k+3;
            qa:= q^( IntegerRing()!(Bil[move[2]][move[2]]/2) );
        else   
            // case B2
            
            if Bil[move[2]][move[2]] eq 4 then
                
                // i.e., b2 is true if we replace the sequence 
                // starting with the short root, by the sequence 
                // starting with the long one. 
                // if both a2 and b2 are false, then we are in the other case.
                b2:= true;
                
            end if;
            
            set:= [ k+1,k+2,k+3,k+4 ];
            up:= k+4;
        end if;

        // `mons' will contain the monomials of `res' (only used for 
        // fast searching for the position of a monomial in `res').
        
        res:= [* *];
        mons:= {@@};
        for i in [1..#expr-1 by 2 ] do
            
            // k1 will be the index of the first element in expr[i] belonging
            // to `set'; k2-1 will be the index of the last such element.
            
            k1:= 0; k2:= #expr[i]+1;
            for j in [1..#expr[i]-1 by 2 ] do
                if expr[i][j] in set and k1 eq 0 then k1:= j; end if;
                if expr[i][j] gt up then k2:= j; break j; end if;
            end for;

            if k1 eq 0 then //i.e., nothing to do 
                Append( ~res, expr[i] ); Append( ~res, expr[i+1] );
                Include( ~mons, expr[i] );
            else
  
                start:= [ expr[i][v] : v in [1..k1-1] ];
                tail:= [ expr[i][v] : v in [k2..#expr[i]] ];
                mn:=  [ expr[i][v] : v in [k1..k2-1] ];
                
                // So now `mn' contains the part of the monomial that needs 
                // treatment.
                // We decrease the indices such that they will fall in the 
                // range [1..3] (A2), or [1..4] (B2).
                
                for j in [1..#mn-1 by 2 ] do
                    mn[j] -:= k;
                end for;
                mn:= [* mn, expr[i+1] *];
                
                // Now we feed `mn' to the rewrite routines (so later on 
                // we need to increase the indices again).
                                
                if a2 then

                    mn:= A2_rewrite( mn, qa );

                elif b2 then
                    
                    mn:= B2_rewrite_1( mn, q );
                    
                else
                    
                    mn:= B2_rewrite_2( mn, q );
                    
                end if;
                
                // We add start and tail again and increase the indices. 
                // Then we add the result to `res'.
                
                for j in [1..#mn-1 by 2 ] do
                    mon:= start;
                    mon1:= mn[j];
                    for l in [1..#mon1-1 by 2] do
                        mon1[l] +:= k;
                    end for;
                    mon cat:= mon1;
                    mon cat:= tail;

                    include_mon( ~res, ~mons, mon, mn[j+1] );
                       
                end for;
            end if;
            
        end for;
        return res;
        
    end if;

end function;


MoveIt:= function( posR, C, B, w1, w2, expr, q )
    
    // Here `posR' is the list of positive roots, in weight basis, 
    // C is the Cartan matrix, and B the matrix of the bilinear form (in root basis).
    // `w1', `w2' are two
    // words in the Weyl group representing the same element.
    // `expr' is a w1-expression. We move it to a w2-expression,
    // by a sequence of elementary moves.

    moves:= GetBraidRelations( posR, C, w1, w2 );
    
    for move in moves do 
        
        // Execute the move.
        
        expr:= EltMove( move, expr, B, q );

    end for;
    return expr;
end function;



//
//   Part two
//
//   In this part we compute commutation relations of the elements E_k, 
//   where E_k = T_{i1}...T_{i_{k-1}}( E_{k} ), where 
//   w0 = s_{i_1}...s_{i_t} is the longest element in the Weyl group,
//   and E_1...E_l are generators of the positive part of the quantum group,
//   where l is the rank of the root system. We use the fact that the T_i 
//   satisfy the braid relations together with the known commutation
//   relations for the rank two cases, to devise a recursive procedure 
//   (`com_rel') that calculates the commutation relations for the general 
//   case.
//   The function `E_tab' puts alll such relations into a table. The function
//   `F_tab' uses the table of the E-elements to create a table of the 
//   F-elements.
//

    
in_p:= function( CF, a, b )

    return Integers()!InnerProduct( Vector( Rationals(), a )*
                                    Matrix( Rationals(), CF ), 
                                    Vector( Rationals(), b ) );
    
end function;
    


forward com_rel;
collect:= procedure( ~expr, ~info, q, j, x, q1, q2, ~GlTab ) 

        // `x' is a word of the form  v = [ i1, i2, i3 .. ik ]
        // It is a reduced word in the Weyl group. 
        // `expr' is an x-expression.
        // q1, q2 are elements of Q(q).
        // We collect q1*expr*T_x(E_j)-q2*T_x(E_j)*expr. 
        // The output is contained in expr.
        // In general iy will be an xs_j-expression.

        R:= info[1];
        posR:= info[6];
        CF:= info[7];

        k:= #x+1;

        // `todo' will be q1*expr*T_x(E_j)-q2*T_x(E_j)*expr.
        // We "stretch" the monomials (e.g., [1,3,2,2] is 
        // represented as [1,1,1,2,2]). 

        todo:= [* *];
        for i in [1..#expr-1 by 2 ] do
            
            // first we `stretch' the monomial:
            m:= [ ];
            for s in [1..#expr[i]-1 by 2] do
                m cat:= [ expr[i][s]: uu in [1..expr[i][s+1]] ];
            end for;
            // Then we add T_x(E_j):
            Append( ~m, k );

            Append( ~todo, m );
            Append( ~todo, expr[i+1]*q1 );

            // Same again, but then prepend T_x(E_j):
            m:= [k];
            for s in [1..#expr[i]-1 by 2] do
                m cat:= [ expr[i][s]: uu in [1..expr[i][s+1]] ];
            end for;
            Append( ~todo, m );
            Append( ~todo, -expr[i+1]*q2 );
        end for;

        v:= x;
        Append( ~v, j );

        // start collecting....
        expr:= [* *];
        mons := {@ @};

        while #todo gt 0 do

            m:= todo[1];
            cf:= todo[2];

            // We try to find the first position in `m' where the 
            // elements are not in the right order.
            
            found:= false;
            ind:= 0;
            for i in [1..#m-1] do
                if m[i] gt m[i+1] then
                    found:= true;
                    ind:= i;
                    break;
                end if;
            end for;
            if not found then

                // We transform the monomial back to non-stretched form,
                // and add the result to `expr'.
                
                mon:= [ ];
                s:= 1;
                while s le #m  do
                    ex:= 1;
                    while s lt #m do 
                        if not m[s+1] eq m[s] then
                           break;
                        else
                           s:= s+1;
                           ex:= ex+1;
                        end if;
                    end while;
                    mon cat:= [ m[s], ex ];
                    s:= s+1;
                end while;
          
                include_mon( ~expr, ~mons, mon, cf );
                      
                Remove( ~todo, 1 );
                Remove( ~todo, 1 );

            else

                // We apply a commutation relation found by a call to `com_rel'.
                // The commutation relation is [ T_{u1u2}(E_r), T_{u1}(E_s) ],
                // with u1, u2 as below, and r = v[m[ind]], 
                // s = v[m[ind+1]]. (Recall that the index of an element
                // T_{w}(E_i) is lenw+1). 
 
                u1:= [ v[uu] : uu in [1..m[ind+1]-1]];
                u2:= [ v[uu] : uu in [m[ind+1]..m[ind]-1]];
                
                rel:= [**];
                com_rel( ~info, q, u1, u2, v[m[ind]], v[m[ind+1]], ~rel, ~GlTab );

                // The commutation relation is 
                // T_{u1u2}(E_r)T_{u1}(E_s) = q^{-(u2(a_r),a_s)}T_{u_1}(E_s)
                //      T_{u1u2}(E_r) + \sigma.
                // Where a_r, a_s are the r-th, and s-th simple roots. 
                // We calculate the exponent of q in this formula.
                
                // first we compute u2( a_{v[m[ind]]} )
                lam:= posR[ v[m[ind]] ];
                for i in [1..#u2] do
                    ii:= u2[#u2-i+1];
                    lam:= lam - lam[ii]*posR[ii];
                end for;

                todo[2]:= todo[2]*q^( -in_p( CF, lam, posR[ v[m[ind+1]] ] ) );

                // Now we change the order of the elements in the principal 
                // monomial, and we add the \sigma (see previous comment).

                st:= m[ind];
                m[ind]:= m[ind+1]; m[ind+1]:= st;
                todo[1]:= m; 
                start:= [ m[u] : u in [1..ind-1] ];
                tail:= [ m[u] : u in [ind+2..#m] ];
                for s in [1..#rel-1 by 2 ] do
                    mon:= start;
                    for t in [1..#rel[s]-1 by 2 ] do
                        mon cat:= [ rel[s][t] : u in [1..rel[s][t+1]] ];
                    end for;
                    mon cat:= tail;
                    Append( ~todo, mon ); Append( ~todo, cf*rel[s+1] ); 
                end for;
            end if;
        end while;


end procedure;


com_rel:= procedure( ~info, q, w, wp, j, m, ~rel, ~GlTab )


    // Here R (as usual) is the root datum. This function computes
    // by a recursive procedure the skew-commutator of T_{w.wp}(E_j) 
    // and T_w(E_m); the result will be in rel, GlTab will contain some
    // more relations...

    Append_and_del:= procedure( ~expr1, expr2 )

          // append expr2 to expr1, deleting if cancellation...
          mons:= {@@};
          for k in [1..#expr1-1 by 2] do
              Include( ~mons, expr1[k] );
          end for;
          for k in [1..#expr2-1 by 2] do
              include_mon( ~expr1, ~mons, expr2[k], expr2[k+1] );
          end for;
    end procedure;

    rel:= [**];
    
    R:= info[1];
    B:= info[2];
    W:= info[3];
    Wfp:= info[4];
    Coxmap:= info[5];
    posR:= info[6];
    CF:= info[7];
    
    // First we check whether the relation is already there
    
    wd1:= w; 
    wd1 cat:= wp;
    Append( ~wd1, j );

    wd2:= w;
    Append( ~wd2, m );
    
    found:= false;

    pos:= Position( GlTab[1], [wd1,wd2] );
    if pos gt 0 then
       rel:= GlTab[2][pos];
       found:= true;
    end if;

    if not found then 

       if #w gt 0 then
          $$( ~info, q, [],  wp, j, m, ~rel, ~GlTab ); 
          for i in [1..#rel-1 by 2 ] do
              for k in [1..#rel[i]-1 by 2 ] do
                  rel[i][k]:= rel[i][k]+#w;
              end for;
          end for;
          Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
          found:= true;
       end if;
    end if;

    // case Len(wp)=1 is straightforward...
    
    if not found and #wp eq 1 then
   
          // they commute
          Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], [**] );
          rel:= [**];
          found:= true;
    end if;

    if not found then
       C:= CartanMatrix(R); 
       i:= wp[#wp];
       u:= [ wp[s] : s in [1..#wp-1] ];
    
       if C[i][j] eq 0 then
        
          $$( ~info, q, [], u, j, m, ~rel, ~GlTab );
          Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
        
       elif C[i][j] eq -1 and C[j][i] eq -1 then
        
          qa:= q^( Integers()!(B[j][j]/2) );
          v:= u;
          Append( ~v, j );
          len:= Length( W, (Wfp!v) @@ Coxmap );
        
          if len gt #u then

             $$( ~info, q, [], u, j, m, ~sigma, ~GlTab ); 
             $$( ~info, q, [], u, i, m, ~rel, ~GlTab );
                                     
             rt1:= ApplyWeylElement( posR, u, posR[j] );
             rt2:= ApplyWeylElement( posR, u, posR[i] ); 
             ip:= in_p( CF, rt1, rt2+posR[m] );
                     
             collect( ~rel, ~info, q, j, u, -q^(-ip), -q^0, ~GlTab );

             for k in [2..#rel by 2] do
                 rel[k]:= rel[k]*(-qa^-1);
             end for;

             ip:= in_p( CF, posR[m], rt2 );
             collect( ~sigma, ~info, q, i, u, -q^(Integers()!(-B[j][j]/2-ip)), 
                                 -q^0, ~GlTab );

             Append_and_del( ~rel, sigma ); 

             Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );

          else
            
             v:= ExchangeElement( posR, u, j );
             bool:= #v eq 0;
             if not bool then bool:= v[1] ne u[1]; end if;
             if bool then
                
                 // the rel is -qa*T_u( E_i )
                
                 rel:= [* [ #u+1, 1 ], -qa *];
                
             else
                 $$( ~info, q, [], v, i, m, ~rel, ~GlTab );
                 Append( ~v, j );
                 rel:= MoveIt( posR, C, B, v, u, rel, q );
             end if;
            
            
             Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
          end if;
        
       elif C[i][j] eq -1 and C[j][i] eq -2 then
        
          v:= u;
          Append( ~v, j );
          len:= Length( W, (Wfp!v) @@ Coxmap );

          if len gt #u  then
            
             $$( ~info, q, [], u, j, m, ~sigma, ~GlTab ); 
             $$( ~info, q, [], u, i, m, ~omega, ~GlTab );
            
             rt1:= ApplyWeylElement( posR, u, posR[j] );
             rt2:= ApplyWeylElement( posR, u, posR[i] ); 
             ip:= in_p( CF, rt1, rt2+posR[m] );
             
             omp:= omega;                       
             collect( ~omp, ~info, q, j, u, -q^(-ip), -q^0, ~GlTab );            
             pi:= omp;
            
             for k in [2..#pi by 2] do
                 pi[k]:= pi[k]*(-q^-2);
             end for;

             ip:= in_p( CF, posR[m], rt2 );
             collect( ~sigma, ~info, q, i, u, -q^(-2-ip), -q^0, ~GlTab );
             Append_and_del( ~pi, sigma ); 
            
             collect( ~pi, ~info, q, i, u, -q^(-ip), -q^0, ~GlTab );
             collect( ~omp, ~info, q, i, u, -q^(-4-ip), -q^0, ~GlTab );
             collect( ~omega, ~info, q, i, u, -q^(-2-ip), -q^0, ~GlTab );
            
             ip:= in_p( CF, posR[m], rt1 );
             collect( ~omega, ~info, q, j, u, -q^(4-ip), -q^0, ~GlTab );
            
             // the result is (pi-omp+q^-2*omega)/(q+q^-1)
            
             rel:= omega;
             for k in [2..#rel by 2] do
                 rel[k]:= rel[k]*q^-2;
             end for;
             Append_and_del( ~rel, pi );
             for k in [2..#omp by 2 ] do
                 omp[k]:= -omp[k];
             end for;
             Append_and_del( ~rel, omp  );
            
             // divide by q+q^-1.
            
             for k in [2..#rel by 2 ] do
                 rel[k]:= rel[k]/(q+q^-1);
             end for;

             Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
              
          else   // i.e. len < #u
            
             v:= ExchangeElement( posR, u, j );
             bool:= #v eq 0;
             if not bool then bool:= v[1] ne u[1]; end if;
             if bool then
                
                // the rel is -(q^2-1)/(q+q^-1)*T_u( E_i )^2
                
                rel:= [* [ #u+1, 2 ], -(q^2-1)/(q+q^-1) *];
                Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
                
             else
                
                x:= v; 
                Append( ~x, i );
                if Length( W, (Wfp!x) @@ Coxmap ) gt #v  then

                   $$( ~info, q, [], u, i, m, ~omega, ~GlTab );

                   va:= v;
                   Append( ~va, j );
                   omega:= MoveIt( posR, C, B, u, va, omega, q );

                   // now we perform the `diffcult algorithm' on omega, i.e., 
                   // we straighten 
                   //     T_v( E_i )*omega-q^(v*i,m)*omega*T_v( E_i ), 
                   // and we do it "by hand".
                   // we collect all results in pi
                   pi:= [* *];
                    
                   rt1:= ApplyWeylElement( posR, v, posR[i] );
                   ip:= in_p( CF, posR[m], rt1 );
                    
                   for k in [1..#omega-1 by 2 ] do
                        
                       mon:= omega[k];
                       if mon[#mon-1] ne #va  then
                          // the monomial does not contain the 
                          // `evil' element i.e., T_v( E_j ); 
                          // we can do the usual thing.
                                 
                          omp:=  [* mon, -omega[k+1] *];
                          collect( ~omp, ~info, q, i, v, -q^(-ip), -q^0, ~GlTab );
                                           
                          Append_and_del( ~pi, MoveIt( posR, C, B, va, u, omp, q ) );
                            
                       else
                          // it does contain the evil element; we are very
                          // distressed; we have to do it all by hand...

                          mon1:= [ mon[t] : t in [1..#mon-2]];
                          // i.e., this is the part without the evil elt.
                          cf:= -omega[k+1];
                            
                          s:= mon[#mon];
                          // i.e., the exponent of the evil element.
                          omp:= [* mon1, cf *];
                          collect( ~omp, ~info, q, i, v, -q^(-ip+s*B[i][j]), 
                                     -q^0, ~GlTab );
                            
                          cf:= cf*q^(-ip+s*B[i][j]); // for later use...
                                     
                          for t in [1..#omp-1 by 2 ] do
                              omp[t] cat:= [ #va, s ];
                          end for;

                          omp:= MoveIt( posR, C, B, va, u, omp, q );
                          Append_and_del( ~pi, omp );             

                          cf1:= q^(2*s);
                          for t in [1..s-1] do
                              cf1:= cf1 + q^(2*s-4*t);
                          end for;
                          if s gt 1 then
                             mon1 cat:= [ #va, s-1 ];
                          end if;
                            
                          ome2:= [* mon1, -cf*cf1 *];
                          ome2:= MoveIt( posR, C, B, va, u, ome2, q );
                          for t in [1..#ome2-1 by 2 ] do
                              ome2[t] cat:= [ #u+1, 1 ];
                          end for;
                            
                          Append_and_del( ~pi, ome2 );
                       end if;    
                   end for;

                   $$( ~info, q, [], v, i, m, ~sigma, ~GlTab );
                   sigma:= MoveIt( posR, C, B, va, u, sigma, q );

                   rt1:= ApplyWeylElement( posR, u, posR[i] );
                   ip:= in_p( CF, posR[m], rt1 );
                   rel:= pi;
                   collect( ~sigma, ~info, q, i, u, -q^(-ip), -q^0, ~GlTab );
                   Append_and_del( ~rel, sigma );
                    
                   // divide by q+q^-1.
            
                   for k in [2..#rel by 2 ] do
                       rel[k]:= rel[k]/(q+q^-1);
                   end for;

                   Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel ); 
                            
                else
                    
                   x:= ExchangeElement( posR, v, i );
                   bool:= #x eq 0;
                   if not bool then bool:= x[1] ne v[1]; end if;
                   if bool then
                        
                      // the rel is -q^2*T_u( E_i )         
                      rel:= [* [ #u+1, 1 ], -q^2 *];
                        
                   else
                      $$( ~info, q, [], x, j, m, ~rel, ~GlTab );
                      Append( ~x, i ); Append( ~x, j );
                      rel:= MoveIt( posR, C, B, x, u, rel, q );
                   end if;
                    
                   Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
                end if;                    
             end if;
          end if;
       elif C[i][j] eq -2 and C[j][i] eq -1 then
        
            v:= u;
            Append( ~v, j );
            len:= Length( W, (Wfp!v) @@ Coxmap );

            if len gt #u then
            
               $$( ~info, q, [], u, j, m, ~sigma, ~GlTab);
               $$( ~info, q, [], u, i, m, ~omega, ~GlTab ); 
            
               rt1:= ApplyWeylElement( posR, u, posR[j] );
               ip:= in_p( CF, rt1, posR[m] );
               rel:= omega;                        
               collect( ~rel, ~info, q, j, u, -q^(2-ip), -q^0, ~GlTab );

               for k in [2..#rel by 2 ] do
                   rel[k]:= rel[k]*(-q^-2);
               end for;

               rt1:= ApplyWeylElement( posR, u, posR[i] );
               ip:= in_p( CF, posR[m], rt1 );
               collect( ~sigma, ~info, q, i, u, -q^(-2-ip), -q^0, ~GlTab ); 
               Append_and_del( ~rel, sigma ); 
               Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
            
            else  // i.e. len < #u

               v:= ExchangeElement( posR, u, j );
               bool:= #v eq 0;
               if not bool then bool:= v[1] ne u[1]; end if;
               if bool then
                
                  // the rel is -(q+q^-1)*T_u( E_i )
                  
                  rel:= [* [ #u+1, 1 ], -(q+q^-1) *];
                  Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
                
               else
                
                  x:= v;
                  Append( ~x, i );

                  if Length( W, (Wfp!x) @@ Coxmap ) gt #v  then

                     $$( ~info, q, [], v, i, m, ~sigma, ~GlTab );
                     $$( ~info, q, [], v, j, m, ~omega, ~GlTab ); 
                    
                     rt1:= ApplyWeylElement( posR, v, posR[i] );

                     ip:= in_p( CF, posR[m], rt1 );
                     rel:= omega;
                     collect( ~rel, ~info, q, i, v, -q^(2-ip), -q^0, ~GlTab );
            
                     for k in [2..#rel by 2 ] do
                         rel[k]:= -rel[k]*q^(-2);
                     end for;
                    
                     rt1:= ApplyWeylElement( posR, v, posR[j] );
                     ip:= in_p( CF, posR[m], rt1 );
                     collect( ~sigma, ~info, q, j, v, -q^(-2-ip), -q^0, ~GlTab );
                     Append_and_del( ~rel, sigma ); 
 
                     // finally we move `rel' to a u-expression:
                     va:= v;
                     Append( ~va, j );    

                     rel:= MoveIt( posR, C, B, va, u, rel, q );
                     Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel ); 
                    
                  else
                    
                     x:= ExchangeElement( posR, v, i );
                     bool:= #x eq 0;
                     if not bool then bool:= x[1] ne v[1]; end if;
                     if bool then
                        
                        // the rel is -q^2T_v( E_j )
                        
                        rel:= [* [ #v+1, 1 ], -q^2 *];
                        va:= v;
                        Append( ~va, j );             
                        rel:= MoveIt( posR, C, B, va, u, rel, q );
                        
                     else

                        $$( ~info, q, [], x, j, m, ~rel, ~GlTab );
                        Append( ~x, i ); Append( ~x, j );
                        rel:= MoveIt( posR, C, B, x, u, rel, q );
                     end if;
                    
                    
                     Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
                  end if; 
               end if;
            end if;
        
        
       elif C[j][i] eq -3 or C[i][j] eq -3 then    

        // Here we are in a G2-case; we fill in the commutators directly. 
        // Let the commutator be written as [ T_uT_{\beta_r}(E_a), E_b ].
        // Then the commutator is zero if the root b does not belong to the 
        // component of type G2 spanned by \beta_r, a (i.e., if b is not 
        // beta_r, or a). 
        // In other cases we use T_uT_{\beta_r}(E_a) = T_xT_{\beta_r}(E_a), 
        // where
        // x is obtained from u by deleting all elements that are not equal to
        // beta_r, a. Then we can fill in the commutation relation, and 
        // finally have
        // to change the result to a us_{\beta_r}-expression again.

            if not m in [ i, j ] then

               rel:= [* *];
               Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );
            
            else
            
               // Let a,b be two simple roots of a root system of type G2,
               // such that <a,b*>=-1, <b,a*>=-3. Then we say that we are in 
               // `case1'
               // if the longest word in the Weyl group that we use is
               // s_a s_b s_a s_b s_a s_b. We are in case2 if 
               // s_b s_a... is used.
               // First we determine in which case we are.

               x:= [ ];
               for s in [1..#u] do 
                   if u[s] in [i,j] then
                      Append( ~x, u[s] );
                   end if;
               end for;
               Append( ~x, i );

               case1:= false; 
               if C[j][i] eq -3 then
                  if x[1] eq i then case1:= true; end if;
               else
                  if x[1] eq j then case1:= true; end if;
               end if;

               if case1 then
       
                  len:= #x;
                  if len eq 1 then
                     rel:= [**];
                     Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], [**] );

                  elif len eq 2 then
                  
                     rel:= [* [ 2, 1 ], -(q+q^-1+q^-3) *];

                  elif len eq 3 then 
  
                     rel:= [* [ 3, 2 ], 1-q^2 *];

                  elif len eq 4 then

                     rel:= [* [ 3, 1 ], -1-q^2 *];

                  else // i.e., len =5

                     rel:= [* [ 5, 1 ], -q^3 *];
     
                  end if;

               else // we are in case 2...

                  len:= #x;
                  if len eq 1 then
                     rel:= [**];
                     Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], [**] );

                  elif len eq 2 then
                  
                     rel:= [* [ 2, 3 ], -(1-2*q^2+q^4)/(1+q^2+q^4) *];

                  elif len eq 3 then 
  
                     rel:= [* [ 2, 2 ], 1-q^2 *];

                  elif len eq 4 then

                     rel:= [* [ 2, 1, 4, 1 ], q^2-q^4, [ 3, 1 ], q^4+q^2-1 *]; 

                  else // i.e., len =5

                     rel:= [* [ 2, 1 ], -q^3 *];
    
                  end if;
               end if;

               // Now we need to correct the indices...
               // We have that rel is an expression relative to an isolated 
               // component of type G2. We now have to change `rel' into an
               // expression relative to `wp'. We write `wp = xv'. Then
               // `rel' is an x-expression, and hence an xv-expression.
               // We use MoveIt to move it into a wp-expression. Note that
               // the move works, because it never executes a move in 
               // the component of type G2.

               for s in [1..#u] do
                   if not u[s] in [i,j] then
                      Append( ~x, u[s] );
                   end if;
               end for;
         
               rel:= MoveIt( posR, C, B, x, wp, rel, q );
               Include( ~GlTab[1], [wd1,wd2] ); Append( ~GlTab[2], rel );

            end if;
        
       end if;
    end if;
    
end procedure;


E_Tab:= function( R, q, w0 )


    B:= Matrix( Integers(), 2*CoxeterForm( R : Basis:= "Root" ) );
    W:= CoxeterGroup( R );
    Wfp, Coxmap:= CoxeterGroup( GrpFP, W );  
    posR:= PositiveRoots( R : Basis:= "Weight" );  
    CF:= 2*CoxeterForm( R : Basis:= "Weight" );
    
    info:= [* R, B, W, Wfp, Coxmap, posR, CF *];
    
    GlTab:= [* {@@}, [**] *];
    comm:= [* *];

    rts1:= [ ];

    for i in [0..#w0-1] do
        for j in [i+1..#w0-1] do

            w:= [ w0[s] : s in [1..i] ];
            rt:= ApplyWeylElement( posR, w, posR[w0[i+1]] );
            pos:=  Position( posR, rt );
            if not pos in rts1 then
               Append( ~rts1, pos );
            end if;
            wp:= [ w0[s]: s in [i+1..j] ];
            com_rel( ~info, q, w, wp, w0[j+1], w0[i+1], ~rel, ~GlTab );
            Append( ~comm, [* [j+1,i+1], rel *] );
        end for;
    end for;

    // add the last element to rts...
    w:= [ w0[s] : s in [1..#w0-1] ];
    rt:= ApplyWeylElement( posR, w, posR[w0[#w0]] );
    pos:=  Position( posR, rt );
    if not pos in rts1 then
       Append( ~rts1, pos );
    end if;
    
    return [* rts1, comm *];
end function;


F_tab:= function( R, Etab, rts, w0, q )

    // The function returns the commutation table of the F-elements. The input
    // is formed by a root datum, and the second and first elements of the 
    // output of `E_Tab', and the parameter q.
    // For computing a commutation relation of F-elements we use the
    // automorphism f of U_q(g) given by f(F_{\alpha})=E_{\alpha}, 
    // f(K_{\alpha}) = K_{\alpha}^-1, f(E_{\alpha}) = F_{\alpha}. Then we have
    // the following formula:
    //
    //   f(T_w(E_{\alpha})) = 
    //    ( \prod_{\gamma\in\Delta} (-q_{\gamma})^{-m_{\gamma}})*
    //                                      T_w(F_{\alpha})
    //
    // where w(\alpha) - \alpha = \sum_{\gamma\in\Delta} m_{\gamma}\gamma.
    // Using this it is straightforward to calculate the commutation table of 
    // the F-elements.

    B:= Matrix( Integers(), 2*CoxeterForm( R : Basis:= "Root" ) );
    posR:= PositiveRoots( R : Basis:= "Root" );  
    
    cfs:= [ ];
    for i in [1..#w0] do

        // Set u = w0{[1..i-1]}, then rts[i] is the image of the simple
        // root a with index w0[i] under u. We compute the coefficient 
        // `c' such that f(T_u(E_a)) = c*T_u(F_a). 
 
        a:= Eltseq( posR[ rts[i] ]-posR[ w0[i] ] );
        c:= q^0;

        for j in [1..#a] do
            c:= c*( (-q^(Integers()!(B[j][j]/2) ))^(Integers()!(-a[j])) );
        end for;
        Append( ~cfs, c );
    end for;

    ftab:= [* *];
    for i in [1..#Etab] do
        
        sigma:= Etab[i][2];
        
        cf:= 1/(cfs[Etab[i][1][1]]*cfs[Etab[i][1][2]]);
        
        // we calculate cf*f(sigma)
        for j in [1..#sigma-1 by 2 ] do
            c:= q^0;
            for k in [1..#sigma[j]-1 by 2 ] do
                c:= c*( cfs[sigma[j][k]]^sigma[j][k+1] );
            end for;
            sigma[j+1]:= sigma[j+1]*c*cf;
        end for;
        Append( ~ftab, [* Etab[i][1], sigma *] );
    end for;
    return ftab;
end function;



//
//  Part three
//
//  The computation of the commutation relations between the E-elements and
//  the F-elements.    
//

FE_table:= function( R, Etab, Ftab, rts, q )
    
    // here the rts are the indices of the positive roots in convex order, 
    // (i.e., if rts[4] = k, then the fourth positive root in the convex order
    // is the k-th root in the normal list of positive roots), 
    // the Etab is the E-mult tab,
    // indexed by the roots in rts. Ftab is the F-mult tab.
    // We use the following indexing of the elements: If i <= s, then 
    // i is the index of an F, if s+1 <= i <= s+rank, then i is the index
    // of a K, if i >= s+rank+1, then i is the index of an E; where 
    // s is the number of positive roots.
    
    
    collect:= procedure( ~expr, ~info, ~Eheads, ~Erels, ~Fheads, ~Frels, 
                         ~FEheads, ~FErels, Ecollect, Fcollect, q )
        
        // collect expr, using known relations and those in Etab.
        // If `Ecollect' is false then we do not collect E's and
        // similarly for Fcollect.
        
        comm_rule:= function( rel, q, j, i, m, n, r )
        
           // commutation rule for x_j^mx_i^n, where x_jx_i=q^rx_jx_i+rel
        
           rule:= [* [ i, n, j, m], q^(n*m*r) *];
           for l in [0..n-1] do
               for k in [0..m-1] do
                   cf:= q^((l*m+k)*r);
                   start:= [ ];
                   if l ne 0 then
                      Append( ~start, i ); Append( ~start, l );
                   end if;
                   if m-1-k ne 0 then
                      Append( ~start, j ); Append( ~start, m-1-k );
                   end if;
                   tail:= [];
                   if k ne 0 then
                      Append( ~tail, j ); Append( ~tail, k );
                   end if;
                   if n-1-l ne 0 then
                      Append( ~tail, i ); Append( ~tail, n-1-l );
                   end if;
                
                   for u in [1..#rel-1 by 2 ] do
                       mn:= start;
                       mn cat:= rel[u];
                       mn cat:= tail;
                       Append( ~rule, mn ); Append( ~rule, cf*rel[u+1] );
                   end for;
               end for;
           end for;
           return rule;
        end function;

        s:= info[1]; 
        rank:= info[2];
        posR:= info[3];
        CF:= info[4];
    
        todo:= expr;
        expr:= [* *];
        mons:= {@@};
        while #todo gt 0 do

            m:= todo[1];
            cf:= todo[2];

            k:= 1; found:= false;
            while k lt #m-2 and not found do
                if m[k] gt m[k+2] then
                    if Ecollect or m[k+2] le s+rank then
                        // i.e., if it is 2 E's and Ecollect is false then we
                        // do not end up here, and so the search will continue.
                        // This means that for those cases we do nothing.
                        
                        if Fcollect or m[k] gt s then
                            // again, if it is two F's and Fcollect is false, 
                            // then we do not end up here; so we  
                            // do nothing in that case either.

                            found:= true;
                            break;
                        else
                            k:= k+2;
                        end if;
                    else
                        k:= k+2;
                    end if;
                elif m[k] eq m[k+2] then

                    // add the exponents...

                    m[k+1]:= m[k+1]+m[k+3];
                    Remove( ~m, k+2 );
                    Remove( ~m, k+2 ); 
                    if m[k+1] eq 0 then
                        Remove( ~m, k ); Remove( ~m, k );
                        k:= k-2;
                    end if;
                    k:= k+2;
                else
                    k:= k+2;
                end if;
            end while;
            
            if not found then

                // Append the monomial to `res'.

                include_mon( ~expr, ~mons, m, cf );
                Remove( ~todo, 1 );
                Remove( ~todo, 1 );

            else
                
                k1:= m[k]; k2:= m[k+2];

                // we know k1 > k2...
                
                if k1 gt s+rank then
                    
                    // i.e., k1 is an E
                    
                    if k2 gt s+rank then
                        
                        // i.e., k2 is also an E, commutation from Etab
                        
                        pos:= Position( Eheads, [ k1-s-rank, k2-s-rank] );
                        r:= in_p( CF, posR[ rts[k1-s-rank] ], posR[ rts[k2-s-rank] ] );

                        rel:= comm_rule( Erels[pos], q, m[k]-s-rank, 
                                      m[k+2]-s-rank, 
                                      m[k+1], m[k+3], -r );
                        start:= [ m[y] : y in [1..k-1] ];
                        tail:= [ m[y] : y in [k+4..#m] ];

                        // We apply the commutation rule; the first monomial 
                        // we get will go to the first position of `todo'.
                        
                        for i in [1..#rel-1 by 2 ] do
                            mn:= start;
                            m1:= rel[i];
                            for j in [1..#m1-1 by 2] do
                                m1[j]:= m1[j]+s+rank;
                            end for;
                            mn cat:= m1; mn cat:= tail;
                            if i eq 1 then
                                todo[1]:= mn;
                                todo[2]:= cf*rel[i+1];
                            else
                                Append( ~todo, mn ); Append( ~todo, cf*rel[i+1] );
                            end if;

                        end for;
                        
                    elif k2 gt s then
                        
                        // i.e., k2 is a K, commutation easy
                        
                        mn:= [ m[y] : y in [1..k-1] ];
                        Append( ~mn, m[k+2] ); Append( ~mn, m[k+3] );
                        Append( ~mn, m[k] ); Append( ~mn, m[k+1] );
                        mn cat:= [ m[y] : y in [k+4..#m] ];
                        todo[1]:= mn;
                        r:= in_p( CF, posR[ rts[k1-s-rank] ], posR[ k2-s ] );
                        todo[2]:= cf*q^( -m[k+1]*m[k+3]*r );

                    else
                        // k2 is an F, commutation from FEtab

                        pos:= Position( FEheads, [k1,k2] );
                        rel:= comm_rule( FErels[pos], q, m[k], m[k+2], 
                                      m[k+1], m[k+3], 0 );

                        start:= [ m[y] : y in [1..k-1] ];
                        tail:= [ m[y] : y in [k+4..#m] ];
                        
                        for i in [1..#rel-1 by 2] do
                            mn:= start;
                            mn cat:= rel[i]; mn cat:= tail;
                            if i eq 1 then
                                todo[1]:= mn; 
                            else
                                Append( ~todo, mn ); Append( ~todo, cf*rel[i+1] );
                            end if;
                        
                        end for;

                    end if;
                elif k1 gt s then
                    
                    // i.e., k1 is a K, 
                    
                    if k2 gt s then
                        
                        // i.e., k2 is also a K; they commute
                    
                        mn:= [ m[y] : y in [1..k-1] ];
                        Append( ~mn, m[k+2] ); Append( ~mn, m[k+3] );
                        Append( ~mn, m[k] ); Append( ~mn, m[k+1] );
                        mn cat:=  [ m[y] : y in [k+4..#m] ];
                        todo[1]:= mn;
                    else
                        
                        // i.e., k2 is an F, commutation easy 
                        
                        mn:= [ m[y] : y in [1..k-1] ];
                        Append( ~mn, m[k+2] ); Append( ~mn, m[k+3] );
                        Append( ~mn, m[k] ); Append( ~mn, m[k+1] );
                        mn cat:=  [ m[y] : y in [k+4..#m] ];
                        todo[1]:= mn;
                        r:= in_p( CF, posR[ k1-s ], posR[ rts[k2] ] );
                        todo[2]:= cf*q^( -m[k+1]*m[k+3]*r );
                    end if;
                else
                    // i.e., k1, k2 are both F's. 
                    // commutation from Ftab
                    
                    pos:= Position( Fheads, [ k1, k2 ] );
                    r:= in_p( CF, posR[ rts[k1] ], posR[ rts[k2] ] );
                    rel:= comm_rule( Frels[pos], q, m[k], m[k+2], 
                                  m[k+1], m[k+3], -r );
                    start:= [ m[y] : y in [1..k-1] ];
                    tail:= [ m[y] : y in [k+4..#m] ];

                    for i in [1..#rel-1 by 2 ] do
                        mn:= start;
                        mn cat:= rel[i]; mn cat:= tail;
                        if i eq 1 then
                            todo[1]:= mn; todo[2]:= cf*rel[i+1];
                        else
                            Append( ~todo, mn ); Append( ~todo, cf*rel[i+1] );
                        end if;
                        
                    end for;
                
                end if;
                
            end if;
        end while;

    end procedure;
        
    posR:= PositiveRoots( R : Basis:= "Root" );
    s:= #posR;
    rank:= Rank( R );

    // We assume that the positive roots are sorted according to level; we loop 
    // through this list.
    
    CF:= Matrix( Integers(), 2*CoxeterForm( R : Basis:= "Root" ) );
    info:= [* s, rank, posR, CF *]; 

    Fheads:= {@@};
    Frels:= [ ];
    Eheads:= {@@};
    Erels:= [ ];
    for i in [1..#Etab] do
        Include( ~Fheads, Ftab[i][1] );
        Append( ~Frels, Ftab[i][2] );
        Include( ~Eheads, Etab[i][1] );
        Append( ~Erels, Etab[i][2] );
    end for;
    
    FEtab:= [* *];
    FEheads:= {@@};
    FErels:= [ ];
    
    for i in [1..rank] do
        for j in [1..s] do

            // We calculate the commutation rule of E_j with F_i. If 
            // j <= rank, then this relation is one of the defining relations 
            // of the qea. Otherwise
            // we use the relations in the multiplication table to write E_j
            // as a polynomial in E_k, where all E_k belong to roots of lower 
            // level.
            // Here E_j corresponds to the j-th element of posR, and 
            // F_i corresponds to the i-th element of the simple roots.

            if j le rank then
                // we know the commrel...
                
                if j ne i then
                    // they commute...
                    head:= [ s+rank+Position(rts,j), Position( rts, i ) ];  
                    Append( ~FEtab, [* head, [**] *] );
                    Append( ~FErels, [**] );
                    Include( ~FEheads, head );                    
                else

                    qa:=  q^( Integers()!(CF[i][i]/2) );
                    cf:= 1/(qa-qa^-1);
                    head:= [ s+rank+Position(rts,j), Position( rts, i ) ];
                    rel:= [* [s+i,1], cf, [ s+i, -1 ], -cf *];
                    Append( ~FEtab, [* head, rel *] );
                    Append( ~FErels, rel );
                    Include( ~FEheads, head ); 
                end if;
            else
                
                // we calculate the com rel of E_j with F_i
                // We write E_j as a polynomial in the E_k of lower level. 

                for k in [1..rank] do

                    // First we find a simple root r such that posR[j]-r 
                    // is also a root

                    k1:= Position( posR, posR[j] - posR[k] );
                    if k1 gt 0 then
                        k1:= Position( rts, k1 );
                        k2:= Position( rts, k );

                        if k1 gt k2 then
                           pair:= [ k1, k2 ];
                        else
                           pair:= [ k2, k1 ];
                        end if;

                        pos:= Position( Eheads, pair );
                        rel:= Erels[pos];

                        // we establish whether E_j is in there
                        Ej:= [ Position( rts, j ), 1 ];
                        pos:= 0;
                        for l in [1..#rel-1 by 2] do
                            if rel[l] eq Ej then
                               pos:= l;
                               break l;
                            end if;
                        end for; 
                        if pos gt 0 then break k; end if;
                    end if;
                end for;

                // We throw away the E_j in `rel'.
                cf:= rel[ pos+1];
                Remove( ~rel, pos ); Remove( ~rel, pos );

                // Get the indexing and the coefficients right:
                for k in [1..#rel-1 by 2] do
                    mon:= rel[k];
                    for l in [1..#mon-1 by 2] do
                        mon[l]:= mon[l] + s+rank;
                    end for;
                    rel[k]:= mon;
                    rel[k+1]:= -(1/cf)*rel[k+1];
                end for;
                
                // Now we add the AB-q^*BA bit:
                    
                Append( ~rel, [ pair[1]+s+rank, 1, pair[2]+s+rank, 1 ] );
                Append( ~rel, 1/cf );
                
                qa:=  q^( -in_p( CF, posR[ rts[k1] ], posR[ rts[k2] ] ) );
                Append( ~rel, [ pair[2]+s+rank, 1, pair[1]+s+rank, 1 ] );
                Append( ~rel, -qa/cf );
        
                // now `rel' is the `definition' of E_j (in terms of pbw
                // elts of lower level). We commute. `expr' will be 
                // the commutator rel*F_i-F_i*rel.  

                expr:= [* *];
                pos:= Position( rts, i ); // this is the index of F_i
                for k in [1..#rel-1 by 2] do
                    mon:= rel[k];
                    mon cat:= [ pos, 1 ];
                    Append( ~expr, mon ); Append( ~expr, rel[k+1] );
                    mon:= [ pos, 1 ];
                    mon cat:= rel[k];
                    Append( ~expr, mon ); Append( ~expr, -rel[k+1] );
                end for;

                // First we collect everything to terms of the form FKE,
                // where, maybe, the F-part and the E-part are uncollected.
                // We do this because a collection of two E-s my result 
                // in an E of higher level. This in turn may lead to a 
                // commutation relation for an F and an E being needed which 
                // is not there (yet).

                collect( ~expr, ~info, ~Eheads, ~Erels, ~Fheads, ~Frels, 
                         ~FEheads, ~FErels, false, false, q );
                // this comes back without the F's; only in the 
                // E-part there may be some collection needed....

                collect( ~expr, ~info, ~Eheads, ~Erels, ~Fheads, ~Frels, 
                         ~FEheads, ~FErels, true, true, q );

                head:= [ s+rank+Position( rts, j ), pos ];
                Append( ~FEtab, [* head, expr *] );
                Append( ~FErels, expr );
                Include( ~FEheads, head ); 

            end if;
        end for;
    end for;
    
    // now we know all comm rels of E_j , F_i for 1<=i<=rank;
    // now we do the rest. (Basically same loop with E,F interchanged).

    for i in [1..s] do
        
        if i gt rank then
        
            // We write F_i as a polynomial in F_k of lower rank.
            // Now F_i corresponds to posR[i]...
            
            for k in [1..rank] do
                // We find a simple root r such that posR[i]-r is also a root.

                k1:= Position( posR, posR[i] - posR[k] );
                if k1 gt 0 then
                   k1:= Position( rts, k1 );
                   k2:= Position( rts, k );

                   if k1 gt k2 then
                      pair:= [ k1, k2 ];
                   else
                      pair:= [ k2, k1 ];
                   end if;

                   pos:= Position( Fheads, pair );
                   rel:= Frels[pos];

                   // we establish whether F_i is in there
                   Fi:= [ Position( rts, i ), 1 ];
                   pos:= 0;
                   for l in [1..#rel-1 by 2] do
                       if rel[l] eq Fi then
                          pos:= l;
                          break l;
                       end if;
                   end for; 
                   if pos gt 0 then break k; end if;
                end if;
            end for;
                
            cf:= rel[ pos+1 ];
            Remove( ~rel, pos ); Remove( ~rel, pos );
            
            for k in [2..#rel by 2 ] do
                rel[k]:= -(1/cf)*rel[k];
            end for;
            
            p1:= pair[1]; p2:= pair[2];
            
            Append( ~rel, [ pair[1], 1, pair[2], 1 ] );
            Append( ~rel, 1/cf );
            
            qa:= q^( -in_p( CF, posR[ rts[k1] ], posR[ rts[k2] ] ) );
            Append( ~rel, [ pair[2], 1, pair[1], 1 ] );
            Append( ~rel, -qa/cf );
            
            // now `rel' is the `definition' of F_i (in terms of pbw
            // elts of lower level). We commute with all E_j.
            
            for j in [1..s] do
                
                expr:= [* *];
                pos:= Position( rts, j )+s+rank; // this is the index of E_j.
                for k in [1..#rel-1 by 2 ] do
                    mon:= rel[k];
                    mon cat:= [ pos, 1 ];
                    Append( ~expr, mon ); Append( ~expr, -rel[k+1] );
                    mon:= [ pos, 1 ];
                    mon cat:= rel[k];
                    Append( ~expr, mon ); Append( ~expr, rel[k+1] );
                end for;
                
                // As above, we end ifrst collect without collecting F's or E's.
                // (Because this may result in an F, or an E of higher level.)
                collect( ~expr, ~info, ~Eheads, ~Erels, ~Fheads, ~Frels, 
                         ~FEheads, ~FErels, false, false, q );

                collect( ~expr, ~info, ~Eheads, ~Erels, ~Fheads, ~Frels, 
                         ~FEheads, ~FErels, true, true, q );

                head:= [ pos, Position( rts, i ) ];
                Append( ~FEtab, [* head, expr *] );
                Append( ~FErels, expr );
                Include( ~FEheads, head );       
          
            end for;
        end if;
        
    end for;
    
    return FEtab;
end function;


// part four: putting it all together...

//
// Some functions for dealing with "generalised binomials" as they 
// appear in the basis of the Lusztig Z-form of the quea. These functions
// rewrite elements as linear combinations of basis elements.
// 
// A binomial as the one below is expressed as [ delta, s ], where
// delta = 0,1 according to whether we multiply by K or not.
// An expression is a linear combination of such things.
//
Multiply_Bin_Expr:= function( s, expr, q )

     // expresses
     //
     //    / K \ 
     //    |   | * expr
     //    \ s / 
     //
     // as a linear combination of such things...
     // The algorithm is simply based on the definition of the binomial,
     // and om some relations found in Lusztig, J. Amer math Soc. 1990
     // 278.

     for i in [1..s] do
         // multiply expr by q^(-i+1)K-q^(i-1)K^-1:
         
         newexp:= [* *];
         mons:= {@@};
         for j in [1..#expr-1 by 2 ] do
             m:= expr[j];
             if m[1] eq 0 then
                n:= m;
                n[1]:= 1;
                include_mon( ~newexp, ~mons, n, expr[j+1]*q^(-i+1) );
             else
                n:= m;
                n[2]:= n[2]+1;
                include_mon( ~newexp, ~mons, n,
                         expr[j+1]*q^(-i+1)*q^m[2]*(q^n[2]-q^-n[2]) );
                n:= m;
                n[1]:= 0;
                include_mon( ~newexp, ~mons, n, expr[j+1]*q^(-i+1)*q^(2*m[2]) );
             end if;
             
             if m[1] eq 0 then
                n:= m;
                n[2]:= n[2]+1;
                include_mon( ~newexp, ~mons, n,
                    expr[j+1]*q^(i-1)*q^-m[2]*(q^n[2]-q^-n[2]) );
                n:=  m;
                n[1]:= 1;
                include_mon( ~newexp, ~mons, n,
                    -expr[j+1]*q^(i-1)*q^(-2*m[2]) );
             else   
                n:= m;
                n[1]:= 0;
                include_mon( ~newexp, ~mons, n, -expr[j+1]*q^(i-1) );
             end if;
         end for;
         expr:= newexp;
     end for;

     cf:= (q-q^-1)^s*GaussianFactorial( s, q );
     for i in [2..#expr by 2 ] do
         expr[i]:= expr[i]/cf;
     end for;
     return expr;

end function;    

Multiply_K_Expr:= function( exx, q )

     // multiply exx by K...

     expr:= [* *];
     mons:= {@@};
     for i in [1..#exx-1 by 2] do
         m:= exx[i];
         if m[1] eq 0 then
            m[1]:= 1;
            include_mon( ~expr, ~mons, m, exx[i+1] );
         else
            m[2]:= m[2]+1;
            include_mon( ~expr, ~mons, m, exx[i+1]*q^(m[2]-1)*(q^m[2]-q^-m[2]) );
            m:= exx[i];
            m[1]:= 0;
            include_mon( ~expr, ~mons, m, exx[i+1]*q^(2*m[2]) );
         end if;
     end for;

     return expr;
end function;

Multiply_Exp_Exp:= function( ex1, ex2, q )

      // multiply the two expressions ex1, ex2.

     res:= [* *];
     mons:= {@@};
     for i in [1..#ex1-1 by 2] do
         expr:= ex2;
         m:= ex1[i];
         if m[1] ne 0 then
            expr:= Multiply_K_Expr( expr, q );
         end if;
         expr:= Multiply_Bin_Expr( m[2], expr, q );
         for j in [1..#expr-1 by 2] do
            include_mon( ~res, ~mons, expr[j], expr[j+1]*ex1[i+1] );
         end for;
     end for;

     return res;
end function;


normalise_rel:= function( R, conv_r, rel, q )

     // writes the relation rel using the basis of Lusztig's
     // Z-form of the quea.

     posR:= PositiveRoots( R : Basis:= "Root" );
     s:= #posR;
     rank:= Rank( R );
     B:= Matrix( Integers(), 2*CoxeterForm( R : Basis:= "Root" ) );

     res:= [* *];
     mons:= {@@};
     for i in [1..#rel-1 by 2 ] do
         m:= rel[i];
         k:= 1;

         // f will contain the F-part of the monomial, ks the K-part 
         // and e the E-part.
         f:= [ ];
         still_looping:= k le #m;
         if still_looping then still_looping:= m[k] le s; end if;
         while still_looping do 
            Append( ~f, m[k] );
            Append( ~f, m[k+1] );
            k:= k+2;
            still_looping:= k le #m;
            if still_looping then still_looping:= m[k] le s; end if;
         end while;
         ks:= [ ];
         still_looping:= k le #m;
         if still_looping then still_looping:= m[k] le s+rank; end if;
         while still_looping do 
            Append( ~ks, m[k] );
            Append( ~ks, m[k+1] );
            k:= k+2;
            still_looping:= k le #m;
            if still_looping then still_looping:= m[k] le s+rank; end if;
         end while;
         e:= [ ];
         while k le #m do
            Append( ~e, m[k] );
            Append( ~e, m[k+1] );
            k:= k+2;
         end while;

         // in the end we multiply by a constant, because the f's and e's
         // are divided powers now...
         c:= 1;
         for k in [1..#f-1 by 2 ] do
             qp:= q^( Integers()!(
                  in_p( B, posR[conv_r[f[k]]], posR[conv_r[f[k]]] )/2) );
             c:= c*GaussianFactorial( f[k+1], qp );
         end for;
         for k in [1..#e-1 by 2 ] do
             qp:= q^( Integers()!(in_p( B, posR[conv_r[e[k]-s-rank]], 
                                    posR[conv_r[e[k]-s-rank]] )/2) );
             c:= c*GaussianFactorial( e[k+1], qp );
         end for;

         k_piece:= [* [ ], q^0 *];
         for j in [1..#ks-1 by 2] do

             qp:= q^( Integers()!(B[ks[j]-s][ks[j]-s]/2) );
             if ks[j+1] gt 0 then
                elm:= [* [1,0], qp^0 *];
                ee:= elm;
                for k in [2..ks[j+1]] do
                    ee:= Multiply_Exp_Exp( ee, elm, qp );
                end for;
             else
                elm:= [* [1,0], qp^0, [0,1], qp^-1-qp *];
                ee:= elm;
                for k in [2..-ks[j+1]] do
                    ee:= Multiply_Exp_Exp( ee, elm, qp );
                end for;
             end if;

             new_piece:= [* *];
             for k in [1..#ee-1 by 2 ] do
                 if ee[k] ne [ 0, 0 ] then 
                    for l in [1..#k_piece-1 by 2 ] do 
                        mon:= k_piece[l];
                        Append( ~mon, ks[j] );
                        if ee[k][1] gt 0 then
                           Append( ~mon, -ee[k][2] );
                        else
                           Append( ~mon, ee[k][2] );
                        end if;
                        Append( ~new_piece, mon );
                        Append( ~new_piece, ee[k+1]*k_piece[l+1] );
                    end for;
                 else
                    // we multiply by a scalar, effectively
                    for l in [1..#k_piece-1 by 2 ] do 
                        mon:= k_piece[l];
                        Append( ~new_piece, mon );
                        Append( ~new_piece, ee[k+1]*k_piece[l+1] );
                    end for; 
                 end if;
             end for;
             k_piece:= new_piece;
         end for;

         for j in [1..#k_piece-1 by 2] do
             m:= f;
             m cat:= k_piece[j];
             m cat:= e;
             include_mon( ~res, ~mons, m, c*k_piece[j+1]*rel[i+1] );
         end for;

     end for;

     return res;
    
end function;
    

QEA_Data:= function( R, q, w0 )

  
     e:= E_Tab( R, q, w0 );
     f:= F_tab( R, e[2], e[1], w0, q );
     fe:= FE_table( R, e[2], f, e[1], q );

     s:= #PositiveRoots( R );
     rank:= Rank( R );

     tab:= [ ];
     for i in [1..s] do
         tab[i]:= [ ];
         tab[s+rank+i]:= [ ];
     end for;

     // fill in f-elements

     for r in f do
         rel:= normalise_rel( R, e[1], r[2], q );
         tab[ r[1][1] ][ r[1][2] ]:= rel;
     end for;

     // e-elements:

     for r in e[2] do
         rel:= [**];
         for i in [1..#r[2]-1 by 2 ] do
             m:= [];
             for j in [1..#r[2][i]-1 by 2 ] do
                 Append( ~m, r[2][i][j]+s+rank );
                 Append( ~m, r[2][i][j+1] );
             end for;
             Append( ~rel, m );
             Append( ~rel, r[2][i+1] );
         end for; 
         rel:= normalise_rel( R, e[1], rel, q );
         tab[ r[1][1]+s+rank ][ r[1][2]+s+rank ]:= rel;
     end for;

     // fe-elements:

     for r in fe do
         rel:= normalise_rel( R, e[1], r[2], q );
         tab[ r[1][1] ][ r[1][2] ]:= rel;
     end for;

     return [* R, q, tab, e[1], 
         Matrix( Integers(), 2*CoxeterForm( R : Basis:= "Root" ) ),
         PositiveRoots( R : Basis:= "Root" ), 
         PositiveRoots( R : Basis:= "Weight" ) *];

end function;

declare attributes AlgQUE: RootDatum, NormalizedCoxeterForm;

intrinsic QuantizedUEA( R::RootDtm : w0:= [ ] ) -> AlgQUE
{Returns the quantized enveloping algebra corresponding to the
   root datum R, with the indeterminate of a function field
   over the rationals as parameter}
    
      if w0 eq [ ] then
         w0:= LongestWeylWord( R );
      else
         // check whether w0 really is a reduced word of longest length...
         W:= CoxeterGroup( GrpFP, CoxeterGroup( R ) );       
         len:= #( W!w0 );
         require len eq #w0 : "The expression for the longest element in the Weyl group is not reduced.";
         require len eq #PositiveRoots( R ) : "The reduced expression given is not an expression for the longest element in the Weyl group."; 
      
         R`LongestWeylWord:= w0;
      end if;

      F := RationalFunctionField( Rationals() ); q := F.1;
      d:= QEA_Data( R, q, w0 );
      d[6] := ChangeUniverse(d[6], RSpace(Integers(), Dimension(Universe(d[6]))));
      U:= InternalQUEA(#PositiveRoots(R),Rank(R),q,
                                       [*d[3],d[4],d[5],d[6],d[7]*]);
      U`RootDatum:= R;
      U`NormalizedCoxeterForm:= d[5];
      U`RootData:= R`Name;
      return U;

end intrinsic;

intrinsic RootDatum( U::AlgQUE ) -> RootDtm
{Returns the root datum corresponding to U.}

      return U`RootDatum; 

end intrinsic;

intrinsic PositiveRootsPerm( U::AlgQUE ) -> SeqEnum
{Returns the order in which the positive roots appear if they are listed according to the weights of the generators}

      return U`Perm;

end intrinsic;

 

