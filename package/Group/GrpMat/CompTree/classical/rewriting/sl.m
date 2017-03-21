freeze;

import "bbclassical.m":B, Evaluate2, BBType, 
  BBField, BBStandardGenerators, BBDimension;
import "subgroups.m": SLPToSiegelTrans;
import "elements.m": SiegelTransformToSLP;

ConjugateXByDUntilZ := function( G, x, d, z : stop )
    
    count := 0;
    
    if stop eq true then
        stop := #BBField( G );
    end if;
        
    while x ne z do
        if count eq stop then
            return false;
        end if;
        count := count+1;
        x := d^-1*x*d;
    end while;
    
    return count;
end function;
    
    
Xin := function( G )
    
    if assigned G`Xin then
        return G`Xin;
    end if; 
    
    gens := BBStandardGenerators( G );
    q := #BBField( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4];
    dim := BBDimension( G );  
    
    xin := [ (T^(S,X))^(-1) ]; xinslp := [ (B.6^(B.5,B.2^-1))^-1 ];
    p := X^-2*S*X; progp := B.2^2*B.5*B.2^-1;
    
    for i in [1..dim-3] do
        Append( ~xin, (xin[i]^p)^(-1) );
        Append( ~xinslp, (xinslp[i]^progp)^(-1) );
    end for;
    
    G`Xin := < xin, xinslp >;
    
    return < xin, xinslp >;
end function;

EntriesOfRootElementBBSL := function( G, x : GetLastEntry := true )
    
    gens := BBStandardGenerators( G );
    q := #BBField( G ); _, _, d := IsPrimePower( q );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    xin := Xin( G );
    T1 := T^(S*X);
    
    dim := BBDimension( G );
    vec := [];
    zz := PrimitiveElement( GF( q ));
    
    for i in [1..dim-2] do
        m := ( x, xin[1][i] ); 
        if m ne One( G ) then
            k := ConjugateXByDUntilZ( G, T1, D^-1, m ); 
            if Category( k ) eq BoolElt then return false, false; end if;
            Append( ~vec, zz^k );
        else
            Append( ~vec, GF( q )!0 );
        end if;
    end for;
    
    if not GetLastEntry then
        return vec;
    end if;
    
    m := ( xin[1][dim-2], (x^(S^X^2)));

    if m eq One( G ) then
        Append( ~vec, GF( q )!0 );
    else
       k := ConjugateXByDUntilZ( G, T1, D^-1, m );
       if Category( k ) eq BoolElt then return false, false; end if;
        Append( ~vec, zz^k );
    end if;    
        
    return vec;
end function;


EntriesOfTransposeRootElement := function( G, x )
   
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    
    r := (T^(-1))^(X*S); 
    s := X^-2*S*X; 
    // r = X(n,2) s = (1,2,...,n-1), W -> (2,3,...,n) (mod sign)
    vec := []; 
    
    q := #BBField( G );
    zz := PrimitiveElement( GF( q ));
    dim := BBDimension( G );
    z0 := (T^-1)^X; // q = X(n,1) 
    
    for i in [1..dim-2] do
        z := z0;
        m := ( r, x ); // 
        k := 0;
        if m ne One( G ) then
            while m ne z do
                if k eq q-2 then
                    return false;
                end if;
                k := k+1;
                z := D*z*D^-1;
            end while;
            Append( ~vec, zz^-k );
        else
            Append( ~vec, GF( q )!0 );
        end if;
        r := (r^s)^-1;
    end for;
    
    return vec;
end function;
    
WriteSimpleRootElementAsSLPBBSL := function( G, x, pos )
    
    if x eq One( G ) then
        return 0;
    end if;
    
    F := BBField( G ); q := #F;
    _, _, d := IsPrimePower( q );
    gens := BBStandardGenerators( G );
    
    _, P := SLPToSiegelTrans( G : EvaluateSLPs := true );
    c := (pos-2)*d+1;
    
    D := gens[4]^(gens[2]^(pos-1));
    
    count := ConjugateXByDUntilZ( G, P[c], D, x );
    
    if Category( count ) eq BoolElt then
        return 0;
    else
        return PrimitiveElement( F )^count;
    end if;
end function;

IsZeroEntry := function( G, g )
  
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    
    n := BBDimension( G );
    Q := T^X;
    
    X1 := Q;
    Z := X^-2*S*X;
    Q1 := Q^(Q^g);
    
    for k in [1..n-1] do
        if ( Q1, X1 ) ne One( G ) then
            return false;
        end if;
        X1 := X1^Z;
    end for;
    
    return true;
end function;
    
    
IsInT := function( G, g )
        
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    
    n := BBDimension( G );
    Q := T^S;
    X1 := Q;
    P := X^-1*S;
    
    for i in [2..n] do
        if ( Q^g, X1 ) ne One( G ) then
            return false;
        end if;
        X1 := X1^P;
    end for;
    
    return true;
end function;

    
IsInTTranspose := function( G, g )
    
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
        
    n := BBDimension( G );
    Q := T;
    X1 := Q;
    P := X^-1*S;
    
    for i in [2..n] do
        if ( Q^g, X1 ) ne One( G ) then
            return false;
        end if;
        X1 := X1^P;
    end for;
    
    return true;
end function;        


ClearTopRightEntry := function( G, g )
    
    dim := BBDimension( G );
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    
    q := #BBField( G );
    
    if IsZeroEntry( G, g ) then
        return One( B ), One( G );
    end if;
    
    if IsZeroEntry( G, g*X ) then
        return  B.2^-1, X;
    end if;
    
    prog1 := B.6^(B.5*B.2^-1);
    X1 := T^(S*X);
    
    k := 1;
    repeat
        if k eq q then
            return false, false;
        end if;
        X1 := D*X1*D^-1;
        k := k+1;
    until IsZeroEntry( G, g*X1 );
    
    prog1 := prog1^(B.4^(-k+1)); 
    return prog1, X1;
end function;
    
ClearFirstRowSLBBDim2 := function( G, g )
    
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    F := BBField( G );
    q := #BBField( G );
    z := PrimitiveElement( BBField( G ));
    
    if Characteristic( F ) eq 2 then
        ns := 1;
    else
        ex := exists( ns ){ i : i in [1..q-1] | 
                      z^0 ne -z^(-2*i) and 
                      IsOdd( Log( z, z^0 + z^(-2*i) ))};        
        assert ex;
        ns := Integers()!ns;
    end if;
    
    if IsZeroEntry( G, g  ) then
        return One( B ), One( B ), One( G ), One( G );
    elif IsZeroEntry( G, g*S ) then
        return One( B ), B.5, One( G ), S;
    end if;
    
    X1 := T; X2 := T*T^(D^ns);
    k := 1;
    
    repeat
        if ( IsOdd( q ) and k ge q/2 ) or ( IsEven( q ) and k ge q ) then 
            return false, false, false, false; 
        end if;
          
        
        X1 := D*X1*D^-1; X2 := D*X2*D^-1;
        k := k+1;
        
        if IsZeroEntry( G, g*X1 ) then
            return One( B ), B.6^(B.4^(-k+1)), One( G ), X1;
        end if;
        
        if IsZeroEntry( G, g*X2 ) then
            return One( B ), (B.6*B.6^(B.4^ns))^(B.4^(-k+1)), One( G ), X2;
        end if;
        
    until false;
end function;

    
ClearFirstColumnSLBBDim2 := function( G, g )
    
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    F := BBField( G );
    q := #F; z := PrimitiveElement( F );
      
    if Characteristic( F ) eq 2 then
        ns := 1;
    else    
        ex := exists( ns ){ i : i in [1..q-1] | 
                      z^0 ne -z^(-2*i) and 
                      IsOdd( Log( z, z^0 + z^(-2*i) ))};        
        assert ex;
        ns := Integers()!ns;
    end if;
        
    if IsZeroEntry( G, g^S ) then
        return One( B ), One( B ), One( G ), One( G );
    end if;
    
    X1 := T^X^-1; X2 := (T*T^(D^ns))^(X^-1);
        
    k := 1;
    repeat
        if ( IsOdd( q ) and k ge q/2 ) or ( IsEven( q ) and k ge q ) then 
            return false, false, false, false; 
        end if;
        X1 := D*X1*D^-1; X2 := D*X2*D^-1;
        k := k+1;
        if IsZeroEntry( G, (X1*g)^S ) then
            return (B.6^B.2^-1)^(B.4^(-k+1)), One( B ), X1, One( G );
        elif IsZeroEntry( G, (X2*g)^S ) then
            return (B.6*B.6^(B.4^ns))^(B.5*B.4^(-k+1)), One( B ), X2, One( G );
        end if;
    until false;
end function;


ClearFirstRowSLBB := function( G, h : FirstCall := false )
    
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    dim := BBDimension( G );
    q := #BBField( G );
      
    if dim eq 2 then
        return ClearFirstRowSLBBDim2( G, h );
    end if;

    pr1, el := ClearTopRightEntry( G, h );
    if Category( pr1 ) eq BoolElt then return false, false, _, _; end if;
    h := h*el;  
    
    g := h; pl := One( B ); pr := One( B ); L := One( G ); R := One( G );
    
    if dim eq 2 or IsInT( G, g ) then
        return pl, pr1, L, el;
    end if;
    
    l := One( G );
    Q := T^X;
    Z := (Q^-1*Q^(Q^g));
        
    if Z eq One( G ) then
        L := T^(S*X);
        P := X^-2*S*X;
        k := 0;
        
        repeat
            if k eq dim-2 then
                return false, false, false, false;
            end if;
            L := L^P;
            g := L*g;
            Z := (Q^-1*Q^(Q^g));
            k := k+1;
        until Z ne One( G );
            
        g := L*h;
        pl := (B.6^(B.5*B.2^-1))^((B.2^2*B.5*B.2^-1)^k);
        Z := (Q^-1*Q^(Q^g));
    end if;
        
    Y1 := ( T, Z );
    
    if Y1 eq One( G ) then
        P := X^-1*S;
        R := R*T^S;
        r := One( G );
        k := 0;
    
        repeat
            if k eq dim-1 then
                return false, false, false, false;
            end if;
            R := R^P;
            g := g*R;
            Z := (Q^-1*Q^(Q^g));
            Y1 := ( T, Z );
            k := k+1;
        until Y1 ne One( G );
        g := L*h*R;
        pr := (B.6^B.5)^((B.2^1*B.5)^k);
        Z := (Q^-1*Q^(Q^g));
        Y1 := ( T, Z );
    end if;
    
    R1 := Q;
    k := 0;
    Y1 := Y1^S;
    
    repeat
        if k eq q-1 then
            return false, false, false, false;
        end if;
        k := k+1;
        R1 := R1^D;
    until Y1 eq R1;
    
    Z := Z*Y1^-1;
    P := S^X;
    Z := (Z^P)^-1;
    
    Z := Z^((D^X)^-k);

    vec := EntriesOfRootElementBBSL( G, Z : GetLastEntry := false );
    pZ := SiegelTransformToSLP( G, vec );
        
    pr := pr*pZ;
    return pl, pr1*pr, L, el*R*Z;
end function;
    
ClearBottomLeftEntryBB := function( G, g )
    
    dim := BBDimension( G );
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    S1 := S^X;
    q := #BBField( G );
    
    if IsZeroEntry( G, g^S1 ) then
        return One( B ), One( G );
    end if;
    
    X1 := T^X;
    prog1 := B.6^B.2^-1;
    
    k := 1;
    repeat
        if k eq q then
            return false, false;
        end if;
        X1 := D*X1*D^-1;
        k := k+1;
    until IsZeroEntry( G, (X1*g)^S1 );
    
    return prog1^(B.4^(-k+1)), X1;
end function;
    
    
ClearFirstColumnSLBB := function( G, h )
    
    gens := BBStandardGenerators( G );
    S := gens[5]; X := gens[2]^-1; T := gens[6]; D := gens[4]; 
    dim := BBDimension( G );
    q := #BBField( G );
      
   if dim eq 2 then
        return ClearFirstColumnSLBBDim2( G, h );
    end if;
      
    g := h;
    
    pr3, el := ClearBottomLeftEntryBB( G, g );
    if Category( pr3 ) eq BoolElt then return false, false, _, _; end if;
    g := el*g;
    
    if BBDimension( G ) eq 2 or IsInTTranspose( G, g ) then
        return pr3, One( B ), el, One( G );
    end if;
    
    Q := T^(S*X);
    Z := Q*(Q^-1)^(Q^(g^-1));
    p := One( B );
    
    if Z eq One( G ) then
    
        P := X^-2*S*X;
        L := T^X;
        k := 0;
        
        repeat
            if k eq dim-2 then
                return false, false, _, _;
            end if;
            L := L^P;
            g := g*L;
            Z := Q*(Q^-1)^(Q^(g^-1));
            k := k+1;
        until Z ne One( G );
        g := h*L;
    end if;
    
    Y := ( T, Z^S );
    k := 0;
    
    repeat
        if k eq q-1 then
            return false, false, _, _;
        end if;
        k := k+1;
        Q := Q^D;
    until Y eq Q;
    
    Z := (Z*Y^-1)^( S^X);
    Z := (Z^((D^X)^-k));
    vec := EntriesOfTransposeRootElement( G, Z );
    pZ := SiegelTransformToSLP( G, vec : Transpose := true );
    
    return pZ*pr3, One( B ), Z*el, One( G );
end function; 
    
DiagonalElementToSLPBBSL2 := function( G, g )
    
    gens := BBStandardGenerators( G );
    F := BBField( G );
    
    d := One( G );
    count := 0;
    foundcentral := false;
    
    repeat
        if d eq g then
            return B.4^-count, d^-1;
        end if;
        
        if ( g*d^-1, gens[3] ) eq One( G ) then
            foundcentral := true;
            cpr := B.4^-count; cel := d^-1;
        end if;
        
        count := count + 1;
        d := d*gens[4];
    until count eq #F;
          
    if foundcentral  then
        return cpr, cel;
    else
        return false, false;
    end if;
end function;
      
      
        
