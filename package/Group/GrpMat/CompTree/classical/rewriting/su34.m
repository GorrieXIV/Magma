freeze;

import "bbclassical.m":B, BBType, BBField, BBStandardGenerators, 
  BBDimension;
import "spsu.m":IsZeroEntry;

Is21ZeroDim3 := function( G, g )
    
    gens := BBStandardGenerators( G ); 
    T := gens[3]; 
    Y := gens[4];
    S := gens[1];
    q0 := Floor( Sqrt( #BBField( G )));
    
    if q0 eq 2 then
        
        return T^(g^S) in sub< Universe( { T, T^S }) | T, T^S >;
        
    end if;

    Y1 := Y^(q0-1);
    
    return Y1^(T^(g^S)) eq Y1;
end function;
    
Clear21EntrySU32 := function( G, g )
    
     gens := BBStandardGenerators( G ); 
     F := BBField( G );
     
     X1 := gens[4]; 
     X2 := gens[6];
    
     if exists(a){ <a,b> : a, b in [0..3] | Is21ZeroDim3( G, g*X1^a*X2^b )} 
        then
         return B.4^a[1]*B.6^a[2], X1^a[1]*X2^a[2];
     end if;
     
     return false;
 end function;
     
              
Clear21EntryDim3 := function( G, g )
    
    gens := BBStandardGenerators( G ); 
    F := BBField( G );
    S := gens[1]; T := gens[3]; D := gens[10]; 
    V := gens[2]; X := gens[8]; Y := gens[4];
    q := #F;
    q0 := Floor( Sqrt( q ));
    
    if q0 eq 2 then
        return Clear21EntrySU32( G, g ); 
    end if;
    
    if IsOdd( q ) then
        X1 := X; X2 := X1^Y;
        progX1 := B.8; progX2 := progX1^B.4;
    else
        X1 := X^V; X2 := X1^Y;
        progX1 := B.8^B.2; progX2 := progX1^B.4;
    end if;
    
    z := PrimitiveElement( GF( q ));
    
    if IsOdd( q ) then
        alpha := z^Round(( q0+1 )/2 );
        gamma := alpha^2;
        offset := z^(q0-2);
    else
        gamma := z^(q0+1);
        offset := z^(q0-1);
    end if;
        
    x2 := One( G ); 
    for i in [1..q0] do
        
        x1 := One( G );
        for j in [1..q0] do
            if Is21ZeroDim3( G, g*x1*x2 ) then
                if i eq 1 then
                    return progX1^(B.10^(j-2)), x1,
                           (gamma^-1)^(j-2);
                elif j eq 1 then
                    return progX2^(B.10^(i-2)), x2,
                           offset*(gamma^-1)^(i-2);
                else
                    return progX1^(B.10^(j-2))*progX2^(B.10^(i-2)), 
                           x1*x2,
                           (gamma^-1)^(j-2)+offset*(gamma^-1)^(i-2);
                end if;
            end if;
            
            if j eq 1 then
                x1 := X1;
            else
                x1 := x1^D;
            end if;
            
        end for;
        if i eq 1 then
            x2 := X2;
        else
            x2 := x2^D;
        end if;
        
    end for;
    
    return false, false;
end function;
    

// the code for SU(4,q)

ClearFirstRowSUBBDim4 := function( G, g : FirstCall := false )
    
    F := BBField( G ); 
    gens := BBStandardGenerators( G );
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[10]; U := gens[5]; X := gens[6]; Y := gens[4];;
    q := #F;
    q0 := Floor( Sqrt( q ));
    
    prog := One( B );
    
    el := One( G );
    
    if IsZeroEntry( G, g*S ) then
        g := g*(X^V);
        el := el*X^V;
        prog := prog*B.6^B.2;
    end if;
    
    if IsZeroEntry( G, g*S ) then
        g := g*(X^S);
        el := el*X^S;
        prog := prog*B.6^B.1;
    end if;
    
    if IsZeroEntry( G, g*S ) then
        g := g*T^S;
        el := el*T^S;
        prog := prog*B.3^B.1;
    end if;
    
    
    T1 := One( G ); 
    z := PrimitiveElement( GF( q ));

    if not IsZeroEntry( G, g*V*S ) then
        X1 := X; c := 0;
        found := false;
        repeat
            c := c+1;
            if IsZeroEntry( G, g*X1*V*S ) then
                found := true;
                prog := prog*B.6^B.4^(c-1);
                break;
            end if;
            X1 := X1^Y;
        until c ge q/2;
        
        if not found then
            ex := exists( l ){ i : i in [1..q-1] | 
                          IsOdd( Log( z, z^0 + z^(2*i) ))}; 
            assert ex;
            c := 0;
            X1 :=  X*X^Y^-l; progX1 := B.6*B.6^B.4^-l;
            repeat
                c := c+1;
                if c gt q then return false, false, false, false; end if;
                X1 := X1^Y;
            until IsZeroEntry( G, g*X1*V*S );
            prog := prog*progX1^B.4^(c);
        end if;
        T1 := X1;
    end if;
    
    if not IsZeroEntry( G, g*V ) then
        X1 := X^S^V; c := 0; progX1 := B.6^B.1^B.2;
        Y1 := Y^S^V; progY1 := B.4^B.1^B.2;
        found := false;
        repeat
            c := c+1;
            if IsZeroEntry( G, g*X1*V ) then
                found := true;
                prog := prog*progX1^progY1^(c-1);
                break;
            end if;
            X1 := X1^Y1;
        until c ge q/2;
        
        if not found then
            X1 := X^S^V;
            c := 0;
            if IsOdd( Round((q0+1)/2)) then
                ex := exists( l ){ i : i in [1..q-1] | 
                              IsEven( Log( z, z^Round((q0+1)/2) + 
                                      z^(Round((q0+1)/2+2*i))))};
            else
                ex := exists( l ){ i : i in [1..q-1] | 
                              IsOdd( Log( z, z^Round((q0+1)/2) + 
                                      z^(Round((q0+1)/2)+2*i)))};
            end if;
            assert ex;
            X1 :=  X1*X1^Y1^-l; progX1 := progX1*progX1^progY1^-l;
            repeat
                c := c+1;
                if c gt q then return false, false, false, false; end if;
                X1 := X1^Y1;
            until IsZeroEntry( G, g*X1*V );
            prog := prog*progX1^progY1^(c);
        end if;
        T1 := T1*X1;
    end if;
    
    g := g*T1;
    
    if not IsZeroEntry( G, g ) then
        c := 0; TT := T;
        repeat
            c := c+1;
            if c gt q then return false, false, false, false; end if;   
            TT := TT^Y;
        until IsZeroEntry( G, g*TT );
        T1 := T1*TT;
        prog := prog*B.3^B.4^c;
    end if;
    
    return One( B ), prog, One( G ), el*T1;
end function;
    
    
ClearFirstRowSUBBDim3 := function( G, g : FirstCall := false )
    
    gens := BBStandardGenerators( G ); 
    F := BBField( G );
    S := gens[1]; T := gens[3]; D := gens[10]; 
    V := gens[2]; Y := gens[4];
    q := #F;
    q0 := Round( Sqrt( q ));
      
    if Is21ZeroDim3( G, g ) then  
        progR := One( B );
    else
        p, z := Clear21EntryDim3( G, g );
        if Category( p ) eq BoolElt then return false, false; end if;
        g := g*z;
        progR := p; 
    end if;
    
    progL := One( B );
    
    Q := T^S;
    
    c := 0; found := false;
    
    T1 := T;
    
    if Q^(Q^(g*S)) eq Q then
        g := g*S;
        progR := progR*B.1;
    elif Q^(Q^g) ne Q then
        c := 0;
        while Q^(Q^(g*T1)) ne Q do
            if c gt q then return false, false; end if;
            c := c+1;
            if IsOdd( q ) then
                T1 := T1^Y;
            else;
                T1 := T1^D;
            end if;
        end while;
        g := g*T1;
        if IsOdd( q ) then
            progR := progR*B.3^(B.4^(c));
        else
            progR := progR*B.3^(B.10^c);
        end if;
    end if;
    
    return One( B ), progR, One( G ), Evaluate( progR, gens );
end function;
    
/* 
  Produces a generator of the center of SU(4). To be revised at a later stage.
*/
    
GeneratorOfCenterSU4 := function( G );
        
    gens := BBStandardGenerators( G ); 
    F := BBField( G );  
    q :=  Round( Sqrt( #F ));
    type := BBType( G );              
                  
    zz := PrimitiveElement( GF( q^2 ))^(q-1);              
                  
                  
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[10]; U := gens[5]; Y := gens[4];
        
    S1 := S*S^V; V1 := V*U; progS1 := B.1*B.1^B.2; progV1 := B.2*B.5;
    
    Y2 := Y*Y^S1; progY2 := B.4*B.4^(B.1*B.1^B.2); 
    
    Y1 := One( G ); progY1 := One( B );
    
    Y1 := Y1*Y2; Y2 := Y2^V1; 
    progY1 := progY1*progY2; progY2 := progY2^(B.2*B.5);
        
    Y1 := Y1^Round((q+1)/GCD( 4, q+1));
    progY1 := progY1^Round((q+1)/GCD( 4, q+1));
    
    if (zz^Round(-4/2+1))^Round((q+1)/GCD(q+1,4)) ne 
               zz^Round((q+1)/GCD(q+1,4)) then
        Y1 := Y1*D^Round((q-1)/2);
        progY1 := progY1*B.10^Round((q-1)/2);
    end if;
    
    return progY1, Y1; 
    
end function;
    
DiagonalElementToSLPSUBBDim4 := function( G, g )
    
    dim := BBDimension( G ); F := BBField( G ); 
    gens := BBStandardGenerators( G );
    S := gens[1]; V := gens[2]; T := gens[3]; 
    D := gens[10]; U := gens[5]; X := gens[6]; Y := gens[4];;
    q := #F;
    q0 := Floor( Sqrt( q ));
    
    prog := One( B );
    
    
    if IsZeroEntry( G, (g*S^V)^V ) then
        g := g*S^V;
        prog := prog*B.1^B.2;
    elif not IsZeroEntry( G, g^V ) then
        T1 := T^V; Y1 := Y^V;
        c := 0;
        repeat
            if c gt q then return false, false; end if;
            c := c+1;
            T1 := T1^Y1;
        until IsZeroEntry( G, (g*T1)^V );
        g := g*T1;
        prog := prog*(B.3^B.2)^(B.4^B.2)^c;
    end if;

    
    if not IsZeroEntry( G, S*V*g*V*S ) then
        
        T1 := T^(S*V); Y1 := Y^(S*V);
        c := 0;
        repeat
            if c gt q then return false, false; end if;
            c := c+1;
            T1 := T1^Y1;
        until IsZeroEntry( G, S*V*g*T1*V*S );
        g := g*T1;
        prog := prog*(B.3^(B.1*B.2))^(B.4^(B.1*B.2))^c;
    end if;

    T1 := T^V;
    c := 0;
    while T1^g ne T1 do;
        if c gt q then return false, false; end if;
        g := g*Y;
        c := c+1;
    end while;

    prog := prog*B.4^c;
    
    c := 0;
    while T^g ne T do
        if c gt q then return false, false; end if;
        g := g*D;
        c := c+1;
    end while;
    
    prog := prog*B.10^c;
    
    Y1 := Y^(q0-1);
    c := 0; found := false; g1 := g;
    repeat
        g1 := g1*Y1;
        c := c+1;
        if X^g1 eq X then
            found := true;
            g := g1;
            prog := prog*B.4^((q0-1)*c);
            break;
        end if;
    until c ge (q+1)/4;
    
    if not found then
        g := g*D^Round((q0-1)/2);
        prog := prog*B.10^Round((q0-1)/2); 
        c := 0; 
        repeat
            if c gt q then return false, false; end if;
            g := g*Y1;
            c := c+1;
        until X^g eq X;
        prog := prog*B.4^((q0-1)*c);
    end if;

    c := 0;
    
    pcent, cent := GeneratorOfCenterSU4( G );
    iscentral := func< x | { true } eq { x^z eq x : z in gens } >;
    foundcentral := false;
    
    repeat
        // if g is the identity then we found the right element
        if g eq One( G ) then 
            return pcent^c*prog, Evaluate(  pcent^c*prog, gens ); 
        end if;
        
        // if g is central then we same this element
        // we will return it if do not find better  
        if iscentral( g ) then 
            foundcentral := true;
            cpr := pcent^c*prog; cel := Evaluate(  pcent^c*prog, gens );
        end if;
        
        // if we tried a lot of elements then we give up
        if c gt GCD( q0+1, dim ) then break; end if;
        g := g*cent;
        c := c+1;
    until false;
    
    if foundcentral then
        return cpr, cel;
    else
        return false, false;
    end if;
    
end function;
    
GeneratorOfCenterSU3 := function( G )
    
    dim := BBDimension( G ); field := BBField( G );
    type := BBType( G );
    gens := BBStandardGenerators( G );
    T := gens[3]; D := gens[10]; S := gens[1]; V := gens[2];
    Y := gens[4];
    q := #field;
      
    q := Round( Sqrt( q ));
        
    D := Y; progD := B.4;
    p := V*S; pp := B.2*B.1;
        
    el1 := D; el := el1;
    pel1 := progD; pel := progD;
    
    return pel^Round((q^2-1)/GCD(dim,Round((q+1)))), 
           el^Round((q^2-1)/GCD( dim,Round((q+1))));
end function;

    
DiagonalElementToSLPSUBBDim3 := function( G, g ) 
    
    gens := BBStandardGenerators( G );
    X := gens[8]; Y := gens[4]; D := gens[10];
    q := #BBField( G );
      
    c1 := 0;
    while X^g ne X do
        if c1 gt q then return false, false; end if;
        g := g*Y;
        c1 := c1+1;
    end while;

    pc, c := GeneratorOfCenterSU3( G );
    c2 := 0;
    q0 := Round( Sqrt( q ));
    iscentral := func< x | { true } eq { x^z eq x : z in gens } >;
    foundcentral := false;
    
    repeat
        // if g is the identity then we found the right element
        if g eq One( G ) then return B.4^c1*pc^c2, Y^c1*c^c2; end if;
        
        // if g is central then we same this element
        // we will return it if do not find better  
        if iscentral( g ) then 
            foundcentral := true;
            cpr := B.4^c1*pc^c2; cel := Y^c1*c^c2;
        end if;
        
        // if we tried a lot of elements then we give up
        if c2 gt GCD( 2, q0+1) then break; end if;
        g := g*c;
        c2 := c2+1;
    until false;
    
    if foundcentral then
        return cpr, cel;
    else
        return false, false;
    end if;
    
    
end function;
    
        
    
    
    
