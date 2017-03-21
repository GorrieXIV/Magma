freeze;

import "bbclassical.m": B, Evaluate2, BBDimension, BBField, 
                        BBType, BBStandardGenerators;

import "subgroups.m":SLPToSiegelTrans;

// this file implements the construction of auxiliary elements
// needed in the rewriting procedures

/*  
  The following function returns T_{f_1,e_2} in the cases of Sp and SU.
  If dim is even then this is one of the generators. In SU( odd, q )
  it needs to be constructed. The code is due to Elliot.
*/ 
    
RootElements := function( G : Transpose := false ) 
    
 /*   if assigned G`RootElements and not Transpose then 
        return G`RootElements[1], G`RootElements[2];
    elif assigned G`RootElementsTranspose and Transpose then
        return G`RootElementsTranspose[1], G`RootElementsTranspose[2];
    end if; */
        
    dim := BBDimension( G );
    F := BBField( G );
    p := Characteristic( F );
    d := Round( Log( p, #F ));
    type := BBType( G );
    gens := BBStandardGenerators( G );
    
    prgens, matgens := SLPToSiegelTrans( G : EvaluateSLPs := true ); 

    if type eq "SL" then
        return [ matgens[x] : x in [1..(dim-2)*d+1 by d ]];
    elif type eq "Omega" or <type,IsOdd( dim )> eq <"SU", true > then 
        roots := [ matgens[x] : x in [1..(dim-4)*d+1 by d ]] cat 
                 [ matgens[ (dim-3)*d+1 ]];
        prroots :=  [ prgens[x] : x in [1..(dim-4)*d+1 by d ]] cat
                    [ prgens[ (dim-3)*d+1 ]];
    elif type eq "Omega-" then
        roots := [ matgens[x] : x in [1..(dim-6)/2*d+1 by d]] cat 
                 [ matgens[x] : x in [(dim-4)/2*d+1..(dim-5)*d+1 by d ]]
                 cat [ matgens[(dim-4)*d+1], matgens[(dim-3)*d+1]];

        prroots := [ prgens[x] : x in [1..(dim-6)/2*d+1 by d]] cat 
                   [ prgens[x] : x in [(dim-4)/2*d+1..(dim-5)*d+1 by d ]]
                   cat [ prgens[(dim-4)*d+1], prgens[(dim-3)*d+1]];
                   
    else
        roots := [ matgens[x] : x in [1..(dim-3)*d+1 by d ]];
        prroots := [ prgens[x] : x in [1..(dim-3)*d+1 by d ]];
    end if;
    
    if Transpose then
        if type eq "Omega+" then
            S := gens[1]*gens[5]; PS := B.1*B.5;
        elif type eq "Omega-" and IsEven( #BBField( G )) then
            S := gens[1]^2; PS := B.1^2;
        else
            S := gens[1]; PS := B.1;
        end if;
        
        roots := [ x^S : x in roots ]; 
        prroots := [ x^PS : x in prroots ];
        
        // get them in the right order
      
        if type eq "Omega+" then  
            list := [ 1 ] cat [ dim-3..2 by -1 ] cat [ dim-2 ];
        elif type eq "Omega" then 
            list := [ dim - 3..1 by -1] cat [dim-2];
        else // type is Omega-
            list := [ dim - 4..1 by -1] cat [ dim-3, dim-2 ];
        end if;
    
        roots := [ roots[i] : i in list ];
        prroots := [ prroots[i] : i in list ];
        
        G`RootElementsTranspose := < roots, prroots >;
        
    else 
        
        G`RootElements := < roots, prroots >;
        
    end if;
        
    return roots, prroots;
end function;

// returns a diagonal element of G as SLP that is needed at the end of the 
// procedure

DiagonalElement := function( type, dim, q )
    
    if type eq "SL" then
        
        p := B.2^-1*B.1;
        pr := B.4^-1;
        
        for i in [1..dim-2] do
            pr := pr*((B.4^-1)^p);
            p := p*B.2^-1*B.1;
        end for;
        
        return pr;
        
    elif type eq "Sp" then
        
        p := B.2*B.5;
        pd := B.4^B.5; pr := pd;
        
        for i in [1..(dim-4)/2] do
            pd := pd^(B.2*B.5);
            pr := pr*pd;
        end for;
        
        pr := pr^Round((q-2)/2);
        return pr;
        
    elif type eq "SU" and dim eq 3 then
        
        return B.4;
        
    elif type eq "SU" and IsEven( dim ) then
        
        progY1 := One( B ); progY2 := B.4*B.4^(B.1*B.1^B.2);
        
        for i in [1..(dim-2)/2] do
            progY1 := progY1*progY2; progY2 := progY2^(B.2*B.5);
        end for;
        
        return progY1;
        
    elif type eq "SU" and IsOdd( dim ) then
        
        progZ1 := (B.4*B.4^B.1)^-1;
        progZ := One( B );
        
        for i in [1..(dim-1)/2] do
            progZ := progZ*progZ1;
            progZ1 := progZ1^B.2;
        end for;
        
        progZ := progZ*B.4^((2*dim div 2));
        
        
        return progZ;
        
    elif type eq "Omega+" then
        
        progZ := One( B );
        progZ1 := B.4^((q-1) div 2);
        V := B.2*B.5;
        
        for i in [1..(dim-2)/2] do
            progZ := progZ*progZ1;
            progZ1 := progZ1^V;
        end for;
        
        return progZ;
        
    elif type eq "Omega-" then
        
        q1 := (q-1) div 2; dim1 := dim div 2-2;
        pd1 := B.11^q1;
        pd2 := (B.11^q1)^B.2^-1;
        for i in [1..dim1-1] do
            pd1 := pd1*pd2;
            pd2 := pd2^B.2^-1;
        end for;
        
        pd1 := pd1*(B.11^B.2)^Round((q+1)/2-q1*dim1);
        return pd1;
        
    elif type eq "Omega" then
        
        return One( B );
        
    end if;
end function;
  
X_ := function( type, dim, q )
    
    if IsEven( dim ) then
        return B.3;
    end if;
    
    // dim is odd, and type eq SU
      
      BX := B.6; BY := B.7; 
    WS1 := B.1*(BY^B.2)^(Round((q^2+q)/2));
    WB := (BX^B.2)^-1*WS1*(BX^B.2*B.5)^-1*B.5*WS1*B.5*WS1*B.5*
          (BX^B.2)^-1;
    
    WX1 := ((WB^B.5*WS1*(BX^B.2)^-1)^(B.5*WS1*B.5*B.2^-2))^-1;

    WX1 := WX1^(B.2^2);
    
    if IsEven( q ) then
        WX1 := WX1*((B.3^B.1)^B.2)^(B.7^B.2^2)*B.3;
        WX1 := WX1^(B.4^Round(q/2));
    end if;    return WX1;
    
    
    return WX1;
end function;

/* 
   This function returns the root element T_{f_1,aw} in SU(odd,q)
   with a in F.
*/

   
Tf1aw := function( dim, q, a )
    
    if a eq 0 then
        return One( B ), 0;
    end if;
    
    F := GF(q^2);
    q := #F; q0 := Floor( Sqrt( q ));
    z := PrimitiveElement( GF( q )); 
    z0 := PrimitiveElement( GF( q0 ));
    
    if IsEven( q ) then
        x1e1f1 := (Trace (z, GF(q0)))^-1*z;
        x2wf1 := z^-(q0-1);
    else
        x1e1f1 := -1/2;
        x2wf1 := -z^-(q0-1);
    end if;

      
    V, f := VectorSpace( GF( q ), GF( q0 ));
    a1 := One( GF( q ));        
    a2 := z^(q0-1);
    
    m := Eltseq( a1@f ); m := m cat Eltseq( a2@f );
    m := GL( 2, q0 )!m;
    
    v := (a@f)^(m^-1); 
    
    if v[2] eq 0 then
        return B.8^B.4^Log( z0^-1, v[1] );
    elif v[1] eq 0 then
        return (B.8^B.9^B.2)^B.4^Log( z0^-1, v[2] );
    else
        return B.8^B.4^Log( z0^-1, v[1] )*(B.8^B.9^B.2)^B.4^Log( z0^-1, v[2] );
    end if;
    
end function;
    
/* 
  the following function returns the three root elements of Omega
  as SLPs.
*/
        
 RootElementsOfOmega := function( type, dim, q );
        
    if dim eq 3 then
        return One( B ), One( B );
    end if;

    classgens := ClassicalStandardGenerators( "Omega", dim, q );
    
    Bf :=  func< h, i | (h^(B.4^i))^-1*(h^B.4)^Round((q-1)/2)*h^(B.4^i) >;
    Bpf := func< h, i | ((h*B.1)^(B.4^i))^-1*(h^B.4)^Round((q-1)/2)*
                (h*B.1)^(B.4^i) >;
    
        
    v := classgens[4]; r := classgens[2];
    r1 := r^v; pr1 := (B.2^B.4);
    
    p2 := Bpf(B.2,2);
    x2 := Evaluate2( p2, classgens );
    pr1 := B.2^B.4;
    
    rel := r1[1,dim];
    x2el := x2[1,dim];
    
    e2 := Integers()!(-x2el/rel);
    
    x2:= r1^e2*x2;
    
    p2 := pr1^e2*p2;
    
    e2 := Integers()!(1/x2[1,3]);
    p2 := p2^e2;
    
    // now calculate the other root
      
    p1 := Bf(B.2,2); 
    x1 := Evaluate2( p1, classgens ); 
    
    rel := r1[1,dim];
    x1el := x1[1,dim];
    
    e1 := Integers()!(-x1el/rel); 
    
    x1 := r1^e1*x1; 
    
    p1 := pr1^e1*p1; 
    
    e1 := Integers()!(1/x1[1,4]); 
    p1 := p1^e1;   
    
    return p2, p1;
end function;
    
X12OMinusChar2_ := function( d, q );

   F := GF( q );
   Q := ClassicalStandardGenerators( "Omega-", d, #F );
                
   if #Q eq 4 then
    Append( ~Q, Q[4] );
   end if;             
                
   G := sub< GL( d,q ) | Q >;
   Q := [GL(d, F)!Q[i] : i in [1..#Q]];
   GGG := sub<GL(d, F)|Q>;
   ww := PrimitiveElement(GF(#F^2));
   w := PrimitiveElement(F);
   sl := SL(2, #F^2);
   /* QO := CreateOmegaPlusGenerators(OmegaPlus(d, F)); */
   e := Degree(F);
   ee := Degree(GF(#F^2));
   q := #F;
   Z := IntegerRing();

   tt := GL(d, F)!Q[1];
   rr := GL(d, F)!Q[2];
   ddelta := GL(d, F)!Q[3];
   u := GL(d, F)!Q[4];
   v := GL(d, F)!Q[5];

   /* #Q should ALWAYS be 5. The fact that it's not in
      standard.m needs to be changed */
   SS := SLPGroup(5);

   if IsOdd(d div 2) then
      t := (GL(d, F)!(v^-1 * tt*v))^-1;
      T := (SS.1 ^ SS.5)^-1;
      r := (GL(d, F)!(v^-1 * rr*v))^-1;
      R := (SS.2 ^ SS.5)^-1;
   else
      t := GL(d, F)!(v^-1 * tt*v);
      T := SS.1 ^ SS.5;
      r := GL(d, F)!(v^-1 * rr*v);
      R := SS.2 ^ SS.5;
   end if;

   delta := GL(d, F)!(v^-1 * ddelta*v);
   DELTA := SS.3 ^ SS.5;
   s := r*t^-1*r;
   S := R*T^-1*R;

   /* We now find the generators of OmegaPlus(d-2, q)
      as words in the generators for OmegaMinus(d, q).

      t^n sends col d-1 to d-1 + n*col 1 and
      col 2 to n^2*col 1 2n*col d-1 + col 2.
   
      Let a = [1, 1], b = [1, d-1], c = [1, 2].
      We need to solve an^2 + 2bn + c = 0 in order
      to get the power of n we need to kill the
      [1, 2] position
   */

   r2bar := r*((r^delta)^(r^v))^(delta^-1);
   R2bar := R*((R^DELTA)^(R^SS.5))^(DELTA^-1);
   /* zz := Log(r2[4, 1]); */
   if (d ne 4) and (d ne 2) then
      zz := Eltseq(r2bar[4, 1]^-1);
   else
      zz := Eltseq(F!1);
   end if;
   r2 := Id(G);
   R2 := Id(SS);
   for i in [1..#zz] do
      if zz[i] eq 1 then
         r2 := r2 * r2bar^(delta^(i-1));
         R2 := R2 * R2bar^(DELTA^(i-1));
      end if;
   end for;

   t2bar := t*((t^delta)^(t^v))^(delta^-1);
   T2bar := T*((T^DELTA)^(T^SS.5))^(DELTA^-1);
   t2 := Id(G);
   T2 := Id(SS);
   for i in [1..#zz] do
      if zz[i] eq 1 then
         t2 := t2 * t2bar^(delta^-(i-1));
         T2 := T2 * T2bar^(DELTA^-(i-1));
      end if;
   end for;

   r1 := t2^s;
   R1 := T2^S;
   t1 := r2^s;
   T1 := R2^S;
   
   return Evaluate( T1, [B.1,B.2,B.3,B.4,B.5]),
          Evaluate( T2, [B.1,B.2,B.3,B.4,B.5]);
end function;
    
    
X12_ := function( type, dim, q )
  
    if dim eq 4 then
        return One( B ), One( B );
    elif IsEven( q ) then
        return X12OMinusChar2_( dim, q );
    end if;
        
    gens := ClassicalStandardGenerators( "Omega-", dim, q );
    
    if #gens eq 4 then
      Append( ~gens, gens[4] );
    end if;
    
    s := gens[1]; v := gens[5]; r := gens[2];
    
    Bf :=  func< h | (h^(B.5^2))^-1*(h^B.5)^Round((q-1)/2)*h^(B.5^2) >;
    Bpf := func< h | ((h*B.1)^(B.5^2))^-1*(h^B.5)^Round((q-1)/2)*
                 (h*B.1)^(B.5^2) >;
    
    p1 := Bf(B.2); p2 := Bpf(B.2);
    x1 := Evaluate2( p1, gens ); x2 := Evaluate2( p2, gens );
    r1 := r^v; pr1 := B.2^B.5;
    
    rel := r1[1,dim-1];
    x1el := x1[1,dim-1];
    x2el := x2[1,dim-1];
    
e1 := Integers()!(-x1el/rel); e2 := Integers()!(-x2el/rel);
    
    x1 := r1^e1*x1; x2 := r1^e2*x2;
    p1 := pr1^e1*p1; p2 := pr1^e2*p2;
    
    e1 := Integers()!(1/x1[1,4]); e2 := Integers()!(1/x2[1,3]);
    
    return p2^e2, p1^-e1;
end function;
    
    
Xr2_ := function( dim, q )
    
  gens := ClassicalStandardGenerators( "Omega-", dim, q );  
  
  if #gens eq 4 then
      Append( ~gens, gens[4] );
  end if;
    
  if IsOdd( q ) then  
      r := gens[2]^gens[5]; pr := B.2^B.5;
  else
      r := gens[1]^gens[5]; pr := B.1^B.5;
  end if;
  
  i1 := dim-1; i2 := dim;

  bas := [ [r[1,i1], r[1,i2]] ]; baspr := [ pr ];
  
  p := PrimeBasis( q )[1];
  d := Round( Log( p, q ));
  
  for i in [1..2*d-1] do
      r := r^gens[3];
      pr := pr^B.3;
      Append( ~bas, [r[1,i1],r[1,i2]] );
      Append( ~baspr, pr );
  end for;
  
  V := VectorSpace( GF( q ), 2 );
  V1, a := VectorSpace( V, GF( p ));
  
  mat := [];
  for i in bas do
      Append( ~mat, Coordinates( V1, i@a ));
  end for;

  mat := GL( 2*d, p )!mat;
  
  coeff := ((V![0,1])@a)^(mat^-1);
  
  prog := One( B );
  
  for i in [1..2*d] do
      prog := prog*baspr[i]^(Integers()!coeff[i]);
  end for;
  
  return prog;
  
end function;
    
/* 
  The various components of this package use different standard bases 
  for the classical groups, and so it is necessary to convert one
  basis for the others. We will use 4 bases:
  
  My basis: the bases used in the ClassicalRewrite package
  Elliot's basis: the bases used in XXXWordInGen
  SX(n,q): the basis used in Magma's SX(n,q) function
  ClassicalStandardGenerators: the basis used by the output of 
  ClassicalStandardGenerators
    
  Symplectic:
  
  My basis: e1,..,en,fn,...,f1
  Elliot: e1,..,en,fn,...,f1
  SX(n,q): e1,..,en,fn,...,f1
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn
  
  Unitary: 
  
  My basis: e1,...,en,fn,...,f1(,w)
  Elliot:  e1,...,en,(w,),fn,...,f1;
  SX(n,q): e1,...,en,(w,),fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn(,w)
    
  Omega+:
    
  My basis: e1,...,en,fn,...,f1
  Elliot:  e1,...,en,,fn,...,f1; 
  SX(n,q): e1,...,en,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn  
  
  Omega-:
    
  My basis: e1,...,en,w1,w2,fn,...,f1,w1,w2 (changed from Version 5)
  Elliot:  e1,f1,e2,f2,...,en,fn,w1,w2; 
  (here he diverged from his convention!)
  SX(n,q): e1,...,en,u1,u2,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn,w1,w2
    
  where Q(w1) eq -2 and Q(w2) eq 2z where z is a primitive root in GF(q)
  Q(u1) eq 1 and Q(u2) is ???  
    
  Omega:
    
  My basis: e1,...,en,fn,...,f1(,w)
  Elliot: e1,f1,e2,f2,...,en,fn,v
  SX(n,q): e1,...,en,u,fn,...,f1;
  ClassicalStandardGenerators: e1,f1,e2,f2,...,en,fn,v
    
  where Q(w) = ???, Q(u) = ???, Q(v) eq ???  
  
*/
    
ConjugateClassicalStandardToMyBasis := function( type, dim, q )
    
    if type eq "SL" then
        
        list := [ i : i in [1..dim]];
        
          
    elif type eq "Omega-" then
        
        list := [ 1.. dim-3 by 2] cat
                [ dim-2 .. 2 by -2 ] cat [ dim-1, dim];

   elif IsEven( dim ) then
        
        list := [ i : i in [1..dim-1 by 2]] cat 
                [ i : i in [dim..2 by -2 ]];
        
    elif IsOdd( dim ) then
        
        list := [ i : i in [1..dim-2 by 2]] cat 
                [ i : i in [dim-1..2 by -2 ]] cat [ dim ];

    end if;
    
    return  GL( dim, q )!PermutationMatrix( GF( q ), Sym( dim )!list )^-1;
end function;

ConjugateClassicalStandardToElliot := function( type, dim, q )
    
    if type in { "SL", "Omega-", "Omega" } then
        
        list := [ i : i in [1..dim]];
        
   /* 
     there is a bug in Elliot's code for SU(2,2^d) and this is
     fixed here.
   */
        
    elif dim eq 2 and type eq "SU" and IsEven( q ) then
       
       gamma := PrimitiveElement( GF( q ));
       q0 := Round( Sqrt( q ));
       return GL(2,q)![gamma^((q0 div 4)*(Round(-Sqrt(q))-1)),0,0,
                      gamma^((q0 div 4)*(Round(Sqrt(q))+1))];
            
    elif type eq "SU" and IsOdd( dim ) then
        
        list := [1..dim-2 by 2] cat [ dim ] cat [dim-1..2 by -2];
        conj := GL( dim, q )!PermutationMatrix( GF( q ), list );
                
    elif IsEven( dim ) then
        
        list := [ i : i in [1..dim-1 by 2]] cat 
                [ i : i in [dim..2 by -2 ]];
        
    elif IsOdd( dim ) then
        
        list := [ dim ] cat [ i : i in [1..dim-2 by 2]] cat 
                [ i : i in [dim-1..2 by -2 ]];

    end if;
    
    return  GL( dim, q )!PermutationMatrix( GF( q ), Sym( dim )!list )^-1;
end function;

/* the following conjugates ClassicalStandardGenerators to the
   generating set required by ClassicalElementToSLP */

ConjugateClassicalStandardToClassicalNatural := function( type, dim, q )
    
    if type eq "SL" then
        
        list := [1..dim];

   elif type eq "Omega" or ( type eq "SU" and IsOdd( dim )) then

        list := [ 1..dim-2 by 2 ] cat [ dim-1..2 by -2 ] cat [dim];

    elif type eq "Omega-" then

        list := [ 1..dim-3 by 2 ] cat [dim-2..2 by -2 ] cat [dim-1,dim];
        
    elif IsEven( dim ) then
        
        list := [ 1..dim-1 by 2] cat [ dim..2 by -2 ];
        
    elif IsOdd( dim ) then
        
        list := [ dim ] cat [1..dim-2 by 2] cat 
                [ dim-1..2 by -2 ];

    end if;
    
    return  GL( dim, q )!PermutationMatrix( GF( q ), Sym( dim )!list )^-1;
end function;

           
U_ := function( d, q )
    
    F := GF( q ); 
    qq := #F; e := Degree( F ); 
    w := PrimitiveElement( F );
        
    QQ := ClassicalStandardGenerators( "Omega", d, qq );
    G := sub< GL( d, q ) | QQ >;
    
    v := QQ[4]; pv := B.4;
    
    if IsOdd((d+1) div 2) then
        t := (GL(d, GF(qq))!(v^-1 * QQ[2]*v))^-1;
        s := (GL(d, GF(qq))!(v^-1 * QQ[1]*v))^-1;
        pt := B.4^-1*B.2^-1*B.4;
        ps := B.4^-1*B.1^-1*B.4;
    else
        t := GL(d, GF(qq))!(v^-1 * QQ[2]*v);
        s := GL(d, GF(qq))!(v^-1 * QQ[1]*v);
        pt := B.4^-1*B.2*B.4;
        ps := B.4^-1*B.1*B.4;
    end if;
    
    r := t^s; pr := pt^ps;
    BB := (t^v)^-1*t^((qq-1) div 2)*t^v;
    pBB := (pt^pv)^-1*pt^((qq-1) div 2)*pt^pv;
    a := BB[1, d];
    
    Z := IntegerRing();
    n := Z!(-a/2);
    
    t2 := t^n*(t^v)^-1*t^((qq-1) div 2)*t^v;
    r2 := (r^n*(r^v)^-1*r^((qq-1) div 2)*r^v)^-1;
    
    pt2 := pt^n*(pt^pv)^-1*pt^((qq-1) div 2)*pt^pv;
    pr2 := (pr^n*(pr^pv)^-1*pr^((qq-1) div 2)*pr^pv)^-1;
      
    BB := ((t*s)^v)^-1*t^((qq-1) div 2)*(t*s)^v;
    pBB := ((pt*ps)^pv)^-1*pt^((qq-1) div 2)*(pt*ps)^pv;
    
    a := BB[1, d];
    n := Z!(-a/2);
    
    t1 := (t^n*((t*s)^v)^-1*t^((qq-1) div 2)*(t*s)^v)^-1;
    r1 := (r^n*((r*s)^v)^-1*r^((qq-1) div 2)*(r*s)^v);
    
    u := (r1^(t1^-1)*r1^2)^-1;
    
    pt1 := (pt^n*((pt*ps)^pv)^-1*pt^((qq-1) div 2)*(pt*ps)^pv)^-1;
    pr1 := (pr^n*((pr*ps)^pv)^-1*pr^((qq-1) div 2)*(pr*ps)^pv);
    
    pu := (pr1^(pt1^-1)*pr1^2)^-1;
    
    KQ := [];
    if d ne 3 then
        Append(~KQ, r1);
        Append(~KQ, r2^-1);
        for i in [1..(d div 2) - 2] do
            if IsOdd(i) then j := 1; else j := -1; end if;
            Append(~KQ, (r1^((v*u)^i))^-j);
            Append(~KQ, (r2^((v*u)^i))^j);
        end for;
    end if;
    
    FF := sub<F|w^2>;
    py := FF!w;
    delta := QQ[3]^QQ[4];
    
    pdelta := B.3^B.4;
    
    
    Ot1 := Id(G); pOt1 := One( B );
    for i in [1..e] do
        Ot1 := Ot1*(t1^(delta^-(i-1)))^Z!Eltseq(py)[i];
        pOt1 := pOt1*(pt1^(pdelta^-(i-1)))^Z!Eltseq(py)[i];
    end for;
    
    Or1 := Id(G); pOr1 := One( B );
    for i in [1..e] do
        Or1 := Or1*(r1^(delta^(i-1)))^Z!Eltseq(py)[i];
        pOr1 := pOr1*(pr1^(pdelta^(i-1)))^Z!Eltseq(py)[i];
    end for;
    
    Ot2 := Id(G); pOt2 := One( B );
    for i in [1..e] do
        Ot2 := Ot2*(t2^(delta^-(i-1)))^Z!Eltseq(py)[i];
        pOt2 := pOt2*(pt2^(pdelta^-(i-1)))^Z!Eltseq(py)[i];
    end for;
    
    Or2 := Id(G); pOr2 := One( B );
    for i in [1..e] do
        Or2 := Or2*(r2^(delta^(i-1)))^Z!Eltseq(py)[i];
        pOr2 := pOr2*(pr2^(pdelta^(i-1)))^Z!Eltseq(py)[i];
    end for;
    
    delta1 := r1*delta*t1;
    pdelta1 := pr1*pdelta*pt1;
    
    for j in [1..e] do
        a := Z!Eltseq((w^-1 - 1))[j];
        if IsOdd(j) then
            delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
            pdelta1 := pdelta1*(pr1^(pdelta^((j-1) div 2)))^a;
        else
            delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
            pdelta1 := pdelta1*(pOr1^(pdelta^((j-2) div 2)))^a;
        end if;
    end for;
    
    delta1 := delta1*Ot1^-1;
    pdelta1 := pdelta1*pOt1^-1;
    
    b := delta1[3, 1];
    for j in [1..e] do
        a := Z!Eltseq(-b/w)[j];
        if IsOdd(j) then
            delta1 := delta1*(r1^(delta^((j-1) div 2)))^a;
            pdelta1 := pdelta1*(pr1^(pdelta^((j-1) div 2)))^a;
        else
            delta1 := delta1*(Or1^(delta^((j-2) div 2)))^a;
            pdelta1 := pdelta1*(pOr1^(pdelta^((j-2) div 2)))^a;
        end if;
    end for;
    
    delta2 := ((delta1^u)^s)^u;
    pdelta2 := ((pdelta1^pu)^ps)^pu;
    
    _, p := IsPrimePower( q );
    
    if d mod 4 eq 1 then
        l2 := -2;
    else
        l2 := 2;
    end if; 
    
    bbgensinv := [ B.1^B.2^-1,(B.8^l2)^B.2^-1,B.4^B.2^-1,B.2,B.5 ];
    
    return Evaluate2( pu, bbgensinv ), 
           Evaluate2( pdelta1, bbgensinv ), 
           Evaluate2( pdelta2, bbgensinv );
end function;

/* The next function calculates the coordinates of field element el    
   in the basis bas. */
  
CoordinatesOfElinBasis := function( G, bas, el : StandardBasis := false )

    F := BBField( G );
    // in case of prime field
    if IsPrimeField( F ) then
        return [ Integers()!el ];
    end if; 
    
    coeff := Eltseq( F!el );
    
    // if we have standard basis then do no more
    
    if StandardBasis then 
        return coeff;
    end if;
        
    p := Characteristic( F );
    V, a := VectorSpace( F, GF( p ));
    W := VectorSpaceWithBasis([ x@a : x in bas ]);
    vec := Coordinates( V, el@a );
   
    return Coordinates( W, W!vec );
end function;


/* The next function returns and SLP that point to a Siegel transform
   given by the vector vec. */
  
SiegelTransformToSLP := function( G, vec : Transpose := false )
                        
    F := BBField( G );
    d := BBDimension( G );
    q := #F;
    type := BBType( G );
    p := Characteristic( F );
    e := Round( Log( p, q ));
    
    // if the vector is the null vector, then we return identity
    if vec eq [ 0 : x in [1..d-1]] then
        return One( B );
    end if;
        
    z := PrimitiveElement( F ); 
    // the following is needed to know when we can use standard basis
    isgoodfield := F.1 eq z or F.1 eq One( F );
    q0 := p^Round(e/2);
    e0 := case< type | "SU": e/2, default: e >; 
    wittindex := case< type | "SL": d, "Omega-": d/2-1, default: Floor( d/2 )>;
    wittdefect := d-2*wittindex;
    
    p := Characteristic( F );  
    prod := One( B );
    
    /* The SLP will be the product of Siegel transformation. 
       the variable prodpos contains the position of the last computed      
       subproduct. Zero means that no such subproduct was computed. */
        
    // count counts how many Siegel transformations we have used.
    siegslps := SLPToSiegelTrans( G : Transpose := Transpose );   
    count := 0;
    
    /* we will need to compute the coefficients of a field element
       in a basis over F_p. We usually use the standard basis. 
       stbas is set true whenever the standard basis is used. */ 
      
    if type eq "SL" and d eq 2 then
        bas := [ z^(2*i) : i in [0..e-1]]; stbas := false;     
    elif type eq "Omega" then
        bas := [ z^(2*i) : i in [0..e-1]]; stbas := false;     
    elif type eq "SU" and d eq 4 then
        bas := [ z^(2*i) : i in [0..e-1]]; stbas := false;
    elif <type,d> eq <"Omega+",4> then
        bas := [z^(-2*i) : i in [0..e-1]]; stbas := false;
    else
        bas := [ z^i : i in [0..e-1]]; stbas := true; 
    end if;
    
    stbas := stbas and isgoodfield;

    word := One( B );
        
    // calculate upper index for the next loop
    for i in [1..case< type | "SL": #vec, default: 2*(wittindex-1)>] do

        /* In the case of SU, we need to change the basis on the middle 
           of the process. */
        if type eq "SU" and IsOdd( q ) and d eq 4 and i eq 2 then
           bas := [z^Round((q0+1)/2+2*i) : i in [0..e-1]];     
           stbas := false; 
        elif <type,i,IsOdd( q )> eq <"SU",Floor( d/2 ),true> then
            bas := [z^Round((q0+1)/2+i) : i in [0..e-1]];
            // stbas is set false now
            stbas := false;
        end if;
            
        // if vec[i] eq 0 then there is nothing to do
        if vec[i] eq 0 then
            count := count+e;
            continue i;
        end if;
        
        // need to know if we can use standard basis
                           
        // computing the coeffs of vec[i]
        coeffs := CoordinatesOfElinBasis( G, bas, vec[i] : 
                          StandardBasis := stbas );
        
        // based on coeffs we complete the product
        for j in [1..e] do
            count := count+1;
            if coeffs[j] eq 0 then
                continue j;
            end if;
            word := word*siegslps[count]^Integers()!coeffs[j];
            // we link the last factor to the product computed so far
        end for;
    end for; 

    // in case of SL and Omega+ we are done
    if type in [ "SL", "Omega+" ] then return word; end if;
    
    // in the case of SU( odd, q ) and Omega( odd, q ), 
    // we take care of the w-entry
    if IsOdd( d ) and #vec eq d-1 then
        // in case of SU we need to change the basis. 
        // in case of Omega, we continue with the basis     
        if type eq "SU" and q eq 4 then 
             bas := [1,z];    
        elif type eq "SU" then    
            bas := [z^((q0-2)*i) : i in [0..e-1]]; 
        end if;
        coeffs := CoordinatesOfElinBasis( G, bas, vec[d-1] ); 
        for j in [1..e] do
            count := count+1;
            if coeffs[j] eq 0 then
                continue j;
            end if; 
            word := word*siegslps[count]^Integers()!coeffs[j];
        end for;   
    end if;
    
    // in Omega- we need to take care of the [e1,w1] and [e1,w2]-entries
    if type eq "Omega-" then
        // basis is [1,omega^2,omega^4,...]
        bas := [ z^(2*i) : i in [0..e-1]];
        
        // first the [e1,w1] entry
        coeffs := CoordinatesOfElinBasis( G, bas, vec[d-2] );
        for j in [1..e] do
            count := count+1;
            if coeffs[j] eq 0 then
                continue j;
            end if; 
            word :=  word*siegslps[count]^Integers()!coeffs[j];
        end for;
            
        // next the [e1,w2] entry    
        coeffs := CoordinatesOfElinBasis( G, bas, vec[d-1] );
        for j in [1..e] do
            count := count+1;
            if coeffs[j] eq 0 then
                continue j;
            end if;
            word := word*siegslps[count]^Integers()!coeffs[j];
        end for;
            
        // and we are done here
        return word;      
    end if;    

    // We are done for Omega
    if type eq "Omega" then return word; end if;
    
    /* Now we need to handle the [e1,f1]-entry. we need to calculate 
       how much the computation so far contributed to this entry (offset). 
       There is a lemma in my paper that explains the calculation here */
      
    offset := 0;
    for i in [1..wittindex-1] do 
        case type:
           when "Sp": offset := offset+vec[i]*vec[d-i-1];
           when "SU": offset := offset-vec[i]*vec[d-i-1-wittdefect]^q0;
        end case;                   
    end for;

    /* In case of SU( odd, q ) offset will have to be modified further.
       See the paper for the theory. */
    if IsOdd( d )  then 
        offs := 0; coeff := 0;
        for i in [0..e-1] do
            exp := Integers()!coeffs[i+1];
            // l is the [e1,f1]-entry 
            if IsOdd( q ) then
                l := 1/2*z^(i*(-q0-1));
            else
                l := z^(-q0-i*(q0+1)); 
            end if;
            b := z^(i*(q0-2));
            l := exp*l+Binomial( exp, 2 )*b*b^q0; 
            offs := offs + l + case< IsOdd( q ) | true: coeff^q0*exp*b, 
                    default: coeff*exp*b^q0 >;
            coeff := coeff+coeffs[i+1]*b;
        end for;

        offset := offset-case< IsOdd( q ) | true: offs^q0, default: offs >;
    end if;
    
    /* lastel is the element we need to produce with a transvection.
       it is vec[#vec-1]-offset */
    lastel := vec[d-1-wittdefect]-offset;
    if lastel eq 0 then
        return word;
    end if;
   
    if type eq "SU" and IsOdd( q ) then
        lastel := lastel*z^Round(-(q0+1)/2);
    end if;

    // set up the basis
    case type:
      when "Sp": 
          bas := [ z^(2*i) : i in [0..e-1]];
      when "SU": 
          bas := [ z^(-2*(q0+1)*i) : i in [0..e0-1]];
          bas := bas cat [z^((q0+1)*i+1) : i in [0..e0-1]];
    end case;

    vec := CoordinatesOfElinBasis( G, bas, lastel );

    // finally modify myslp
    for j in [1..e0] do
        count := count+1;
        if vec[j] eq 0 then
            continue j;
        end if;
        
        word := word*siegslps[count]^Integers()!vec[j];
    end for; 
        
    return word;
end function;

