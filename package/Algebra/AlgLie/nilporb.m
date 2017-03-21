freeze;

//////////////////////////////////////////////////////////////////////////////////////

declare attributes NilpOrbAlgLie: WeightedDynkinDiagram, SL2Triple, AmbientLieAlgebra, 
Representative, Partition;

declare attributes RootDtm: IsomorphismToStandardSCDtm;

declare attributes AlgLie: SigTable, NilpotentOrbits;

weighted_dyn_diags:= function( type, rank )

      if type eq "A" and rank ge 1 then

         part:= Partitions( rank+1 );
         diags:= [ ];
         for p in part do
             d:= [ ];
             for k in p do
                 d cat:= [ k -2*(i-1)-1 : i in [1..k] ];
             end for;
             Sort(~d);
             h:= Reverse( d );
             Append( ~diags, [ h[i]-h[i+1] : i in [1..rank] ] );
         end for;

         return diags, part;
  
      elif type eq "B" and rank ge 2 then

         part:= Partitions( 2*rank+1 );
         new:= [ ];
         for p in part do
             q:= [ ];
             cur:= p[1];
             k:= 1;
             m:= 0;
             while k le #p do
                m:= m+1;
                if k lt #p then
                   if p[k+1] ne cur then
                      Append( ~q, [ cur, m ] );
                      cur:= p[k+1];
                      m:= 0;
                   end if;
                end if;
                k:= k+1;
             end while;
             Append( ~q, [ cur,m ] );
             good:= true;
             for k in [1..#q] do           
                 if IsEven(q[k][1]) and not IsEven(q[k][2]) then
                    good:= false;    
                    break k;
                 end if;
             end for;
             if good then
                Append( ~new, p );
             end if;
         end for;
         part:= new;

         diags:= [ ];
         for p in part do
             d:= [ ];
             for k in p do
                 d cat:= [ k-2*(i-1)-1 : i in [1..k] ];
             end for;
             // Get rid of a zero;
             for k in [1..#d] do
                 if d[k] eq 0 then
                    Remove( ~d, k );
                    break k;
                 end if;
             end for;
             Sort(~d);
             d:= Reverse( d );
             h:= [ d[i] : i in [1..rank] ];
             diag:= [ h[i]-h[i+1] : i in [1..rank-1] ];
             Append( ~diag, h[rank] );
             Append( ~diags, diag );
         end for;

         return diags,part;

      elif type eq "C" and rank ge 2 then     

           part:= Partitions( 2*rank );
           new:= [ ];
           for p in part do
               q:= [ ];
               cur:= p[1];
               k:= 1;
               m:= 0;
               while k le #p do
                  m:= m+1;
                  if k lt #p then
                     if p[k+1] ne cur then
                        Append( ~q, [ cur, m ] );
                        cur:= p[k+1];
                        m:= 0;
                     end if;
                  end if;
                  k:= k+1;
               end while;
               Append( ~q, [ cur,m ] );
               good:= true;
               for k in [1..#q] do           
                  if IsOdd(q[k][1]) and not IsEven(q[k][2]) then
                     good:= false;
                     break k;
                  end if;
               end for;
               if good then
                  Append( ~new, p );
               end if;
           end for;

           part:= new;
           diags:= [ ];
           for p in part do
               d:= [ ];
               for k in p do
                   d cat:= [ k -2*(i-1)-1 : i in [1..k] ];
               end for;
               Sort(~d);
               d:= Reverse( d );
               h:= [ d[i] : i in [1..rank] ];
               diag:= [ h[i]-h[i+1] : i in [1..rank-1] ];
               Append( ~diag, 2*h[rank] );
               Append( ~diags, diag );
           end for;

           return diags, part;

      elif type eq "D" and rank ge 4 then

           part:= Partitions( 2*rank );
           new:= [ ];
           for p in part do
               q:= [ ];
               cur:= p[1];
               k:= 1;
               m:= 0;
               while k le #p do
                  m:= m+1;
                  if k lt #p then
                     if p[k+1] ne cur then
                        Append( ~q, [ cur, m ] );
                        cur:= p[k+1];
                        m:= 0;
                     end if;
                  end if;
                  k:= k+1;
               end while;
               Append( ~q, [ cur,m ] );
               good:= true;
               for k in [1..#q] do           
                   if IsEven(q[k][1]) and not IsEven(q[k][2]) then
                      good:= false;
                      break k;
                   end if;
               end for;

               if good then
                  Append( ~new, p );
               end if;
           end for;

           part:= new;
           diags:= [ ];
           new:= [ ];
           for p in part do
               is_very_even:= &and[ IsEven(u) : u in p ];
               d:= [ ];
               for k in p do
                   d cat:= [ k -2*(i-1)-1 : i in [1..k] ];
               end for;
               Sort(~d);
               d:= Reverse( d );
               h:= [ d[i] : i in [1..rank] ];
               if not is_very_even then
                  diag:= [ h[i]-h[i+1] : i in [1..rank-1] ];
                  Append( ~diag, h[rank-1]+h[rank] );
                  Append( ~diags, diag );
                  Append( ~new, p );
               else
                  if rank mod 4 eq 0 then a:= 0; else a:= 2; end if;
                  b:= 2-a;
                  diag:= [ h[i]-h[i+1] : i in [1..rank-2] ];
                  Append( ~diag, a ); Append( ~diag, b ); 
                  Append( ~diags, diag );
                  Append( ~new, p );
                  diag:= [ h[i]-h[i+1] : i in [1..rank-2] ];
                  Append( ~diag, b ); Append( ~diag, a ); 
                  Append( ~diags, diag );
                  Append( ~new, p );
               end if;
           end for;

           return diags,new;

      elif type eq "E" and rank eq 6 then
         return [ [0,1,0,0,0,0], [1,0,0,0,0,1], [0,0,0,1,0,0], 
                  [0,2,0,0,0,0], [1,1,0,0,0,1], [2,0,0,0,0,2], [0,0,1,0,1,0],
                  [1,2,0,0,0,1], [1,0,0,1,0,1], [0,1,1,0,1,0], [0,0,0,2,0,0], 
                  [2,2,0,0,0,2], [0,2,0,2,0,0], [1,1,1,0,1,1], [2,1,1,0,1,2], 
                  [1,2,1,0,1,1], [2,0,0,2,0,2], [2,2,0,2,0,2], [2,2,2,0,2,2], 
                  [2,2,2,2,2,2] ], [];
      elif type eq "E" and rank eq 7 then
           return [ [1,0,0,0,0,0,0], [0,0,0,0,0,1,0], [0,0,0,0,0,0,2], [0,0,1,0,0,0,0],
                  [2,0,0,0,0,0,0], [0,1,0,0,0,0,1], [1,0,0,0,0,1,0], [0,0,0,1,0,0,0], 
                  [2,0,0,0,0,1,0], [0,0,0,0,0,2,0], [0,2,0,0,0,0,0], [2,0,0,0,0,0,2],
                  [0,0,1,0,0,1,0], [1,0,0,1,0,0,0], [0,0,2,0,0,0,0], [1,0,0,0,1,0,1],
                  [2,0,2,0,0,0,0], [0,1,1,0,0,0,1], [0,0,0,1,0,1,0], [2,0,0,0,0,2,0],
                  [0,0,0,0,2,0,0], [2,0,0,0,0,2,2], [2,1,1,0,0,0,1], [1,0,0,1,0,1,0],
                  [2,0,0,1,0,1,0], [0,0,0,2,0,0,0], [1,0,0,1,0,2,0], [1,0,0,1,0,1,2],
                  [2,0,0,0,2,0,0], [0,1,1,0,1,0,2], [0,0,2,0,0,2,0], [2,0,2,0,0,2,0], 
                  [0,0,0,2,0,0,2], [0,0,0,2,0,2,0], [2,1,1,0,1,1,0], [2,1,1,0,1,0,2],
                  [2,0,0,2,0,0,2], [2,1,1,0,1,2,2], [2,0,0,2,0,2,0], [2,0,2,2,0,2,0],
                  [2,0,0,2,0,2,2], [2,2,2,0,2,0,2], [2,2,2,0,2,2,2], [2,2,2,2,2,2,2] ], [];
      elif type eq "E" and rank eq 8 then
           return [ [0,0,0,0,0,0,0,1], [1,0,0,0,0,0,0,0], [0,0,0,0,0,0,1,0], [0,0,0,0,0,0,0,2],
                  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,1], [0,0,0,0,0,1,0,0], [1,0,0,0,0,0,0,2],
                  [0,0,1,0,0,0,0,0], [2,0,0,0,0,0,0,0], [1,0,0,0,0,0,1,0], [0,0,0,0,0,1,0,1],
                  [0,0,0,0,0,0,2,0], [0,0,0,0,0,0,2,2], [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,1],
                  [0,1,0,0,0,0,1,0], [1,0,0,0,0,1,0,0], [2,0,0,0,0,0,0,2], [0,0,0,1,0,0,0,0], 
                  [0,1,0,0,0,0,1,2], [0,2,0,0,0,0,0,0], [1,0,0,0,0,1,0,1], [1,0,0,0,1,0,0,0],
                  [1,0,0,0,0,1,0,2], [0,0,0,1,0,0,0,1], [0,0,0,0,0,2,0,0], [2,0,0,0,0,1,0,1],
                  [0,0,0,1,0,0,0,2], [0,0,1,0,0,1,0,0], [0,2,0,0,0,0,0,2], [2,0,0,0,0,0,2,0],
                  [2,0,0,0,0,0,2,2], [0,0,0,1,0,0,1,0], [1,0,0,1,0,0,0,1], [0,0,1,0,0,1,0,1],
                  [0,1,1,0,0,0,1,0], [1,0,0,0,1,0,1,0], [0,0,0,1,0,1,0,0], [1,0,0,0,1,0,1,2],
                  [0,0,0,0,2,0,0,0], [2,0,0,0,0,2,0,0], [0,1,1,0,0,0,1,2], [1,0,0,1,0,1,0,0],
                  [0,0,0,1,0,1,0,2], [2,0,0,0,0,2,0,2], [0,0,0,0,2,0,0,2], [2,1,1,0,0,0,1,2],
                  [2,0,0,0,0,2,2,2], [1,0,0,1,0,1,0,1], [1,0,0,1,0,1,1,0], [1,0,0,1,0,1,0,2],
                  [2,0,0,1,0,1,0,2], [0,0,0,2,0,0,0,2], [2,0,0,0,2,0,0,2], [1,0,0,1,0,1,2,2], 
                  [0,1,1,0,1,0,2,2], [0,0,0,2,0,0,2,0], [2,1,1,0,1,1,0,1], [0,0,0,2,0,0,2,2],
                  [2,1,1,0,1,0,2,2], [2,0,0,2,0,0,2,0], [2,0,0,2,0,0,2,2], [2,1,1,0,1,2,2,2],
                  [2,0,0,2,0,2,0,2], [2,0,0,2,0,2,2,2], [2,2,2,0,2,0,2,2], [2,2,2,0,2,2,2,2],
                  [2,2,2,2,2,2,2,2] ], [];
      elif type eq "F" and rank eq 4 then
           return [ [1,0,0,0], [0,0,0,1], [0,1,0,0], [2,0,0,0], [0,0,0,2],
                    [0,0,1,0], [2,0,0,1], [0,1,0,1], [1,0,1,0], [0,2,0,0], [2,2,0,0],
                    [1,0,1,2], [0,2,0,2], [2,2,0,2], [2,2,2,2] ], [];
      elif type eq "G" and rank eq 2 then
           return [ [1,0], [0,1], [0,2], [2,2] ], []; 
      end if;

end function;

intrinsic IsomorphismToStandardSCDtm( R::RootDtm ) -> SeqEnum
{ Sequence describing the isomorphism of R to a standard root datum.}

    // Let a be the result, and alpha_1,...,alpha_r the simple roots of R,
    // then alpha_a[1],...,alpha_a[r] are the simple roots in "standard" order.

    if assigned R`IsomorphismToStandardSCDtm then
       return R`IsomorphismToStandardSCDtm;
    end if;

    S:= RootDatum( CartanName(R) : Isogeny:= "SC" );
    b,p:= IsIsomorphic( S, R );

    R`IsomorphismToStandardSCDtm:= p;

    return p;

end intrinsic;

intrinsic AmbientLieAlgebra( o::NilpOrbAlgLie ) -> AlgLie
{ The Lie algebra in which the orbit lies. }

   return o`AmbientLieAlgebra;

end intrinsic;

intrinsic NilpotentOrbit( L::AlgLie, wd::SeqEnum ) -> NilpOrbAlgLie
{ Create the nilpotent orbit in L with weighted Dynkin diagram wd. } 

    R:= RootDatum(L);
    require #wd eq Rank(R): "The weighted Dynkin diagram has to have length equal to 
                              the rank of the root datum.";
    o:= CreateNilpOrbAlgLie( R );
    o`WeightedDynkinDiagram:= wd;
    o`AmbientLieAlgebra:= L;
    return o;    

end intrinsic;

intrinsic NilpotentOrbit( L::AlgLie, x::AlgLieElt ) -> NilpOrbAlgLie
{ Create the nilpotent orbit in L with representative x. } 

    R:= RootDatum(L);
    require x in L: "The element x does not lie in the Lie algebra L.";
    o:= CreateNilpOrbAlgLie( R );
    o`Representative:= x;
    o`AmbientLieAlgebra:= L;
    return o;    

end intrinsic;

intrinsic NilpotentOrbits( L::AlgLie ) -> SeqEnum
{ Get all nilpotent orbits of the simple Lie algebra L. }

    if assigned L`NilpotentOrbits then
       return L`NilpotentOrbits;
    end if;

    _,_,_,C:= RootSystem(L);
    R:= RootDatum( C : Isogeny:= "SC" );
    require IsSemisimple(R) : "This function is only implemented for simple Lie algebras in 
                               characteristic 0.";
    require Characteristic( BaseField(L) ) eq 0: 
        "This function is only implemented for simple Lie algebras in 
                               characteristic 0.";
    require IsIrreducible(R) : "This function is only implemented for simple Lie algebras in 
                               characteristic 0.";

    p:= IsomorphismToStandardSCDtm(R);
    type:= CartanName( R )[1];
    rank:= Rank( R );

    wdd, parts:= weighted_dyn_diags( type, rank );

    orbs:= [ ];
    for k in [1..#wdd] do
        wd:= wdd[k];
        if not &and[ IsZero(u) : u in wd ] then
           w0:= [ ];
           for i in [1..rank] do
               w0[p[i]]:= wd[i];
           end for;
           o:= NilpotentOrbit( L, w0 );
           if #parts gt 0 then o`Partition:= parts[k]; end if;
           Append( ~orbs, o );
        end if;
    end for;
    L`NilpotentOrbits:= orbs;
    return orbs;

end intrinsic;

intrinsic Partition( o::NilpOrbAlgLie ) -> SeqEnum
{ The partition corresponding to the orbit, for Lie algebras of classical type.}

    if assigned o`Partition then
       return o`Partition;
    end if;
    L:= AmbientLieAlgebra( o );
    R:= RootDatum( L );
    require IsIrreducible(R) : "This function is only implemented for nilpotent orbits in 
                                simple Lie algebras.";
    type:= CartanName( R )[1];
    require type in ["A","B","C","D"] : "Partitions are only defined for nilpotent orbits
                                         in Lie algebras of classical type.";

    orbs:= NilpotentOrbits(L);
    wd:= WeightedDynkinDiagram(o);

    pos:= 0;
    for i in [1..#orbs] do 
        if WeightedDynkinDiagram(orbs[i]) eq wd then
           pos:= i; break i;
        end if;
    end for;

    require pos gt 0 : "The weighted Dynkin diagram of the orbit does not appear to correspond
                        to a genuine nilpotent orbit.";

    p:= orbs[pos]`Partition;
    o`Partition:= p;
    return p;

end intrinsic;

    
intrinsic IsGenuineWeightedDynkinDiagram( L::AlgLie, wd::SeqEnum ) -> BoolElt, SeqEnum
{ True iff wd is a weighted Dynkin diagram corresponding to a nilpotent orbit of L. }

    require Rank( RootDatum(L) ) eq #wd: "The sequence must be of length equal to the 
                                          rank of the Lie algebra.";
    _,rv,_,C:= RootSystem(L);
    C:= Matrix( Rationals(), C );
    _,_,hh:= CanonicalGenerators( L );
    c:= Vector( Rationals(), wd )*(Transpose(C))^-1;
    h:= &+[ c[i]*hh[i] : i in [1..#hh] ];
    g2:= [ ];
    gm:= [ ];
    g0:= hh;
    for v in rv do
        hv:= h*v;
        if hv eq 2*v then
           Append( ~g2, v );
        elif hv eq -2*v then
           Append( ~gm, v );
        elif IsZero(hv) then
           Append( ~g0, v );
        end if;
    end for;

    if #g2 eq 0 then
       return false, [ Zero(L), Zero(L), Zero(L) ];
    end if;

    Omega:= [1..Dimension(L)];
    found:= false;  // find a dense orbit in g2
    VL:= VectorSpace( BaseField(L), Dimension(L) );
    while not found do
        cf:= [ Random(Omega) : u in g2 ];
        e:= &+[ cf[i]*g2[i] : i in [1..#g2] ];
        sp:= sub< VL | [ VL!Eltseq(u*e) : u in g0 ] >;
        if Dimension(sp) eq #g2 then
           found:= true;
        end if;
    end while;

    // now make e a bit nicer...
    for i in [1..#cf] do
        done:= false;
        k:= 0;
        while not done do
           cf[i]:= k;
           e:= &+[ cf[i]*g2[i] : i in [1..#g2] ];
           sp:= sub< VL | [ VL!Eltseq(u*e) : u in g0 ] >;
           if Dimension(sp) eq #g2 then
              done:= true;
           else
              k:= k+1;
           end if;
        end while;
    end for;

    // next see whether there is a matching f...
    sp:= VectorSpaceWithBasis( [ VL |  VL!Eltseq(b) :  b in g0 ]);    
    eqns:= Matrix( BaseField(L), [ Coordinates( sp, VL!Eltseq(e*u) ) : u in gm ] );
    lhs:= Vector( BaseField(L), Coordinates( sp, VL!Eltseq(h) ) );
    b,sol:= IsConsistent( eqns, lhs );
    if not b then
       return b,[Zero(L),Zero(L),Zero(L)];
    end if;
    f:= &+[ sol[i]*gm[i] : i in [1..#gm] ];
       
    return b, [f,h,e];

    
end intrinsic;


intrinsic SL2Triple( o::NilpOrbAlgLie ) -> SeqEnum
{ Get an sl2-triple corresponding to the nilpotent orbit o. }

    if assigned o`SL2Triple then
       return o`SL2Triple;
    end if;

    b,t:= IsGenuineWeightedDynkinDiagram( AmbientLieAlgebra(o), WeightedDynkinDiagram(o) );
    require b : "The weighted Dynkin diagram of the orbit does not correspond to a 
                 genuine nilpotent orbit.";
       
    return t;

end intrinsic;


intrinsic SigTable( L::AlgLie ) -> List
{ The signature table of the simple Lie algebra. } 

    if assigned L`SigTable then
       return L`SigTable;
    end if;

    R:= RootDatum(L);
    require IsIrreducible(R) : "This function is only implemented for simple Lie algebras.";

    type:= CartanName( R )[1];
    if type ne "D" then

       V:= VectorSpace( Rationals(), Rank(R) );
       pR:= PositiveRoots(R);
       sp:= VectorSpaceWithBasis( [ V!Eltseq(pR[i]) : i in [1..Rank(R)] ] );
       orb:= NilpotentOrbits(L);
       dimTab:= [ ];
       for o in orb do
           wd:= WeightedDynkinDiagram(o);
           dim:= [ ];
           for p in pR do
               cf:= Coordinates( sp, V!Eltseq(p) );
               u:= &+[ cf[i]*wd[i] : i in [1..#wd] ]+1;
               u:= Integers()!u;
               if IsDefined( dim, u ) then
                  dim[u] +:= 1;
               else
                  dim[u]:= 1;
               end if;
           end for;
           for i in [1..#dim] do
               if not IsDefined( dim, i ) then dim[i]:= 0; end if;
           end for;
           dim[1]:= 2*dim[1]+Rank(R);
           Append( ~dimTab, dim );
       end for;

       L`SigTable:= [* "notD", dimTab *];
       return L`SigTable;

    else

       _,_,_,C:= RootSystem(L);
       R:= RootDatum( C : Isogeny:= "SC" );
       p:= IsomorphismToStandardSCDtm( R );
       w1:= [ 0 : i in [1..Rank(R)] ];
       w1[ p[1] ]:= 1;
       V1:= HighestWeightModule( L, w1 );
       orbs:= NilpotentOrbits( L );
       dims1:= [ ];
       for o in orbs do
           h:= SL2Triple(o)[2];
           mh:= ActionMatrix( V1, h ); // we know that this matrix is diagonal...
           dim:= [Integers()| ];
           for i in [1..NumberOfRows(mh)] do
               k:= Integers()!mh[i][i];
               if k ge 0 then
                  if not IsDefined( dim, k+1 ) then
                     dim[k+1]:= 1;
                  else
                     dim[k+1] +:= 1;
                  end if;
               end if;
           end for;
           for i in [1..#dim] do
               if not IsDefined( dim, i ) then dim[i]:= 0; end if;
           end for;
           Append( ~dims1, dim );
       end for;

       w2:= [ 0 : i in [1..Rank(R)] ];
       w2[ p[#p] ]:= 1;
       V2:= HighestWeightModule( L, w2 );
       orbs:= NilpotentOrbits( L );
       dims2:= [ ];
       for o in orbs do
           h:= SL2Triple(o)[2];
           mh:= ActionMatrix( V2, h ); // we know that this matrix is diagonal...
           dim:= [Integers()| ];
           for i in [1..NumberOfRows(mh)] do
               k:= Integers()!mh[i][i];
               if k ge 0 then
                  if not IsDefined( dim, k+1 ) then
                     dim[k+1]:= 1;
                  else
                     dim[k+1] +:= 1;
                  end if;
               end if;
           end for;
           for i in [1..#dim] do
               if not IsDefined( dim, i ) then dim[i]:= 0; end if;
           end for;
           Append( ~dims2, dim );
       end for;

       L`SigTable:= [* "isD", dims1, V1, dims2, V2 *];
       return L`SigTable;

    end if;


end intrinsic;


intrinsic SL2Triple( L::AlgLie, e::AlgLieElt ) -> SeqEnum
{ Get an sl2-triple with e as nilpositive element. }

    n:= Dimension(L);
    F:= BaseField(L);
    T:= BasisProducts( L : Rep:= "Sparse" );
    xc:= Coordinates( L, e );
    eqs:= ZeroMatrix( F, 2*n, 2*n );

    // First we try to find elements z and h such that [x,z]=h
    // and [h,x]=2x (i.e., such that two of the three defining equations
    // of sl_2 are satisfied).
    // This results in a system of 2n equations for 2n variables.

    for t in T do
        i:= t[1]; j:= t[2]; l:= t[3];
        eqs[i][l] +:= xc[j]*t[4];
        eqs[n+i][n+l] +:= xc[j]*t[4];
    end for;
    for i in [1..n] do 
     eqs[n+i][i]:= One( F );
    end for;

    b:= [];
    for i in [1..n] do
      b[i]:= Zero( F );
      b[n+i]:= 2*One( F )*xc[i];
    end for;

    isc, v:= IsConsistent( eqs, Vector( F, b ) );
    require isc : "There is no sl2 containing the given element.";

    z:= L![ v[i] : i in [1..n] ];
    h:= L![ v[n+i] : i in [1..n] ];

    R:= Centralizer( L, e );

    // ad h maps R into R. H will be the matrix of that map.

    H:= [ Coordinates( R, R!(h*L!R.i) ) : i in [1..Dimension(R)] ];
    H:= Matrix( F, H );

    // By the proof of the lemma of Jacobson-Morozov (see Jacobson,
    // Lie Algebras, p. 98) there is an element e1 in R such that
    // (H+2)e1=e0 where e0=[h,z]+2z.
    // If we set y=z-e1 then x,h,y will span a subalgebra of L
    // isomorphic to sl_2.

    H:= H+2*IdentityMatrix( F, Dimension( R ) );

    e0:= Coordinates( R, R!(h*z + 2*z) );
    isc,e1:= IsConsistent( H, Vector( F, e0 ) );
    require isc : "There is no sl2 containing the given element.";

    f:= z- L!(R!e1);

    return [f,h,e];


end intrinsic;

intrinsic Representative( o::NilpOrbAlgLie ) -> AlgLieElt
{ A representative of the orbit. }

    if assigned o`Representative then
       return o`Representative;
    end if;

    e:= SL2Triple(o)[3];
    o`Representative:= e;
    return e;

end intrinsic;

intrinsic WeightedDynkinDiagram( o::NilpOrbAlgLie ) -> SeqEnum
{ Return the weighted Dynkin diagram of the nilpotent orbit.}

    // o has either been created by giving a weighted Dynkin diagram, or 
    // a representative. In the first case it is easy; in the second case
    // we have to work.

    if assigned o`WeightedDynkinDiagram then
       return o`WeightedDynkinDiagram;
    end if;

    L:= AmbientLieAlgebra( o );
    sig:= SigTable(L);
    e:= Representative( o  );
    h:= SL2Triple( L, e )[2];

    if sig[1] eq "notD" then

       k:= 0;
       adh:= Matrix( BaseField( L ), AdjointMatrix( L, h ) );
       I:= IdentityMatrix( BaseField(L), Dimension(L) );
       C:= Centralizer( L, h );
       dim:= [ Dimension(C) ];
       sum:= 0;
       while Dimension(C)+2*sum lt Dimension(L) do
          k:= k+1;
          d:= Dimension(Kernel( adh-k*I ) );
          Append( ~dim, d );
          sum +:= d;
       end while;
       pos:= Index( sig[2], dim ); 
       o`WeightedDynkinDiagram:= WeightedDynkinDiagram(NilpotentOrbits(L)[pos]);
    else

       mh:= ActionMatrix( sig[3], h );
       dim:= [Integers()| ];
       r:= Roots( CharacteristicPolynomial( mh ) );

       for t in r do 
           k:= Integers()!t[1];
           if k ge 0 then
              dim[k+1]:= Integers()!t[2];
           end if;
       end for;       
       for i in [1..#dim] do 
           if not IsDefined( dim, i ) then dim[i]:= 0; end if;
       end for;

       inds:= [ ];
       for i in [1..#sig[2]] do
           if sig[2][i] eq dim then
              Append( ~inds, i );
           end if;
       end for;
       if #inds eq 1 then
          o`WeightedDynkinDiagram:= WeightedDynkinDiagram(NilpotentOrbits( L )[inds[1]]);
       end if;

       mh:= ActionMatrix( sig[5], h );
       dim:= [Integers()| ];
       r:= Roots( CharacteristicPolynomial( mh ) );

       for t in r do 
           k:= Integers()!t[1];
           if k ge 0 then
              dim[k+1]:= Integers()!t[2];
           end if;
       end for;       
       for i in [1..#dim] do 
           if not IsDefined( dim, i ) then dim[i]:= 0; end if;
       end for;

       for i in [1..#sig[4]] do
           if i in inds and sig[4][i] ne dim then
              pos:= Index( inds, i );
              Remove( ~inds, pos );
           end if;
       end for;

       o`WeightedDynkinDiagram:= WeightedDynkinDiagram(NilpotentOrbits( L )[inds[1]]);

    end if;
    return o`WeightedDynkinDiagram;


end intrinsic;
