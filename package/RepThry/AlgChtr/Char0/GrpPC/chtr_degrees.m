freeze;

AppendCollectedList := procedure( ~list1, list2 )
    local pair, toadd;
    for pair in list2 do
      toadd:= true;
      for i in [1..#list1] do
        if list1[i][1] eq pair[1] then
          list1[i][2] +:= pair[2];
          toadd:= false;
          break;
        end if;
      end for;
      if toadd then
        Append( ~list1, pair );
      end if;
    end for;
end procedure;

forward ProjectiveCharDegs;

CharDegs := func<G,q | ProjectiveCharDegs(G,Id(G),q) >;

ProjectiveCharDegs := function( G, z, q )
/* G is a finite soluble PC-group, z is an element in the centre of G,
 * q is 0 or a prime power.
 * Compute degrees of absolutely irreducible characters of G/<z> in
 * characteristic q which restrict to some particular faithful linear
 * character of <z>.  (It is irrelevant which one!) using algorithm of
 * S. Conlon (J. Symbolic Comput. 9, 1990, 551-570)
 * The result is returned as a list of pairs [d,m], meaning
 * there are m characters of degree d.
 * Code adapted from GAP4 functions attributed to H.U. Besche & T. Breuer
 */

    local og, oz, N, r, i, f, imz, hz, imc, hc, L, imp, hp, idgp, invrep, cp,
          hm, mg, k, imk, hk, c, ci, zn, t, p, P, O, orbs, stab;

    /*
    if not ( q eq 0 or IsPrime( q ) ) then
      error "<q> mut be zero or a prime" ;
    end if;
    */

    oz:= Order( z );

    // For abelian groups, there are only linear characters.
    if IsAbelian( G ) then
      og:= #G;
      if q ne 0 then
        while og mod q eq 0 do
          og:= og  div  q;
        end while;
      end if;
      return [ < 1, og div oz > ];
    end if;

    // Now `G' is not abelian.
    imz, hz := quo< G | sub<G|z> >;
    N:= MinimalNormalSubgroup(imz);

    // `N' is a normal subgroup such that `N div <z>' is a chief factor of `G'
    // of order `i' which is a power of `p'.
    i:= #N;
    f:= Factorisation( i );
    p:= f[1][1];
    N:= N @@ hz;

    if not IsAbelian( N ) then

      imc, hc := quo< G |  Centralizer( G, N ) >;
      
      c:= Complements( imc, N@hc );
      L := c[1] @@ hc;
      // L is a complement to N in G mod <z> which contains centralizer of N
      r:= p^(f[1][2] div 2); 
      return [ <x[1]*r,x[2] > : x in ProjectiveCharDegs( L, z, q ) ];
    end if;

    // `N' is abelian, `P' is its Sylow `p' subgroup.
    P:= SylowSubgroup( N, p );

    if p eq q then
      // Factor out `P' (lies in the kernel of the repr.)
      imp, hp := quo<G | P>;
      return ProjectiveCharDegs( imp, z@hp, q );
    elif i eq #P then
      // `z' is a p'-element, `P' is elementary abelian.
      // Find the character degrees of the factor group needed.
      imp, hp := quo<G | P>;
      r:= ProjectiveCharDegs( imp, z@hp, q );

      if p eq i then
        // `P' has order `p'.
        zn:= P.1;
        t:=  Centralizer( G, zn );
        i:= #G  div  #t;
        AppendCollectedList( ~r,
      [  < x[1]*i, x[2]*(p-1) div i > : x in ProjectiveCharDegs(t, zn*z, q) ]);
        return Sort(r);
      else
        // `P' has order strictly larger than `p'.
        // we need the contragredient operation of `G' on `P'.
        // `dg' will be the action matrices for this operation.
        m, im := GModule(G,P);
        dg := [ Transpose(ActionGenerator(m,i)^-1) : i in [1..Nagens(m)]];
        mg := sub< GL(Dimension(m),p) | dg >;
        /* We need to patch together an inverse map from mg to G
         * Unfortunately, mg may have eliminated generators!
         */
        idgp := [ Position(dg,mg.i) : i in [1..Ngens(mg)] ];
        invrep := hom< mg->G | [G.i : i in idgp] >;
        cp := Centraliser(G,P);
        /* Not really a homomorphism - it is the inverse map of the
         * representation affording the dual module of m.
         * of which the kernel is Centraliser(G,P)
         */
        
        orbs := [Representative(l).1 : l in LineOrbits(mg)];
        hm := Hom(VectorSpace(m),VectorSpace(GF(p),1));

        for orb in orbs do
          // `k' is the kernel of the character - pull back to G.
          k := Kernel(hm!Transpose(Matrix(orb)));
          k := sub<G | [(m!g) @@ im : g in Generators(k)] >;  

          stab:= Stabilizer( mg, sub<Parent(orb)|orb> );
          // pull back to G using invrep
          stab := sub<G | cp, [ s @ invrep : s in Generators(stab)] >;
          imk, hk:= quo< stab | k >;

          // `zn' is an element of `imk'.
          // Note that the image of `P' under `h' has order `p'.
          zn:= (P@hk).1 *  z@hk;

          // `c' is stabilizer of the character,
          // `ci' is the number of orbits of characters with equal kernels
          if p eq 2 then
            c  := imk;
            ci := 1;
          else
            c  := Centraliser( imk, zn );
            ci := #imk div #c;
          end if;
          k:= #G  div #stab * ci;
          AppendCollectedList( ~r,
           [ <x[1]*k, x[2]*(p-1) div ci> : x in  ProjectiveCharDegs(c, zn, q)]);

        end for;
        return Sort(r);
      end if;
    elif IsCyclic( P ) then
   // Choose a generator `zn' of `P'.
      zn := P.1;
      t  := Centraliser( G, zn );
      if G eq t then
       // `P' is a central subgroup of `G'.
        return [<x[1], x[2]*p> : x in ProjectiveCharDegs(G, zn*z, q)];
      else
        // `P' is not central in `G'.
        return [<x[1]*p, x[2]> : x in ProjectiveCharDegs(t, zn*z, q)];
      end if;
    end if;

    // `P' is the direct product of the Sylow `p' subgroup of `z'
    // and an elementary abelian `p' subgroup.
    O:= Omega( P, 1 );

    // `zn' is a generator of the intersection of <z> and `O'
    zn := z^(oz div p);
    r  := [];
    // we need the contragredient operation of `G' on `O'.
    // `dg' will be the action matrices for this operation.
    m, im := GModule(G,O);
    dg := [ Transpose(ActionGenerator(m,i)^-1) : i in [1..Nagens(m)]];
    mg := sub< GL(Dimension(m),p) | dg >;
    /* We need to patch together an inverse map from mg to G
     * Unfortunately, mg may have eliminated generators!
     */
    idgp := [ Position(dg,mg.i) : i in [1..Ngens(mg)] ];
    invrep := hom< mg->G | [G.i : i in idgp] >;
    cp := Centraliser(G,O);
    /* Not really a homomorphism - it is the inverse map of the
     * representation affording the dual module of m.
     * of which the kernel is Centraliser(G,P)
     */
        
    orbs := [Representative(l).1 : l in LineOrbits(mg)];
    hm := Hom(VectorSpace(m),VectorSpace(GF(p),1));
    // In this case the stabilizers of the kernels are already the
    // stabilizers of the characters.
    for orb in orbs do
      k := Kernel(hm!Transpose(Matrix(orb)));
      k := sub<G | [(m!g) @@ im : g in Generators(k)] >;  

      if not zn in k then
        // The kernel avoids `zn'.
        stab:= Stabilizer( mg, sub<Parent(orb)|orb> );
        //stab:= Stabilizer( mg, orb );
        // pull back to G using invrep
        stab := sub<G | cp, [ s @ invrep : s in Generators(stab)] >;
        imk, hk:= quo< stab | k >;

        t:= #G div #stab;
        AppendCollectedList( ~r,
          [ <x[1]*t, x[2]> : x in ProjectiveCharDegs(imk, z@hk, q) ]);
      end if;
    end for;
    return Sort(r);
end function;

degrees_from_character_table := function(G)
/* assumes table is sorted by degree */
    X := CharacterTable(G);
    degs := [Integers()|Degree(x) : x in X];
    res := [];
    this := degs[1]; count := 1;
    for i := 2 to #degs do
	if degs[i] eq this then count +:= 1;
	else
	    Append(~res, <this, count>);
	    this := degs[i]; count := 1;
	end if;
    end for;
    Append(~res, <this, count>);
    return res;
end function;

intrinsic CharacterDegrees(G::GrpPC) -> SeqEnum
{}
    if IsAbelian(G) then 
	return [ <1,#G> ];
    end if;
    if #FactoredOrder(G) eq 1 then
	p := FactoredOrder(G)[1,1];
	Q := CharacterDegreesPGroup(G);
	return [ <p^(i-1),Q[i]>:i in [1..#Q] | Q[i] gt 0 ];
    end if;
    return ProjectiveCharDegs(G, Id(G), 0);
end intrinsic;

intrinsic CharacterDegrees(G::GrpAb) -> []
{}
    require IsFinite(G): "Argument must be finite";
    return [<1,#G>];
end intrinsic;

intrinsic CharacterDegrees(G::GrpGPC) -> []
{}
    require IsFinite(G): "Argument must be finite";
    return CharacterDegrees(PCGroup(G));
end intrinsic;

intrinsic CharacterDegrees(G::GrpPerm) -> []
{}
    if IsSoluble(G) then
	return CharacterDegrees(PCGroup(G));
    end if;
    return degrees_from_character_table(G);
end intrinsic;

intrinsic CharacterDegrees(G::GrpMat) -> []
{The sequence [<d_1,c_1>,<d_2,c_2>, ...] where c_i is the number of irreducible characters of G with degree d_i for the finite group G}
    require IsFinite(G): "Argument must be finite";
    if IsSoluble(G) then
	return CharacterDegrees(PCGroup(G));
    end if;
    return degrees_from_character_table(G);
end intrinsic;

intrinsic CharacterDegrees(G::GrpPC, z::GrpPCElt, p::RngIntElt) -> SeqEnum
{When z is in Z(G) and p is prime or 0, return the character degree sequence
giving the number of absolutely irreducible characters of G in characteric p
lying over some faithful linear character of <z>}

    require p eq 0 or IsPrime(p):"Argument 3 must be a prime or zero";
    require z in Centre(G):"Argument 2 must be central in the group";
    return ProjectiveCharDegs(G, z, p);
end intrinsic;

intrinsic SymmetricCharacterDegrees(n::RngIntElt) -> SeqEnum
{The sequence [<d_1,c_1>,<d_2,c_2>, ...] where c_i is the number of irreducible characters of G with degree d_i for the G the symmetric group on n letters}
    local	degs, d2;
    require n gt 0: "Argument 1 must be positive";
    degs := {* NumberOfStandardTableaux(p): p in Partitions(n) *};
    d2 := MultisetToSet(degs);
    d2 := Sort(SetToSequence(d2));
    return [ <d, Multiplicity(degs, d)>: d in d2];
end intrinsic;
