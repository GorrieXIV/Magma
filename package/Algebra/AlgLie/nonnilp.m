freeze;

//
//  IsNilpotent( L, x )
//
intrinsic IsNilpotent( L::AlgLie, x::AlgLieElt ) -> BoolElt
{ True if the element x of the Lie algebra L is nilpotent}

   require IsCoercible(L, x): "Argument 2 must be coercible into argument 1";
   M:= MatrixAlgebra( CoefficientRing(L), Dimension(L) )!AdjointMatrix( L, x );
   return M^Dimension(L) eq 0*M;

end intrinsic;


//
//  NonNilpotentElement( L )
//
intrinsic NonNilpotentElement( L::AlgLie ) -> AlgLieElt
{A non-nilpotent element of the Lie algebra L}

    // First rule out some trivial cases.
    n:= Dimension( L );
    if n eq 1 or n eq 0 then
      return Zero(L);
    end if;

    F:= CoefficientRing( L );

    if Characteristic( F ) ne 0 then

      // D will be a basis of a nilpotent subalgebra of L.
      if IsNilpotent( L, L.1 ) then
        D:= [ L.1 ];
      else
        return L.1;
      end if;

      // r will be the dimension of the span of D.
      // If r = n then L is nilpotent and hence does not contain
      // non nilpotent elements.
      r:= 1;
      V:= VectorSpace( F, Dimension( L ) );

      while r lt n do

        sp:= sub< V | [ V!Eltseq(D[i]) : i in [1..#D] ] >;

        // We first find an element b of L that does not lie in sp.
        found:= false;
        i:= 2;
        while not found do
          b:= L.i;
          if V!Eltseq(b) in sp then
            i:= i+1;
          else
            found:= true;
          end if;
        end while;

        // We now replace b by b * D[i] if
        // b * D[i] lies outside sp in order to ensure that
        // [b,sp] \subset sp.
        // Because sp is a nilpotent subalgebra we only need
        // a finite number of replacement steps.

        i:= 1;
        while i le r do
          c:= b*D[i];
          if V!Eltseq(c) in sp then
            i:= i+1;
          else
            b:= c;
            i:= 1;
          end if;
        end while;

        if IsNilpotent( L, b ) then
          Append( ~D, b );
          r:= r+1;
        else
          return b;
        end if;

      end while;

    else

      // Now char F =0.
      // In this case either L is nilpotent or one of the
      // elements $L.1, \ldots , L.n, L.i + L.j; 1 \leq i < j$
      // is non nilpotent.

      for i in [ 1 .. n ] do
        if not IsNilpotent( L, L.i ) then
          return L.i;
        end if;
      end for;

      for i in [ 1 .. n ] do
        for j in [ i+1 .. n ] do
          elm:= L.i+L.j;
          if not IsNilpotent( L, elm ) then
            return elm;
          end if;
        end for;
      end for;

    end if;

    // A non nilpotent element has not been found,
    // hence L is nilpotent.
    return Zero(L);

end intrinsic;


