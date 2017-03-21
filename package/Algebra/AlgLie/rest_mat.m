freeze;

/*
  $Id: rest_mat.m 52911 2016-05-31 01:44:13Z allan $

  Code from Robert Zeier <robert.zeier@gmail.com> 2013-06-05

  See (e.g.) Section 2c of McKay/Patera/Sankoff:
  The computation of branching rules for representations of semisimple
  Lie algebras, in Beck/Kolman: Computers in nonassociative rings and algebras, 
  pp. 235-277 (1977)
*/

weights_sorted := function( R, hw )
    //copied and modified from magma2.19-6/package/Algebra/AlgLie/module.m 
    //(see ModuleData) by Robert Zeier
    ch,mm := DominantCharacter( R, hw );

    www := [ ];
    mults := [ ];
    W := CoxeterGroup( R );

    for i in [1..#ch] do
        o := [ Eltseq(x) : x in WeightOrbit(W, ch[i] : Basis:="Weight") ];
        www := www cat o;
        mults := mults cat [ mm[i] : k in [1..#o] ];
    end for;

    /*
     www:= {@ wt : wt in www @};
    */

    // `levels' will be a list of lists, and `levels[k]' is the list of
    // weights of level `k-1'.
    // `weights' will be the list of all weights, sorted according to level.
    // `wd' will be the list of the weights of the extended weight diagram,
    // also sorted according to level.
    // `levwd' will be the list of the levels of the elements of `wd'.

    rank := Rank( R );
    levels := [ [ hw ] ];
    weights := [ ];
    k := 1;
    wd := [ hw ];
    levwd := [ 0 ];
    posR := PositiveRoots(R : Basis:= "Weight");
    novar := #posR;
    posR := [ Eltseq( posR[i] ) : i in [1..novar] ];
    lcombs := PositiveRoots(R : Basis:= "Root");
    lcombs := [ Eltseq(lcombs[i]) : i in [1..novar] ];
    hts := [ &+lcombs[i] : i in [1..novar] ];

    while k le #levels do
        for i in [1..#levels[k]] do
            w := levels[k][i];
            for j in [1..#posR] do
                w1 := [ w[q] - posR[j][q] : q in [1..rank] ];
                lev := IntegerRing()!(k + hts[j]);
                if w1 in www then
                 //changed:
                    multiplicity := mults[Position(www,w1)]-1;
                    if IsDefined(levels, lev) then
                        if not w1 in levels[lev] then
                            Append(~levels[lev], w1);
                          //changed:
                            for l := 1 to multiplicity do
                                Append(~levels[lev], w1);
                            end for;
                        end if;
                    else
                        levels[lev] := [ w1 ];
                         //changed:
                        for l := 1 to  multiplicity do
                            Append(~levels[lev], w1);
                        end for;
                    end if;
                end if;
                if not w1 in wd then
                    Append(~wd, w1);
                    Append(~levwd, lev-1);
                end if;
            end for;
        end for;
        k := k+1;
    end while;

     // we have to sort the elements in dom according to level...
    f := function(a, b)
        if a lt b then return -1; end if;    
        if a eq b then return 0; end if;
        return 1;
    end function;

    /*
    Sort( ~levwd, f, ~p );
    wd1:= [ ];
    for i in [1..#wd] do
        j:= i^p;
        wd1[i]:= wd[j];
    end for;
    wd:= wd1;
    */

     //changed:
    for k in [1..#levels] do Sort(~levels[k],f); end for;
    for k in levels do weights cat:= k; end for;

    return weights;
end function;

intrinsic RestrictionMatrix(rd1::MonStgElt,wt1::SeqEnum,
    rd2::MonStgElt,wt2::SeqEnum) -> Mtrx
{The restriction matrix corresponding to the highest weights wt1 and wt2
 of the root data of types rd1 and rd2}
    RD := RootDatum(rd1 : Isogeny:="SC");
    rd := RootDatum(rd2 : Isogeny:="SC");
    require IsSemisimple(RD) : "first root datum is not semisimple";
    require IsSemisimple(rd) : "second root datum is not semisimple";
    M := Transpose(Matrix(weights_sorted(RD,wt1)));
    m := Transpose(Matrix(weights_sorted(rd,wt2)));
    sol1,sol2,sol3 := IsConsistent(M,m);
    require sol1 : "weight spaces are not consistent"; 
    return Transpose(sol2);
end intrinsic;

intrinsic RestrictionMatrix(rd1::MonStgElt,wt1::ModTupFldElt,
    rd2::MonStgElt,wt2::ModTupFldElt) -> Mtrx
{"} // "
    return RestrictionMatrix(rd1,Eltseq(wt1),rd2,Eltseq(rd2));
end intrinsic;

intrinsic RestrictionMatrix(rd1::RootDtm,wt1::SeqEnum,
    rd2::RootDtm,wt2::SeqEnum) -> Mtrx
{The restriction matrix corresponding to the highest weights wt1 and wt2
 of the root data rd1 and rd2}
    require IsSimplyConnected(rd1) : "first root datum is not simply connected";
    require IsSimplyConnected(rd2) : "second root datum is not simply connected";
    require IsSemisimple(rd1) : "first root datum is not semisimple";
    require IsSemisimple(rd2) : "second root datum is not semisimple";
    M := Transpose(Matrix(weights_sorted(rd1,wt1)));
    m := Transpose(Matrix(weights_sorted(rd2,wt2)));
    sol1,sol2,sol3 := IsConsistent(M,m);
    require sol1 : "weight spaces are not consistent"; 
    return Transpose(sol2);
end intrinsic;

intrinsic RestrictionMatrix(rd1::RootDtm,wt1::ModTupFldElt,
    rd2::RootDtm,wt2::ModTupFldElt) -> Mtrx
{"} // "
    return RestrictionMatrix(rd1,Eltseq(wt1),rd2,Eltseq(rd2));
end intrinsic;

intrinsic RestrictionMatrix(v1::LieRepDec, v2::LieRepDec) -> Mtrx
{The restriction matrix corresponding to the decompositions v1 and v2}
    require IsSemisimple(v1`R) : "root datum of first argument is not semisimple";
    require IsSemisimple(v2`R) : "root datum of second argument is not semisimple";
    w1, m1 := Weights(v1);
    w2, m2 := Weights(v2);
    require &+(m1) eq 1 : "first representation is not irreducible";
    require &+(m2) eq 1 : "second representation is not irreducible";
    w1 := [Eltseq(ChangeRing(j,Integers())) : j in w1];
    w2 := [Eltseq(ChangeRing(j,Integers())) : j in w2];
    M := Transpose(Matrix(weights_sorted(v1`R,Rep(w1))));
    m := Transpose(Matrix(weights_sorted(v2`R,Rep(w2))));
    sol1,sol2,sol3 := IsConsistent(M,m);
    require sol1 : "weight spaces are not consistent"; 
    return Transpose(sol2);
end intrinsic;


