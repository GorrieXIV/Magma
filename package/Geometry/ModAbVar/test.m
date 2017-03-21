freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: test.m
   DESC: try to crash the modular abelian varieties package.

   Creation: 01/31/04
      
 ***************************************************************************/

/*
> Attach("package/Geometry/ModAbVar/test.m");
> DecomposeRandomJZero(10);
> DecomposeRandomJOne(10);
> EndRandomJZero(10);
> DecomposeRandomJZero(20 : how_hard:=Random([1..8]) );
*/

intrinsic DecomposeRandomJZero(times::RngIntElt : how_hard:=2 )
{Compute random JZero(N)'s and decompose them over Q.}
    for t in [1..times] do 
       print "DecomposeRandomJZero -", t,"th try.";
       repeat
          N := Random([1..100*how_hard]);
          sign := Random([-1,0,1]);
          k := Random([2,4,6,8,10,12,14,16,18,20]);
       until N*k lt 50*how_hard;
       print "N=", N;
       print "k=", k;
       print "sign=", sign;
       J := JZero(N,k,sign);
       Decomposition(J);
    end for;
end intrinsic;

intrinsic DecomposeRandomJOne(times::RngIntElt)
{Compute random JOne(N)'s and decompose them over Q.}
    for t in [1..times] do 
       print "DecomposeRandomJOne -", t,"th try.";
       repeat
          N := Random([1..200]);
          sign := Random([-1,0,1]);
          k := Random([2,4,6,8,10,12,14,16,18,20]);
       until N*k lt 50;
       print "N=", N;
       print "k=", k;
       print "sign=", sign;
       J := JOne(N,k,sign);
       Decomposition(J);
    end for;
end intrinsic;


intrinsic EndRandomJZero(times::RngIntElt)
{Compute random JZero(N)'s and their endomorphism ring over Q.}
    for t in [1..times] do 
       print "EndRandomJZero -", t,"th try.";
       repeat
          N := Random([1..200]);
          sign := Random([-1,0,1]);
          k := Random([2,4,6,8,10,12,14,16,18,20]);
       until N*k lt 100;
       print "N=", N;
       print "k=", k;
       print "sign=", sign;
       J := JZero(N,k,sign);
       B := Basis(End(J));
      #B;
    end for;
end intrinsic;

