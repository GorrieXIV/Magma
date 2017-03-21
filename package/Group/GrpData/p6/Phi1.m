freeze;
 
/* do not use intrinsic AbelianGroup since it limits prime */

Phi1 := function(p)

F := FreeGroup(6);
A := [F.i: i in [1..6]];
family := &cat[[(A[i], A[j]) = Id (F) : j in [i + 1..6]]: i in [1..6]];

Pres := [];

 // [6] 
 Q := quo < F | family, [
                   A[6]^p = A[5],
                   A[5]^p = A[4],
                   A[4]^p = A[3],
                   A[3]^p = A[2],
                   A[2]^p = A[1],
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,6));
 
 // [5,1] 
 Q := quo < F | family, [
                   A[6]^p = A[4],
                   A[5]^p = Id(F),
                   A[4]^p = A[3],
                   A[3]^p = A[2],
                   A[2]^p = A[1],
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,5));
 
 // [4,2] 
 Q := quo < F | family, [
                   A[6]^p = A[4],
                   A[5]^p = A[3],
                   A[4]^p = A[2],
                   A[3]^p = Id(F),
                   A[2]^p = A[1],
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,4));
 
 // [4,1,1] 
 Q := quo < F | family, [
                   A[6]^p = A[3],
                   A[5]^p = Id(F),
                   A[4]^p = Id(F),
                   A[3]^p = A[2],
                   A[2]^p = A[1],
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,4));
 
 // [3,3] 
 Q := quo < F | family, [
                   A[6]^p = A[4],
                   A[5]^p = A[3],
                   A[4]^p = A[2],
                   A[3]^p = A[1],
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,3));

 // [3,2,1] 
 Q := quo < F | family, [
                   A[6]^p = A[3],
                   A[5]^p = A[2],
                   A[4]^p = Id(F),
                   A[3]^p = A[1],
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,3));

 // [3,1,1,1] 
 Q := quo < F | family, [
                   A[6]^p = A[2],
                   A[5]^p = Id(F),
                   A[4]^p = Id(F),
                   A[3]^p = Id(F),
                   A[2]^p = A[1],
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,3));

 // [2,2,2] 
 Q := quo < F | family, [
                   A[6]^p = A[3],
                   A[5]^p = A[2],
                   A[4]^p = A[1],
                   A[3]^p = Id(F),
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,2));

 // [2,2,1,1] 
 Q := quo < F | family, [
                   A[6]^p = A[2],
                   A[5]^p = A[1],
                   A[4]^p = Id(F),
                   A[3]^p = Id(F),
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,2));

 // [2,1,1,1,1] 
 Q := quo < F | family, [
                   A[6]^p = A[1],
                   A[5]^p = Id(F),
                   A[4]^p = Id(F),
                   A[3]^p = Id(F),
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,2));

 // [1,1,1,1,1,1] 
 Q := quo < F | family, [
                   A[6]^p = Id(F),
                   A[5]^p = Id(F),
                   A[4]^p = Id(F),
                   A[3]^p = Id(F),
                   A[2]^p = Id(F),
                   A[1]^p = Id(F)
               ] >;
 Append (~Pres, pQuotient(Q,p,1));

return Pres;

end function;
