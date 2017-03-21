freeze;

import "pgroup-unipotent.m": GetPFlagWithCache, PChiefSeriesGeneratorsWithCache;

/*
Dan Roozemond, Mar 2011.

While cleaning up *this* file (because there was some duplication with ^^ that
file, package/Group/GrpPC/pgrps/unipotent.m), I came across the following 
differences, and changed things so that:

* GetBaseForPGroup in *this* file was equivalent to PChiefSeriesGeneratorsWithCache
  in *that*, provided the latter is called with InitStr = "XB";

*/

FindPower := function(s, Y, weight)

   p := #PrimeField(BaseRing(Y));
   j0 := weight[1];
   j1 := weight[2];
   j2 := weight[3];
   F := BaseRing(Y);

   beta := -Eltseq(Y[j1, j0 + j1])[j2]/Eltseq(s[j1, j0 + j1])[j2];
   beta := IntegerRing()!beta;
   Y := Y*(s^beta);

   return beta, Y;
end function;

/* This part of the algorithm works by knocking out entries of Y using
   generators of least weight in S until Y is the identity matrix. */

KillEntries := function(Y, S, SSLP)

   yslp := Identity(Parent(SSLP[1]));

   /* Calculating the element of S with the least weight */
   weight := [<S[i], InternalMatrixWeight(S[i])> : i in [1..#S]];
   weights := [weight[i, 2] : i in [1..#S]];
   weight1 := [];
   for w in [1..#weight] do
      Append(~weight1, weight[w, 2, 1]);
   end for;
   j0 := Minimum(weight1);
   weight2 := [];
   for w in [1..#weight] do
      if weight[w, 2, 1] eq j0 then
         Append(~weight2, weight[w, 2, 2]);
      end if;
   end for;
   j1 := Minimum (weight2);
   weight3 := [];
   for w in [1..#weight] do
      if (weight[w, 2, 1] eq j0) and (weight[w, 2, 2] eq j1) then
         Append(~weight3, weight[w, 2, 3]);
      end if;
   end for;
   j2 := Minimum (weight3);

   while #S ne 0 do
      pos := Position(weights, [j0, j1, j2]);
      s := S[pos];
      sslp := SSLP[pos];
      beta, Y := FindPower(s, Y, [j0, j1, j2]);
      yslp := yslp * sslp^beta;
      Remove(~S, pos);
      Remove(~SSLP, pos);
      Remove(~weight, pos);
      if #S eq 0 then break; end if;

      weights := [weight[i, 2] : i in [1..#S]];
      weight1 := [];
      for w in [1..#weight] do
         Append(~weight1, weight[w, 2, 1]);
      end for;
      j0 := Minimum(weight1);
      weight2 := [];
      for w in [1..#weight] do
         if weight[w, 2, 1] eq j0 then
            Append(~weight2, weight[w, 2, 2]);
        end if;
      end for;
      j1 := Minimum (weight2);
      weight3 := [];
      for w in [1..#weight] do
         if (weight[w, 2, 1] eq j0) and (weight[w, 2, 2] eq j1) then
            Append(~weight3, weight[w, 2, 3]);
        end if;
      end for;
      j2 := Minimum (weight3);
   end while;

   return yslp;
end function;

/* Y is an element of the p-group K. 
   Return an slp for Y in the generators of K. */

MatrixPGroupWordInGen := function(Y, K: ComputeBase := true)

   q := #BaseRing(Y);
   V := VectorSpace(GF(q), Degree(Y));
   SSLP := WordGroup(K);

   /* trivial case */
   if Ngens(K) eq 0 then
      return SSLP!1;
   end if;

   /* we upper uni-triangularise the matrices */
   CB := GetPFlagWithCache(V, K);
   S := [K.i^CB : i in [1..Ngens(K)]];
   Y := Y^CB;

   /* should return false but cannot at present due to impinging on
      the other algorithms */
   if not IsUpperTriangular(Y) then return SSLP!1; end if;

   SSLP := [SSLP.i : i in [1..Ngens(SSLP)]];

   /* As the process for correcting all the matrix weights later on
      is not being carried out, you must carry out this step
      regardless of what ComputeBase is set to.  */

   S, SSLP := PChiefSeriesGeneratorsWithCache(K, S, SSLP, "XB");

   yslp := KillEntries(Y, S, SSLP);

   return yslp^-1;
end function;
