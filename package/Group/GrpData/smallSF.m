freeze;

/*
The file provides the functions:

 - SmallGroupSF(size,i)       - the ith group of order `size'.
 - SmallGroupsSF(size)        - all groups of order `size'.
 - NumberSmallGroupsSF(size)  - the number of groups of order `size'.
 - IdGroupSF(G)               - returns i so that G is isomorphic with
                                SmallGroupSF(|G|,i)

 where `size' and |G| must be a square free integer.

 The functions implement the special case of square-free orders within
 the more general case of cube-free orders described in the paper:
 Heiko Dietrich and Bettina Eick. On the groups of cube-free order.
 J. Algebra 292 (2005), pages 122-137.

*/

/* implementation of construction and identification of groups 
   of square-free order; adapted from Eick GAP code by 
   Eamonn O'Brien June 2007 */

CoefficientsMultiadic := function (ints, int)
   vec := [];
   for i in [#ints..1 by -1]  do
      vec[i] := (int mod ints[i]);
      int := (int div ints[i]);
   end for;
   return vec;
end function;

/* record of information on groups having square-free order size */

InfoRecSF := function (size)

   if size eq 1 then error "size must be at least 2"; end if;

   primes := Factorisation (size);
   lp := &+[primes[i][2]: i in [1..#primes]];
   primes := &cat[[p[1]: j in [1..p[2]]]: p in primes];

   // build up matrice of incidences for q mod p = 1
   M := MatrixAlgebra (Integers (), lp);
   mat := Zero (M);

   for i in [1 .. lp - 1] do
      for j in [i + 1 .. lp] do
        if primes[j] mod primes[i] eq 1 then
          mat[i][j] := 1;
        end if;
      end for;
   end for;

   kp_cand := [i : i in [1 .. lp] | 1 in Eltseq (mat[i])];

   SFrec := recformat <kp, kp_dim, kp_n_ops, kp_op_sp, number>;
   set := rec <SFrec | kp := [], number := 1>;
   Irec := recformat <primes, sets, number, roots>;
   inforec := rec <Irec | primes := primes, sets := [set]>;

   // run through all possible socles
   for i in [1 .. 2^#kp_cand - 1] do
      i_list := [0: x in primes];
      v := CoefficientsMultiadic ([2: k in kp_cand], i);
      for j in [1..#kp_cand] do 
         i_list[kp_cand[j]] := v[j];
       end for;

      // choose primes for K and S
      kp := [j : j in [1 .. lp] | i_list[j] eq 1];
      sp := [x : x in [1.. lp] | not (x in kp)];

      // check out dimension of p-sylow subgroups of Aut(S) and find
      // number of different operations

      kp_dim := [];
      for x in [1..#primes] do
         y := Eltseq (mat[x]);
         kp_dim[x] := &+y[sp];
      end for;
      kp_n_ops:= [(primes[kp[x]]^kp_dim[kp[x]] - 1) div 
               (primes[kp[x]] - 1): x in [1..#kp]];
      number := &*(kp_n_ops);

      if number gt 0 then
         // note which K_p might operate on which S_p
         kp_op_sp := [[x : x in sp | mat[k][x] eq 1] : k in kp];

         new_kp_dim := [kp_dim[x] : x in kp];

         s := rec<SFrec| kp := kp, kp_dim   := new_kp_dim,
                              kp_n_ops := kp_n_ops,
                              kp_op_sp := kp_op_sp,
                              number   := number>;
         Append (~inforec`sets, s);
      end if;
   end for;

   inforec`number := &+[x`number: x in inforec`sets];
   inforec`roots := [PrimitiveRoot(x): x in primes]; 

   return inforec;
end function;

/* i-th group having square-free order size */

SmallGroupSF := function (size, i: InfoSF := false)

   if size eq 1 then error "size must be at least 2"; end if;

   if Type (InfoSF) eq BoolElt then 
      inforec := InfoRecSF (size);
   else 
      inforec := InfoSF;
   end if;

   if i eq 1 then return PCGroup (AbelianGroup (inforec`primes)); end if;

   n := inforec`number;
   if i gt n then
      error "there are just ", n, " groups of size ", size; 
   end if;

   // select the proper set of groups (all groups in one set have same socle)
   set := 1;
   while inforec`sets[set]`number lt i do
      i := i - inforec`sets[set]`number;
      set +:= 1;
   end while;
   set := inforec`sets[set];

   primes := inforec`primes;
   kpr := [primes[i]: i in set`kp];

   F := FreeGroup (#(primes));
   rels := [F.i^primes[i] = 1: i in [1..#primes]];

   // find the index for the operation of every p-component
   op_indices := CoefficientsMultiadic (set`kp_n_ops, i - 1);
   op_indices := [x + 1 : x in op_indices]; 

   // run through every p-component of K and build up the operation
   for j in [1 .. #kpr] do
      op_index := op_indices[j];

      // the operation on the "leading coefficient" is always "1", 
      // thus finding the right operation is technical
      lc := 1;
      while kpr[j]^(lc - 1) lt op_index do
         op_index := op_index - kpr[j]^(lc - 1);
         lc +:= 1;
      end while;
      op := [0: k in [1 .. set`kp_dim[j]]];
      op[set`kp_dim[j] - lc + 1] := 1;
      value := [kpr[j]: index in [1..lc - 1]];
      value := CoefficientsMultiadic (value, op_index-1);
      a := set`kp_dim[j] - lc + 2; b := set`kp_dim[j]; 
      for k in [1..b - a + 1] do 
         op[a + k - 1] := value[k];
      end for;
      // Add relations for generators s of socle and k of K
      for n in [1 .. #(op)] do
         if op[n] gt 0 then
           s := set`kp_op_sp[j][n];
           k := set`kp[j];
           root := inforec`roots[s]^((primes[s]-1) div primes[k]) mod primes[s]; 
           a := (root^op[n] mod primes [s]);
           Append (~rels, F.s^F.k = F.s^a); 
         end if;
      end for;
   end for;

   H := quo <GrpPC : F | rels: Check := false>;
   return H;
end function;
   
/* identify position number of G in list of groups 
   of ths square-free order */

IdGroupSF := function (H: InfoSF := false)

   size := #H;

   assert IsSquarefree (size);

   if IsAbelian (H) then return <size, 1>; end if;

   if Type (InfoSF) eq BoolElt then 
      inforec := InfoRecSF (size);
   else 
      inforec := InfoSF;
   end if;

   primes := inforec`primes;

   // calculate special pcgs and find references towards 'primes'
   G := SpecialPresentation (H);
   lg := SpecialWeights (G);
   p_ind := [1 .. #primes];
   lg3 := PCPrimes (G);
   ParallelSort (~lg3, ~p_ind);

   spcgs := [G.i: i in [1..NPCgens (G)]];

   // find simultaneous matrices 'mat' with operations and K by 'kp'
   mat := [];
   kp := {@ @};
   for m in [1 .. #primes - 1] do
      k := p_ind[m];
      if lg[k][1] eq 1 then
         mat[m] := [0 : i in [1..#primes]];
         for n in [m + 1 .. #primes] do
            s := p_ind[n];
            if lg[s][1] eq 2 and primes[n] mod primes[m] eq 1 then
               im := spcgs[s]^spcgs[k];
               if im ne spcgs[s] then
                  root := inforec`roots[n]^
                     ((primes[n] - 1) div primes[m]) mod primes[n];
                  F := GF (primes[n]);
                  mat[m][n] := Log (F!root, F!LeadingExponent(im));
                  Include (~kp, m);
               end if;
            end if;
         end for;
      end if;
   end for;
   kp := [x : x in kp];

   // find the set of groups (socles) G belongs to and initialise result
   // counter i
   set := 2;
   i := 1;
   while inforec`sets[set]`kp ne kp do
      i +:= inforec`sets[set]`number;
      set +:= 1;
   end while;
   set := inforec`sets[set];

   op_indices := [];
   for m in [1 .. #kp] do

      // normalise operation of sylow_k generator and find index
      k := kp[m];
      index := set`kp_op_sp[m];
      op := [mat[k][ell]: ell in index];
      depth := 0;
      repeat depth +:= 1; until op[depth] gt 0 or depth gt #op;
      assert op[depth] gt 0;
      op := [(x div op[depth]) mod primes [k] : x in op];
      op_index := 1;
      for n in [Position(op, 1) + 1 .. set`kp_dim[m]] do
         op_index := op_index + (op[n]+1) * primes[k]^(set`kp_dim[m]-n);
      end for;
      Append (~op_indices, op_index);
   end for;

   // find overall position in set and return id
   m := op_indices[1] - 1;
   for n in [2 .. #(kp)] do
      m := m * set`kp_n_ops[n] + op_indices[n] - 1;
   end for;
   return <size, i + m + 1>;
end function;

SmallGroupsSF := function (size)
   assert size gt 1 and IsSquarefree (size);
   inforec := InfoRecSF(size);
   n := inforec`number;
   return [SmallGroupSF (size, i: InfoSF := inforec): i in [1..n]];
end function;

NumberSmallGroupsSF := function (size)
   assert size gt 1 and IsSquarefree (size);
   inforec := InfoRecSF(size);
   return InfoRecSF(size)`number;
end function;

intrinsic NumberOfGroupsSF(n :: RngIntElt) -> RngIntElt
{The number of groups with square-free order n}
    return NumberSmallGroupsSF(n);
end intrinsic;

intrinsic SmallGroupSF(n::RngIntElt, i::RngIntElt) -> GrpPC
{The ith group of square free order n}
    return SmallGroupSF(n,i);
end intrinsic;

intrinsic SmallGroupSFId(G::Grp) -> RngIntElt
{}
    if Type(G) ne GrpPC then GG := PCGroup(G);
    else GG := G; end if;
    return IdGroupSF(GG)[2];
end intrinsic;
