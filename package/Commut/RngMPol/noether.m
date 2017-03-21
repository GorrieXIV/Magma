freeze;

declare attributes RngMPol: NoetherNormalisation;

////////////////////////////////////////////////////////////////////
//     Functions for Noether Normalisation of Affine Rings        //
//               Mike Harrison 05/2004                            //
////////////////////////////////////////////////////////////////////

/*  Currently only linear changes of variables are considered and
    there could be failure in small characteristic.               */

//////////////   Test Functions  ///////////////////////////////////
//  The following two functions test whether k[x_(n-dim+1),..x_n] //
//  is a Noether normalisation for R/I. The first gives a faster  //
//  test for homogeneous I and the second is general.             //

// Here we use the criterion that if I is homogeneous in R=k[x_1,..x_n]
// and <I,x_r,x_(r+1),..,x_n> is zero dimensional then R/I is integral
// over k[x_r,..x_n].If further, r = n-dim+1 where Dim(R/I) = dim then
// also k[x_r,..x_n] injects into R/I (see note in the function).
// This is false for I non-homog as the simple example n=2,
// I := <x*y+x-1> r=1 shows (have injection but not integrality!).
function HomogeneousTest(I,dim)

   R := Generic(I); n := Rank(R);
   if IsZeroDimensional(I+ideal<R|[R.i : i in [n-dim+1..n]]>) then
   // NB: if x1,..x_dim are R.n,R.(n-1),..R.(n-dim+1) and
   // I1 + <x1,x2,..x_dim> is height n then, for any prime ideal P
   // minimal over I1 and of height n-dim, we have that the map
   // Spec(R/P) -> Spec(k[x1,..x_dim]) has a non-empty finite fibre over
   // (0,0,..0). As Spec(R/P) and Spec(k[x1..x_dim]) have the same
   // dimension, Chevalley's results on fibres of morphisms shows
   // that the map is generically surjective, so
   //  k[x1..x_dim] injects into R/P and, a fortiori, into R/I1.
       return true;
   else
       return false;
   end if;

end function;

// General test following Greuel/Pfister "A Singular Introduction To
//  Commutative Algebra" p.213.
function NonHomogeneousTest(I,dim)

   R := Generic(I); // this has guaranteed lex order
   n := Rank(R);
   lts := [LeadingTerm(b) : b in GroebnerBasisUnreduced(Basis(I))];
   if lts[#lts] gt (R.(n-dim+1))^TotalDegree(lts[#lts]) then
   // condition <=> k[R1.(n-dim+1),..,R1.n] intersect I1 = 0
      // now, given the leading terms of a lex (unreduced) Grobner
      // basis of I1, check that some element of I1 has leading term
      // x_i^m_i for each 1 <= i <= dim .
      I1 := ideal<R | Reduce(lts cat [R.i : i in [n-dim+1..n]])>;
      MarkGroebner(I1); // little white lie!
      if IsZeroDimensional(I1) then
         return true;
      else
         return false;
      end if;
   end if;
   return false;

end function;

//////////////////    Main function.  /////////////////////////

//  I is an ideal in R=k[x_1,..x_n] (k a field) of (co-)dimension dim.
//  Looks for a LINEAR change of variables, giving the map h:R->R s.t.
//  k[x_(n-dim+1),..x_n] is a Noether normalisation of R/h(I).
//  the sequence of normalising variables 
//    [h^(-1)(x_(n-dim+1),..,h^(-1)(x_n)],
//        h and h^(-1) is returned.
//  Partially following the above Greuel/Pfister reference, we begin
//  by looking at permutation variable changes but then move on to
//  ones given by random lower triangular matrices if this fails.
//  As only linear variable changes are currently considered, this
//  may fail in non-zero characteristic, though in practise only if
//  the field is small and we are unlucky.
intrinsic NoetherNormalisation(I::RngMPol) -> SeqEnum,Map,Map
{ Finds a Noether normalisation for ideal I }
  
   if assigned I`NoetherNormalisation then 
     return Explode(I`NoetherNormalisation);
   end if;

   R := Generic(I);
   n := Rank(R);
   dim, inds0 := Dimension(I);
   idR := hom<R -> R | [R.i : i in [1..n]]>; //identity map

   if dim eq n then // I = 0
      I`NoetherNormalisation := <[R.i : i in [1..n]],idR,idR>;
      return Explode(I`NoetherNormalisation);
   end if;
   if dim le 0 then // R/I is a finite k-algebra
      I`NoetherNormalisation := <[],idR,idR>;
      return Explode(I`NoetherNormalisation);
   end if;

   bHom := IsHomogeneous(I);
   end_vars := [R.i : i in [n-dim+1..n]]; 
   K := BaseRing(R);
   R1 := PolynomialRing(K,n);//poly ring with guaranteed lex order

   // first try subsets of indices [1..n] of size dim starting with
   // inds0 (which often does the job!)
   bFirst := true;
   for sub in Subsets({1..n},dim) do
      inds := Sort(Isetseq(SetToIndexedSet(sub)));
      if bFirst then
         inds_saved := inds; inds := inds0;
         bFirst := false;
      else
         if inds eq inds0 then inds := inds_saved; end if;
      end if;

      perm := [i : i in [1..n] | i notin inds] cat inds;
      h := hom<R -> R | [R.j where j is Index(perm,i) : i in [1..n]]>;
      hinv := hom<R -> R | [R.i : i in perm]>;

      I1 := ideal<R | [h(b) : b in Basis(I)]>;
      if bHom then //simplified criterion in the homogeneous case
        if HomogeneousTest(I1,dim) then
            I`NoetherNormalisation := <[hinv(v) : v in end_vars],h,hinv>;
            return Explode(I`NoetherNormalisation);
        end if;
      else
        if NonHomogeneousTest(ChangeOrder(I1,R1),dim) then
            I`NoetherNormalisation := <[hinv(v) : v in end_vars],h,hinv>;
            return Explode(I`NoetherNormalisation);
        end if;
      end if;
   end for;
   
   /* now try transformations h of the form
        x1 -> x1
        x2 -> a_2,1 x1 + x2
        x3 -> a_3,1 x1 + a_3,2 x2 + x3
        ...
      for random a_i,j for n >= i > j >= 1.
      We only consider a_i,j in the ground field unless K is a
      finite field and in order to try
      to keep the coefficients low in char 0 we start with small
      bounds on the size of a_i,j and keep raising them.        */

   b_ff := IsFinite(K);
   char := Characteristic(K);
   N := 1;
   if b_ff then
       t_max := 100;
   else
       t_max := Min(20,3^((n*(n-1)) div 2));
   end if;
   tries := 0;
   while true do
     if tries eq t_max then
//printf "Doubling N.\n";
        N *:= 2;
        if b_ff or ((char gt 0) and (N ge char)) then
          error "Failed to find a Noether normalisation.";
        end if;
        tries := 0; t_max := Min(20,(2*N+1)^((n*(n-1)) div 2));
     end if;
     // find random linear change of vars
     M := ScalarMatrix(n,K!0);
     if b_ff then
         InsertBlock(~M,LowerTriangularMatrix([Random(K):
                         i in [1..(n*(n-1)) div 2]]),2,1);
     else
         InsertBlock(~M,LowerTriangularMatrix([K!Random(-N,N):
                         i in [1..(n*(n-1)) div 2]]),2,1);
     end if;
     M +:= ScalarMatrix(n,K!1);
     Minv := M^-1;
     h := hom<R -> R | [&+[M[i,j]*R.j : j in [1..n]] : i in [1..n]]>;
     hinv := hom<R -> R | [&+[Minv[i,j]*R.j : j in [1..n]] : i in [1..n]]>;
     tries +:= 1;
//printf "Try number %o.\n",tries;
     I1 := ideal<R | [h(b) : b in Basis(I)]>;
     if bHom then //simplified criterion in the homogeneous case
       if HomogeneousTest(I1,dim) then
            I`NoetherNormalisation := <[hinv(v) : v in end_vars],h,hinv>;
            return Explode(I`NoetherNormalisation);
       end if;
     else
       if NonHomogeneousTest(ChangeOrder(I1,R1),dim) then
            I`NoetherNormalisation := <[hinv(v) : v in end_vars],h,hinv>;
            return Explode(I`NoetherNormalisation);
       end if;
     end if;
   end while;
   
end intrinsic;
