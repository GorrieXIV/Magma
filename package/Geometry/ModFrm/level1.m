freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: level1.m  -- tricks for computing with modular forms
                      in the special case of level 1.

   04/06/03: programmed around stupid shortcoming in MAGMA;
             See comments in EigenvectorOfMatrixWithCharpoly

   $Log: level1.m,v $
   Revision 1.2  2002/04/25 05:33:51  was
   some improvements.

   Revision 1.1  2001/05/30 18:55:12  was
   Initial revision

   Revision 1.1  2001/05/16 03:50:33  was
   Initial revision

      
 ***************************************************************************/

/* The functions below are used in q-expansions.m and operators.m in the
   special case of level one to speed things up. */


forward CharpolyModp,
        CRT_vec,
        CRT_mat,
        EigenvectorOfMatrixWithCharpoly,
        Level1Basis,
        Level1CharacteristicPolynomialOfTp,
        LiftToZ,
        Tp;
  

function Level1Basis(k, prec)
   assert Type(k) eq RngIntElt;
   assert Type(prec) eq RngIntElt;

   if IsOdd(k) or k lt 4 then
      return [];
   end if;
   S := PowerSeriesRing(RationalField());
   q := S.1;
   E4 := Eisenstein(4,q+O(q^prec));
   E6 := Eisenstein(6,q+O(q^prec));

   ab := [<Integers()!((k-6*b)/4),b> : b in [0..Floor(k/6)] 
                                     | (k-6*b)/4 in Integers()];
   E4pows := [1, E4]; 
   for i in [1..Max([x[1] : x in ab])] do
      Append(~E4pows, E4pows[#E4pows]*E4);
   end for;
   E6pows := [1, E6]; 
   for i in [1..Max([x[2] : x in ab])] do
      Append(~E6pows, E6pows[#E6pows]*E6);
   end for;

   gens := [E4pows[x[1]+1]*E6pows[x[2]+1] : x in ab]; 
   V := VectorSpace(RationalField(),prec);
   vecs := [V![Coefficient(g,n) : n in [0..prec-1]] : g in gens];
   W := sub<V|vecs>;    // reduced row-echelon form
   basis := [S!Eltseq(b) + O(q^prec): b in Basis(W)];
   return basis;
end function;

function Level1CharacteristicPolynomialOfTp(k,p,d,eigen)
// The characteristic polynomial of the nth Hecke operator acting
// on weight k CUSP FORMS for SL_2(Z).
// eigen is an eigenvector of T2 over an extension field, e.g.,
//    eigen := EigenvectorOfMatrixWithCharpoly(T2, f2) where f2 is
// the charpoly of T2.

   assert Type(k) eq RngIntElt;
   assert Type(p) eq RngIntElt;
   assert Type(d) eq RngIntElt;
   assert k ge 2;
   assert p gt 2 and p le d ;
//   assert IsPrime(p);

/*
   vprint ModularForms, 2: "First computing characteristic polynomial of T_2 using standard algorithm.";
   t := Cputime();
   f := CharacteristicPolynomial(T2 : 
               Proof := false, Al := "Modular");
   vprintf ModularForms, 2: "Time = %o seconds\n", Cputime(t);
*/

   N := 1; 
   ell := 17; 
   t := 1; 
   M := [* *];
   
   tm := Cputime();
   while true do
      f := CharpolyModp(eigen[1],eigen[p],ell);
      if Type(f) eq RngUPolElt and Degree(f) eq d then
         Append(~M,Eltseq(f));  
         t +:= 1;
         if t mod 5 eq 0 then
            v := CRT_vec(M); 
            if LiftToZ(v) eq LiftToZ(M[1]) then
               break;
            end if;
            M := [* v *];
            vprintf ModularForms,2: "CRT step: Now ell = %o.  (%o seconds elapsed)\n", ell, Cputime(tm);
         end if;
      end if;
      ell := NextPrime(ell);
   end while;

   return PolynomialRing(Integers())!LiftToZ(v);
end function;

/* The characteristic polynomial of b / a modulo p */
function CharpolyModp(a, b, p)
   assert Type(a) eq RngUPolResElt;
   assert Type(b) eq RngUPolResElt;
   assert Type(p) eq RngIntElt and IsPrime(p);

   K := GF(p);
   R := PolynomialRing(K);
   S := Parent(a);
   f := R!Modulus(S);
   if (Discriminant(f) eq 0) or (Coefficient(f,0) eq 0) then
      return false;   
   end if;
   L := quo<R|f>;
   t, a := IsCoercible(R,(S!a));
   if not t then
      return false;
   end if;
   amod := L!a;
   if Coefficient(MinimalPolynomial(amod),0) eq 0 then
      return false;
   end if;
   t, b := IsCoercible(R,(S!b));
   if not t then
      return false;
   end if;
   bmod := L!b;

   return MinimalPolynomial(bmod/amod);
end function;

function LiftToZ(T)
   if Type(T) eq AlgMatElt then
      return MatrixAlgebra(Rationals(),Degree(Parent(T)))!LiftToZ(Eltseq(T));
   end if;
   assert Type(T) eq SeqEnum;

   d := #T;
   N := Characteristic(Parent(T[1]));

   T0 := [];
   for i in [1..d] do
      if (Integers()!T[i]) ge N/2 then     // or something like this.
         T0[i] := (Integers()!T[i])-N;
      else
         T0[i] := Integers()!T[i];
      end if;
   end for;

   return T0;
end function;


function CRT_vec(list)
   // input is a list of vectors of the same degree modulo various primes
   assert Type(list) eq List;
   assert #list gt 0;

   d := #list[1];
   assert d gt 0;
   M := [Characteristic(Parent(v[1])) : v in list];
   return [Integers(LCM(M))| CRT([Integers()!v[i] : v in list], M) : i in [1..d] ];
end function;

/*
function CRT_mat(M)
   assert Type(M) eq List;
   V := [* *];
   for m in M do
      Append(~V, Eltseq(m));
   end for;
   crt := CRT_vec(V);
   N := Characteristic(Parent(crt[1]));
   return MatrixAlgebra(IntegerRing(N),Degree(Parent(M[1])))!crt;
end function;
*/

function MatrixAction(v, T)
   // v is a sequence and T is a matrix and this computes v*T.
   return [&+[v[i]*T[i,j] : i in [1..#v]] : j in [1..#v]];
end function;

function EigenvectorOfMatrixWithCharpoly(T, f)
   /* Let T be an nxn matrix over K with irreducible characteristic
   polynomial f.  This function returns an eigenvector for T
   over the extension field K[x]/(f(x)). */
   assert Type(T) eq AlgMatElt;
   assert Type(f) eq RngUPolElt;
   assert Type(BaseRing(Parent(f))) eq Type(BaseRing(Parent(T)));

   // This is implemented using a quotient of a polynomial ring
   // because this works generically for any field.
   n  := Degree(f);
   K  := RationalField();
   if n eq 1 then
      return VectorSpace(K,n)![1];
   end if;
   R := PolynomialRing(K); x := R.1;
   L<a> := quo<R | f>;
   if Coefficient(f,0) eq 0 then
      return false;
   end if;
   b    := 1/a;
   c    := [-b*Coefficient(f,0)];
   for i in [1..Degree(f)-1] do
      Append(~c, (c[i] - Coefficient(f,i))*b);
   end for;

/*
   // this is what we *should* do, because it is sensible.
   // HOWEVER, it is an example in which MAGMA is *ANNOYING*, in that
   // creating the RSpace over L can easily take *hours* even though
   // the rest of the computation takes no time.  I think the creation
   // of the RSpace involves checking whether or not L is a field (we
   // know it is...), and the irreducibility test in MAGMA isn't good
   // enough.   So we instead fake all this below by working with sequences,
   // which might seem slower, but is vastly faster since we avoid
   // the problem of trying to create RSpace(L,n).  
   // An example in which creating this RSpace is VERY hard: 
   // SetVerbose("ModularForms",2);S := CuspForms(1,130);time f := HeckePolynomial(S,3);
   //
   // Comment by Steve:
   // This problem seems to have gone away -- the RSpace in this example now takes 0.020 sec.
   // (Note that obviously RSpace should not involve any kind of test on the ring at all.)

   Ln := RSpace(L,n);
   v  := Ln!0;
   v[Random(1,n)] +:= Random(1,10);
   v[Random(1,n)] +:= Random(1,10);
   T  := RMatrixSpace(L,n,n)!T;
   cnt := 0;
   repeat
      v[Random(1,n)] +:= 1;
      w  := c[1]*v;
      vv := v;
      for i in [2..#c] do 
         vv := vv*T;
         w +:= c[i]*vv;
      end for;
      cnt := cnt + 1;
      if cnt gt 100 then
         print "WARNING: EigenvectorOfMatrixWithCharpoly -- algorithm not converging!";
      end if;
   until w ne 0;
*/

   v  := [L!0 : i in [1..n]];
   v[Random(1,n)] +:= Random(1,10);
   v[Random(1,n)] +:= Random(1,10);
   cnt := 0;
   repeat
      v[Random(1,n)] +:= 1;
      w  := [c[1]*x : x in v];
      vv := v;
      for i in [2..#c] do 
         vv := MatrixAction(vv,T);
         w := [w[j] + c[i]*vv[j] : j in [1..n]];
      end for;
      cnt := cnt + 1;
      if cnt gt 100 then
         print "WARNING: EigenvectorOfMatrixWithCharpoly -- algorithm not converging!";
      end if;
   until exists(i){w[i] : i in [1..#w] | w[i] ne 0};

   return w;   
end function;


