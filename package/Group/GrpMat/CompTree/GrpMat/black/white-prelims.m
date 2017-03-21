freeze;

//////////////////////////////////
// Some preliminary functions	      
/////////////////////////////////

ImageInLtilde := function(g, comL)
    gen := Generic(Parent(g));
    gmod := GModule(sub<gen | g>);
    comLingmod := sub<gmod | comL>;
    return ActionGenerator(comLingmod, 1);
end function;

norm := function(a, F0)
    return a*Frobenius(a, F0);
end function; 

trace := function(a, F0)
    return a + Frobenius(a, F0);
end function;

// the following function takes in the hermitian form matrix, b 
// and returns (a, b). Note that V is a vector space over GF(q^2)
form := function(a, b, B, l) 
    M := Parent(a);
    F := BaseRing(M);
    a := Matrix(a);
    b := Matrix(b);
    ab := a*B*(Transpose(FrobeniusImage(b, l)));
    return ab[1][1];
end function;

CommutatorSpace := function (F, gens)
    V := VectorSpace (F, Nrows (Rep (gens)));
    return sub< V | [v - v * g: g in gens, v in Generators(V)]>;
 end function;

IsPowerOfTwo := function(j)
    SmallPowersOfTwo := [2^i : i in [1..100]];
    return exists{x : x in SmallPowersOfTwo | j eq x};
end function;

IsOrderMoreThanThree := function(g)	
    id := Identity(Parent(g));
    return (g ne id and g^2 ne id and g^3 ne id);
end function;

//tests whether p (where p has at most 32 digits) is a mersenne prime.
IsMersenne := function(p) 
    // M determines the first 10 mersenne primes
    M := [2, 3, 5, 7, 13, 17, 19, 31, 61, 89];
    return exists{m : m in M | p eq 2^m-1};
end function;

//list of small fermat primes
IsFermat := function(p)
    F := [2^(2^i)+1 : i in [0..4]];
    return p in F;
end function;

Isppdhash := function(d, p, n)                                                 
    if n eq 1 then
        if ((IsFermat(p) and d mod 4 eq 0) or 
            ((not(IsFermat(p))) and not(IsPowerOfTwo(d)))) then
            return true;
        else
            return false;
        end if;
    end if;
    if n eq 6 and p eq 2 then
        return (d mod 21 eq 0);
    end if;
    if n eq 2 and IsMersenne(p) and (d mod 4 eq 0) then 
        return true; 
    end if;
    L := Factorization(d);
        return exists{x : x in L | (p^n-1) mod x[1] eq 0 and 
               forall{i : i in [1..n-1] | (p^i-1) mod x[1] ne 0}};
end function;

/* Constructs change of basis matrix: new basis -> old basis. 
   i.e. B -> Generators(V); */
MyChangeOfBasisMatrix := function(V, B)
    CB := [];
    for i in [1..#B] do
       B[i] := Vector(B[i]);
    end for;
    for i in [1..Dimension(V)] do
       CB := CB cat (Coordinates(V, B[i]));
    end for;
    CB := (GL(Dimension(V), BaseRing(V)))!CB;
    return CB;
end function;

/* 
 Lemmas from Brooksbank's "Constructive recognition of 
  classical groups in their natural representation" 
*/

/* LEMMA 3.5.i.
Input: 
       (1) A field F.
       (2) An element beta of F
Output:
	(1) an element alpha of F s.t. alpha + alpha^q = beta 
*/

ElementHavingPrescribedTrace := function(F, beta)
    rho := F.1;
    k := Degree(F) div 2;
    p := Characteristic(F);
    q := p^k;
    FF := GF(p);
    V, f := VectorSpace(F, FF);
    vbeta := beta @ f; 
    rhoiq := [((rho^(i*q)) @ f) : i in [0..2*k-1]];
    rhoij := Matrix(rhoiq);
    equations := rhoij + Identity(Parent(rhoij));
    valpha, N := Solution(equations, vbeta);
    if valpha eq Parent(valpha)!0 then 
        valpha := valpha + N.1;
    end if;
    alpha := &+[ valpha[i]*rho^(i-1) : i in [ 1..2*k ] ];
    assert alpha + alpha^q eq beta;
    return alpha;
end function;
			    			    
/* LEMMA 3.5.ii.
   The input is:
       (1) b in F0, F, F0
   The output is:
        a in F* such that N(a) = b.
*/

ElementHavingPrescribedNorm := function(b, F0, F, q)
   p := Characteristic(F); 
   P<x> := PolynomialRing(F); 
   i := 1; 
   repeat
      r := (Roots(x^2 - b))[1][1];
      i +:= 1;
   until i eq 2 or r^2 eq b;
   assert r^2 eq b;
   if r*Frobenius(r, F0) eq b or Frobenius(r, F0) eq r then 
      return r; 
   end if;
   if q mod 4 eq 1 then							
      d := (Roots(x^2+1))[1][1];
      return r*d;
   end if;
   if q mod 4 eq 3 then 
      i := 1;
      while (q+1) mod 2^i eq 0 do i +:= 1; end while;
      i := i-1;
      assert i gt 1;								       
      if p eq 8191 then
         d := F.1 + 1508;
      elif p eq 127 then
         d := F.1^63; 
      else 
         d := (Roots(x^(2^i) +1))[1][1];
      end if;
      assert d^(2^i)+1 eq 0;
      return r*d;
   end if;
end function;

/* LEMMA 3.6. */

/* The formRest function coerces a and b into V then produces the 
   image of the form B (which is defined over V).
   This function was created to deal with calculating the form of elements 
   of U := sub<V | ..>;
*/

formRest := function(a, b, B, k, V)
   aa := V!a;
   bb := V!b;
   return form(aa, bb, B, k);
end function;

OrthogonalComplement := function(U, V, B, l)
   d := Dimension(V);
   r := Dimension(U);
   F := BaseRing(V);
   m := Matrix(F, d, r, [<i, j, form(V.i, (V!U.j), B, l)> : i in [1..d], j in [1..r]]);
   N := NullSpace(m);
   return sub<V|N>;
end function;

/* LEMMA 3.7. */

IsSingular := function(v, B, k, V)
   return (formRest(v, v, B, k, V) eq 0);
end function;

FindHyperbolicPair := function(F0, F, L, B, k, V)
   p := Characteristic(BaseRing(V));
   q := p^k;
   assert Ngens(L) eq 2;	
   v := L.1; w := L.2;
   if IsSingular(v, B, k, V) then
      assert formRest(v, w, B, k, V) ne 0;			
      //if above fails then L is not hyperbolic
      e := v; 
      formwv := formRest(w, v, B, k, V);
      w := w/formwv;
      assert formRest(v, w, B, k , V) eq 1;
      alpha := ElementHavingPrescribedTrace(F, -(formRest(w, w, B, k, V)));
      assert alpha+alpha^q eq -formRest(w, w, B, k, V);
      f := alpha*v +w;
      assert formRest(e, f, B, k, V) eq 1;
      assert formRest(e, e, B, k, V) eq 0;
      assert formRest(f, f, B, k, V) eq 0;
      return e, f;
   else	     
      m := Matrix(F, 2, 1, 
           [<i, j, formRest(L.i, v, B, k, V)> :  i in [1..2], j in [1..1]]);
      N := NullSpace(m);
      assert Dimension(N) ne 0;
      w := L!N.1;
      assert not(IsSingular(w, B, k, V));
      assert formRest(v, w, B, k, V) eq 0;
      alpha := ElementHavingPrescribedNorm
         (-(formRest(v, v, B, k, V))/(formRest(w, w, B, k, V)), F0, F, q);
      v := alpha*w+v;
      assert formRest(v, v, B, k, V) eq 0;
      assert formRest(v, w, B, k, V) ne 0;	
      //if above fails then L is not hyperbolic
      e := v; 
      pp := (formRest(w, v, B, k, V)); 
      w := w/pp;
      assert formRest(v, w, B, k, V) eq 1;
      alpha := ElementHavingPrescribedTrace(F, -(formRest(w, w, B, k, V)));
      assert trace(alpha, F0) eq -(formRest(w, w, B, k, V));
      f := alpha*v +w;
      assert formRest(e, f, B, k, V) eq 1;
      assert formRest(e, e, B, k, V) eq 0;
      assert formRest(f, f, B, k, V) eq 0;
      return e, f;
   end if;
end function;

/*
 Input: (1) The generating set for Q, TQ.
        (2) A element u of Q
Output: A vector v corresponding to the coset uT in Q/T \simeq (Z_p)^(2k)
*/
GetVector := function(TQ, u)
    E := BaseRing(Parent(u));
    k := Degree(E) div 2;
    p := Characteristic(E);
    F := GF(p);
    V, f := VectorSpace(E, F);
    v := (u[3][2] @ f);
    return v;
end function;

GetFpBasisVectors := function(TQ)
    k := Degree(BaseRing(TQ[1])) div 2;
    FpBasis := [TQ[i] : i in [1..2*k]];
    vFpBasis := [GetVector(TQ, FpBasis[i]) : i in [1..#FpBasis]];
    return vFpBasis;
end function;
