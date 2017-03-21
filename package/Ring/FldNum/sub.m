freeze;
//
//

/*
   support for the sub-constr.
   we want to be able to do sub<FldAlg| ???> where ??? specifies some elements
   in the larger field. And we want this to be "structure created" to
   avoid duplicates
   Similarly, we want sub<ComplexField() | place> and sub<RealField() | place>
   to create number fields with a default embedding. But this we leave for 
   later as it is complicated (impossible) to do a look-up.

   The plan is easy:
     compute the block containing 1 for each of the elements
     compare it with known blocks...
  
   TODO: should porobably be redone in C in connection with a partial re-write
   of JK's subfields.
   
   Canot use GaloisSubfieldLattice as it would produce circular references
*/     

declare attributes FldNum: Subfields;
/* Subfields is a sequence of tuples, each tuple representing one 
 * subfield.
 * A subfield is a tuple where the 1st component contains the list
   (sequence) of generators and the third is again a sequence
   of tuples containing pairs of the form <prime, block>  
   The second is an integer that has to be avoided....
   
   The first entry in Subfields corresponds to the number field, but
   The tuple has the primitive element and a sequence of tuples containing
   the prime and the roots in a splitting field for that prime.
   For a nonsimple or non-absolute field, we store a primitive element
   and instead of the roots, the matrix mapping the basis element into
   the finite field
*/     

intrinsic AbsoluteDegree(P::PlcNumElt) -> RngIntElt
  {The degree over Q of the place P}

  if IsFinite(P) then
    if IsAbsoluteField(NumberField(P)) then
      return Degree(P);
    else
      return Degree(P) * AbsoluteDegree(Place(Ideal(P) meet CoefficientRing(Order(Ideal(P)))));
    end if;
  elif IsReal(P) then
    return 1;
  else 
    return 2;
  end if;
end intrinsic;

intrinsic AbsoluteDecomposition(K::FldAlg, p::Infty) ->
  []
{The decomposition of the infinite place in K}
  return AbsoluteDecomposition(K, 0);
end intrinsic;

intrinsic AbsoluteDecomposition(K::FldAlg, p::RngIntElt) ->
  []
{The decomposition of the rational prime p into places in K}   
  if p eq 0 then
    return [<x, RamificationIndex(x)> : x in InfinitePlaces(K)];
  end if;
  require IsPrime(p) : 
    "p must be a rational prime";

  M := MaximalOrder(K);
  return [ <Place(x[1]), x[2]> : x in Decomposition(M!p)];

  if not IsAbsoluteField(K) then
    l := AbsoluteDecomposition(CoefficientField(K), p);
    l := &cat [[<x[1], x[2]*P[2]> : x in Decomposition(K, P[1])] : P in l];
  else
    return Decomposition(K, p);
  end if;
  return l;
end intrinsic;

function new_roots(K) // will find a new prime and compute the roots
                      // wrt. to the new prime

  if #K`Subfields[1][3] eq 0 then
    p := 2^20;
  else
    p := Maximum([x[1] :x in K`Subfields[1][3]]);
  end if;


  deg_max := AbsoluteDegree(K);
  deg_max := Minimum(deg_max, deg_max div 4);
  deg_max := Maximum(deg_max, 1);
  repeat
    repeat
      p := NextPrime(p);
    until forall{x : x in K`Subfields | x[2] mod p ne 0};
    D := AbsoluteDecomposition(K, p);
  until LCM([AbsoluteDegree(x[1]) :  x in D]) le deg_max;

  F := GF(p, LCM([AbsoluteDegree(x[1]) : x in D]));
  if IsSimple(K)  and IsAbsoluteField(K) then
    r := Roots(Polynomial(F, DefiningPolynomial(K)));
    assert forall{x : x in r | x[2] eq 1};

    su := K`Subfields;
    su[1][3] := Append(su[1][3], <p, [x[1] : x in r]>);
    K`Subfields := su;

  elif IsAbsoluteField(K) then
    r := [[x[1] : x in Roots(Polynomial(F, f))] : f in DefiningPolynomial(K)];
    su := K`Subfields;
    mb := [[hom<K -> F | [x[i] : i in [1..#r]]>(b) : x in CartesianProduct(r)] : b in Basis(K)];
    mb := Matrix(mb);

    su := K`Subfields;
    su[1][3] := Append(su[1][3], <p, mb>);
    K`Subfields := su;
  else    
    Q := Rationals();
    function get_conjugates(L, C)
      if not IsAbsoluteField(L) then
        C := get_conjugates(CoefficientField(L), C);
      end if;
      if IsSimple(L) then
        H := [];
        for c in C do
          r := Roots(Polynomial([c(x) : x in Eltseq(DefiningPolynomial(L))]));
          assert #r eq Degree(L);
          assert forall{x : x in r | x[2] eq 1};
          H cat:= [hom<L -> F | c, x[1]> : x in r];
        end for;
      else
        H := [];
        for c in C do
          r := [Roots(Polynomial([c(x) : x in Eltseq(y)])) : y in DefiningPolynomial(L)];
          r := [ [x[i][1] : i in [1..#r]] : x in CartesianProduct(r)];
          H cat:= [hom<L -> F | c, x> : x in r];
        end for;
      end if;
      return H;
    end function;
    C := get_conjugates(K, [hom<Q -> F | >]);
    mb := [[h(b) : h in C] : b in AbsoluteBasis(K)];
    mb := Matrix(mb);

    su := K`Subfields;
    su[1][3] := Append(su[1][3], <p, mb>);
    K`Subfields := su;
  end if;
  return su[1][3][#su[1][3]];
end function;

function ith_prime(K, i)
  while #K`Subfields[1][3] lt i do
    _ := new_roots(K);
  end while;

  return K`Subfields[1][3][i];
end function;

function find_prime(K, p)
  su := K`Subfields;
  i := Position([x[1] : x in K`Subfields[1][3]], p);
  assert i ne 0;
  return K`Subfields[1][3][i];
end function;

function get_block(data, g)
  if Type(data[2]) eq SeqEnum then
    F := Universe(data[2]);
    n := #data[2];
    b := &meet[ {i : i in [1..#data[2]] | Evaluate(f, data[2][i]) eq o} where o := Evaluate(f, data[2][1]) where f := Polynomial(F, e) : e in g];
  else
    F := CoefficientRing(data[2]);
    n := Ncols(data[2]);
    b := &meet [{ x : x in [1..n] | m[1][x] eq m[1][1]} where m := Matrix(F, [e])*data[2] : e in g];
  end if;
  return b;
end function;


procedure  InternalFldNum_NewSubfield(K, g) 

  if not ISA(Type(K), FldNum) then
    K := NumberField(K);
    g := ChangeUniverse(g, K);
  end if;

  n := AbsoluteDegree(K);  
  Z := Integers();
  if not assigned K`Subfields then
    f := DefiningPolynomial(K);
    if Type(f) eq RngUPolElt then
      d := LCM([Denominator(x) : x in Eltseq(f)]);
      f := Polynomial(Z, f*d);
      d := Discriminant(f);
      d := LCM(d, LeadingCoefficient(f));
    else
      d := LCM([Lcm([Denominator(x) : x in Eltseq(y)]) : y in f]);
      f := [Polynomial(Z, x*d) : x in f];
      d := Lcm([Discriminant(x) : x in f]);
    end if;
    pe := PrimitiveElement(K);
    d := LCM(d, Denominator(pe));
    K`Subfields :=  [<[Eltseq(pe)], d, [**]>];
  end if;
  d := LCM([Denominator(x) : x in g]);
  i := 1;
  repeat
    data := ith_prime(K, i);
    i +:= 1;
  until d mod data[1] ne 0;
  g := [Eltseq(K!x, Rationals()) : x in g];
  b := get_block(data, g);
  su := K`Subfields;
  if #b ne 1 and #b ne n then
    Append(~su, <g, d, [*<data[1], b>*]>);
  end if;
//  "Found K or Q:", #b;
  K`Subfields := su;
end procedure;

function find_subfield(K, g)
  if not assigned K`Subfields then
    InternalFldNum_NewSubfield(K, g);
    return 2;
  end if;
  n := AbsoluteDegree(K);
  d := LCM([Denominator(x) : x in g]);
  g := [Eltseq(K!x, Rationals()) : x in g];
  i := Position([x[1] : x in K`Subfields], g);
  if i ne 0 then
    return i;
  end if;
  this := <g, d, [**]>;
  to_do := {2..#K`Subfields};
  for s in [2..#K`Subfields] do
    for t in K`Subfields[s][3] do
      if d mod t[1] ne 0 then
        data := find_prime(K, t[1]);
        i := Position([x[1] : x in this[3]], data[1]);
        if i eq 0 then
          b := get_block(data, g);
        else
          b := this[3][i][2];
        end if;
        if #b eq 1 then
          return 1;
        end if;
        if #b eq n then
          return 0; // Q
        end if;
        if b eq t[2] then
          return s;
        end if;
        if i eq 0 then
          Append(~(this[3]), <t[1], b>);
        end if;
        Exclude(~to_do, s);
        break;
      end if;
    end for;
  end for;
  while #to_do ne 0 do
    data := new_roots(K);
    for s in to_do do
      if K`Subfields[s][2] mod data[1] ne 0 and
         d mod data[1] ne 0 then
        b := get_block(data, g);
        c := get_block(data, K`Subfields[s][1]);
        Append(~(K`Subfields[s][3]), <data[1], c>);
        if b eq c then
          return s;
        end if;
        Append(~(this[3]), <data[1], b>);
        Exclude(~to_do, s);
      end if;
    end for;
  end while;
  Append(~(K`Subfields), this);
  return #K`Subfields;
end function;


intrinsic InternalFldNum_EqSubfield(K::FldAlg, g::[FldAlgElt], h::[FldAlgElt]) 
    -> BoolElt
  {}
  if not ISA(Type(K), FldNum) then
    K := NumberField(K);
    g := ChangeUniverse(g, K);
    h := ChangeUniverse(h, K);
  end if;
  if not assigned K`Subfields then
    k := CoefficientField(K);
    while k cmpne Rationals() do
      InternalFldNum_NewSubfield(K, Generators(k, Rationals()));
      k := CoefficientField(k);
    end while;
    InternalFldNum_NewSubfield(K, g);
  end if;

  ig := find_subfield(K, g);
  ih := find_subfield(K, h);
  return ig eq ih;
end intrinsic;
  
    

