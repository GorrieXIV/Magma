freeze;

/******************************************************************************
 *
 * mynumfld.m
 *
 * date:   10/9/2002
 * author: Nils Bruin
 *
 * Some features missing for number field and related objects
 *
 ******************************************************************************/

/* We'll be saving information in prime ideals later on. Therefore, it is good
to be able to get a "standard version" of a prime ideal.  With LookupPrime,
we store & retrieve standard versions of a prime ideal. Be sure to call

p:=LookupPrime(p);

whenever you want to use the functions here in order to get higher consistency
in returned values and a better performance */

declare attributes RngOrd: StandardPrimeIdeals;

intrinsic LookupPrime(P::RngOrdIdl) -> RngOrdIdl
  {Routine to get *IDENTICAL* prime ideals for a number field.
  Calling this routine several times with equal prime ideals of the same order
  is guaranteed to return identical prime ideals. This enables attributes to
  be stored in prime ideals and preserved along different instantiations
  of that prime ideal}
  O:=Order(P);
  if not(assigned O`StandardPrimeIdeals) then
    O`StandardPrimeIdeals:={};
  end if;
  if exists(Q){R:R in O`StandardPrimeIdeals| P eq R} then
    return Q;
  else
    Include(~O`StandardPrimeIdeals,P);
    return P;
  end if;
end intrinsic;

IdealRecordFormat:=recformat<LocalTwoSelmerMap,SafeUniformiser,
Completion,ComplMap>;

/**
 ** Completion with memory
 ** (not necessary anymore ???)

function toNpAdic(OR)
  if ISA(Type(OR),FldLoc) then
    pi:=UniformizingElement(OR);
    IOR:=IntegerRing(OR);
    toNIOR:=toNpAdic(IOR);
    NIOR:=Codomain(toNIOR);
    NOR:=FieldOfFractions(NIOR);
    Npi:=NOR!toNIOR(IOR!pi);
    return map<OR->NOR|
       a:->toNIOR(IOR!(a/pi^Valuation(a)))*Npi^Valuation(a),
       b:->(NIOR!(b/Npi^Valuation(b)))@@toNIOR*pi^Valuation(b)>;
  elif RamificationDegree(OR) eq 1 and InertiaDegree(OR) eq 1 then
    p:=Prime(OR);
    pi:=UniformizingElement(OR);
    NOR:=NpAdicRing(p:Precision:=OR`DefaultPrecision);
    Npi:=NOR!(Integers()!p);
    return map<OR->NOR|a:->NOR!(Integers()!a)+O(Npi^AbsolutePrecision(a)),
                b:->OR!(Integers()!b)+O(pi^AbsolutePrecision(b))>;
  else
    f:=DefiningPolynomial(OR);
    Zp:=BaseRing(f);
    toNZp:=$$(Zp);
    NZp:=Codomain(toNZp);
    NZpX:=PolynomialRing(NZp);
    Nf:=NZpX![toNZp(c):c in Eltseq(f)];
    NOR:=ext<NZp|Nf>;
    if RamificationDegree(NOR) eq 1 then
      gOR:=OR.2;
    else
      gOR:=OR.1;
    end if;
    return map<OR->NOR|
       a:->&+[NOR!(toNZp(Eltseq(a)[i]))*NOR.1^(i-1):i in [1..Degree(OR)]],
       b:->&+[((Eltseq(b)[i])@@toNZp)*gOR^(i-1):i in [1..Degree(OR)]]>;
  end if;
end function;

***********************************/

intrinsic MyCompletion(p::RngOrdIdl:Precision:=false)->FldPad,Map
  {Returns a completion with memory. If precision is given and is different from
  a stored completion, then stored field will be changed (recreated)}
  if not(assigned p`Record) then
    p`Record:=rec<IdealRecordFormat|>;
  end if;
  if not(assigned p`Record`Completion) or Precision cmpne false or
     ISA(Type(p`Record`Completion),FldPad) then
    if Precision cmpne false then
      Kp,mp:=Completion(NumberField(Order(p)),p:Precision:=Precision);
    else
      Kp,mp:=Completion(NumberField(Order(p)),p:Precision:=
           Minimum(p) eq 2 select 80 else 30);
    end if;
    rc:=p`Record;
    rc`Completion:=Kp;
    rc`ComplMap:=mp;
    p`Record:=rc;
  end if;
  return p`Record`Completion,p`Record`ComplMap;
end intrinsic;

intrinsic MyCompletion(p::RngIntElt:Precision:=false)->FldPad,Map
{"} // "
  require IsPrime(p): "Can only complete Q at a prime";
  if Precision cmpne false then
    k:=pAdicField(p:Precision:=Precision);
  else
    k:=pAdicField(p:Precision:= (p eq 2) select 80 else 30);
  end if;
  return k, Bang(Rationals(),k);
end intrinsic;

intrinsic InertiaDegree(p::RngIntElt)->RngIntElt
{Returns 1}
  return 1;
end intrinsic;

/**
 ** SafeUniformiser
 **
 ** retrieve or compute and store an element of valuation 1 at the given prime
 ** and valuation 0 at the other primes above the same rational prime.
 **/

intrinsic SafeUniformizer(p::RngFunOrdIdl)->RngFunOrdElt
{Same as SafeUniformiser}
  return SafeUniformiser(p);
end intrinsic;

intrinsic SafeUniformizer(p::RngOrdIdl)->RngOrdElt
{Same as SafeUniformiser}
  return SafeUniformiser(p);
end intrinsic;

intrinsic SafeUniformiser(p::RngOrdIdl)->RngOrdElt
  {returns an element of valuation 1 at the given prime and of
   valuation 0 at the other primes over the same rational prime.}

   require Order(p) eq MaximalOrder(NumberField(Order(p))) and IsPrime(p): 
             "p must be a prime ideal of the maximal order";
   if not(assigned p`Record) then
     p`Record:=rec<IdealRecordFormat|>;
   end if;
   if not(assigned p`Record`SafeUniformiser) then
     K := NumberField(Order(p));
     if not IsAbsoluteField(K) then
        Kabs := AbsoluteField(K);
        Oabs := MaximalOrder(Kabs);
        pabs := ideal< Oabs | [Kabs!b : b in Generators(p)] >;
        u := Order(p)!K!SafeUniformiser(pabs);
     else
        pfact := Factorisation(Norm(p)*Order(p));
        require p in [ q[1] : q in pfact ] : "p must be a prime ideal";
        I := [q[1]: q in pfact | q[1] ne p];
        u := WeakApproximation([p]cat I,[1] cat [0: i in I]);
     end if;
     rc:=p`Record;
     rc`SafeUniformiser:=u;
     p`Record:=rc;
   end if;
   return p`Record`SafeUniformiser;
end intrinsic;

// Steve's adaption of the above for function fields.
intrinsic SafeUniformiser(I::RngFunOrdIdl)->RngFunOrdElt
{For a prime ideal I of a maximal order in a function field, 
this returns an element which has valuation 1 at the given prime and 
which has valuation 0 at all other primes lying over the same prime
of the underlying rational function field.}
   
   O := Order(I);
   FF := FunctionField(O);
   if not IsAbsoluteOrder(O) then
      absO := AbsoluteOrder(O);
      absI := ideal< absO | [ absO!gen : gen in Generators(I) ] >;
      return O!SafeUniformiser(absI);
   elif O eq MaximalOrderFinite(FF) or O eq MaximalOrderInfinite(FF) then
      factNormI := Factorisation(ideal< O | Norm(I) >);
      require I in [ q[1] : q in factNormI ] : "The ideal should be prime";
      Icomp := [q[1]: q in factNormI | q[1] ne I];
      return WeakApproximation( [I] cat Icomp,
                                [1] cat [0: i in Icomp] );
   else require false: "The ideal must be an ideal of a maximal order (finite or infinite)";
   end if;
end intrinsic;

/**
 ** LocalTwoSelmerMap
 **
 ** This routine returns a map from K^* -> Kp^* /(Kp^*2). If called twice with
 ** the same prime, returns the identical map. If called on equal but not
 ** identical primes, returns different maps that may not even agree
 ** coordinate-wise.
 **/

// Some preliminary stuff on classes mod squares in p-adic fields
// Added by Sebastian Stamminger

// Find smallest positive integer d such that d*x is integral.
function Denom(x)
  // x::FldNumElt
  // f := AbsoluteMinimalPolynomial(x);
  // return LCM([Denominator(c) : c in Coefficients(f)]);
  den1 := LCM([Denominator(c) : c in Eltseq(x)]);
  O := Integers(Parent(x));
  x1 := O!(den1*x);
  num := GCD(den1, GCD(ChangeUniverse(Eltseq(x1), Integers())));
  return ExactQuotient(den1, num), O!(x1/num);
end function;

// We represent a p-adic field by the following data:
// + a number field K;
// + a prime ideal in O, the integers of K, lying above p.
// From these, we deduce
// + a uniformizer;
// + a homomorphism K^* -->> finite elementary abelian 2-group with
//   kernel the elements that are squares in the completion.

// Return the map  K^* -> a GF(2)-vector space
function MakeModSquares(K, pid)
  // (K::FldNum, pid::prime ideal in K) -> ModTupFld, Map
  O := Integers(K);
  p := Minimum(pid);
  e := RamificationIndex(pid, p);
  f := Degree(pid);
  _, pi := TwoElementNormal(pid);   //pi is the uniformizer.
  F, m := ResidueClassField(pid);
  U, mU := UnitGroup(F);
  nonsq := (mU(U.1)) @@ m;
  if IsOdd(p) then
    V := AbelianGroup([2,2]); //KSpace(GF(2), 2); // the codomain of our homomorphism
    h := map< K -> V | x :-> V![GF(2) | v, IsSquare(m(y)) select 0 else 1]
                                        where y := x/(pi^v) where v := Valuation(x, pid),
                       v :-> pi^Eltseq(v)[1]*nonsq^Eltseq(v)[2]>; //is nonsq right?
  else
    // p = 2
    // c is a pid-adic square and a pid-unit, but lies in all other prime ideals above 2 in O.
    c := ChineseRemainderTheorem(pid^(2*e+1), ideal<O | O!2>/pid^e, O!1, O!0);
    // Our elementary abelian 2-group K_pid^*/(K_pid^*)^2 has rank 2 + e*f.
    V := KSpace(GF(2), 2 + e*f);
    // A pid-unit is a square in K_pid iff it is a square in R.
    R := quo<O | pid^(2*e+1)>;
    // reps is a lift to O of an F_2-basis of F.
    reps := [ R!((F![ i eq j select 1 else 0 : i in [1..f] ]) @@ m) : j in [1..f] ];
    // A basis of pid-units modulo squares is given by
    //  [ 1 + r*pi^(2*i-1) : r in reps, i in [1..e] ] cat [ unr ] ,
    // where unr = 1 + 4*u such that the absolute trace of the image
    // of u in the residue field is non-zero. Together with pi itself,
    // we get a basis of pid-adics modulo squares.
    sc := function(y) // y in K is a pid-unit
          r := [GF(2) | ];
          // Make y integral without changing its class mod squares
          dy := Denom(y);
          if IsEven(dy) then
            y *:= c^Valuation(dy, 2);
            dy := Denom(y);
            error if IsEven(dy), "Something is wrong in MakeModSquares in selmer.m!";
          end if;
          y := (dy mod 8)*O!(dy*y);
          z := (R!y)^(2^f-1); // put it into 1 + pid
          for i := 1 to e do
            // Determine contribution of (1 + ?*pi^(2*i-1))
            seq := Eltseq(m((K!O!(z - 1))/pi^(2*i-1)));
            r cat:= seq;
            for j := 1 to f do
              if seq[j] ne 0 then
                z *:= 1 + reps[j]*(R!pi)^(2*i-1);
              end if;
            end for;
            if i lt e then
              // Determine contribution of (1 + ?*pi^i)^2
              z2 := Sqrt(m((K!O!(z - 1))/pi^(2*i)));
              z *:= (1 + (R!(z2 @@ m))*(R!pi)^i)^2;
            else
              // Determine unramified contribution
              r cat:= [AbsoluteTrace(m((K!O!(z - 1))/K!4))];
            end if;
          end for;
          return r;
    end function;
    h := map< K -> V | x :-> V!([GF(2) | v] cat sc(x/pi^v)) where v := Valuation(x, pid)>;
  end if;
  return V, h;
end function;

intrinsic LocalTwoSelmerMap(p::RngIntElt)->Map
  {A map from Q^* to the group Qp^*/(Qp^*2)}
  require IsPrime(p):"p must be prime";
  if p eq 2 then
    S:=AbelianGroup([2,2,2]);
    L:=[S!0,S.2,S.3,S.2+S.3];
    function fn(a)
      v:=Valuation(a,2);
      i:=((Integers()!(a/2^v))-1) div 2 +1;
      //now i=1,2,3,4 depending on whether a/2^v = 1,3,5,7 mod 8.
      return v*S.1+L[i];
    end function;
    function fni(b)
      v:=Eltseq(b);
      return 2^v[1]*3^v[2]*5^v[3];
    end function;
  else
    S:=AbelianGroup([2,2]);
    k:=GF(p);
    bl:=exists(u){u: u in k | not(IsSquare(u))};
    u:=Integers()!u;
    assert bl;
    function fn(a)
      v:=Valuation(a,p);
      i:=IsSquare(k!(a/p^v)) select 0 else 1;
      return S![v,i];
    end function;
    function fni(b)
      v:=Eltseq(b);
      return p^v[1]*u^v[2];
    end function;
  end if;
  return map<Rationals()->S| a:->fn(a), b:->fni(b)>;
end intrinsic;

intrinsic Random(Z::RngInt, m :: RngIntElt) ->RngIntElt
{A random integer lying in the interval [-m, m]}
  return Random(-m,m);
end intrinsic;

intrinsic LocalTwoSelmerMap(p::RngOrdIdl)->Map
  {A map from K^* to the group Kp^*/(Kp^*2)}
  if not(assigned p`Record) then
    p`Record:=rec<IdealRecordFormat|>;
  end if;
  if not(assigned p`Record`LocalTwoSelmerMap) then
    // We assume that grp1 is returned in Smith Normal Form!!!
    // therefore, by construction, we know that grp1 has all its
    // factors of even order.
    grp1,mp1i:=RayResidueRing(p^(Valuation(Order(p)!4,p)+1));
    grp2,mp2:=quo<grp1|[2*grp1.i: i in [1..Ngens(grp1)]]>;
    mp1:=Inverse(mp1i);
    mp2i:=Inverse(mp2);
    grp:=AbelianGroup([2:i in [1..#Invariants(grp1)+1]]);
    FF:=FieldOfFractions(Order(p));
    u:=SafeUniformiser(p);
    fn:=function(a) 
        // assumes a ne 0, otherwise gives error
        a*:=Denominator(FF!a)^2;
	v:=Valuation(a,p);
	a/:=u^v;
        return grp!([v] cat Eltseq(mp2(mp1(a))));
    end function;
    fni:=function(b)
        v:=Eltseq(b);
        return u^v[1]*mp1i(mp2i(grp2![v[i]:i in [2..#Invariants(grp1)+1]]));
    end function;
    if Minimum(p) le 2 then  
      grpmap:=pmap<NumberField(Order(p))->grp|a:->fn(a),b:->fni(b)>;
    else  // Sebastian added this case to speed it up at large primes
      _,grpmap := MakeModSquares(NumberField(Order(p)),p);
    end if;
    rc:=p`Record;
    rc`LocalTwoSelmerMap:=grpmap;
    p`Record:=rc;
  end if;
  return p`Record`LocalTwoSelmerMap;
end intrinsic;

intrinsic Minimum(P::RngIntElt)->RngIntElt
{}
  return Abs(P);
end intrinsic;

intrinsic MinimalInteger(P::RngIntElt)->RngIntElt
{}
  return Abs(P);
end intrinsic;

intrinsic Order(P::RngIntElt)->RngInt
{}
  return Integers();
end intrinsic;

intrinsic SafeUniformiser(P::RngIntElt)->RngIntElt
{}
  return P;
end intrinsic;

/**
 ** Support(RngOrdIdl)
 **
 ** factorisation without multiplicity.
 **/

intrinsic Support(I::RngOrdFracIdl) -> SetEnum
  {returns the prime divisors of an ideal as a set}
  return {PowerIdeal(Order(I))|p[1]:p in Factorisation(I)};
end intrinsic;
