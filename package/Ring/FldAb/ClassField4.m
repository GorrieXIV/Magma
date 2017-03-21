freeze;


declare verbose GrunwaldWang, 2;

intrinsic SplittingField(data::SeqEnum[Tup]) -> FldAb
  {Gives a sequece of tuples <p, n_p>, find an extension of the base field 
    such that the completion at p has degree n_p and is umramified at all 
    the p's}

  // p can be 0 or a prime number (in which case the base field is Q)
  // or a place in which case the base field is whatever...


  if #data eq 0 then
    require not IsNull(data) :
      "Illegal empty sequence passed in";
    k := Universe(data)[1];
    if k cmpeq RngInt then
      ZZ := ext<Integers()|Polynomial([1,1])>;
      A := AbelianExtension(1*ZZ);
      return A;
    end if;
    error "sorry, cannot guess the number field";
  end if;  
  // data cannot be empty I'm afraid...
  if Type(data[1][1]) eq RngIntElt then
    k := Rationals();
    IsRel := false;
    is_inf := func<x|x eq 0>;
  else
    k := NumberField(data[1][1]);
    IsRel := true;
    is_inf := IsInfinite;
  end if;
  
  d := Lcm([x[2] : x in data]);
  vprint GrunwaldWang, 1 : "Looking for cyclic extension of degree", d;
  lp := Factorisation(d);
  lp := [x[1]^x[2] : x in lp];
  vprint GrunwaldWang, 2 : "Factorisation", lp;

  fin_data := [x : x in data | not is_inf(x[1])];
  inf_data := [x : x in data | is_inf(x[1]) and x[2] eq 2];
  if IsRel then
    ZZ := MaximalOrder(k);
    fin_data := [<Ideal(x[1]), x[2]> : x in fin_data];
    co := &meet [PowerIdeal(ZZ)|x[1] : x in fin_data ];
    co := Minimum(co);
    inf := [ b where a,b := IsInfinite(x[1]) : x in inf_data];
  else
    ZZ := ext<Integers()|Polynomial([-1,1])>;
    co := &*[Integers()|x[1] : x in data | x[1] ne 0];
    fin_data := [<x[1]*ZZ, x[2]> : x in fin_data];
    if #inf_data ne 0 then
      inf := [1];
    else
      inf := [];
    end if;
  end if;
  two_data := [x : x in fin_data | Minimum(x[1]) eq 2];
  c := 1*ZZ * &* [Parent(1/2*ZZ)| x[1]^(d-1+d*Valuation(2*ZZ, x[1])) : x in two_data];
  c := ZZ!!c;
  // There is an obstructio to the G-W theorem at 2 which means that we
  // have to allow ramification here. Easy example: [<2, 8>]: there
  // is no cyclic unramifed extension of degree 8 over Q_2.
  // (but this is the only problem)
  // The exact criterium can be found in Gras: Class Field Theory.
  p := 2;
  function local_degree(x, map)
    if Minimum(x) eq 2 then
      return y[1][1]*y[1][2] where 
        y := DecompositionType(AbelianExtension(map), x);
    else
      return Order(x@@map);
    end if;
  end function;
  repeat
    repeat
      p := NextPrime(p);
    until Gcd(p, co) eq 1 and exists{x : x in lp | p mod x eq 1};
    vprint GrunwaldWang, 2: "enlarging conductor by", p;

    c *:= p;
    R, mR := RayClassGroup(c, inf);
    q, mq := quo<R|[d*R.i : i in [1..Ngens(R)]]>;
    if #q eq 1 then //TODO: fix: if q is 1, the Conductor may die
      continue;
    end if;
    if Exponent(q) lt d then
      vprint GrunwaldWang, 1: "after factorisation by ", d, "group is too small";
      c := Conductor(AbelianExtension(Inverse(mq)*mR));
      continue;
    end if;
    if exists(x){x : x in fin_data | local_degree(x[1], Inverse(mq)*mR) lt x[2]} then
      vprint GrunwaldWang, 2 : "group to small at", x[1];
      c := Conductor(AbelianExtension(Inverse(mq)*mR));
      continue;
    end if;
    if #inf_data ne 0 and not inf subset b where a,b := Conductor(AbelianExtension(Inverse(mq)*mR)) then
      vprint GrunwaldWang, 2: "wrong order at infinite places";
      continue;
    end if;
    m := [((x[1])@@mR@mq) : x in fin_data | Minimum(x[1]) ne 2];
    qq, mqq := quo<q|[fin_data[i][2]*m[i] : i in [1..#m]]>;
    if exists(x){x : x in [1..#m] | Order(m[x]@mqq) ne fin_data[x][2]} then
      vprint GrunwaldWang, 2 : "group to small at", fin_data[x][1];
      c := Conductor(AbelianExtension(Inverse(mq)*mR));
      continue;
    end if;
    if exists(x){ x : x in two_data | local_degree(x[1], Inverse(mqq)*Inverse(mq)*mR) le x[2]} then
      vprint GrunwaldWang, 2 : "group to small at", fin_data[x][1];
      c := Conductor(AbelianExtension(Inverse(mq)*mR));
      continue;
    end if;
    s := sub<qq|[ (x[1])@@mR@mq@mqq : x in fin_data | Minimum(x[1]) ne 2]>;
    // maybe the kernel of the projection
    // c, inf -> c
    // need to be removed as well.
    // in general, all prescribed ramification has to be removed this way.
    if #inf ne 0 or #two_data ne 0 then
      cc := c*&*[Parent(1/2*ZZ)|x[1]^-Valuation(c, x[1]) : x in two_data];
      cc := Parent(c)!cc;
      S, mS := RayClassGroup(cc);
      m := InducedMap(mR, mS, 
           map<PowerIdeal(ZZ) -> PowerIdeal(ZZ) | x :-> x>, Minimum(c));
      s := sub<qq|s, Kernel(m) @mq @ mqq>;
    end if;

    f, cc := HasComplement(qq, s);
    
    if f then
      // not enough! qqq (s) is not neccessarily cyclic!!
      // SplittingField([<5,2>, <11,3>, <19,2>]);
      qqq, mqqq := quo<qq|cc>;
      ls := Subgroups(qqq:Quot := [d]);
      for i in ls do
        qqqq, mqqqq := quo<qqq|i`subgroup>;
        A := AbelianExtension(Inverse(mq*mqq*mqqq*mqqqq)*mR);
        a,b := Conductor(A);
        if inf subset b and
           forall{x : x in data | y[1]*y[2] eq x[2] where 
                               y := DecompositionType(A, x[1])[1]} then
          return A;
        end if;
      end for;
      vprint GrunwaldWang, 1: "no useful cyclic factor found";
    else
      vprint GrunwaldWang, 1: "no complement found";
      c := Conductor(AbelianExtension(Inverse(mq)*mR));
      continue;
    end if;
  until p gt 90*#data;
  error "SplittingField: primes exhausted, maybe too complicated example?";
  return false;
end intrinsic;

    
/*
<example>
k := MaximalOrder(x^4-13);
m := k;
k := NumberField(m);
p := Decomposition(k, 53) cat Decomposition(k, 59);
R, mR := RayClassGroup(5*3*m);
A := AbelianExtension(mR);
mKp := [ <q,w> where q,w := Completion(k, x[1]) : x in p];
Gp := [ <q,w, r> where 
    q,w, r := Completion(A, Ideal(p[i][1]):Comp := mKp[i]) : i in [1..#p]];
mUp := [ <Inverse(mq)*Gp[x][1], Inverse(mq)*Gp[x][3]>
    where _, mq := quo<Domain(Gp[x][1]) | Gp[x][2]> : x in [1..#Gp]];

R, mR := RayClassGroup(17*13*5^2*3^2*m);
q, mq := quo<R|[12*R.i : i in [1..Ngens(R)]]>;

q, w := GWW([x[1] : x in mUp], [x[2] : x in mKp], [x[2] : x in mUp], Inverse(mq)*mR, [Ideal(x[1]) : x in p]);

i := sub<Codomain(w[1]) | [ Image(x) : x in w]>;
I := Codomain(w[1]);
_, c := HasComplement(I, i);

D := [<Ideal(p[i][1]), mUp[i][1], mKp[i][2], mUp[i][2]> : i in [1..#p]];
GrunwaldWangTheorem(D);

</example>

<example>
  k := NumberField(x^3-4);
  m := MaximalOrder(k);
  lp := [ x[1] : x in Factorisation(5*7*m)];
  A := AbelianGroup([3,3]);
  im := [A.1, A.2, A.1+A.2];
  D := [ CreateCyclicData(lp[i], 3, im[i]) : i in [1..3]];
  
</example>


*/ 
