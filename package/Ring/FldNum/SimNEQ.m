freeze;

intrinsic SimNEQ(K::FldNum, e::FldNumElt, f::FldNumElt:S := false, HasSolution := false) -> BoolElt, []
  {Tries to find simultaneous solutions to the NEQ(e, K) and NEQ(f, K)}


  E := Parent(e);
  F := Parent(f);

  require IsSubfield(E, K): "e must be in a subfield of K";
  require IsSubfield(F, K): "f must be in a subfield of K";

  C, mC := ClassGroup(K:Bound := 500);
  rE := RelativeField(E, K);
  rF := RelativeField(F, K);
  Z_K := MaximalOrder(K);
 
  if S cmpeq false then
    S := Support(ideal<Z_K|Discriminant(rE)>) join Support(ideal<Z_K|Discriminant(rF)>);
    U := sub<C| [ x@@mC : x in S]>;
    p := 2;
    while U ne C do
      lp := Factorization(Z_K*p);
      ll := [ x[1] : x in lp | Norm(x[1]) lt 2000 or Degree(x[1]) eq 1];
      for i in lp do
        c := i @@ mC;
        if not c in U then
          U := sub<C|U, i>;
          Include(~S, i);
        end if;
      end for;
      p := NextPrime(p);
    end while;
  end if;
  S := Set(S) join Support(ideal<Z_K|e>) join Support(ideal<Z_K|f>);
  S := &join { Support(Z_K*K!p) : p in Set([Minimum(P) : P in S])};
  S := [ x : x in S];
  repeat
    U, mU, Base := SUnitGroup(S:Raw);

    n1 := map<K -> K | x :-> K!Norm(rE!x)>;
    N1 := SUnitAction(mU, n1, S:Base := Base);
    
    n2 := map<K -> K | x :-> K!Norm(rF!x)>;
    N2 := SUnitAction(mU, n2, S:Base := Base);

    pU, pUi, pUp := DirectSum([U, U]);
    N := hom<U -> pU | [ pUi[1](N1(U.i)) + pUi[2](N2(U.i)) : i in [1..Ngens(U)]]>;

    Uef := SUnitDiscLog(mU, [K!e, K!f, K!2], S:Base := Base);
    r := pUi[1](Uef[1]) + pUi[2](Uef[2]);
    
    if r in Image(N) then
      r := r@@N;
      r := mU(r);
      r := PowerProduct(Base, r);
      return true, [r];
    else
      if not HasSolution then
        return false, _; 
      end if;
    end if;
    p := Maximum([Minimum(s) : s in S]);
    repeat
      p := NextPrime(p);
      lp := Factorization(Z_K*p);
    until #[x : x in lp | Degree(x[1]) eq 1 or Norm(x[1]) lt 2000] ne 0;
    for x in lp do
      if Norm(x[1]) lt 2000 or Degree(x[1]) eq 1 then
        Append(~S, x[1]);
      end if;
    end for;
  until false;
end intrinsic;

intrinsic Hilbert90(a::FldNumElt, b::Map[FldNum, FldNum]:S := false) -> FldNumElt
  {Given an element a of norm 1, find an element x such that x/b(x) = a.}
  K := Parent(a);
  require Domain(b) eq Codomain(b) and Domain(b) eq K:
     "2nd argument must be an endomorphism of the field.";
  require Norm(a) eq 1: "1st argument must have norm 1.";

  if Type(K) eq FldQuad then
    C, mC := ClassGroup(K);
  else
    C, mC := ClassGroup(K:Bound := 500);
  end if;
  Z_K := MaximalOrder(K);
 
  if S cmpeq false then
    S := Support(ideal<Z_K|Discriminant(K)>);
    U := sub<C| [ x@@mC : x in S]>;
    p := 2;
    while U ne C do
      lp := Factorization(Z_K*p);
      ll := [ x[1] : x in lp | Norm(x[1]) lt 2000 or Degree(x[1]) eq 1];
      for i in lp do
        c := i @@ mC;
        if not c in U then
          U := sub<C|U, i>;
          Include(~S, i);
        end if;
      end for;
      p := NextPrime(p);
    end while;
  end if;
  S := Set(S) join Support(ideal<Z_K|a>);
  S := &join { Support(Z_K*K!p) : p in Set([Minimum(P) : P in S])};
  S := [ x : x in S];
  //CF TODO: use direct approach (see matrices) rather than SUnits...
  repeat
    U, mU, Base := SUnitGroup(S:Raw);

    n := map<K -> K | x :-> x/b(x)>;
    N := SUnitAction(mU, n, S:Base := Base, CheckAction := false);
    
    Ua := SUnitDiscLog(mU, K!a, S:Base := Base);
    
    if Ua in Image(N) then
      r := Ua@@N;
      r := mU(r);
      r := PowerProduct(Base, r);
      return K!r;
    end if;
    p := Maximum([Minimum(s) : s in S]);
    repeat
      p := NextPrime(p);
      lp := Factorization(Z_K*p);
    until #[x : x in lp | Degree(x[1]) eq 1 or Norm(x[1]) lt 2000] ne 0;
    for x in lp do
      if Norm(x[1]) lt 2000 or Degree(x[1]) eq 1 then
        Append(~S, x[1]);
      end if;
    end for;
  until false;

end intrinsic;
  

