freeze;

  /* by Claus Fieker, Feb 2003 */

/* <EXAMPLE>
// has C_6 clg
SetMemoryLimit(10^8);
kx := PolynomialRing(FiniteField(5)); x := kx.1;
kxy := PolynomialRing(kx); y := kxy.1;
SetKantVerbose("NUR_ZUM_TEST", 1);
K<a> := ext<FieldOfFractions(kx) | y^2-y*x+x^3+x^2*y+x^7>;
O := MaximalOrderFinite(K);
lp := Factorisation(a*O);
p := lp[1][1];
m := 3*Place(lp[1][1]) + 5*Place(lp[2][1]);
am,bm := RayClassGroup(m);

RayClassField(m, sub<am|am.7>);



</EXAMPLE> */

  // reduces a mod q-th powers (hopefully)
function GenReduce(a, q)
//intrinsic GenReduce(a::FldFunElt, q :: RngIntElt) -> FldFunElt
//  {}
  s,b := ProductRepresentation(a);
  b := [ x mod q : x in b];
  a := ProductRepresentation(s, b);
  d := Divisor(a);
  s,b := Support(d);
  d := &+ [Parent(d)| Sign(b[i])* (Abs(b[i]) div q) * s[i] : i in [1..#s]];
  td, r, A, z := Reduction(d);
  a := a*z^q;
  return a;
end function;

function MModpow(a, m, p)
  // p must be a place over some coefficient ring of the Parent of a

  function mmod(b)
    if Parent(b) cmpne FunctionField(p) then
      return Parent(b)![$$(x) : x in Eltseq(b)];
    else
      return Lift(Evaluate(b, p), p);
    end if;
  end function;

  s := mmod(a);
  b := Parent(a)!1;
  while m gt 0 do
    if IsOdd(m) then
      b := mmod(s*b);
    end if;
    if m gt 1 then
      s := mmod(s*s);
    end if;
    m div:= 2;
  end while;

  return b;
end function;

function MyExpand(a, p:AbsPrec := 10, PE := false) 
  v := Valuation(a, p);
  aa := a;
  if true and Degree(p) eq 1 and PE cmpeq false and 
     Type(BaseRing(FunctionField(p))) eq FldFunRat then
       i := 5;
       repeat
         z, pi := Expand(a, p:AbsPrec := AbsPrec+i);
         i+:=2;
       until AbsolutePrecision(z) ge AbsPrec;
    if false and GetAssertions() ge 1 then   
      e := Evaluate(z, pi);
      x := Valuation(e - a, p);
      if x lt AbsPrec then
        "Expand(", a, ", ", p, ":AbsPrec := ", AbsPrec, ");";
      end if;
      assert x ge AbsPrec;
    end if;
    return z;
  end if;
  if a eq 0 then
    return Zero(LaurentSeriesRing(ResidueClassField(p)));
  end if;
  v := Valuation(a, p);
  if PE cmpeq false then
    pi := UniformizingElement(p);
  else
    pi := PE;
  end if;
  assert Valuation(pi, p) eq 1;
  pi := 1/pi;
  a := a*pi^v;
  assert Valuation(a, p) eq 0;
  l := [];
  for i in [v..AbsPrec-1] do
    Append(~l, Evaluate(a, p));
    assert Valuation(a -Lift(l[#l], p), p) ge 1;
    a := (a-Lift(l[#l], p))*pi;
    assert Valuation(a, p) ge 0;
  end for;
  if l eq [] then
    l := [ResidueClassField(p)!0];  // XXX think about this!
  end if;
  zz := elt<LaurentSeriesRing(Universe(l))|v, l, #l>;
  if false and GetAssertions() then
    pi:= 1/pi;
    z := elt<LaurentSeriesRing(Parent(a)) | v, [Lift(x, p) : x in l], #l>;
    Parent(z);
    e := Evaluate(z, pi);
    x := Valuation(e - aa, p);
    "should be >= ", AbsPrec, x;
    assert x ge AbsPrec;
  end if;

  return zz;

  // l := [] will die!
end function;
  
intrinsic NonSpecialDivisor(m::DivFunElt: Exception := false) -> DivFunElt, RngIntElt
{Enlarges m into a non-special divisor. i.e. rD - m will be non-special, D and r are returned}

  K := FunctionField(m);
  deg := 1;  
  lp := Support(m);
  while Exception cmpeq false do
    llp := Places(K, deg);
    for i in llp do
      if not i in lp then
        Exception := i;
        break;
      end if;
    end for;
    deg +:= 1;
  end while;

  A := Exception; // to save typing...
  r := 0;
  while IndexOfSpeciality(r*A - m) gt 0 do
    r +:= 1;
  end while;

  return A, r;
end intrinsic;


intrinsic StrongApproximation(m::DivFunElt, a::[Tup]: Exception := false, Raw := false, Strict := false) -> FldFunElt
{a has to contain tuples of the form <PlcFunElt, FldFunElt>}

  require IsEffective(m): "m must be effective (positive)";
  require Exception cmpeq false or 
    Type(Exception) in {PlcFunElt, DivFunElt}:
    "Exception must be a place";
  require Exception cmpeq false or IsZero(Gcd(Exception, m)) :
    "The expectional place must be coprime to m";
  if #a eq 0 then
    return FunctionField(m)!1;
  end if;
  require #a ge 1 and #a[1] eq 2 and
          Type(a[1][1]) in {PlcFunElt, RngFunOrdIdl} and
          (Type(a[1][2]) in {FldFunElt, RngFunOrdElt} or
            Type(a[1][2]) eq SeqEnum and
              Type(a[1][2][1]) in {FldFunElt, RngFunOrdElt}):
    "a must be a sequence of tuples <PlcFunElt, FldFunElt>";

  if Strict then
    // we'll do it twice!
    // should be improved using some undocumented features and only
    // one call to StrongApproximation...
    
    require not Raw: "Cannot use Raw together with Strict";

    mm := m + &+ [ 1*p[1] : p in a];
    f := StrongApproximation(mm, a:Exception := Exception);
    a := [<p[1], UniformizingElement(p[1])^(Valuation(m, p[1]))> : p in a];
    return f+StrongApproximation(mm, a:Exception := Exception);
  end if;

  if Type(a[1][2]) in {FldFunElt, RngFunOrdElt} then
    if exists{x[2] : x in a | Valuation(x[2], x[1]) lt 0} then
      al := 0*m;
      am := [];
      K := FunctionField(m);
      for i in a do
        v := -Valuation(i[2], i[1]);
        if v gt 0 then
          if Type(i[1]) eq PlcFunElt then
            al +:= (v+1)*i[1]; // need +1 here, so that
                               // Valuation of al at P will be v and not >= v
            Append(~am, <i[1], UniformizingElement(i[1])^v>);
          else
            al +:= (v+1)*Place(i[1]);
            Append(~am, <i[1], PrimitiveElement(i[1])^v>);
          end if;
        else
          if Type(i[1]) eq PlcFunElt then
            al +:= Valuation(m, i[1])*i[1];
            Append(~am, <i[1], K!1>);
          else
            al +:= Valuation(m, i[1])*Place(i[1]);
            Append(~am, <i[1], K!1>);
          end if;

        end if;
      end for;
      al := StrongApproximation(al, am);
      pal, eal := Support(Divisor(al));
      //since we have to divide by al, we need to make sure that
      //after the division no negative valuations remain. So we extend
      //our approximation problem to force positive valuations at all
      //the places where al has.
      //Carefully avoiding the Exception of course...
      n := m;
      for i in a do
        n +:= Valuation(al, i[1])*i[1];
      end for;
      Exception := NonSpecialDivisor(-m);
      for i in pal do
        if not i in [ j[1] : j in a] then
          v := Valuation(al, i);
          if v gt 0 and Valuation(1*Exception, i) eq 0 then
            n +:= v*i;
            Append(~a, <i, UniformizingElement(i)^v>);
          end if;
        end if;
      end for;
      if Raw then
        q,w,r := StrongApproximation(n, [<i[1], al*i[2]> : i in a]: 
                                        Exception := Exception, Raw := Raw);
        q := [x/al : x in q];
        return q,w,r;
      else
        q := StrongApproximation(n, [<i[1], al*i[2]> : i in a]:
                                        Exception := Exception, Raw := Raw);
        q := q/al;
        if Type(a[1][2]) ne SeqEnum then
          assert forall{ x : x in a | 
                     Valuation(q - x[2], x[1]) ge Valuation(m, x[1])};
        end if;
        return q;
      end if;
    end if;
  end if;
 
  K := FunctionField(m);
  lp, lv := Support(m);

  A, r := NonSpecialDivisor(m :Exception := Exception);

  // now split a into places and elements...
  lpa := [x[1] : x in a];
  if Type(lpa[1]) eq RngFunOrdIdl then
    lpa := [Place(x) : x in lpa];
  end if;
  lpe := [x[2] : x in a];

  La := [K|];
  Lb := [];
  for i in [1..#lpa] do

    pl := lpa[i];
    if not pl in lp then
      exp := 0;
      continue;
    else
      exp := lv[Position(lp, pl)];
    end if;

    D := m - exp*pl;
    B := Basis(r*A - D);

    k := ConstantField(K);
    // can't use Expand here, Florian does not support deg > 1
    // I'm sure he had a a reason!
    // (he had: Expand is kind of wrongish in the general situation, i.e.
    // it is not a ring embedding but it should preserve the k-vector space
    // structure) (which is all we need here)

    M := Matrix( [ &cat [ Eltseq(Coefficient(x, i), k) : i in [0..exp-1]] 
      where x := MyExpand(K!y, pl: AbsPrec :=  exp) : y in B]);
    //can't use Eltseq because it's not returning leading zeroes!
    
    if Type(lpe[i]) in {FldFunElt,RngFunOrdElt} then
      v := Matrix( [ &cat [ Eltseq(Coefficient(x, j), k) : j in [0..exp-1]]])
                 where x := MyExpand(K!lpe[i], pl: AbsPrec:= exp);

      Append(~La, &+ [ B[j] * v[1][j] : j in [1..#B]]
                 where v := Solution(M, v)); 
    else
      lj := [];
      for j in lpe[i] do
        v := Matrix( [ &cat [ Eltseq(Coefficient(x, j), k) : j in [0..exp-1]]])
                   where x := MyExpand(K!j, pl: AbsPrec:= exp);

        Append(~lj, &+ [ B[j] * v[1][j] : j in [1..#B]]
                   where v := Solution(M, v)); 
      end for;             
      Append(~La, lj);
    end if;

    if Raw then
      v *:= 0;
      v[1][1] := 1; // v is the expansion of 1
      Append(~Lb, &+ [ B[j] * v[1][j] : j in [1..#B]]
                 where v := Solution(M, v));

    end if;
  end for;

  if Raw then
    return La, Lb, r*A;
  else 
    return &+ La;
  end if;
end intrinsic;
  

function pCeiling(a, p) // do better, this is incredible slow....
  return p^Ceiling(Maximum(Log(p, a), 0));
end function;

function UnitsModPtoM(p, m)
  // computes (and returns) a basis for the multiplicative group
  // of O/p^m. p should be a prime ideal and m>0

  if Type(p) eq PlcFunElt then
    p := Ideal(p);
  end if;

  F, mF := ResidueClassField(p);

  ppi := PrimitiveElement(F) @@ mF;
  B := [<ppi, #F-1> ];
  pi := PrimitiveElement(p);
  j := 1;
  pj := pCeiling(m/j, Characteristic(F));
  bas := AbsoluteBasis(F);
  bas := [x@@mF : x in bas];
  while j lt m do
    pij := pi^j;
    B cat:= [ <1+i*pij, pj> : i in bas];
    repeat
      j +:= 1;
    until j mod Characteristic(F) ne 0;
    pj := pCeiling(m/j, Characteristic(F));
  end while;
  return B;
end function;

function DiscLogModPtoM(elt, p, m:UseProdRep := true)
  // DiscLog wrt B as produced by UnitsModPtoM
  //  "DiscLogModPtoM(", elt, ", ... : UseProdRep := ", UseProdRep, ");";

  if Type(p) eq PlcFunElt then
    p := Ideal(p);
  end if;

  if UseProdRep then
    ba, ex := ProductRepresentation(elt);
    if #ba gt 1 then
      tv := 0;
      tdl := false;
      pi := PrimitiveElement(p);
      for i in [1..#ba] do
        v := Valuation(ba[i], p);
        if v ne 0 then
          tv +:= v*ex[i];
          if v gt 0 then
            r := ba[i] / pi^v;
          else
            r := ba[i] * pi^(-v);
          end if;
        else
          r := ba[i];
        end if;
        dl := DiscLogModPtoM(r, p, m:UseProdRep := false);
        if tdl cmpeq false then
          tdl := [j*ex[i] : j in dl];
        else
          tdl := [tdl[j] + dl[j]*ex[i] : j in [1..#dl]];
        end if;
      end for;
      assert tv eq 0;
      return tdl;
    end if;
  end if;
  
  assert e cmpne 0 and e cmpne Infinity() where e := Evaluate(elt, Place(p));

  F, mF := ResidueClassField(p);
  O := Parent(elt);
  Z := Integers();
 
  a := Log(Evaluate(elt, Place(p)));
  b := [a];
  pm := p^m;
  mpm := Minimum(pm);
  while not ISA(Type(mpm), RngElt) do
    mpm := Minimum(mpm);
  end while;

  if m eq 1 then
    return b;
  end if;

  pi := PrimitiveElement(p);
  ppi := PrimitiveElement(F) @@ mF;
  r := (#F-1)*#F^(m-1);
  elt := elt*Modexp(Order(p)!ppi, (a*(r-1)) mod r, mpm);
//  if elt in Order(p) then
//    elt := Order(p)!elt;
//    elt := elt mod pm;
//  end if;

  bas := AbsoluteBasis(F);

  j := 1;
  pj := pCeiling(m/j, Characteristic(F));

  while j lt m do
    pij := Modexp(pi, j, mpm);
    a := (elt - 1)/pij;
    fa, re := Valuation(j, Characteristic(F));
    fa := Characteristic(F)^fa;
    // as long as I know whats going on: (roughly)
    //
    //Let U := (1+p*O) (one-units) and
    //    U^n := 1+p^n*O (of level n)
    // we know (by Auer's Diss, p 38) U/U^n has a basis
    // (1+b p*r) where b in B (a basis for the constant field over the
    // prime field) and 1 <= r <n. (n,p) = 1.
    // Furthermore, ord(1+b*p^r) = pCeiling(n/r)
    // so we basically do on each level:
    // subtract 1, divide by p^level and map into the finite field.
    // Then divide by the decomposition.
    // The problem now is that this way we have to do it for all levels
    // and not only for those coprime to p!
    // But we have to adjust things as the basis is fixed:
    // on level p we should use the same basis as on level 1 but to the p-th
    // power....
    aa := Flat(Root(Evaluate(a, Place(p)), fa)); 
    b cat:= ChangeUniverse(aa, Z);
    me := Modexp(pi, re, mpm);
    
    elt *:= &* [ Modinv(Modexp(1+(bas[i])@@mF* me, fa*Z!aa[i], mpm
                               ),pm
                        ) : i in [1..#bas]] ;
//    if elt in Order(p) then
//      elt := Order(p)!elt;
//      elt := elt mod pm;
//    end if;
                           
    j +:= 1;
    assert Valuation(elt -1, p) ge j;

    pj := pCeiling(m/j, Characteristic(F));
  end while;

  // now reduce it to reflect the Basis ...
  // essentially if the "level" is divisible by the characteristic,
  // copy them down
  j := m;
  while j ge 1 do
    repeat 
      j -:= 1;
    until j mod Characteristic(F) eq 0;
    if j eq 0 then
      break;
    end if;
    for i in [1..#bas] do
      b[1+(j div Characteristic(F)-1)* #bas+i] +:= 
                               Characteristic(F)*b[1+(j-1)* #bas+i];
    end for;
    for i in [1..#bas] do
      Remove(~b, 1+ (j-1)* #bas+1);
    end for;
  end while;
  return b;
end function;

DivFunEltRecFmt := recformat<RayResidueRingMap : Tup, RayClassGroupMap : Tup>;

intrinsic RayResidueRing(D::DivFunElt) -> GrpAb, Map
{The Residue ring mod^* D}
  if HasAttribute(D, "Record")  and assigned D`Record`RayResidueRingMap then
    return Domain(x), x where x := D`Record`RayResidueRingMap[1];
  end if;
  require IsPositive(D): "Divisor must be positive";

  D_orig := D;
  if IsRationalFunctionField(FunctionField(D)) then
    k := FunctionField(D);
    K := RationalExtensionRepresentation(k);
    D := DivisorGroup(K)!D;
    convert := true;
  else
    convert := false;
  end if;  

  lp, lv := Support(D);
  K := FunctionField(D);
  g := [];
  b := [];
  for i in [1..#lp] do
    m := lv[i];
    G := UnitsModPtoM(lp[i], m);
    Append(~b, [K|x[1] : x in G]);
    Append(~g, [x[2] : x in G]);
  end for;

  // use CRT to find different generators. Problem is that
  // generators for p1 may be in p2 rather than coprime to everything.
  // Do we have weak approximation for Alff's? Yes, but we also have strong
  // approximation...
  // now change generators...
  // Further optimization shows that we don't need generators...
  rel := [];
  for i in [1..#lp] do
    x := [ [0*j: j in k ] : k in g];
//    zz := b[i][1]^g[i][1];
    pm := Ideal(lp[i])^lv[i];
    mpm := Minimum(pm);
    while not ISA(Type(mpm), RngElt) do
      mpm := Minimum(mpm);
    end while;

    z := Modexp(Order(Ideal(lp[i]))!b[i][1], g[i][1], mpm);

    x[i] := DiscLogModPtoM(z, lp[i], lv[i]);
//    _y := DiscLogModPtoM(zz, lp[i], lv[i]);
//    assert x[i] eq _y;
    x[i][1] := -g[i][1];
    if (#g[i] gt 1) then
      g[i][1] *:= Maximum(g[i][2..#g[i]]); 
    end if;
                  // the order is p^? * old g[i][1], but ALWAYS a multiple 
                  // of the order coming from the relation in x[i].
                  // The maximum SHOULD be a p-th power.
    Append(~rel, &cat x);
    for j in [2..#b[i]] do
      x[i] := [0 : k in [1..j-1]] cat [g[i][j]] cat [0: k in [j+1..#b[i]]];
      Append(~rel, &cat x);
    end for;
  end for;

  GG := AbelianGroup(&cat g);
  G, qG := quo<GG | rel>;
  F := FunctionField(D);

  sta := [0];
  for i in [1..#b] do
    sta[i+1] := sta[i] + #b[i];
  end for;

  // maybe one should store lp[i]^lv[i] somewhere....
  // but currently this does not produce runtime problems so why make it
  // more complicated?
  //
  // Alternate approach: do a PowerProduct mod D with the generators as
  // computed above (c). Problem here is that D might contain finite and
  // infinite places so reduction modulo the ideal is hard.
  function mo(id)
    m := Minimum(id);
    while not ISA(Type(m), RngElt) do
      m := Minimum(m);
    end while;
    return m;
  end function;  
  function f1(x)
    x := Eltseq(x @@ qG);
    x := [&* [Modexp(Order(id)!b[i][j], x[sta[i]+j], mo(id))
                   where id := Ideal(lp[i])^lv[i]
             : j in [1..#b[i]]] mod (Ideal(lp[i])^lv[i])
               : i in [1..#lp]];
               
    s := StrongApproximation(D, [<lp[i], x[i]> : i in [1..#lp]]);
    if convert then
      return FunctionField(D_orig)!s;
    else
      return s;
    end if;
  end function;
  function f2(y:Ignore := false)
    if convert then
      y := K!y;
    end if;
    r := [];
    for i in [1..#lp] do
      if Ignore cmpne false and lp[i] in Ignore then
        r cat:= [0 : j in [1..#g[i]]];
      else
        r cat:= DiscLogModPtoM(y, (lp[i]), lv[i]);
      end if;
    end for;
    return qG(GG!r);
  end function;

  mp := map<G -> F | x :-> f1(x), y:-> f2(y)>;
  if not HasAttribute(D_orig, "Record") then
    D_orig`Record := rec<DivFunEltRecFmt | >;
  end if;
  r := D_orig`Record;
  r`RayResidueRingMap := <mp, qG, g, f2>;
  D_orig`Record := r;
  return G, mp;
end intrinsic;

function make_coprime(id, m0)
  // finds an element a such that id*a is an integral ideal coprime to m0
  // (which better be an integeral ideal of the same order)
  // we'll do it for DIVISORS!!!!!

  F := FunctionField(id);
  if Set(Support(id)) meet Set(Support(m0)) eq {} then
    return F!1;
  end if;
  a := Gcd(id, m0);
  
  p := [<p, UniformizingElement(p)^Valuation(id, p)> : p in Support(id)]
    cat [ <p, UniformizingElement(p)^0> : p in Support(m0)
                                              | Valuation(a, p) eq 0];

  a := Set(Support(id));
  b := Set(Support(m0));
  m := 0*id;
  for i in a do
    m +:= Max(1, Valuation(id, i)+1)*i;
  end for;
  for i in b diff a do
    m +:= Valuation(m0, i)*i;
  end for;

  r := StrongApproximation(m, p);
  assert Set(Support(id-Divisor(r))) meet Set(Support(m0)) eq {};

  return r;
end function;  

intrinsic RayClassGroup(m::DivFunElt) -> GrpAb, Map
{The Ray class group mod m}

  if HasAttribute(m, "Record") and assigned m`Record`RayClassGroupMap then
    return Domain(x), x where x := m`Record`RayClassGroupMap[1];
  end if;

  require IsEffective(m): "Argument 1 must be an effective (positive) divisor";

  K := FunctionField(m);
  k := ConstantField(K);
  ecf, mecf := ExactConstantField(K);

  cg, mcg := ClassGroup(K);

  ngen := [ make_coprime(mcg(cg.i), m) : i in [1..Ngens(cg)]];

  rg, mrg := RayResidueRing(m);

  fx := mecf(PrimitiveElement(ecf));

  // we have to think in terms of
  // (RayResidueRing | ClassGroup) mod ecf. So the number of genereators
  // is Ngens(rg) + Ngens(cg) and then factor out by
  //  - the ecf
  //  - the generators for cg.i^order(cg.i) in rg
  //  I think I'll ignore the Z factor in the cg for now....

  rels := [];
  nrg := Ngens(rg);
  ngens := nrg + Ngens(cg);
  for i in [1..Ngens(rg)] do
    a := [0 : i in [1..ngens]];
    a[i] := Order(rg.i);
    Append(~rels, a);
  end for;
  for i in [1..Ngens(cg)-1] do
    q,w := IsPrincipal(Order(cg.i)*(cg.i@mcg));
    assert q;
    w *:= ngen[i]^-Order(cg.i);
    a := Eltseq(-(w @@ mrg)) cat [0: j in [1..i-1]] cat [Order(cg.i)]
                          cat [0: j in [i+1..Ngens(cg)]];
    Append(~rels, a);
  end for;

  a := Eltseq(fx @@ mrg) cat [0: j in [1..Ngens(cg)]];
  Append(~rels, a);

  GG := FreeAbelianGroup(ngens);
  G, qG := quo<GG|rels>;

  function f1(x) // map from G to Div
    x := Eltseq(x@@qG);
    a := rg!x[1..nrg];
    a := a @ mrg;
    d := &+ [ x[nrg+i]*(mcg(cg.i) - Divisor(ngen[i]) ) : i in [1..Ngens(cg)]];
    d +:= Divisor(a);
    return d;
  end function;

  ll := [(mcg(cg.i) - Divisor(ngen[i])) : i in [1..Ngens(cg)]];

  function f2(y:Ignore := false) // the inverse...
    if Ignore cmpeq false then
      if not IsPositive(-Gcd(y, m)) then
        error "Error: argument must be coprime to the modulus";
      end if;
    end if;
    x := (1*y)@@mcg;
    x := Eltseq(x);
    y -:= &+ [ x[i] * ll[i] : i in [1..#x]];
    w, y := IsPrincipal(y);
    assert w;
    if Ignore cmpeq false then
      z := (1*y)@@mrg;
    else
      z := m`Record`RayResidueRingMap[4](y:Ignore := Ignore);
    end if;
    z := qG(GG!(Eltseq(z) cat x));
    return z;
  end function;

  h := map<G -> Parent(m)| x:->f1(x), y:->f2(y)>;
  r := m`Record;
  r`RayClassGroupMap := <h, qG, [car<DivisorGroup(K), G>|], f2>;
  m`Record := r;
  return G, h;
end intrinsic;

intrinsic RayClassGroupDiscLog(y::DivFunElt, m::DivFunElt) -> GrpAbElt
{}
  am, bm := RayClassGroup(m);
  store := m`Record`RayClassGroupMap[3];
  i := Position([x[1] : x in store], y);
  if i ne 0 then
    return store[i][2];
  end if;

  z := y@@bm;
  Append(~store, <y, z>);
  r := m`Record;
  r`RayClassGroupMap[3] := store;
  m`Record := r;
  return z;
end intrinsic;
intrinsic RayClassGroupDiscLog(y::PlcFunElt, m::DivFunElt) -> GrpAbElt
{The intrinsic version of the Disc-Log function for ray class groups mod y}
  return RayClassGroupDiscLog(1*y, m);
end intrinsic;




// ClassFields...
// Strategy:
//  - split into p^n powers
//  - compute the discriminant of the field
//  - for p eq Characteristic 
//    - use the discriminant and StrongApproximation with Raw to get an
//      Riemann-Roch space containing or Artin-Schreier generator
//    - get a F_p (NOT F_q) basis for L(D)/ AS(L(D))
//    - if dim == 1: done
//    - otherwise: establish Artin-map and find "the" generator
//  - p ne Characteristic:
//    - adjoin (if neccessary) the Roots of unity. This is unramified!
//    - compute the discriminant of the class field + roots of unity
//    - compute S-Units for S containing m and the class group gens
//    - establish Artin-map
//    - find generator
//    - decent (get rid of roots of unity)
//
//  TODO: 
//        Constant Field extension + Automorphisms
//        p-Torsion of Clgp (Florian)
//


// Think of the field E := F(a : where a^n in gens). F has to contain a
// primitive n'th root of unity (zeta). The
// ArtinAutomorphism to any such a (the Frobenius) at p can be
// represented as
// a^Norm(Ideal(p)) = a zeta^x mod p
// where x in [0..n-1]. This function returns the sequence of the x
// or false if some gen is not coprime to p
function KummerDiscLog(gens, zeta, n, p)
//intrinsic KummerDiscLog(gens :: [ FldFunElt ], zeta, n, m::DivFunElt, p::PlcFunElt) -> Mtrx
//{Returns a Matrix containing the ArtinAutomorphism of p}

  F := Universe(gens);
  k := ConstantField(F);
  Fp := PrimeField(k);

  l := Characteristic(F);
  assert Gcd(n, l) eq 1;
  dl := [];
  ex := #k^Degree(p);
  assert ex mod n eq 1;
  assert ex eq #ResidueClassField(p);
  ex := ex div n;
  zeta := Evaluate(zeta, p);
  zeta := [Parent(zeta) | 1, zeta];
  for i in [3..n] do
    zeta[i] := zeta[i-1] * zeta[2];
  end for;
  assert #Set(zeta) eq n; 

  for i in gens do
    a := Evaluate(i, p);
    if a eq 0 then
      return false;
    end if;
    
    a := a^ex;
    Append(~dl, Position(zeta, a)-1);
  end for;

  return Matrix([dl]);
end function;

function CondDisc(m:Cond := false, SG := false, Ignore := false)
  Ghom := m`Record`RayClassGroupMap[1];
  G := Domain(Ghom);
  qG := m`Record`RayClassGroupMap[2];

  rGhom := m`Record`RayResidueRingMap[1];
  rG := Domain(rGhom);
  rqG := m`Record`RayResidueRingMap[2];
  ords := m`Record`RayResidueRingMap[3];
  // explanation(?):
  // #ords = #Support(m)
  // #ord[i] = number of Cyclic factors in o/p^n. It is <= then the exponent
  // ord[i][1] will be #RCF()-1
  // ord[i][2] .. will be Char^l
  //           ..         char^(l-1)
  //           ..         
  //           ..         char
  // and they correspond to the generators of rqG IN THIS ORDER          

  if SG cmpeq false then
    SG := sub<G|>;
  end if;

  lp := Support(m);
  // life is even worse: we have to go back another level to the
  // RayResidueRing generators...
  // meaning, we have to strip off the last components (they come from the
  // class group), lift the front part and glue it back together.
  n := Ngens(Domain(qG));

  F := FunctionField(m);
  k := ConstantField(F);
  char := Characteristic(k);

  Gp, qGp := quo<G|SG>;
  if not Cond then
    if not IsFinite(Gp) then
      error "Error: defining group must be finite";
    end if;
  else
    cond := 0*m;
  end if;

  if not Cond then
    Disc := #Gp*m;
  end if;

  if Ignore cmpne false then
    sub_group := [ [G!x : x in Generators(SG)]];
  end if;


  for ip in [1..#lp] do
    if Ignore cmpne false and
      not lp[ip] in Ignore then
        continue;
    end if;
    p := lp[ip];
    f := Degree(k, PrimeField(k))* Degree(p);
    start := &+ [Integers()| #ords[i] : i in [1..ip-1]];
    gp := Gp;
    qgp := qGp;
    kmax := 0;
    for k in Reverse([1..Valuation(m, p)-1]) do
      // compute the RayClassGroup of m - k*p
      // 1st find the the generator, 2nd it's order...
      pos := k;
      ord := 1;
      while pos mod char eq 0 do
        ord *:= char;
        pos div:= char;
      end while;
      pos -:= #[i : i in [1..pos] | i mod char eq 0];
      nng := [];
      for j in [1..f] do
        ng := ord * Domain(rqG).(start+f*(pos-1)+j+1);
        ng := rqG(ng);
        ng := Eltseq(ng);
        ng cat:= [0: i in [1..n-#ng]]; /* for the class group generators */
        ng := Domain(qG)!ng;
        ng := qG(ng);
        Append(~nng, ng);
      end for;

      if Ignore cmpne false then
        Append(~sub_group, nng);
      elif Cond then
        if not forall{ng : ng in nng | ng in SG} then
          kmax := k+1;
          break;
        end if;
      else
        gp, nqgp := quo<gp | [qgp(ng) : ng in nng]>;
        qgp := qgp * nqgp;
        Disc -:= #gp * p;
      end if;
    end for;
    // now deal with the 1st factor...
    if (Cond and kmax eq 0) or not Cond or Ignore cmpne false then
      ng :=  Domain(rqG).(start+1);
      ng := rqG(ng);
      ng := Eltseq(ng);
      ng cat:= [0: i in [1..n-#ng]]; /* for the class group generators */
      ng := Domain(qG)!ng;
      ng := qG(ng);
      if Ignore cmpne false then
        Append(~sub_group, [ng]);
      elif Cond then
        if not ng in SG then
          kmax := 1;
        end if;
      else
        gp, nqgp := quo<gp | qgp(ng)>;
        qgp := qgp * nqgp;
        Disc -:= #gp * p;
      end if;
    end if;
    if Cond then
      cond +:= kmax * p;
    end if;
  end for;
  if Ignore cmpne false then
    return sub_group;
  elif Cond then
    return cond;
  else
    return Disc;
  end if;
end function;

/*
intrinsic IgnoreConductor(m::DivFunElt, SG::GrpAb, lp::[PlcFunElt]) -> DivFunElt
{The conductor of the RayClassGroup mod m}
  return CondDisc(m : SG := SG, Ignore := lp);
end intrinsic;
*/

intrinsic Conductor(m::DivFunElt) -> DivFunElt
{The conductor of the RayClassGroup mod m}
  return CondDisc(m : Cond := true);
end intrinsic;

intrinsic Conductor(m::DivFunElt, SG :: GrpAb) -> DivFunElt
{The conductor of the quotient of the RayClassGroup mod m by SG}
  require HasAttribute(m, "Record") and assigned m`Record`RayClassGroupMap : 
    "the RayClassGroup of m must be known";  
  require SG subset Domain(m`Record`RayClassGroupMap[1]) : 
    "the group must be a subgroup of the RayClassGroup";
  return CondDisc(m : Cond := true, SG := SG);
end intrinsic;

intrinsic DiscriminantDivisor(m::DivFunElt, SG :: GrpAb) -> DivFunElt
{The DiscriminantDivisor of the RayClassField mod m and SG.}
  require HasAttribute(m, "Record") and assigned m`Record`RayClassGroupMap : 
    "the RayClassGroup of m must be known";  
  require SG subset Domain(m`Record`RayClassGroupMap[1]) : 
    "the group must be a subgroup of the RayClassGroup";
  return CondDisc(m : Cond := false, SG := SG);
end intrinsic;

intrinsic DegreeOfExactConstantField(m::DivFunElt) -> RngIntElt
{The degree of the exact constant field of the extension defined by the data over the constant field}
  return Valuation(0, 3);
end intrinsic;

intrinsic DegreeOfExactConstantField(m::DivFunElt, SG::GrpAb) -> RngIntElt
{The degree of the exact constant field of the extension defined by the data over the constant field}

  require (HasAttribute(m, "Record") and assigned m`Record`RayClassGroupMap)
           or SG cmpeq false : 
    "the RayClassGroup of m must be known";  
  require SG subset Domain(m`Record`RayClassGroupMap[1]) : 
    "the group must be a subgroup of the RayClassGroup";
  am, bm := RayClassGroup(m);

  if SG cmpeq false then
    SG := sub<am|>;
  end if;

  h := hom<am -> FreeAbelianGroup(1) | [ 0 : i in [1..Ngens(am)-1]] cat
                                          [Degree(am.Ngens(am) @ bm)]>;
  d := [Eltseq(h(x))[1] : x in Generators(SG)];
  if #d eq 0 then 
    return a where a := Valuation(0, 3); // infinity - but I don't know
                                         // how to create it properly
  end if;
  d := Gcd([Eltseq(h(x))[1] : x in Generators(SG)]);
  return d;
end intrinsic;

function Hurwitz(m, SG);
  // m is a divisor
  // d has to be (I think) the degree of the constant field extension
  // inside our class field!!!!!!!!
  // According to Florian (and not unlikely) d is the minimum (non zero) of 
  // degrees in SG. Since the last factor (summand) in the group does
  // correspond to Z and is generated by the non deg 0 things, we just project
  // onto it and get the generator for the resulting group.
  bm := m`Record`RayClassGroupMap[1];
  am := Domain(bm);

  h := hom<am -> FreeAbelianGroup(1) | [ 0 : i in [1..Ngens(am)-1]] cat
                                          [Degree(am.Ngens(am) @ bm)]>;
  d := Gcd([Eltseq(h(x))[1] : x in Generators(SG)]);
  // we need more: the degree of the extension
  deg := #quo<am|SG>;

  k := FunctionField(m);

  return Integers()!((deg * (Genus(k)-1) + 1/2*Degree(CondDisc(m:Cond := false, SG := SG)))/d + 1);
  
end function;

intrinsic Genus(m::DivFunElt, SG :: GrpAb) -> RngIntElt
{The genus of the RayClassField mod m and SG}
  require HasAttribute(m, "Record") and  assigned m`Record`RayClassGroupMap : 
    "the RayClassGroup of m must be known";  
  require SG subset Domain(m`Record`RayClassGroupMap[1]) : 
    "the group must be a subgroup of the RayClassGroup";
  return Hurwitz(m, SG);
end intrinsic;

//TODO: interface to Auer like conventions (according to Florian: always
//      ramify the infinite place)
//      Do place enum in C as this is rather hackish...

//import "ClassField1.m" : CreateHom;

function CreateHom(G, GG, mp)
  // h := hom<G -> GG | mp>;  // does not work ...
  // mp is a list of pairs. We want to constuct the map
  // that sends mp[i][1] -> mp[i][2].
  // XXX this seems to be wrong in rare cases, no idea why.
 
  m1 := Matrix(Integers(), [Eltseq(x[1]) : x in mp]);
  m1 := VerticalJoin(m1, DiagonalMatrix([ Order(G.x) : x in [1..Ngens(G)]]));
  _, t := EchelonForm(m1);
  m1 := Matrix(Integers(), [Eltseq(x[2]) : x in mp]);
  t := Matrix(Integers(), [ Eltseq(t[i])[1..#mp] : i in [1..Nrows(t)]]);
  m1 := t*m1;
  mp := [ GG!Eltseq(m1[i]) : i in [1..Ngens(G)]];
  h := hom<G -> GG | mp>; 
  return h;
end function;  

function MyDecompositionType(K, p) 
//intrinsic MyDecompositionType(K::FldFun, p::PlcFunElt) -> []
//{}
  // assumes that p is NOT ramified and coprime to almost everything
  // will return false if it encounters any problems.
  f := DefiningPolynomial(K);
  f := Eltseq(f);
  g := [];
  for i in f do
    j := Evaluate(i, p);
    if j cmpeq Infinity() then
      return false;
    end if;
    Append(~g, j);
  end for;
  g := Polynomial(g);
  if Degree(g) ne #f-1 then
    return false;
  end if;
  g := Factorisation(g);
  if exists{x : x in g | x[2] gt 1} then
    return false;
  end if;
  return [ <Degree(i[1]), i[2]> : i in g];
end function;

function MyDivisor(a,b)
  if Type(a) eq RngFunOrdIdl then
    return Divisor(a,b);
  elif Type(a) eq FldFunRatUElt then
    fin := func<X| &+ [Parent(X)|b[i]*a[i] : i in [1..#a] | IsFinite(a[i])] where a,b := Support(X)>;
    inf := func<X| &+ [Parent(X)|b[i]*a[i] : i in [1..#a] | not IsFinite(a[i])] where a,b := Support(X)>;
    return fin(Divisor(a)) + inf(Divisor(b));
  else
    error "not supported";
  end if;
end function;

intrinsic NormGroup(E::FldFun : Cond := false,AS := false, Extra := 5) -> DivFunElt, GrpAb
{Compute the probable norm group of the extension E.}

  // do better: use PolyDisc rather than DifferentDivisor (which means maximal
  // order computation and is therefore a tiny bit expensive...)
  // Careful about non integral polys!
  // Not neccessarily better, the index might be HUGE
  // Try to use the ArtinSchreierWitt attribute when present
  K := BaseField(E);
  if assigned E`ArtinSchreierWitt and AS cmpeq false then
    AS := E`ArtinSchreierWitt;
  end if;
  if AS cmpne false and Cond cmpeq false then
    a := Eltseq(AS);
    p := Characteristic(K);
    c := 0*Divisor(K!1);
    for i in [1..#a] do
      c := Gcd(p*c, Divisor(a[i]));
    end for;
    c := -c;
    a,b := Support(c);
    c := &+ [ (b[i]+1)*a[i] : i in [1..#a]];
    Cond := c;
  end if;
  if Cond cmpeq false then
    c := MyDivisor(Norm(a), Norm(b)) where a,b := Ideals(DifferentDivisor(E));

//    Mf := MaximalOrderFinite(K);
//    Mi := MaximalOrderInfinite(K);
//    c := Divisor(Mf*Discriminant(Polynomial(K,
//                             DefiningPolynomial(EquationOrderFinite(E)))),
//                 Mi*Discriminant(Polynomial(K,
//                             DefiningPolynomial(EquationOrderInfinite(E)))));
  else
    c := Cond;
  end if;

  K := CoefficientField(E);
  p := Characteristic(K);
  _ := Support(c); // for printing
  vprint ClassField, 1: "RCG...", c;
  am, bm := RayClassGroup(c);
  vprint ClassField, 1: "is ", AbelianInvariants(am);
  d := Degree(E);
  s := sub<am | [d*am.i : i in [1..Ngens(am)]]>;
  s := sub<am |>;

  x := PolynomialRing(K).1;
  r := PlaceEnumInit(K : Coprime := c);
  done := Extra;
  G := AbelianGroup([Degree(E)]);
  repeat
    p := PlaceEnumNext(r);
    l := MyDecompositionType(E, p);
    if l cmpeq false then
      vprint ClassField, 2: "ignore";
      continue;
    end if;
    assert forall{e[2] : e in l | e[2] eq 1};
    assert forall{e[1] : e in l | e[1] eq l[1][1]};
    s := sub<am | s, [i[1] * RayClassGroupDiscLog(p, c) : i in l]>; 
    vprint ClassField, 2: "group now: ", AbelianInvariants(quo<am|s>);
    if IsFinite(q) and #q le Degree(E) where q := quo<am|s> then
      done -:= 1;
    end if;
  until done eq 0;

  return c, s;
end intrinsic;
    
//next step: the kummer theory....
//(and then the combining things)
//
// as we currently don't store cyclotomic extensions, this is only efficient
// because FldFun's with class groups are structure created and will NEVER
// be deleted...
// so one deletion is handled properly, we have to cache this information.

declare attributes FldFun : CylcotomicExtensions, ArtinSchreierWitt, ArtinSchreierWittTower;

function KummerGenerators(m, SG:WithAut := false)
//intrinsic KummerGenerators(m::DivFunElt, SG::GrpAb:WithAut := false) -> FldFunElt
//{Generators for some abelian extension...}
  am, bm := RayClassGroup(m);
  Q, mQ := quo<am| SG>;
  q := #Q;
  lp := Factorisation(q);
  K := FunctionField(m);
  
  error if not (#lp eq 1 and Gcd(lp[1][1], Characteristic(K)) eq 1),
//  require #lp eq 1 and Gcd(lp[1][1], Characteristic(K)) eq 1:
    "This must define a cyclic group of prime power order, coprime to the characteristic";

  
  Fq := ConstantField(K);
  EFq, mEFq := ExactConstantField(K);

  if (#EFq-1) mod q eq 0 then
    vprint ClassField, 1: "Have enough roots of unity";
    easy := true;
    F := K;
    Fa := F;
    zeta := RootOfUnity(q, EFq);
    zeta := mEFq(zeta);
    N := func<c|c>;
    J := N;
    au := hom<F -> F | F.1>;
  else
    vprint ClassField, 1: "need to adjoin some roots of unity";
    easy := false;
    mult := 1;
    repeat
      mult +:= 1;
      f := (#Fq)^mult-1;
    until f mod q eq 0;
    Fq := CommonOverfield(ext<Fq|mult>, EFq);
    vprint ClassField, 2: "need to extend ConstantField to ", Fq;
    f := DefiningPolynomial(Fq, EFq);
    F := ext<K| Polynomial(K, f): Check := false>;
    vprint ClassField, 2: "computing RationalExtensionRepresentation..";
    vtime ClassField, 2: Fa := RationalExtensionRepresentation(F);
    zeta := RootOfUnity(q, Fq);
    ho := hom<Fq -> F | F.1>;
    zeta := Fa!(ho(zeta));
    assert zeta ^ q eq 1;
    for i in Divisors(q) do
      if i ne q then
        assert zeta^i ne 1;
      end if;
    end for;
    if K eq RationalFunctionField(ConstantField(K)) then
      fin := func<X| &+ [b[i]*a[i] : i in [1..#a] | IsFinite(a[i])] where a,b := Support(X)>;
      inf := func<X| &+ [b[i]*a[i] : i in [1..#a] | not IsFinite(a[i])] where a,b := Support(X)>;
      N := func<x |IsFinite(x) select fin(D) else inf(D) where D := Gcd(Divisor(K!Norm(a)), Divisor(K!Norm(b))) where a,b := TwoGenerators(x)>;
      J := func<x |IsFinite(x) select fin(D) else inf(D) where D := Gcd(Divisor(Fa!a), Divisor(Fa!b)) where a,b := TwoGenerators(x)>;
    else
      N := func<x |Divisor(Norm((IsFinite(x) select MaximalOrderFinite(F) else MaximalOrderInfinite(F))!!Ideal(x)))>;
      J := func<x|Divisor((IsFinite(x) select MaximalOrderFinite(Fa) else MaximalOrderInfinite(Fa))!!Ideal(x))>;
    end if;
    auR := hom<F -> F | F.1^(#EFq)>;
    au := map<Fa -> Fa | x :-> F!auR(F!x)>;
    w1, w2 := GetSeed();
    assert Evaluate(DefiningPolynomial(Fa), au(Fa.1)) eq 0;
    SetSeed(w1, w2);
  end if;

  vprint ClassField, 1 : "Starting class group of larger(?) field";
  /* maybe (definetely!!) I should store this extension in F */
  /* and worry about deletion some other time */

  C, mC := ClassGroup(Fa);
  vprint ClassField, 1: "Classgroup is ", C;

  /* now we need S-units for a set S that is
   * - large enought to generate C
   * - comtains all primes in m
   * and we need to be careful with the difference between divisor class group
   * and picard group of some order probably... 
   * If I feel like it, I could compute the conductor 1st
   */

  S := &join [ { x : x in Support(J(y))} : y in Support(m)];   
  s := sub<C | [ (1*x)@@mC : x in S]>;
  r := PlaceEnumInit(Fa);
  while not IsFinite(x) or Gcd(#x, q) ne 1 where x := quo<C|s> do
    p := PlaceEnumNext(r);
    cp := (1*p)@@mC;
    if not cp in s then
      s := sub<C|s, cp>;
      Include(~S, p);
    end if;
  end while;

  vprint ClassField, 1: "Set S (of size ", #S, ") is now ", S;

  U, mU := SUnitGroup(S);
  vprint ClassField, 1: "S-unit group ", U;

  g := [mU(U.i) : i in [1..Ngens(U)]];

  r := PlaceEnumInit(Fa : Coprime := S);
  A := AbelianGroup([ q : x in g]);
  s := sub<A|>;
  lq := [];

  vprint ClassField, 2: "Building 1st Artin step";
  while s ne A do
    p := PlaceEnumNext(r);
    a := KummerDiscLog(g, zeta, q, p);
    if a cmpne false then
      a := A!Eltseq(a);
      if not a in s then
        s := sub<A|s, a>;
        P := N(p);
        b := (1*P) @@ bm @ mQ;
        lq cat:= [<a, b>];
      end if;
    end if;
  end while;

  vprint ClassField, 2: "OK, have enough elements to establish hom!";

  h := CreateHom(A, Q, lq);
  /* Trouble is that we might have part of the CF already contained
   * in the constant field extension. Over GF(3):
   * y^2 + (2*x^2 + 2*x + 1)*y + 2*x^4 + x^3 + 2*x^2
   * P being the only infinite place and the CF the HCF.
   * the assertion is hit in every(?) example of this type.
   * The Problem is most likely that P is of degree 2.
   *
  assert Image(h) eq Q; //CF: not neccessarily correct
  for i in lq do
    assert h(i[1]) eq i[2];
  end for;
  */

  deg := #quo<A|Kernel(h)>;

  /* now we need elements (one) that is orthogonal to the Kernel 
   * (i.e. that is invariant under all transformations that are in the kernel)
   */
     
      
  k := Kernel(h);
  if #k eq 1 then
    mm := Matrix(Integers(q), 0, Ngens(A), []);
  else
    mm := Matrix(Integers(q), Matrix([ Eltseq(A!k.i) : i in [1..Ngens(k)]]));
  end if;
  ns := KernelMatrix(Transpose(mm));
  assert Nrows(ns) eq 1;
  ns := Matrix(Integers(), ns);
 
  f := Gcd(Eltseq(ns));
  assert q div deg eq f;
  
  b := &*[g[j]^(ns[i][j] div f) : j in [1..#g]] where i := 1;
 
  vprint ClassField, 2: "Generator over the larger field is ", b;

  /* now use galois decent to get a generator over our original field
   * traditionally, this involves 
   *  - getting the automorphisms used for the cyclotomic extension
   *  - extending them to the Kummer extension generated by b
   *  - establish Artin isomorphism again, now for the Kummer ext
   *  - find a primitive element for Kummer ofer start field
   *  - get the relative minimal polynomial for it
   *  - some coefficient should work.
   * Well, there's a lot to do!
   * (A reduction of b would also be nice!)
   */
  
  vtime ClassField, 1: b := GenReduce(b, q);   
  vprint ClassField, 2: "Generator over the larger field is reduced to ", b;
   
  E := ext<F | PolynomialRing(F).1^deg - F!b:Check := false>;

  if easy then
    if WithAut then
      h := hom<E -> E| E.1*zeta>;
      return E, h, E.1, _;
    else
      return E, _, E.1, _;
    end if;
  end if;

  vprint ClassField, 1: "Starting Galois decent";

  // and now the ruddy decent.
  // starting with the automorphisms and their extension.
  // Benefit: FiniteFields are always cyclic, so we have to extend at
  // most one aut!
  // The automorphism in question is the Frobenius x -> x^qq where
  // qq is the size of the OLD ECF. I think I'll define it up where the
  // field is constructed!
  // the pain, oh the pain: the extension to E.
  // OK, E.1 has to map to z * E.i^s where s is the same as zeta -> zeta^s
  // (and therefore s = #EFq by construction)
  // for zz we obviously now get
  
  zz := Root(au(b)/b^(#EFq), deg);
  if GetAssertions() ge 1 then
    w1, w2 := GetSeed();
    assert zz^deg eq au(b)/b^(#EFq);
    MP := AbsoluteMinimalPolynomial(E.1);
//    "AbsPol: ", MP;
    SetSeed(w1, w2);
  end if;

  Au := hom<E -> E | map<F ->E | x :-> E!F!au(x)>, (F!zz)*E.1^(#EFq)>;
  Bu := hom<E -> E | F!zeta^(q div deg)*E.1>;

  // Now Au and Bu should generate the full automorphism group
  // and it remains to establish Artin reciprocity again...
 
  m_to_r := Au(E.1);
  assert Evaluate(MP, m_to_r) eq 0;
  for i in [2..Degree(F)] do
    m_to_r := Au(m_to_r);
    assert Evaluate(MP, m_to_r) eq 0;
  end for;
  assert Evaluate(MP, m_to_r) eq 0;
  // OK, now find the s such that Bu^s = Au^deg.
  // m_to_r should be (by now) zeta^s * E.1, so we take the
  // second coefficient
  zeta_s := Fa!Eltseq(m_to_r)[2];
  // and find the zeta power for it!
//  "q: ", q, " deg: ", deg;
  z_to_r := zeta^(q div deg);
//  z_to_r;
//  zeta_s;
  i := 1;
  while z_to_r ne zeta_s do
    i +:= 1;
    z_to_r *:= zeta^(q div deg);
  end while;
//  "i: ", i;

  // now our abelian group should be <a,b | a^Deg(F) = b^i, b^Deg(E)>
  
  G := AbelianGroup([Degree(F) * deg , deg]);
  Gq, mGq := quo<G | Degree(F)*G.1 = i*G.2, deg * G.2>;

  vprint ClassField, 1: "Automorphism group computed as ", Gq;

  // now for the Artin reciprocity...
  // a place (sufficiently coprime) is mapped to the Frobenius automorphism.
  // The Frob is (here) determined by it's action on the 2 generators:
  // E.1 and F.1, so we send E.1 -> E.1^N and F.1 -> F.1^N.
  // Modulo P this should correspond to some element in G.

  // I think we need to compute all automorphisms
  // Since powers of Bu should be much cheaper (we could even implement
  // them seperately by just changinf coefficients), we'll do few Au
  // iterations and then do Bu iterations. Actually, we should reuse the
  // iterations initiated above...

  vprint ClassField, 2: "Computing all automorphisms...";

  gp_l := [<(G![0,0])@mGq, hom<E->E | E.1>, E!F.1, E.1>];
  for i in [1..Degree(F)-1] do
    Append(~gp_l, <gp_l[i][1]+G.1@mGq, gp_l[i][2]*Au,
                              gp_l[i][3]@Au, gp_l[i][4]@Au>);
  end for;
  for i in [1..deg-1] do
    s := (i-1)*Degree(F);
    for j in [1..Degree(F)] do
      Append(~gp_l, <gp_l[s+j][1]+G.2@mGq, gp_l[s+j][2]*Bu,
                              gp_l[s+j][3]@Bu, gp_l[s+j][4]@Bu>);
    end for;                          
  end for;

  vprint ClassField, 2: ".. done";

  assert #{x[1] : x in gp_l} eq #Gq;
  assert #{<x[3], x[4]> : x in gp_l} eq #Gq;

  function special_artin(p)
    vprint ClassField, 3: "2nd Artin map called on ", p;
    N := #ResidueClassField(p);
    if zz cmpeq 0 or zz cmpeq Infinity() where zz := Evaluate(Norm(F!b), p) then
      return [false];
    end if;
    z := MModpow(E.1^(N mod deg)*MModpow(F!b,(N div deg), p), 1, p);
    y := E!MModpow(F.1, N, p);
    for i in gp_l do
      if z eq MModpow(i[4], 1, p) and y eq MModpow(i[3], 1, p) then
        return i;
      end if;
    end for;
    error "(1)this should better NOT happen";
  end function;

  vprint ClassField, 2: "Building 2nd Artin step";
  s := sub<Gq|>;
  r := PlaceEnumInit(K:Coprime := m);
  h := [];
  repeat
    p := PlaceEnumNext(r);
    l := special_artin(p)[1];
    if l cmpne false and not l in s then
      s := sub<Gq | s, l>;
      Append(~h, <l, (1*p)@@bm@mQ>);
    end if;
  until s eq Gq;

  h := CreateHom(Gq, Q, h);
  
  is_primitive := func<s | #{ x[3]*s + x[4] : x in gp_l} eq #Gq>;
  s := 0;
  Gqq, mGqq := quo<Gq|Kernel(h)>;
  cos := {x@@mGqq : x in Gqq};
  while true do
    // OK, now we need a primitive element for E/K. E.1 + sth* F.1 should do.
    // it is primitive if all the images under Gq are different...
    vprint ClassField, 2: "searching for primitive element..";
    while not is_primitive(s) do
      s := Random(K, 3);
    end while;

    vprint ClassField, 3: "primitive element found for s = ", s;

    // now the relative trace...
    vprint ClassField, 2: "relative trace...";
    k := Kernel(h);
    tr := &+ [ x[3]*s + x[4] : x in gp_l | x[1] in k];

    // now check if tr is primitive enough:
    vprint ClassField, 2: "is primitive?";

    c_tr := {tr@x[2] : x in gp_l | x[1] in cos};
    if #c_tr eq q then
      vprint ClassField, 2: "Yes, found generator for field";
      vprint ClassField, 2: "Computing minimal polynomial";
      f := &* [ PolynomialRing(E).1 - x : x in c_tr];
      vprint ClassField, 2: " done, starting on the generating automorphism";
      g := Polynomial(K, f);
      KK := ext<K|g : Check := false>;
Embed(KK, E, tr);
assert MinimalPolynomial(E!KK.1, K) eq g;
      if not WithAut then
        return KK, _, tr, _;//Rep(c_tr);
      end if;
      // now compute a generating automorphism ... by doing linear algebra
      // since we know all automorphisms in E, is' easy to get the one
      // we want.
      vprint ClassField, 3: "computing powers";
      m := [ 1, tr];
      for i in [2..q-1] do
        m[i+1] := tr*m[i];
      end for;
      g := Q.1 @@ h;
      i := Position([x[1] : x in gp_l], g);
      m[q+1] := tr@ gp_l[i][2];

      m := [ &cat [ Eltseq(x) : x in Eltseq(y) ] : y in m];
      m := Matrix(m);
      vprint ClassField, 3: "computing kernel";
      k := KernelMatrix(m);
      assert Nrows(k) eq 1;
      vprint ClassField, 1: "Ready!";
      return KK, hom<KK -> KK | KK!(Eltseq(k)[1..q])/(-k[1][q+1])>, tr, f;
    end if;
    vprint ClassField, 2: "not primitive, try again";
  end while;
end function;
  
intrinsic FunctionField(e::RngWittElt : WithAut := true, Check := false, Abs := false) -> FldFun, Map
{The cyclic extension defined by e and a generator for the automorphism group}

  W := Parent(e);
  K := BaseRing(W);
  p := Characteristic(K);

  ee := Eltseq(e); // need to check that ee[1] is not in the image of 
                   // the AS operator

  z := [0];
  E := K;
  Z := Integers();
  Q := Rationals();
  Zx := PolynomialRing(Z, 2*#ee);
  AssignNames(~Zx, &cat [ ["t" cat IntegerToString(i),
                           "b" cat IntegerToString(i)] : i in [1..#ee]]);  
  el := [ [0,0] : i in ee];
  z0 := [Zx!0];
  ec := el; ec[1] := [0,0];
  c := [1];
  h := hom<K->K | K.1>;

  for i in [1..#ee] do
//    "creating E";
    x := PolynomialRing(E).1;
    if i eq 1 then
      if IsRationalFunctionField(E) then
        E := FunctionField(Polynomial(E, x^p-x) - E!ee[i]- z[i]:Check := true);
      else
        E := ext<E | Polynomial(E, x^p-x) - E!ee[i]- z[i]:Check := Check>;
      end if;
    else    
      E := ext<E | Polynomial(E, x^p-x) - E!ee[i]- z[i]:Check := false>;
    end if;    
    if i eq #ee and not WithAut then
      break;
    end if;
//    "starting on f";
    // comes from H.L. Schmid: Zur Arithmetik der zyklischen Koerper
    f := &+ [Zx| (Zx.(2*j-1)^(p^(i-j+1)) + 
                             Zx.(2*j-0)^(p^(i-j+1)) -
                             (Zx.(2*j-1) + Zx.(2*j-0) + z0[j])^(p^(i-j+1))
                             ) * p^(j)  : j in [1..i]] div p^(i+1);
//    "done";
    Append(~z0, f);
    el := [ChangeUniverse(x, E) : x in el];
    ec := [ChangeUniverse(x, E) : x in ec];
//    "change z";
    ChangeUniverse(~z, E);
    ChangeUniverse(~c, E);
//    "asign";
    el[i] := [E.1,E!ee[i]];
    if i eq 1 then
      ec[i] := [E.1, 1];
    else
      ec[i] := [E.1, 0];
    end if;
//    "Eval";
    if i ne #ee then
      Append(~z, Evaluate(f, &cat el));
    end if;
    if WithAut then
      Append(~c, Evaluate(f, &cat ec));
    //according to Schmid: Zyklische algebraische Funktonenkoerper...
    //we can use the same polynomials for c and z and evaluate them
    //differently.

      h := hom<E -> E | map<CoefficientField(E) -> E | x :-> h(x)>, E.1+c[i]>;
    end if;
  end for;

  if Abs then
// //    "getting minpoly ...";
//     chi := DefiningPolynomial(E);
//     j := 1;
//     while j lt #ee do
//       chi := Norm(chi);
//       j := j+1;
//     end while;    
//     F := FunctionField(chi:Check := false);
// //    F := FunctionField(MinimalPolynomial(E.1, K):Check := false);
    if true then
    F := UnderlyingField(E,K);
    else
    F := FunctionField(MinimalPolynomial(E.1, K));
    end if;
    F`ArtinSchreierWitt := e;
    if WithAut then
//      "getting powers...";
      l := [1, E.1];
      for i in [2..Degree(F)-1] do
        l[i+1] := E.1 * l[i];
      end for;
//      "buiding matrix";
      b := [ Eltseq(x, K) : x in l cat [h(E.1)]];
      b := Matrix(b);
//      "kernel...";
      k := KernelMatrix(b);
      assert Nrows(k) eq 1;
      k := -k/k[1][Ncols(k)];
      h := hom<F -> F | F!Eltseq(k)[1..Degree(F)]>;
      F`ArtinSchreierWittTower := E;
      return F, h;
    else
      F`ArtinSchreierWittTower := E;
      return F, _;
    end if;
  end if;

  E`ArtinSchreierWitt := e;

  if WithAut then
    return E, h;
  else
    return E, _;
  end if;
end intrinsic;

function WittRingDiscLog(E)
  // the WittRing of length n over a finite prime field is cyclic, generated
  // by (1,0,...). This computes the disc log wrt to this generator.

  if #BaseRing(Parent(E)) eq 2 then
    return SequenceToInteger(ChangeUniverse(Eltseq(E), Integers()), 2); 
  end if;
  W := Parent(E);
  F := BaseRing(W);
  if PrimeField(F) eq F then
    _, hR := LocalRing(Parent(E));
    a := hR(E);
    return (Integers()!a) mod Characteristic(BaseRing(W))^Length(W);
  end if;
end function;
 
function CF_WittTrace(e)
//intrinsic Trace(e :: RngWittElt) -> RngWittElt
//  {}
  if Type(e) cmpne RngWittElt then
    return Trace(e);
  end if;
  W := Parent(e);
  F := BaseRing(W);
  p := Characteristic(F);
  m := Round(Log(#F)/Log(p));
  assert p^m eq #F;

  phi := FrobeniusMap(W);

  gens := [e];
  sum := gens;
  
  for i in [1..m-1] do
    gens := [ x@phi : x in gens];
    for j in [1..#gens] do
      sum[j] +:= gens[j];
    end for;
  end for;

  return sum[1];
end function;

function ArtinSchreierWittDiscLog(Gens, p)
//intrinsic ArtinSchreierWittDiscLog(Gens::[RngWittElt], p::PlcFunElt) -> RngIntElt
//{}
  // From Schmid, same idea (really) as for the ArtinSchreier case, difference
  // we have to compute the traces ourselves...
  K := BaseRing(Parent(Gens[1]));
  F := ResidueClassField(p);
  n := #Eltseq(Gens[1]);

  wF := WittRing(F, n);
  // this assumes everything is coprime!!!! (and integral and such)
  gens := [];
  for y in Gens do
    w := [];
    for x in Eltseq(y) do
      z := Evaluate(x, p);
      if (z cmpeq 0 or z cmpeq Infinity()) and z ne 0 then
        return false;
      end if;
      Append(~w, z);
    end for;
    Append(~gens, wF!w);
  end for;

  Gens := gens;

  p := Characteristic(F);

  _, mR := LocalRing(wF);
  R := Codomain(mR);
  F := BaseRing(R);
  gens := [mR(x) : x in gens];
  sum := gens;
  repeat
    sum := [CF_WittTrace(x) : x in sum]; //CHECK
  until Type(Universe(sum)) eq RngPadRes;
  
  ChangeUniverse(~sum, Integers());

  delete wF`LocalRingMap;  // to help(?) deletion...

  return sum;
end function;

function ArtinSchreierWittGenerators(m, SG)
//intrinsic ArtinSchreierWittGenerators(m::DivFunElt, SG::GrpAb) -> FldFunElt
//{If the quotient by SG defines a cyclic group of order p^n, find Artin-Schreier-Witt generator for the corresponding extension}

  K := FunctionField(m);
  p := Characteristic(K);
  k := ConstantField(K);

  am, bm := RayClassGroup(m);
  q, mq := quo<am|SG>;

  lq := Factorisation(#q);
  assert IsCyclic(q) and #lq eq 1 and p eq lq[1][1];

  gen := [];
  last_c := 0*m;
  exep := NonSpecialDivisor(-m);

  for expo := 1 to lq[1][2] do
    sg := sub<am|SG, p^expo*(q.1@@ mq)>;
    q, mq := quo<am|sg>;
    vprint ClassField, 1: "Layer now ", expo;

    W := WittRing(K, expo);
    if (gen cmpne []) then
      gen := Eltseq(gen);
      Append(~gen, K!0);
      gen := W!gen;
    end if;
   
    c := Conductor(m, sg);
    vprint ClassField, 1: "Conductor: ", c;
    a,b := Support(c);
    D := 0*c;
    for i in [1..#a] do
      assert b[i] ge 2;
      D +:= (b[i]-1)*a[i];
    end for;
    assert IsEffective(D);

    D := Lcm(D, p*last_c);
    last_c := D;

    vprint ClassField, 1: "Divisor used...", D;
    // I thin we can improve ths a little bit. Schmid claims that
    // the maximum can only be reached ONCE


    // THE Artin-Schreier-Witt generator we are looking for has valuation
    // equal to -D + poles divisible by the char at at most one more place
    // elsewhere it's integral!
    // (in the new component + the old one)
    A, r := NonSpecialDivisor(0*D:Exception := exep);

    r *:= p^expo;  // I'm certain I proved that p^expo MUST work!
    vprint ClassField, 1: "Special place:", r*A;
             
    //our elements should now be in some RR space, if I only knew which!
    //I think L(D + A*r) should do it.

    B := RiemannRochSpace(1*(D+r*A));

    a,b := Support(1*(D+r*A));
    C := 0*D;
    for i in [1..#a] do
      C +:= (b[i] div p)*a[i];
    end for;

    C := RiemannRochSpace(C);
    f := Degree(k, PrimeField(k));

    M := KSpace(PrimeField(k), Dimension(B)*f);
    // M is isomorphic to B, but as a Fp not Fq vectorspace!
    a := AbsoluteBasis(k);
    function to_M(r)
      r := Eltseq(r);
      r := &cat [ Flat(x) : x in r];
      return M!r;
    end function;
    qM, mqM := quo<M | [to_M((B!((K!x*y)^p-K!x*y))) : x in Basis(C), y in a]>;
   
    vprint ClassField, 1: "the quotient space: ", qM;

    assert #qM ne 0;

    b := [];
    g := Eltseq(0*gen);

    function from_M(r)
      r := Eltseq(r);
      r := B![ k!r[i*f+1..(i+1)*f] : i in [0..Dimension(B)-1]];
      return r;
    end function;

    if expo ne 1 then
      Append(~b, gen);
    end if;

    for i in Basis(qM) do
      g[expo] := K!(from_M(i@@mqM));
      Append(~b, W!g);
    end for;

    r := PlaceEnumInit(K : Coprime :=  m);

    A := AbelianGroup([ p : x in b]);
    pe1 := p^(expo-1);

    m1 := [];
    m2 := [];
    m3 := [];
    m4 := [];
    vprint ClassField, 1: "creating Artin map...";
    repeat
      pl := PlaceEnumNext(r);
      vprint ClassField, 3: "Trying to use ", pl;
      f := ArtinSchreierWittDiscLog(b, pl);
      if f cmpne false then
        Append(~m1, [(Integers()!x) div pe1 : x in f]);
        Append(~m4, f);
        Append(~m2, RayClassGroupDiscLog(pl, m)@mq);
        Append(~m3, pl);
      end if;
      if #m1 gt 0 then
        M := Matrix(Integers(p), Matrix(m1));
        vprint ClassField, 2: "Rank now: ", Rank(M);
      end if;
    until #m1 gt 0 and Rank(M) eq #b;

    G := FreeAbelianGroup(#m3);
    h := hom<G -> q | m2>;
    assert Image(h) eq q;

    kk := Kernel(h);
    mm := [];
    for i in Generators(kk) do
      n := Eltseq(G!i);
      Append(~mm, [&+ [ Integers()!(n[j]*m4[j][l])  : j in [1..#n]]
                                : l in [1..#b]]);
    end for;
    for i in [1..#mm] do
      for j in [1..#mm[1]] do
        mm[i][j] div:= pe1;
      end for;
    end for;
    mm := Matrix(mm);
    mm := Matrix(Integers(p), mm);
    ns := KernelMatrix(Transpose(mm));
    vprint ClassField, 2: "ns:", ns;
    if expo ne 1 then
      assert Nrows(ns) eq 2;
      // one row must have a unit in pos 1, this is the row we need.
      // the other row corresponds to a degree p extension, the generator
      // will have zeroes in the first expo-1 coordiantes.
      // We could consider using this for reduction.
      f := exists(i){i : i in [1..Nrows(ns)] | IsUnit(ns[i][1])};
      assert f;
      ns := Matrix(ns[i]);
      ns := (1/ns[1][1])*ns;
    else
      assert Nrows(ns) eq 1;
    end if;
    ns := Eltseq(ns[1]);
    gen := &+ [ (Integers()!ns[i]) * b[i] : i in [1..#b]];
    vprint ClassField, 1: "generator now:", gen;
  end for;

  return gen;
end function;  

intrinsic InternalRayClassField(m::DivFunElt, SG::GrpAb:WithAut := false) -> [], []
{Returns the ray class field as a function field.}
  am, bm := RayClassGroup(m);
  require SG subset am:
    "SG must be a subgroup of the ray class group of m";

  q, mq := quo<am|SG>;

  require IsFinite(q):
    "SG must define a define a finite quotient";

  K := FunctionField(m);

  if #q eq 1 then
    return FunctionField([PolynomialRing(K)![1,1]]), [], [];
  end if;
  lf := Factorisation(#q);

  gen := [];
  au := [* *];
  witts := [* *];
  for i in lf do
    a := i[1]^i[2];
    sg := sub<am|Generators(SG) join {a*x : x in Generators(am)}>;
    q1, mq1 := quo<am|sg>;

    assert #q1 eq a;
    g := Generators(q1);
    g := [x@@mq1 : x in g];

    for j in g do
      ss := sub<am| Generators(sg) join { x : x in g | x ne j}>;
      o := Order(mq1(j));
      if Gcd(o, Characteristic(K)) eq 1 then
        a, b, E, _ := KummerGenerators(m, ss: WithAut := WithAut);
	Append(~witts, E);
      else
        aa := ArtinSchreierWittGenerators(m, ss);
        a,b := FunctionField(aa:Abs, WithAut := WithAut);
	Append(~witts, <aa, a`ArtinSchreierWittTower>);
      end if;
      Append(~gen, a);
      if WithAut then
        Append(~au, b);
      end if;
    end for;

  end for;
  if WithAut then
    return gen, au, witts;
  else
//  "FunctionField(", [DefiningPolynomial(x) : x in gen]," : Check := false);";
    F := FunctionField([DefiningPolynomial(x) : x in gen] : Check := false);
    return F, _, witts;
// Since gen is not kept around these embeddings may not last. Don't put them in
// here, put them in where they are needed (e.g. MaximalOrder*)
    for i in [1 .. #gen] do
	Embed(gen[i], F, F.i);
    end for;
  end if;
end intrinsic;

function decomposition_type(D, SG, lp)
  r, mr := RayClassGroup(D);
  q, mq := quo<r|SG>;
  l := [];

  s := Support(D);
  for i in lp do
    if i in s then
      S := CondDisc(D : SG := SG, Ignore := [i]);
      mp := D`Record`RayClassGroupMap[4];
      nq, mnq := quo<r|&cat S>;
      x := mp(i:Ignore := [i]);
      Append(~l, <Order(x@mnq), #q div #nq>);
    else
      Append(~l, <Order(RayClassGroupDiscLog(i, D)@mq), 1>);
    end if;
  end for;
  return l, #q;
end function;

intrinsic DecompositionType(D::DivFunElt, SG::GrpAb, p::PlcFunElt) -> []
  {}
  a,n := decomposition_type(D, SG, [p]);
  n div:= a[1][1]*a[1][2];
  return [a : i in [1..n]];
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOne(D::DivFunElt, SG::GrpAb) -> RngIntElt
  {}
  K := FunctionField(D);  
  lp := Places(K, 1);  
  a, n := decomposition_type(D, SG, lp);
  // as a shortcut: n is the degree of the extension.
  return &+[Integers()|n div x[2] : x in a | x[1] eq 1];
end intrinsic;

intrinsic InducedMap(r1::Map, r2::Map, h::Map, Coprime :: DivFunElt) -> Map
{Returns the map between (the RayClassGroups) r1 and r2 that is induced by h}

  G := Domain(r1);
  H := Domain(r2);
  if #G*#H eq 1 then
    return hom<G -> H | [ H.0 : i in [1..Ngens(G)]]>;
  end if;

  li := [ ];
  lg := [ ];
  F := FunctionField(Codomain(r1));
  deg := 1;
  repeat
    lp := Places(F, deg);
    for i in lp do
      if not IsZero(GCD(Divisor(i), Coprime)) then
	continue;
      end if;
      ii := i@@ r1;
      if not ii in sub<G|lg> then
	  Append(~lg, ii);
	  Append(~li, h(i) @@ r2);
      end if;  
    end for;
    deg +:= 1;
  until sub<G|lg> eq G;

  return CreateHom(G, H, [<lg[i], li[i]> : i in [1..#lg]]);
  return map<G -> H | [<lg[i], li[i]> : i in [1..#lg]]>;
end intrinsic;

