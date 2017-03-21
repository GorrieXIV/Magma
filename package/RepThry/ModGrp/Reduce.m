freeze;
//


/* <example>

  G := DihedralGroup(8);
  T := CharacterTable(G);
  R := Representations(T[7]);
  K := CyclotomicField(8);
  S := Minimize(R[1][1]);

  
  G := DihedralGroup(9*8);
  T := CharacterTable(G);
  T;
  R := Representations(T[35]);
  Minimize(R[1][1]);
  R := Representations(T[36]);
  Minimize(R[1][1]);

  G := PCGroup(WreathProduct(Sym(3), DihedralGroup(4)));
  #G;
  Reps := AbsolutelyIrreducibleRepresentationsSchur(G, Q);
  #Reps;
  Reps;
  time s := [* *]; for i in Reps do Append(~s, Minimize(i)); end for;
  s;
  Minimize(s[54][1]);



  > Attach("/home/magma/nonexport/package/Prof/prof.m");  
  > G := ExtraSpecialGroup(GrpPC, 3, 3);
  > K := CyclotomicField(3);
  > L := AbsolutelyIrreducibleRepresentationsSchur(G, K);
  > l := [ Degree(Codomain(x)) : x in L];
  > assert Position(l, 27) eq 366;
  > R := L[366];
  > L := CyclotomicField(12);
  > P := MatrixAlgebra(L, 27);
  > p := P![Random(L, 2) : x in [1..27^2]];
  > time pi := p^-1;
  > // Time: 1.400
  > m := [ R(i) : i in Generators(G)];
  > time mm := [ pi*P!Eltseq(x)*p : x in m]; 
  > SetKantVerbose("MOD_KERNEL", 5);
  > GetX(mm, hom<L ->L |L.1>);

  G := Group<a,b,z|a^2=b^2=z^12=1, b^a=b, z^a=z^5, z^b=z^-1>;
  GG := CosetImage(G, sub<G|>);
  K := CyclotomicField(12); z := K.1;
  ra := Matrix(K, [[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]]);
  rb := Matrix(K, [[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]);
  rc := Matrix(K, [[z,0,0,0],[0,z^-1,0,0],[0,0,z^5,0],[0,0,0,z^-5]]);
  
  r := GModule(GG, [ra, rb, rc]);  
  r := Representation(r);        
  s := Minimize(r);
  t := Minimize(s[1]);

  G := TransitiveGroup(10, 30);
  X := CharacterTable(G);
  z := Minimize(G, X);
  [ <i, Degree(BaseRing(Codomain(z[i][2][1]))), 
    Degree(BaseRing(Codomain(z[i][1])))> : i in [1..#z]];

  
 
  SetIsClaus(false);
  load "~billu/Magma/Chtr/chtr_package";
  G := GroupOfLieType("G2", GF(2));
  m := StandardRepresentation(G);
  g := Generators(G);
  s := sub<Codomain(m) | [ m(x) : x in g]>;
  GG := s;
  Z := CosetImage(GG, sub<GG|>);
  Z := DegreeReduction(Z);
  X := ChtrTable(Z);
  R := RepresentationOfCharacter(Z, X[3]);
  S := Minimize(R);

  
  </example>
*/

declare verbose Isomorphic, 2;  


function InduceAut(M, s)
  if ISA(Type(M), ModTupFldElt) then
    l := Eltseq(M);
    l := [ s(x) : x in l];
    return Parent(M)!l;
  elif ISA(Type(M), Mtrx) then
    l := Eltseq(M);
    l := [ s(x) : x in l];
    return Matrix(Nrows(M), Ncols(M),l);
  else
    error "case not supported";
  end if;
end function;



function GetX(L1, L2:DoTest := false, Deg := false)
//       GetX(L1::[Mtrx], L2::[Mtrx]:DoTest := false, Deg := false) -> Mtrx
  K := CoefficientRing(L1[1]);
  n := Nrows(L1[1]);
  if L1 eq L2 then
    return IdentityMatrix(K, n);
  end if;
  M := MaximalOrder(K);
  p := NextPrime(2^30);
  pp := 1;
  rat := false;
  pos := false;
  if Type(K) eq FldCyc then
    c := Conductor(K);
  end if;
  while true do
    repeat
      p := PreviousPrime(p);
      if Type(K) eq FldCyc then
        if c eq 1 or p mod c eq 1 then
          lp := Decomposition(M, p);
        else
          lp := [];
        end if;
      else
        lp := Decomposition(M, p);
      end if;
    until #lp eq Degree(K);

    vprint Isomorphic, 1: "using ", p;

    // check for valid p's...

    re_p := false;
    lT := [];
    for i in lp do
      F, mF := ResidueClassField(i[1]);
      l1 := [ Matrix(F, n, n, [mF(x) : x in Eltseq(y)]) : y in L1];
      m1 := RModule(l1);
      if not IsAbsolutelyIrreducible(m1) then
        vprint Isomorphic, 1: "fail(-1)";
        continue;
      end if;
      l2 := [ Matrix(F, n, n, [mF(x) : x in Eltseq(y)]) : y in L2];
      m2 := RModule(l2);
      if not IsAbsolutelyIrreducible(m2) then
        vprint Isomorphic, 1: "fail(0)";
        continue;
      end if;
      bool, T := IsIsomorphic(m1, m2);
      if not bool then
        vprint Isomorphic, 1: "fail(1)";
        return false;
        break;
      end if;
    
      Append(~lT, <T, i[1]>);

      if pos cmpeq false then
        pos := Position([x eq 0: x in Eltseq(T[1])], false);
        vprint Isomorphic, 1: "pos : ", pos;
      end if;
      if not re_p then
        re_p := true;
        T := T/T[1][pos];
        T := Matrix(M, n, n, [x@@mF : x in Eltseq(T)]);
        S := T;
        prod_p := i[1];
      else  
        f, a, b := Idempotents(prod_p, i[1]);
        T := T/T[1][pos];
        T := Matrix(M, n, n, [x@@mF : x in Eltseq(T)]);
        S := S*b + T*a;
        prod_p *:= i[1];
      end if;
    end for;
    if not assigned bool or not bool then
      vprint Isomorphic, 1: "fail(2)";
      continue;
    end if;

    if pp eq 1 then
      pp := p;
      res := S;
    else
      g, a, b := Xgcd(pp, p);    
      res := res*M!(b*p) + S*M!(a*pp);
      pp *:= p;
    end if;
    vprint Isomorphic, 1: "prod now ", pp;

    ra := [];
    Zm := Integers(pp);
      
    for i in Eltseq(res) do
      l := [];
      for j in Eltseq(i) do
        f, g := RationalReconstruction(Zm! j);
        if f then
          Append(~l, g);
        else
          vprint Isomorphic, 1: "fail(3)";
          break;
        end if;
      end for;
      if f then
        Append(~ra, K!FieldOfFractions(M)!l);
      else
        vprint Isomorphic, 1: "fail(4)";
        break;
      end if;
    end for;
    if f then
      cur := Matrix(K, n, n, ra);
    else
      cur := false;
    end if;

    if rat cmpne false and cur cmpne false then
      if cur eq rat then
        done := true;
        if DoTest then
          for i in [1..#L1] do
            if rat * L1[i] ne L2[i] * rat then
              vprint Isomorphic, 1: "Test failed!";
              done := false;
              break;
            end if;
          end for;
        end if;

        if done then 
          return rat; 
        end if;
      end if;
    end if;
    rat := cur;
  end while;
end function;
    
function IntMinimize(R)
  K := BaseRing(Codomain(R));
  if K eq Rationals() then
    return R;
  end if;
  if Type(K) eq FldCyc then
    A, mA := CyclotomicAutomorphismGroup(K);
  else
    A, _, mA := AutomorphismGroup(K:Abelian);
  end if;
  G := Domain(R);
  L := [ R(G.i) : i in [1..Ngens(G)]];
  ls := [sub<A|>];
  la := [];
  for i in A do
    if i eq A.0 then continue; end if;
    U := sub<A|i>;
    if not U in ls then
      Append(~ls, U);
      Append(~la, i);
    end if;
  end for;
  i := 1;
  repeat
    la := [x : x in la | InduceAut(y, mA(x)) eq y] where y := L[i];
    i +:= 1;
  until #la eq 0 or i gt #L;

  if #la eq 0 then
    return R, L;
  end if;

  k, mk := FixedField(K, [mA(i) : i in la]);
  L := [InduceAut(y, Inverse(mk)) : y in L];
  M := GModule(G, L);
  return Representation(M);
end function;

function GetMu(C, s) 
  // TODO: don't multiply matrices, just apply them to a random vector
  id := Domain(s).1;
  S := s(id);
  P := C;
  while S ne id do
    C := InduceAut(C, s);
    P *:= C;
    S := s(S);
  end while;

  return P[1][1];
end function;

function CharPoly(M)
  Strassen := func<a,b| a*b>;
  if ISA(Type(M), FldAlgElt) then
    tr := [ Trace(x) : x in Basis(Parent(M))];  
    n := Degree(Parent(M));
    function MyTrace(x)
      return &+ [ tr[i]*x[i] : i in [1..n]];
    end function;
    i := 0;
    I := 1;
    C := I;
    a := [Parent(M)|1];
    repeat
      i +:= 1;
      if i eq n then
        a[i+1] := -MyTrace(M*C)/n;
        return a;
      end if;
      C *:= M;
      a[i+1] := -MyTrace(C)/i;
      C +:= a[i+1];
    until i eq -1;
  elif ISA(Type(M), Mtrx) then
    i := 0;
    I := IdentityMatrix(BaseRing(M), Ncols(M));
    C := I;
    a := [BaseRing(M)|1];
    n := Ncols(M);
//    "CharPoly of matrix...";
    repeat
      i +:= 1;
      if i eq n then
//        "last Strassen";
        a[i+1] := -Trace(Strassen(M,C))/n;
        return a;
      end if;
//      "Strassen for ", i;
      C := Strassen(M,C);
      a[i+1] := -Trace(C)/i;
      for j in [1..Ncols(C)] do
        C[j][j] +:= a[i+1];
      end for;
    until i eq -1;
  else
    error "case not supported";
  end if;
end function;

function Evaluate(f, M)
  Strassen := func<a,b| a*b>;
  I := IdentityMatrix(BaseRing(M), Ncols(M));
  f := Reverse(Eltseq(f));
  R := f[1]*M;
  i := 2;
  while i le #f do
    if f[i] ne 0 then
      for j in [1..Ncols(M)] do
        R[j][j] +:= f[i];
      end for;
    end if;
    if i lt #f then
      R := Strassen(R, M);
    end if;
    i+:=1;
  end while;

  return R;
end function;
    
function Inverse(M)
//  "Inverse started";
  fc := CharPoly(M);  
//  "CharPoly done";
  f := Polynomial(Reverse(fc[1..#fc-1]));
//  "Eval started";
  e :=  -Evaluate(f, M)/fc[#fc];
//  "Inverse computed...";
  return e;
end function;

function DecomposeC(C, s) 
  k := BaseRing(C);
  b := 1;
  t := 1;
  n := Ncols(C);
  X := IdentityMatrix(k, n);
  M := MaximalOrder(k);
  lp := Decomposition(M, NextPrime(2^20))[1][1];
  F, mF := ResidueClassField(lp);
  repeat
    vprint Isomorphic, 1: "fail";
    for i in [1..Maximum([Floor(n/2), 1])] do
      X[Random(n-1)+1][Random(n-1)+1] +:= k.1*Random(0,1);
    end for;
    A := X;
    id := Domain(s).1;
    S := s(id);
    while S ne id do
      A := C*InduceAut(A, s)+X;
      S := s(S);
    end while;
  // TODO: do a proper modular test instead if a complete determinant 
  vprint Isomorphic, 1: "test";
  until Determinant(InduceAut(A, mF)) ne 0;
  vprint Isomorphic, 1: "OK";

  return A;
end function;

function Contents(X)
  if ISA(Type(X), Mtrx) then
    M := MaximalOrder(BaseRing(X));
    FM := FieldOfFractions(M);
    c := &+ [ M*FM!x :x in Eltseq(X)];
    return c;
  else
    error "case not supported";
  end if;
end function;

function MYNgens(G)
  if Type(G) eq GrpPC then
    return #PCGenerators(G);
  else
    return Ngens(G);
  end if;
end function;

intrinsic InternalNice(M::Map) -> .
  {}
  G := Domain(M);
  return hom<G -> GL(Degree(Codomain(M)), CoefficientRing(Codomain(M))) 
                                  | InternalNice([M(G.i) : i in [1..MYNgens(G)]])>;
end intrinsic;

intrinsic InternalNice(L1:: [Mtrx]: Inv := false) -> Mtrx
  {}
 
  f, cm := HasComplexConjugate(CoefficientRing(L1[1]));
  require f: "Field must have complex conjugation";

  if Inv cmpeq false then
    L2 := [ x^-1 : x in L1];
  else 
    L2 := Inv;
  end if;
  T, Ti, Mo, L := InternalMakeIntegral(L1:Inv := L2);
  Gram := &+ [ x*Transpose(InduceAut(x, cm)): x in L];
  p := PseudoBasis(Mo);

  F := BaseRing(p[1][2]);
  Gram := Matrix(BaseRing(p[1][2]), Gram);
  q, w := InternalLLL(p:Gram := Gram);
  wi := w^-1;
  wT := w*T;
  wTi := Ti*wi;
  return [ wT*x*wTi : x in L1], L2;
end intrinsic;

intrinsic InternalNice(L1:: [Mtrx], OldX :: Mtrx, sigma::Map) -> Mtrx
  {}

  L2 := [ x^-1 : x in L1];
 
//  "MakeIntegral(2)";
  T, Ti, Mo, L := InternalMakeIntegral(L1:Inv := L2);
  Gram := &+ [ x*Transpose(InduceAut(x, ComplexConjugate)): x in L];
  p := PseudoBasis(Mo);

  F := BaseRing(p[1][2]);
  Gram := Matrix(BaseRing(p[1][2]), Gram);
//  ":L::";
  q, w := InternalLLL(p:Gram := Gram);
//  "done";

  wis := InduceAut(w, (sigma))^-1;
  Tis := InduceAut(Ti, (sigma));
  trans := w*T;
  transis := Tis*wis;
  transi := trans^-1;
  XX := trans*OldX*transis;
  cX := Contents(OldX);
  _, fx := ClassRepresentative(cX);
  XX := XX/fx;
  cX := Contents(XX);
  _, fx := ClassRepresentative(cX);
  XX := XX/fx;
  
  return XX, trans, transi;
end intrinsic;

 
intrinsic Minimize(R::Map: 
      All := false, Char := false, FindSmallest := false) -> Map
  {Change the coefficient field of the absolute irreducible representation R to the smallest sub-field.}
  // R should be a representation of some group over some abelian field  
  //
  G := Domain(R);
  require ISA(Type(G), Grp) : "R must be a representation";

  L := InternalAbsoluteModuleOverMinimalField(R: All := All, Char := Char, FindSmallest := FindSmallest);
  if All then
    return L;
  else
    return L[1];
  end if;
end intrinsic;

