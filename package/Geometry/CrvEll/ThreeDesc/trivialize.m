freeze;

/**********************************************************
 * General trivialization of CSAs                         *
 *                                                        *
 * Michael Stoll                                          *
 * started 2006-01-24                                     *
 **********************************************************/

// TO DO:
//
// * Rewrite MaximalOrder to really give a maximal order in all cases

declare verbose CSAMaximalOrder, 3;

intrinsic ChangeBasisCSAlgebra(A::AlgAss, one::AlgAssElt, bas::SeqEnum, 
                               flag::BoolElt)
  -> AlgAss, AlgAssElt, Map, .
{Change structure constants to be with respect to another basis.}
  require Universe(bas) eq A: "Basis elements are not in A.";
  V := Module(A);
  basV := ChangeUniverse(bas, V);
  n := Dimension(A);
  require #bas eq n: "Basis sequence has wrong length.";
  require sub<V | basV> eq V: "Basis elements are not independent.";
  h := hom<V -> V | basV>;
  multtab := [[Eltseq((bas[i]*bas[j]) @@ h) : j in [1..n]] : i in [1..n]];
  newA := AssociativeAlgebra<V | multtab>;
  newone := newA!(one @@ h);
  if flag then
    return newA, newone, h, &+[Abs(c) : c in &cat &cat multtab];
  else
    return newA, newone, h, _;
  end if;
end intrinsic;

/* Turns out the general MaximalOrder is faster anyway
intrinsic StollMaximalOrder(A::AlgAss[FldRat]) -> SeqEnum
{A maximal order in the central simple Q-algebra A.}
  return StollMaximalOrder(A, []);
end intrinsic;
*/

intrinsic MaximalOrder(A::AlgAss, primelist::[RngIntElt]) -> SeqEnum
{An order in the central simple Q-algebra A that is maximal at the primes in the primelist.}
  require BaseRing(A) cmpeq Rationals(): "Algebra must be over the rationals.";
  vprintf CSAMaximalOrder, 1: "MaximalOrder(primelist = %o)\n", primelist;
  V := Module(A);
  n := Dimension(V);
  flag, nn := IsSquare(n);
  require flag: "Dimension of A must be a square.";
  bas := [A!V.i : i in [1..n]];
  require forall{b : b in  bas | bas[1]*b eq b}:
          "First basis element must be unit.";
  multtab := [[bas[i]*bas[j] : j in [1..n]] : i in [1..n]];
  dps := &join{&join{Seqset(PrimeDivisors(Denominator(c))) : c in Eltseq(e)}
                : e in &cat multtab};
  lcm := LCM(&cat[[Denominator(c) : c in Eltseq(e)] : e in &cat multtab]);
  bas := [bas[1]] cat [lcm*b : b in bas[2..n]];
  Mat, mmat := MatrixAlgebra(A);
  tr0 := map<A -> Rationals() | x :-> 1/nn*Trace(mmat(x))>;
  Q1 := KSpace(Rationals(), 1);
  tr1 := hom<V -> Q1 | [Q1 | [tr0(A!V.i)] : i in [1..n]]>;
  tr := map<A -> Rationals() | x :-> tr1(V!x)[1]>;
  trmat := Matrix([[tr(bas[i]*bas[j]) : j in [1..n]] : i in [1..n]]);
  det := Determinant(trmat);
  if IsEmpty(primelist) then
    primelist := [p : p in PrimeDivisors(Integers()!det)];
  end if;
  primes := Setseq(Seqset(primelist) join dps);
  vprintf CSAMaximalOrder, 2: "  New primelist = %o\n", primes;
  if IsVerbose("CSAMaximalOrder", 2) then
    printf "    Valuations of discriminant: ";
    for p in primes do
      printf "<%o, %o> ", p, Valuation(det, p);
    end for;
    printf "\n";
  end if;
  errorflag := false;  // Added by TAF
  for p in primes do
    vprintf CSAMaximalOrder, 2: "  Maximizing at prime p = %o\n", p;
    F := GF(p);
    VF := KSpace(F, n);
    val := Valuation(det, p) div 2;
    // some useful functions
    lift := func<a | 2*l gt p select l-p else l where l := Integers()!a>;
    function annihilator(idl, bas, h)
      liftA := func<v | A!&+[lift(v[i])*bas[i] : i in [1..n]]>;
      if Dimension(idl) eq 0 then return idl; end if;
      idlbas := [V | liftA(b) : b in Basis(idl)];
      L := Lattice(Matrix([V | p*b : b in bas] cat idlbas));
      BL := Basis(L);
      hBL := hom<V -> V | BL>;
      multtabL := [Matrix([VF!(((A!V!BL[i])*(A!V!BL[j])) @@ hBL)
                            : j in [1..n]])
                    : i in [1..n]];
      // find annihilator
      ann := &meet[Kernel(m) : m in multtabL];
      annB := [VF | &+[b[i]*BL[i] : i in [1..n]] @@ h : b in Basis(ann)];
      return sub<VF | annB>;
    end function;
    ind := function(b)
             i := 1; while b[i] eq 0 do i +:= 1; end while;
             assert b[i] eq 1;
             return i;
           end function;
    function newbasis(ann, bas)
      liftA := func<v | A!&+[lift(v[i])*bas[i] : i in [1..n]]>;
      newB := [<ind(b), V!liftA(b)> : b in Basis(ann)];
      if newB[1,1] eq 1 then
        i := 2; while Basis(ann)[1,i] eq 0 do i +:= 1; end while;
        b1 := 1/Basis(ann)[1,i]*Basis(ann)[1];
        newB := Append([newB[i] : i in [2..#newB]], <i, V!liftA(b1)>);
      end if;
      if IsVerbose("CSAMaximalOrder", 2) then
        printf "      Adding new basis elements\n";
        for b in newB do printf "        %o/%o\n", b[2], p; end for;
      end if;
      bas1 := bas;
      for b in newB do
        bas1[b[1]] := 1/p*b[2];
      end for;
      return bas1;
    end function;
    // now enter the loop
    while val ne 0 do
      // bas is a Z-basis of the order currently considered
      // liftA lifts an element of this order mod p, expressed on bas,
      //  to an element of A, expressed on its given basis
      liftA := func<v | A!&+[lift(v[i])*bas[i] : i in [1..n]]>;
      h := hom<V -> V | [V | b : b in bas]>;
      multtab := [[(V!(bas[i]*bas[j])) @@ h : j in [1..n]] : i in [1..n]];
      assert LCM(&cat[[Denominator(c) : c in Eltseq(e)] : e in &cat multtab])
               eq 1;
      // find radical
      vprintf CSAMaximalOrder, 2: "    Computing radical ...\n";
      rad := VF;
      for m := 0 to Floor(Log(p, nn)) do
        basrad := Basis(rad);
        basloc := [liftA(b) : b in basrad];
        trmat1 := Matrix(F, [[tr((b1*b2)^(p^m))/p^m : b2 in basloc]
                              : b1 in basloc]);
        rad := sub<VF | [&+[b[i]*basrad[i] : i in [1..#basrad]]
                          : b in Basis(Kernel(trmat1))]>;
      end for;
      dim := Dimension(rad);
      vprintf CSAMaximalOrder, 2: "    Radical has dimension %o\n", dim;
      if dim gt 0 and IsVerbose("CSAMaximalOrder", 3) then
        printf "      Basis of radical:\n";
        for b in Basis(rad) do
          printf "        %o\n", b;
        end for;
      end if;
      // try if radical leads to a larger order
      ann := annihilator(rad, bas, h);
      dimann := Dimension(ann);
      vprintf CSAMaximalOrder, 2: "    Annihilator has dimension %o\n", dimann;
      if dimann gt 0 and IsVerbose("CSAMaximalOrder", 3) then
        printf "      Basis of annihilator:\n";
        for b in Basis(ann) do
          printf "        %o\n", b;
        end for;
      end if;
      if dimann gt 0 then
        bas := newbasis(ann, bas);
        val -:= dimann;
      else // dimann eq 0
        // look for minimal ideals above radical and try them in turn
        vprintf CSAMaximalOrder, 2:
                "    Computing minimal ideals above radical ...\n";
        // set up quotient algebra
        R, red := quo<VF | rad>;
        Rbas := [liftA(b @@ red) : b in Basis(R)];
        scs := [[red(VF!((V!(b1*b2)) @@ h)) : b2 in Rbas] : b1 in Rbas];
        AR := AssociativeAlgebra<R | scs>;
        // find center
        CR := Center(AR);
        vprintf CSAMaximalOrder, 3: "      Center has dimension %o.\n", 
                                    Dimension(CR);
        VCR := Module(CR);
        // find subspace fixed under x |-> x^p
        soc := Kernel(hom<VCR -> VCR | [(CR!b)^p - (CR!b) : b in Basis(VCR)]>);
        if Dimension(soc) eq 0 then soc := VCR;  // 'if' statement added by TAF as part of a bug fix
        elif Dimension(soc) eq 1 and errorflag then soc := VCR; 
        end if;
        dimsoc := Dimension(soc);
        vprintf CSAMaximalOrder, 2:
                "    There are %o minimal ideals.\n", dimsoc;
        // split this
        if Dimension(soc) eq 1 then
          es := [AR!CR!(Basis(soc)[1])];
        else
          work := [soc];
          es := [];
          while not IsEmpty(work) do
            sp := work[#work]; Prune(~work);
            repeat
              el := CR!Random(sp);
              pol := MinimalPolynomial(el);
            until Degree(pol) gt 1;
            elpwrs := [el^i : i in [0..Degree(pol)-1]];
            roots := [Parent(pol).1 - r[1] : r in Roots(pol)];
            spl := [sub<VCR | [VCR | e*CR!c : c in Basis(sp)]
                              where e := &+[Coefficient(q,i)*elpwrs[i+1]
                                             : i in [0..Degree(q)]]
                              where q := ExactQuotient(pol, r)>
                     : r in roots];
            work cat:= [s : s in spl | Dimension(s) gt 1];
            es cat:= [AR!CR!(Basis(s)[1]) : s in spl | Dimension(s) eq 1];
          end while;
        end if;
        // es is list of generators
        idlsR := [sub<R | [R | r1*e*r2 : r1, r2 in Basis(AR)]> : e in es];
        // lift back to A
        idls := [I @@ red : I in idlsR];
        if IsVerbose("CSAMaximalOrder", 3) then
          Icount := 0;
          for I in idls do
            Icount +:= 1;
            printf "      Ideal #%o (dimension %o) has basis\n", 
                   Icount, Dimension(I);
            for b in Basis(I) do
              printf "        %o\n", b;
            end for;
          end for;
        end if;
        flag := false;
        Icount := 0;
        for I in idls do
          Icount +:= 1;
          ann := annihilator(I, bas, h);
          dimann := Dimension(ann);
          vprintf CSAMaximalOrder, 2:
                  "    Annihilator of ideal #%o has dimension %o\n",
                  Icount, dimann;
          if dimann gt 0 and IsVerbose("CSAMaximalOrder", 3) then
            printf "      Basis of annihilator:\n";
            for b in Basis(ann) do
              printf "        %o\n", b;
            end for;
          end if;
          if dimann gt 0 then
            bas := newbasis(ann, bas);
            val -:= dimann;
            flag := true;
            break;
          end if;
        end for;
        if not flag then
          // break;
          // Bug fix from TAF:
          temptrmat := Matrix([[tr(bas[i]*bas[j]) : j in [1..n]] : i in [1..n]]);
          if Valuation(Determinant(temptrmat),p) eq 0 then 
            vprintf CSAMaximalOrder, 1: "  Order is maximal at p = %o.\n", p;
            break; 
          end if;
          errorflag := true;
        end if;
      end if; // dimann gt 0
    end while;
  end for;

  return bas;
end intrinsic;

function TraceMatrix(A,b)
  n := Dimension(A);
    _, mm := MatrixAlgebra(A);
      return Matrix(n,n,[1/3*Trace(mm(b[i]*b[j])) : i,j in [1..n]]);
end function;

function matsize(mat)
  return &+[c^2 : c in Eltseq(mat)];
end function;

function siz(matseq)
  return &+[matsize(mat) : mat in matseq];
end function;

function act(matseq, T)
  return [&+[iT[i,j]*seq0[j] : j in [1..#seq0]] : i in [1..#seq0]]
         where iT := T1^-1
         where seq0 := [Transpose(T1)*mat*T1 : mat in matseq]
         where T1 := ChangeRing(T, CoefficientRing(Universe(matseq)));
end function;


/*
intrinsic Reduce1(M::Mtrx : Blocks := 50) -> Mtrx
{Reduce a symmetric matrix with integral entries.
 Returns the transformation matrix and the transformed matrix.}
  M := ChangeRing(M, Integers());
  require IsSymmetric(M): "Matrix must be symmetric.";
  if Blocks le 0 then Blocks := 10; end if;
  n := NumberOfRows(M);
  size := func<mat | Ceiling(Log(10, Max([Abs(c) : c in Eltseq(mat)])))>;
  s := size(M);
  vprintf ThreeDescent, 3: "Reduce1: size = %o digits.\n", s;
  if s le Blocks then
    U := Upper(ChangeRing(M, Rationals()) : Precision := Blocks);
    U +:= Transpose(U);
    _, T := LLLGram(U);
    Mr := T*M*Transpose(T);
    vprintf ThreeDescent, 3: "Reduce1: end size = %o digits.\n", size(Mr);
    return T, Mr;
  end if;
  B := 10^(s-Blocks);
  Mu := Matrix([[M[i,j] div B : j in [1..n]] : i in [1..n]]);
  T1 := Reduce1(Mu : Blocks := Blocks);
  M1 := T1*M*Transpose(T1);
  s1 := size(M1);
  vprintf ThreeDescent, 3: 
          "Reduce1: after reducing high part: size = %o digits.\n", s1;
  if s1 lt s then
    T2, M2 := Reduce1(M1 : Blocks := Blocks);
    return T2*T1, M2;
  else
    return Reduce1(M : Blocks := 2*Blocks);
  end if;
end intrinsic;
*/


function ZeroDivisorSearch(A, basisA)
  
  P := PolynomialRing(Rationals()); X:=P.1;
  N1 := func<x|IsIrreducible(X^3-X^2-y) select Abs(y) else 0
               where y is (x^3-x^2)[1]>;
  N2 := func<x|IsPower(y,3) select 0 else y
               where y is Abs((x^3)[1])>;
  pqrslist := [[4,5,8,7],[5,6,9,8],[6,4,7,9],
               [4,8,5,7],[5,9,6,8],[6,7,4,9],
               [7,5,8,4],[8,6,9,5],[9,4,7,6]];
  ijlist := [[1,2],[2,3],[3,1],[2,1],[3,2],[1,3]];
  rslist := [[4,7],[5,8],[6,9],[7,4],[8,5],[9,6]];

  bb := basisA;
  //  trmat := TraceMatrix(A,bb);
  ctr := 0;
  oldn := [N1(bb[i]): i in [1..3]] cat [N2(bb[i]): i in [4..9]];
  vprintf ThreeDescent, 1 : "  (3) Performing graph search.\n";
  vprintf ThreeDescent, 2 : "Basis has reduced norms\n%o\n",oldn;
  oldscore := &+oldn;
  repeat
    ctr +:= 1;
    p,q,r,s := Explode(Random(pqrslist));
    t := Random([-1,1]);
    bbp := bb[p] + t*bb[q];
    bbr := bb[r] - t*bb[s];
    newn := oldn;
    newn[p] := N2(bbp);if newn[p] eq 0 then elt := bbp; break; end if;
    newn[r] := N2(bbr);if newn[r] eq 0 then elt := bbr; break; end if;
    newscore := &+newn;
    if newscore lt oldscore then
      bb[p] := bbp;
      bb[r] := bbr;
      oldscore := newscore;
      oldn := newn;
      ctr := 0;
      vprintf ThreeDescent, 2 : "%o\n",oldn;
    end if;
    i,j := Explode(Random(ijlist));
    r,s := Explode(Random(rslist));
    bbr := bb[r] - bb[s] + bb[i] - bb[j];
    bbi := bb[i] - bb[s];
    bbj := bb[j] + bb[s];
    newn := oldn;
    newn[r] := N2(bbr);if newn[r] eq 0 then elt := bbr; break; end if;
    newn[i] := N1(bbi);if newn[i] eq 0 then elt := bbi; break; end if;
    newn[j] := N1(bbj);if newn[j] eq 0 then elt := bbj; break; end if;
    newscore := &+newn;
    if newscore lt oldscore then
      bb[r] := bbr;
      bb[i] := bbi;
      bb[j] := bbj;
      oldscore := newscore;
      oldn := newn;
      ctr := 0;
      vprintf ThreeDescent, 2 : "%o\n",oldn;
    end if;
    if ctr gt 20 then oldscore*:=1.5; end if;
  until false; 
  pp := MinimalPolynomial(elt);
  ff := Factorization(pp);
  assert exists(p){f[1] : f in ff | Degree(f[1]) eq 1};
  error if Evaluate(p,elt) eq 0, "ZeroDivisorSearch has come up with the zero element";
  return Evaluate(p,elt);
end function;



function TrivialisationFromZeroDivisor(A,x)
  Z := Integers();
  Q := Rationals();
  x := x*LCM([ Denominator(n) : n in &cat[Eltseq(x*A.i) : i in [1..9]] ]);
  mat := Matrix(Z,9,9,[Eltseq(x*A.i): i in [1..9]]);
  assert Rank(mat) in {3,6};
  if Rank(mat) eq 6 then mat := KernelMatrix(mat); end if;
  V := RModule(Z,9);
  U,map := sub<V|[V!mat[i]: i in [1..Nrows(mat)]]>;
  assert Dimension(U) eq 3;
  mat := Matrix(Z,3,9,[Eltseq(map(U.i)): i in [1..3]]);
  mat := LLL(mat);
  mat := RMatrixSpace(Q,3,9)!mat;
  V := VectorSpace(Q,3);
  map := hom<V -> A|mat>;
  bb := [map(V.i): i in [1..3]];
  mats := [Matrix(Q,3,3,[Eltseq((b*A.j) @@ map) : b in bb]) : j in [1..9]];
  Mat := Universe(mats);
  iso:= map< A -> Mat | a :-> &+[ Eltseq(a)[i]*mats[i] : i in [1..9]] >;
  return iso;
end function;



// Given a central simple algebra of dimension 3^2 with unit 'one',
// and an element t in it satisfying t^2 = 0, 
// return an isomorphism with the matrix algebra, 
// and a basis of A corresponding to the standard basis of the matrix algebra.
function TrivialisationFromNilpotent(Aa, one, t, bas)

  error if not Aa eq Parent(t), "t must live in Aa.";
  error if not Dimension(Aa) eq 9, "Aa must be of dimension 9.";
  error if not t*t eq Aa!0 and t ne Aa!0, "t must satisfy t^2 = 0 and be nonzero.";
  error if not Universe(bas) eq Aa and #bas eq 9
          and Dimension(sub<Module(Aa) | ChangeUniverse(bas, Module(Aa))>) eq 9,
          "bas must be a basis of Aa.";
  V := Module(Aa);
  h := hom<V -> V | bas>;
  th := t @@ h;
  error if not forall{c : c in Eltseq(th) | Denominator(c) eq 1},
          "t must be in order generated by bas.";
  th := 1/GCD(ChangeUniverse(Eltseq(th), Integers()))*th;
  for i := 1 to 9 do if t[i] ne 0 then ti := i; break; end if; end for;
  quott := func<u | u[ti]/t[ti]>;
  // first step: set up linear form l such that t*x*t = l(x)*t
  vprintf ThreeDescent, 1: "ConstructIsomorphism: t = %o\n", th;
  lin := [quott(t*b*t) : b in bas];
  g, gs := XGCD(ChangeUniverse(lin, Integers()));
  assert g eq 1;
  e1 := t*Aa!h(V!gs);
  assert e1^2 eq e1;
  e1h := e1 @@ h;
  vprintf ThreeDescent, 2: "  Found idempotent e1 = %o\n", e1h;
  // second step: set up linear form L such that e1*x*t = L(x)*t
  lin1 := [quott(e1*b*t) : b in bas];
  sol := Solution(Transpose(Matrix(Integers(), [lin, lin1])), Vector([1, 0]));
  e2 := (Aa!h(V!sol))*t;
  e2h := e2 @@ h;
  vprintf ThreeDescent, 2: "  Found idempotent e2 = %o\n", e2h;
  assert e2^2 eq e2 and e1*e2 eq Aa!0 and e2*e1 eq Aa!0;
  e3 := one - e1 - e2;
  e3h := e3 @@ h;
  assert e3*e3 eq e3 and e3*e1 eq Aa!0 and e1*e3 eq Aa!0
         and e3*e2 eq Aa!0 and e2*e3 eq Aa!0;
  vprintf ThreeDescent, 2: "  Found idempotent e3 = %o\n", e3h;
  // now take e1 to [[100][000][000]], e2 to [[000][010][000]],
  // e3 to [[000][000][001]]
  // find other basis elements as intersections of left and right ideals
  lme1 := Matrix(Integers(), [Eltseq((e1*b - b) @@ h) : b in bas]);
  rme1 := Matrix(Integers(), [Eltseq((b*e1 - b) @@ h) : b in bas]);
  lme2 := Matrix(Integers(), [Eltseq((e2*b - b) @@ h) : b in bas]);
  rme2 := Matrix(Integers(), [Eltseq((b*e2 - b) @@ h) : b in bas]);
  lme3 := Matrix(Integers(), [Eltseq((e3*b - b) @@ h) : b in bas]);
  rme3 := Matrix(Integers(), [Eltseq((b*e3 - b) @@ h) : b in bas]);
  B12 := Basis(Kernel(lme1) meet Kernel(rme2));
  assert #B12 eq 1;
  e12 := Aa!h(B12[1]);
  B23 := Basis(Kernel(lme2) meet Kernel(rme3));
  assert #B23 eq 1;
  e23 := Aa!h(B23[1]);
  B31 := Basis(Kernel(lme3) meet Kernel(rme1));
  assert #B31 eq 1;
  e31 := Aa!h(B31[1]);
  for i := 1 to 9 do if e1[i] ne 0 then e1i := i; break; end if; end for;
  e1231 := e12*e23*e31;
  s := e1[e1i]/e1231[e1i];
  assert s in {-1, 1};
  e31 := s*e31;
  e21 := e23*e31;
  e32 := e31*e12;
  e13 := e12*e23;
  assert e12*e23*e31 eq e1 and e13*e32*e21 eq e1;
  basis := [e1,e12,e13, e21,e2,e23, e31,e32,e3];
  Mat := MatrixAlgebra(BaseRing(Aa), 3);
  h := Inverse(hom<V -> V | ChangeUniverse(basis, V)>);
  iso:= map<Aa -> Mat | a :-> &+[v[i]*Basis(Mat)[i] : i in [1..9]]
                           where v := h(a)>;
  mat := [V | Eltseq(iso(Aa.i)) : i in [1..9]];
  hh := Inverse(hom<V -> V | mat>);
  bas1 := [Aa | hh(V.i) : i in [1..9]];
  assert [iso(b) : b in bas1] eq Basis(Mat);
  return iso, bas1;
end function;







function UpperR(mat)  // Mtrx -> Mtrx
  D, T := OrthogonalizeGram(mat);
  Ti := T^-1;
  n := NumberOfRows(mat);
  return Ti*DiagonalMatrix([Abs(D[i,i]) : i in [1..n]])*Transpose(Ti);
end function;



intrinsic Trivialize(Aa::AlgAss, bas::SeqEnum) -> BoolElt, AlgAssElt
{Given a split central simple algebra over Q and a basis of a maximal order, 
 find an explicit isomorphism of this maximal order with the matrix algebra.}
  vprintf ThreeDescent, 1: "Trivialize ...\n";
  n := Dimension(Aa);
  flag, nn := IsSquare(n);
  require flag: "Dimension of Aa must be a square.";
  // require n eq 9: "Dimension of Aa has to be 9.\n";
  _, mm := MatrixAlgebra(Aa);
  trmat := Matrix([[1/nn*Trace(mm(bas[i]*bas[j])) : j in [1..n]] : i in [1..n]]);
  require Abs(Determinant(trmat)) eq 1:
          "Aa must be split, and bas must be a basis of a maximal order.";
  V := Module(Aa);
  h := hom<V -> V | bas>;
  sss := [[Eltseq((bas[i]*bas[j]) @@ h) : j in [1..n]] : i in [1..n]];
  mmats := [Matrix([[sss[i,j,k] : j in [1..n]] : i in [1..n]]) : k in [1..n]];
  size := siz(mmats);
  vprintf ThreeDescent, 2: "    Size = %o\n", size;
  // first reduce trace form
  vprintf ThreeDescent, 2: "  Reduce trace form ...\n";
  U := UpperR(trmat);
  _, T := LLLGram(U + Transpose(U));
  bas := [&+[T[i,j]*bas[j] : j in [1..n]] : i in [1..n]];
  T := Transpose(T);
  mmats := act(mmats, T);
  size := siz(mmats);
  vprintf ThreeDescent, 2: "    Size = %o\n", size;
  vprintf ThreeDescent, 2: "  Reduce forms for x^2 = 0 ...\n";
  // put in new method, acting directly on the matrices

  // NEW VERSION (2006-06-27): try reducing every separate symmetrized matrix,
  // plus all together, with various weights,
  // and pick the reduction that gives the smallest size
  function tweakU(U)
    U +:= Transpose(U);
    fa := 0.0001;
    while not IsPositiveDefinite(U) do
      U +:= fa*Parent(U)!1;
      fa *:= 2;
    end while;
    return U;
  end function;
  
  n3 := nn^3;
  origsize := size;
  oldsizes := {size};
  for jj := 1 to 2000 do 
    olds := size;
    Us := [UpperR(m + Transpose(m)) : m in mmats];
    mss := [Sqrt(matsize(m)) : m in mmats];
    UsR := [ChangeRing(U, RealField()) : U in Us];
    Us1 := [&+UsR, &+[1/mss[i]*UsR[i] : i in [1..#mss]],
            &+[1/Sqrt(mss[i])*UsR[i] : i in [1..#mss]]];
    Us1 := [tweakU(U) : U in Us1];
    Ts := [Transpose(T) where _, T := LLLGram(U) : U in Us]
         cat [Transpose(T) where _, T := LLLGram(U) : U in Us1];
    mmatss := [act(mmats, T) : T in Ts];
    size, pos := Min([siz(mm) : mm in mmatss]);
    mmats := mmatss[pos];
    bas := [&+[T[j,i]*bas[j] : j in [1..n]] : i in [1..n]] where T := Ts[pos];
    vprintf ThreeDescent, 3: "     pos = %o ==>\n", pos;
    vprintf ThreeDescent, 2: "    Size = %o\n", size;
    vprintf ThreeDescent, 2: "      Sizes:";
    // END OF THE NEW  (2006-06-27) SECTION
    if IsVerbose("ThreeDescent", 2) then
      for mat in mmats do
        s := matsize(mat);
        if s ge 1000 then
          printf "  %od", 1 + Floor(Log(10, s));
        else
          printf "  %o", s;
        end if;
      end for;
      printf "\n";
    end if;
    if size lt 1000 and size in oldsizes then break;
    elif size gt Min(oldsizes)^1.5 or jj gt 50 and size ge origsize 
                                   or Abs(size-olds)/size lt 1/10^5 
      then return 0; 
    elif jj eq 1000 then 
      print "\n  *** PLEASE SEND THIS EXAMPLE TO magma-bugs@maths.usyd.edu.au ***\n\n";
      return 0;
    end if;
    Include(~oldsizes, size); 
  end for;
  vprintf ThreeDescent, 2: "  Done with x^2 = 0 reduction.\n", size;

  // If one of the basis elements is nilpotent, it's easy ...
  for b in bas do
    if b^2 eq 0 then 
       iso := TrivialisationFromNilpotent(Aa, Aa.1, b, bas);
       return iso;
    end if;
  end for;

  // None of the basis elements are nilpotent, so find a zero divisor ...
  zd := ZeroDivisorSearch(Aa, bas);
  return TrivialisationFromZeroDivisor(Aa,zd);

end intrinsic;

