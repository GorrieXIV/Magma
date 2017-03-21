freeze;

import "outers.m": GOMinusSO, CGOMinusGO, SOMinusOmega;
import "graphauts.m": GAutSp, GAutO8Plus;

AddAttribute(GrpMat,"AutInfo");
AddAttribute(GrpPerm,"AutInfo");

MatToQ := function(A,q)
  local B;
// raise every element of matrix A to q-th power
  B := MatrixAlgebra(BaseRing(A),Nrows(A))!0;
  for i in [1..Nrows(A)] do for j in [1..Ncols(A)] do
    B[i][j] := A[i][j]^q;
  end for; end for;
  return B;
end function;

UT := function(mat)
//replace UT by upper triangular matrix representing same quadratic form
  local n, K, nmat;
  n:=Nrows(mat);
  K:=BaseRing(mat);
  nmat := MatrixAlgebra(K,n)!mat;
  for i in [2..n] do for j in [1..i-1] do
     nmat[j][i] +:=  nmat[i][j];  nmat[i][j]:=0;
  end for; end for;
  return nmat;
end function;

InitialiseAutInfoC := procedure(S)
/* S must be a quasisimple classical group in its natural representation.
 * Initialize the record for storing information on outer automorphisms
 * induced on S. This record is stored as the attribute S`AutInfo.
 * This must be called before calling any of the later functions on S.
 */

  /* Define the format for the AutInfo record.
   * Each automorphism has level in range [0..5].
   * 0 = inner
   * 1 = SO-Omega (types "O", "O+", "O-" only) 
   * 2 = G - S
   * 3 = CG - G (types "Sp", "O+", "O-" with odd q only)
   * 4 = field
   * 5 = graph (type "L" and Sp(4,even) only)
   * 6 = graph for type "O8+". These are not processed, but we need at
   *     most two of them.
   * automorphisms in levels 0-3 are represented by conjugating matrices.
   * In general an automorphism is described by a tuple <i, j, mat>
   * where i = 0, 1, -1, or 3,-3 and is 1 only in type "L" for level 5
   * and -1 only for Sp(4,2^e) in level 5
   * and 3 or -3 only for O^+(8,q) in level 5. (all very arbitrary)
   * j = power of field automorphism phi induced by raising to p-th power
   * mat is conjugating matrix in Magma standard version of group.
   * In case "O-", mat is the product cmat[j] * mat',
   * with mat' in CGO-(d,q). 
   * for level <= 5, the automorphism represented is graph(i) * phi^j * mat
   * Note that, in the nonlinear cases, all calcualtions are carried out not
   * with S itself but by a conjugate cS which fixes Magma's standard form.
   */
  local AutInfoRFC, d, q, fac, p, e, autrec, cfs, type, form, SS, cf, cmat,
        CF, mat, K, X, S1, S2, gens, imgens, h, diag, w, ng, commgp, commslp,
        commf, g, cS, g2, isp, scal, scalrt, formim, epsilon, d8;
  AutInfoRFC := recformat<
    type: MonStgElt, //"L", "U", "S", "O", "O+", or "O-"
    form: AlgMatElt, //(type not "L") form preserved by cS (cS is the
               //conjugate of S equal to Magma standard verison).
   //so form is preserved by result returned by Magma function SU, Sp, etc
    fmat: GrpMatElt, //transforms form to fix Magma's form for classical group
    commslp: SeqEnum, //slp's of some commutators generating S
    gen: List,    //generators of overgroup inducing stored automorphisms
    slp: List,    //SLPs describing these generators.
    level: SeqEnum,  //levels of the generators (all > 0)
    tuple: SeqEnum,  //the 3-tuples describing the induced automorphisms
    cmat: SeqEnum,   //case "O-" only. cmat[i] is a matrix such that
                     //raising entries of elements of S to power p^i
                     //and then conjugating by cmat[i] gives an
                     //automorphism of S 
    comat: GrpMatElt,//case "O" only - since CGOMinusGO does not return
                     //same result each time, we store an element of CO
                     //that induces an outer automorphism of order 2
    gaut: UserProgram  //cases Sp(4,even) O^+(8,q):  graph auto of cS
  >;
  d := Dimension(S);
  q := #BaseRing(S);
  fac := Factorisation(q);
  p := fac[1][1]; e := fac[1][2];
  autrec := rec< AutInfoRFC | >; 
  cfs := ClassicalForms(S);
  if d eq 2 and cfs`formType eq "symplectic" then
    cfs`formType  := "linear";
  end if;
  type := cfs`formType;
  type := type eq "linear" select "L" else
          type eq "unitary" select "U" else
          type eq "symplectic" select "S" else
          type eq "orthogonalcircle" select "O" else
          type eq "orthogonalplus" select "O+" else
          type eq "orthogonalminus" select "O-" else "";
  autrec`type := type;

  //exclude small cases where S not quasisimple
  if type eq "L" then
    assert d gt 1 and not <d,q> in {<2,2>,<2,3>};
  elif type eq "U" then
    assert d gt 2 and <d,q> ne <3,2>;
  elif type eq "S" then
    assert d gt 2 and <d,q> ne <4,2>;
  elif type eq "O" then
    assert d gt 2 and IsOdd(q);
  elif type eq "O+" then assert d gt 4;
  elif type eq "O-" then assert d gt 2;
  end if;

  CF := type eq "U" select SU
   else type eq "S" select Sp
   else type eq "O" select Omega
   else type eq "O+" select OmegaPlus
   else type eq "O-" select OmegaMinus
   else SL;

  if type eq "L" then
    autrec`fmat := Id(S);
  else
    autrec`fmat := TransformForm(S);
  end if;
  cS := S^(autrec`fmat);
  cfs := ClassicalForms(cS);
    
  if type eq "U" then
    form := cfs`sesquilinearForm;
    assert form eq ClassicalForms(CF(d,q))`sesquilinearForm;
  elif (type eq "O+" or type eq "O-") and p eq 2 then
    form := cfs`quadraticForm;
    assert form eq ClassicalForms(CF(d,q))`quadraticForm;
  elif type ne "L" then
    form := cfs`bilinearForm;
    assert form eq ClassicalForms(CF(d,q))`bilinearForm;
  end if;
  if type ne "L" then autrec`form := form; end if;
  autrec`gen := [* *];
  autrec`slp := [* *];
  autrec`level := [];
  autrec`tuple := [];

  /* Since the automorphisms we process may only be correct modulo scalars,
   * we find some new generators of cS that are commutators of the original
   * generators. The value of the automorphism of cS computed on the commutators
   * will then be correct.
   */
  ng := Ngens(cS);
  gens := [ cS.i : i in [1..ng] ];
  commgp := SLPGroup(ng);
  commf := FreeGroup(ng);
  h := hom< commf->commgp | [commgp.i: i in [1..ng]] >;
  commslp := &cat[ [ (commgp.i,commgp.j) : i in [1..j-1] ] : j in [2..ng]];
  while #commslp lt 6 do
    Append(~commslp, (Random(commslp)*Random(commslp))^h(Random(commf,2,3)) );
  end while;
  
  X := sub<Generic(cS) | [Evaluate(s,gens) : s in commslp] >;
//need [X,X] to be absolutely irreducible, or RecogniseClassical might fail
  PX := RandomProcess(X);
  Y := sub<Generic(cS)| [ (Random(PX),Random(PX))^Random(PX) : i in [1..10] ] >;
  while not IsAbsolutelyIrreducible(Y) do
    fga := FreeGroup(#commslp); fgb := SLPGroup(#commslp);
    hh := hom< fga->fgb | [fgb.i: i in [1..#commslp]] >;
    Append(~commslp,
             Evaluate(hh(Random(fga,8,10)), commslp) ^ h(Random(commf,8,10)) );
    X := sub<Generic(cS) | [Evaluate(s,gens) : s in commslp] >;
    PX := RandomProcess(X);
    Y :=
     sub<Generic(cS) | [ (Random(PX),Random(PX))^Random(PX) : i in [1..10] ] >;
  end while;
  while not RecogniseClassical( X : Case := cfs`formType ) do
    fga := FreeGroup(#commslp); fgb := SLPGroup(#commslp);
    hh := hom< fga->fgb | [fgb.i: i in [1..#commslp]] >; 
    Append(~commslp,
             Evaluate(hh(Random(fga,8,10)), commslp) ^ h(Random(commf,8,10)) );
    X := sub<Generic(cS) | [Evaluate(s,gens) : s in commslp] >;
  end while;
  ims := [Evaluate(s,gens) : s in commslp];
  autrec`commslp := [];
  //don't want repetitions in the image
  for i in [1..#ims] do
    if not IsIdentity(ims[i]) and not ims[i] in [ims[k]:k in [1..i-1]] then
      Append(~(autrec`commslp), commslp[i]);
    end if;
  end for;

  if type in {"O-","O+"} and IsOdd(q) then
    //store element inducing outer automorphism of order 2 in CO-GO
    epsilon := type eq "O+" select 1 else -1;
    g := CGOMinusGO(d,q,epsilon);
    //see if g induces auto of order 2 or 4 - depends on SpinorNorm of g^2
    d8 := d mod 4 eq 0 select epsilon eq 1 else
          (epsilon eq 1 and q mod 4 eq 1) or (epsilon eq -1 and q mod 4 eq 3); 
    if d8 then
      g2 := g^2;
      formim := g2 * form * Transpose(g2);
      for i in [1..d] do if form[1][i] ne 0 then
         scal := formim[1][i]/form[1][i];
         assert formim eq scal * form;
         break;
      end if; end for;
      //scal should be square!
      isp, scalrt := IsSquare(scal); assert isp;
      g2 := g2 * ScalarMatrix(d, scalrt^-1);
      assert g2 * form * Transpose(g2) eq form;
      if SpinorNorm(GL(d,q)!g2, form) eq 1 then
        g := g * GOMinusSO(d, q, epsilon);
  //check
        g2 := g^2;
        formim := g2 * form * Transpose(g2);
        for i in [1..d] do if form[1][i] ne 0 then
          scal := formim[1][i]/form[1][i];
          assert formim eq scal * form;
          break;
        end if; end for;
        //scal should be square!
        isp, scalrt := IsSquare(scal); assert isp;
        g2 := g2 * ScalarMatrix(d, scalrt^-1);
        assert SpinorNorm(GL(d,q)!g2, form) eq 0;
      end if;
    end if;
    autrec`comat := g;
  end if; //type in {"O-","O+"} and IsOdd(q)

  if type in {"O-","O+"} and IsEven(q) then
    autrec`comat := Id(S); //just to avoid crashes
  end if;
  
  if type eq "O-" and e gt 1 then
    SS:=sub<GL(d,p^e)| [MatToQ(cS.i,p): i in [1..Ngens(cS)]]>;
    tf := TransformForm(SS);
    cmat := [tf];
    for i in [2..e] do //do e-th one to find out what e-th power is.
      tf := MatToQ(tf,p);
      Append(~cmat,tf*cmat[#cmat]);
    end for;
    if IsOdd(e) and IsOdd(q) and Determinant(cmat[e]) eq -1 then
      //correct to get determinant 1, so field auto has order e, not 2e
      //but I think cmat[1[=I in thios case anyway!
      vprint LMG,3: "This is surprising!";
      tf := cmat[1] * GOMinusSO(d,q,-1);
      cmat := [tf];
      for i in [2..e] do
        tf := MatToQ(tf,p);
        Append(~cmat,tf*cmat[#cmat]);
      end for;
    end if;
    if IsOdd(e) and SpinorNorm(GL(d,p^e)!cmat[e],form) eq 1 then
      //correct to get spinor norm 0, so field auto has order e, not 2e
      vprint LMG,3: "This is very surprising!";
      tf := cmat[1] * SOMinusOmega(d,q,-1);
      cmat := [tf];
      for i in [2..e] do
        tf := MatToQ(tf,p);
        Append(~cmat,tf*cmat[#cmat]);
      end for;
    end if;
    vprint LMG,3: "cmat:",cmat;
    autrec`cmat := cmat;
  end if;

  if type eq "S" and d eq 4 and IsEven(q) then
    //store graph automorphism
    autrec`gaut := GAutSp(q);
    //note the square of this automorphism is g->MatToQ(g,2).
  end if;

  if type eq "O+" and d eq 8 then
    //store graph automorphism
    autrec`gaut := GAutO8Plus(q); //triality (order 3)
  end if;

  S`AutInfo := autrec;
end procedure;

AutTuple := function(S,genims : genims1:=[], genims2:=[] )
/* S must be a quasisimple classical group in its natural representation.
 * genims is a list of the images of the generators of S under an
 * automorphism of S. Return the 3-tuple representing this automorphism,
 * as defined earlier.
 */
  local type, d, K, q, fac, p, e, omtwist, F, h1, h2, graphl, graphs, grapho,
   found, x, g, img, cp, imcp, f1, fp1, f2, fp2, f3, fp3,
   tup1, tup2, tup3, newcommi, M1, M2, isit, testcommi, gaut, isp, scal,
   formim, scalrt, commslp, commg, commi, Sg, Si, cS, cgenims, commai,
   commaai, Sai, Saai, ha1, haa1, ag, aag;
  assert #genims eq Ngens(S);
  cS := S^(S`AutInfo`fmat);
  cgenims := [x^(S`AutInfo`fmat) : x in genims];
  type := S`AutInfo`type;
  d := Dimension(S);
  K := BaseRing(S);
  q := #K;
  fac := Factorisation(q);
  p := fac[1][1]; e := fac[1][2];
  omtwist := type eq "O-" and e gt 1;
  if omtwist then cmat := S`AutInfo`cmat; end if;
  graphl := type eq "L" and d gt 2;
  graphs := type eq "S" and d eq 4 and IsEven(q);
  grapho := type eq "O+" and d eq 8;
  if graphs or grapho then gaut:=S`AutInfo`gaut; end if;

  //we need to look at the images of some random elements of S under the
  //automorphism, but most elements will work, so they do not need to be
  //very random!
  //But we will not use the original generators of S but the commutators
  //stored as slps
  commslp := S`AutInfo`commslp;
  commg := [ Evaluate(s, [cS.i: i in [1..Ngens(cS)]]) : s in commslp ];
  commi := [ Evaluate(s, cgenims) : s in commslp ];
  Sg := sub< GL(d,q) | commg >; //avoid testing membership in S.
  Si := sub< GL(d,q) | commi >; //avoid testing membership in S.
  F:=FreeGroup(#commslp);
  
  h1 := hom< F->GL(d,q) | commg >;
  h2 := hom< F->GL(d,q) | commi >;

  if grapho then
    cgenims1 := [x^(S`AutInfo`fmat) : x in genims1];
    cgenims2 := [x^(S`AutInfo`fmat) : x in genims2];
    commai := [ Evaluate(s, cgenims1 ) : s in commslp ];
    commaai := [ Evaluate(s, cgenims2 ) : s in commslp ];
    ha1 := hom< F->GL(d,q) | commai >;
    haa1 := hom< F->GL(d,q) | commaai >;
  end if; 

  if graphl or grapho or e gt 1 then //always have e gt 1 for graphs!
    found := false;
    while not found do
      x := Random(F,0,40);
      g := h1(x); img := h2(x);
      if grapho then ag := ha1(x); aag := haa1(x); end if;
      cp := Coefficients( CharacteristicPolynomial(g) );
      if sub< K | cp[2] > ne K then continue; end if;
      imcp := Coefficients( CharacteristicPolynomial(img) );
      //identify field automorphism induced
      f1 := false; f2 := false; f3 := false;
      for i in [0..e-1] do
        if imcp[2] eq cp[2]^(p^i) then
          if forall {j : j in [3..#cp] | imcp[j] eq cp[j]^(p^i) } then
            f1 := true;
            fp1 := i;
            break;
          end if;
        end if;
      end for;

      //in case "L" identify graph x field automorphism induced
      if graphl then
        cpr := [ cp[1]^-1 * c : c in Reverse(cp) ]; //char poly of g^-T
        for i in [0..e-1] do
          if imcp[2] eq cpr[2]^(p^i) then
            if forall {j : j in [3..#cpr] | imcp[j] eq cpr[j]^(p^i) } then
              f2 := true;
              fp2 := i;
              break;
            end if;
          end if;
        end for;
        if f1 and f2 then
          vprint LMG,3: "linear ambiguity";continue;
        end if;
      end if;

      if graphs then //similarly
        cp := Coefficients( CharacteristicPolynomial( gaut(g) ) );
        if sub< K | cp[2] > ne K then continue; end if;
        //identify field automorphism induced
        for i in [0..e-1] do
          if imcp[2] eq cp[2]^(p^i) then
            if forall {j : j in [3..#cp] | imcp[j] eq cp[j]^(p^i) } then
              f2 := true;
              fp2 := i;
              break;
            end if;
          end if;
        end for;
        if f1 and f2 then
          vprint LMG,3: "Sp4 ambiguity";continue;
        end if;
      end if;

      if grapho then //have to do this slightly differently
          //because triality is not an automorphism of OmegaPlus(8,q)
        imcp := Coefficients( CharacteristicPolynomial( ag ) );
        if sub< K | imcp[2] > ne K then continue; end if;
        //identify field automorphism induced
        for i in [0..e-1] do
          if imcp[2] eq cp[2]^(p^i) then
            if forall {j : j in [3..#cp] | imcp[j] eq cp[j]^(p^i) } then
              f2 := true;
              fp2 := i;
              break;
            end if;
          end if;
        end for;
          
        imcp := Coefficients( CharacteristicPolynomial( aag ) );
        if sub< K | imcp[2] > ne K then continue; end if;
        //identify field automorphism induced
        for i in [0..e-1] do
          if imcp[2] eq cp[2]^(p^i) then
            if forall {j : j in [3..#cp] | imcp[j] eq cp[j]^(p^i) } then
              f3 := true;
              fp3 := i;
              break;
            end if;
          end if;
        end for;

        if (f1 and f2) or (f1 and f3) or (f2 and f3) then
          vprint LMG,3: "O8+ ambiguity";continue;
        end if;
      end if;

      if not f1 and not f2 and not f3 then
        error "Unrecognised automorphism.";
      end if;
      found := true;
    end while;
  
    if graphl and f2 then //graph isomorphism present
      tup1 := 1;
      tup2 := fp2;
      newcommi :=
         [ Transpose( MatToQ( (Sg.i)^-1, p^fp2 ) ) : i in [1..Ngens(Sg)] ];
    elif graphs and f2 then //graph isomorphism present
      vprint LMG,3: "Sp4 graph automorphism encountered";
      tup1 := -1;
      tup2 := fp2;
      newcommi :=
         [ ( MatToQ( gaut(Sg.i), p^fp2 ) ) : i in [1..Ngens(Sg)] ];
    elif grapho and f2 then //graph isomorphism present
      vprint LMG,3: "O8+ triality automorphism squared encountered";
      tup1 := -3;
      tup2 := fp2;
      newcommi :=
         [ MatToQ(Sg.i, p^fp2) : i in [1..Ngens(Sg)] ];
      commi := commai;
    elif grapho and f3 then //graph isomorphism present
      vprint LMG,3: "O8+ triality automorphism encountered";
      tup1 := 3;
      tup2 := fp3;
      newcommi :=
         [ MatToQ(Sg.i, p^fp3) : i in [1..Ngens(Sg)] ];
      commi := commaai;
    else
      tup1 := 0;
      tup2 := fp1;
      newcommi := [  MatToQ(Sg.i, p^fp1) : i in [1..Ngens(Sg)] ];
      if omtwist and fp1 gt 0 then
        newcommi := [ cmat[fp1]^-1 *g * cmat[fp1] : g in newcommi ];
      end if;
    end if;
  else
    tup1:=0; tup2:=0;
    newcommi := [Sg.i : i in [1..Ngens(Sg)]];
  end if;

  M1 := GModule(Sg, newcommi);
  M2 := GModule(Sg, commi);
  isit, tup3 := IsIsomorphic(M1, M2);
//if not isit then PrintFileMagma("bug",genims); end if;
  assert isit;
  if omtwist and fp1 gt 0 then
    tup3 := cmat[fp1] * tup3;
  end if;
  if graphs then //in this case we need tup3 to fix form (not just mod scalars)
    form := S`AutInfo`form;
    formim := tup3 * form * Transpose(tup3);
    for i in [1..d] do if form[1][i] ne 0 then
       scal := formim[1][i]/form[1][i];
       assert formim eq scal * form;
       break;
    end if; end for;
    //scal should be square!
    isp, scalrt := IsSquare(scal); assert isp;
    tup3 *:= ScalarMatrix(d, scalrt^-1);
  end if;

  /* For now, let's try and check the result */
   testcommi := [Sg.i: i in [1..Ngens(Sg)]];
   if tup1 ne 0 then
      testcommi := graphl select [Transpose(x^-1) : x in testcommi]
                    else  graphs select [ gaut(x) : x in testcommi]
                    else  testcommi;
   end if; 
   testcommi := [MatToQ(x, p^tup2) : x in testcommi];
   testcommi := [tup3^-1 * x * tup3 : x in testcommi];
   assert testcommi eq commi;

  return < tup1, tup2, tup3 >;
end function;

TupProduct := function(tup1, tup2 : gaut:=0, S:=0 )
/* Compute and return tuple representing composite of automorphisms
 * defined by tup1 and tup2.
 * gaut option is used for Sp(4,2^e) and O^+(8,q)
 * need to specify simple group S in Case O8+
 */
  local q, fac, p, e, mat1, mat2;
  q := #BaseRing(tup1[3]);
  fac := Factorisation(q);
  p := fac[1][1]; e := fac[1][2];
  mat1 := tup1[3]; mat2 := tup2[3];
  if tup2[1] eq 1 then
    mat1 := Transpose(mat1^-1);
  elif tup2[1] eq -1 then
    mat1 := gaut(mat1);
  elif tup2[1] in {3,-3} then
    //triality of O8+: usual method won't work, so we'll just have
    //have to work out the automorphism from scratch 
    mat := S`AutInfo`fmat;
    imat := mat^-1;
    GS := GL(8,q);

    f := map< GS->GS | g :-> g >;
    if tup1[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup1[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup1[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup1[2]) >;
    end if;
    f := map< GS->GS | g :-> tup1[3]^-1 * f(g) * tup1[3] >;
    if tup2[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup2[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup2[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup2[2]) >;
    end if;
    f := map< GS->GS | g :-> tup2[3]^-1 * f(g) * tup2[3] >;
//AutTuple expects genims for original S
    genims := [f(S.i^mat)^imat : i in [1..Ngens(S)]];

    f := map< GS->GS | g :-> gaut(g) >;
    if tup1[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup1[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup1[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup1[2]) >;
    end if;
    f := map< GS->GS | g :-> tup1[3]^-1 * f(g) * tup1[3] >;
    if tup2[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup2[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup2[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup2[2]) >;
    end if;
    f := map< GS->GS | g :-> tup2[3]^-1 * f(g) * tup2[3] >;
    genims1 := [f(S.i^mat)^imat : i in [1..Ngens(S)]];

    f := map< GS->GS | g :-> gaut(gaut(g)) >;
    if tup1[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup1[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup1[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup1[2]) >;
    end if;
    f := map< GS->GS | g :-> tup1[3]^-1 * f(g) * tup1[3] >;
    if tup2[1] eq 3 then f := map< GS->GS | g :-> gaut(f(g)) >;
    elif tup2[1] eq -3 then f := map< GS->GS | g :-> gaut(gaut(f(g))) >;
    end if;
    if tup2[2] ne 0 then
      f := map< GS->GS | g :-> MatToQ(f(g),p^tup2[2]) >;
    end if;
    f := map< GS->GS | g :-> tup2[3]^-1 * f(g) * tup2[3] >;
    genims2 := [f(S.i^mat)^imat : i in [1..Ngens(S)]];
    return AutTuple(S, genims : genims1:=genims1, genims2:=genims2 );
  end if;
  if tup2[2] ne 0 then
    mat1 := MatToQ(mat1, p^tup2[2]);
  end if;
  tp1 := tup1[1]+tup2[1];
  if tp1 eq 2 then
    tp1:=0;
  elif tp1 eq -2 then
    tp1:=0;
    tup1[2] +:= 1; //recall gaut^2 = g->MatToQ(g,2).
  end if;
  return < tp1, (tup1[2]+tup2[2]) mod e, mat1*mat2 >;
end function;

TupInverse := function(tup : gaut:=0 )
/* Compute and return tuple representing inverse of automorphism defined by tup
 * gaut option is used only for Sp(4,2^e)
 * In fact this is used only when tup[1]=0 and currently would not work
 * when triality auto of O^+8 is present.
 */
  local q, fac, p, e, mat, tup2;
  q := #BaseRing(tup[3]);
  fac := Factorisation(q);
  p := fac[1][1]; e := fac[1][2];
  if tup[1] eq 1 then
    mat := Transpose(tup[3]);
    tup2 := tup[2] eq 0 select 0 else e-tup[2];
  elif tup[1] eq -1 then
    tup2 := e - tup[2] - 1;
  else
    mat := tup[3]^-1;
    tup2 := tup[2] eq 0 select 0 else e-tup[2];
  end if;
  if tup[2] ne 0 then mat := MatToQ(mat, p^tup2); end if;
  return< tup[1], tup2, mat >;
end function;

ProcessAutC := function(S, genims, g, s : genims1 := [], genims2 := [] ) 
/* S must be a quasisimple classical group in its natural representation.
 * genims is a list of the images of the generators of S under a
 * (possibly inner) automorphism of S.
 * g is an element from the parent matrix group which induces this
 * automorphism and s is a straight line program representing g.
 * If possible, multiply g (and slp) by automorphisms already stored in
 * S`AutInfo to reduce the level of g.
 * return true/false, amended g, amended slp, and if true a matrix in S.
 * true is returned if the automorphism induced by the amended g is inner,
 * and the matrix returned is then an element of S inducing it.
 * If the level cannot be reduced to 0, then append g and its induced
 * automorphism to the lists stored in S`AutInfo.
 *
 * WARNING: for code to operate properly, each element processed must
 * either lie in stored group or multiply order of stored group by a prime.
 */
 local type, gen, slp, level, tuple, cmat, p, d, q, fac, e, rtq, inds, F, A,
    SA, x, ag, as, tup, h, w, lg, ptup, form, formim, scal, isp, scalrt,
    diag, f, cS;
  cS := S^(S`AutInfo`fmat);
  type := S`AutInfo`type;
  if type ne "L" then
     form := S`AutInfo`form;
  end if;
  gen := S`AutInfo`gen;
  slp := S`AutInfo`slp;
  level := S`AutInfo`level;
  tuple := S`AutInfo`tuple;
  d := Dimension(S);
  q := #BaseRing(S);
  fac := Factorisation(q);
  p := fac[1][1]; e := fac[1][2];
  if type eq "U" then rtq := p^(e div 2); end if;

  inner := false;
  ag:=g; as:=s;
  tup := AutTuple(S, genims : genims1:=genims1, genims2:=genims2);

//deal with level 5 component
  if tup[1] ne 0  then
    vprint LMG,3: "level 5 component";
    inds := [i : i in [1..#gen] | level[i] eq 5 ];
    if #inds eq 0 then
      Append(~S`AutInfo`gen, ag);
      Append(~S`AutInfo`slp, as);
      Append(~S`AutInfo`tuple, tup);
      Append(~S`AutInfo`level, 5);
      vprint LMG,3: "stored";
      return false, ag, as, _;
    end if;
    if tup[1] in {1,-1} then
      ag := ag * gen[ inds[1] ]; 
      as := as * slp[ inds[1] ];
      tup := type eq "L" select TupProduct(tup, tuple[ inds[1] ]) 
           else //graph auto of Sp(4,2^e)
               TupProduct(tup, tuple[ inds[1] ] : gaut:=S`AutInfo`gaut);
    else //O8+
      //complicated because stored auto could be of order 3 or 2
      ag1 := ag * gen[ inds[1] ]; 
      as1 := as * slp[ inds[1] ];
      tup1 := TupProduct(tup, tuple[ inds[1] ] :
                                gaut:=S`AutInfo`gaut, S:=S);
      if tup1[1] eq 0 then
        ag:=ag1; as:=as1; tup:=tup1; //"Got 1";
      else
        ag1 := ag1 * gen[ inds[1] ]; 
        as1 := as1 * slp[ inds[1] ];
        tup1 := TupProduct(tup1, tuple[ inds[1] ] :
                                gaut:=S`AutInfo`gaut, S:=S);
        if tup1[1] eq 0 then
          ag:=ag1; as:=as1; tup := tup1; //"Got 2";
        else
          ag := gen[ inds[1] ] * ag; 
          as := slp[ inds[1] ] * as;
          tup := TupProduct(tuple[ inds[1] ], tup :
                                gaut:=S`AutInfo`gaut, S:=S);
          if tup[1] ne 0 then
            ag := ag * gen[ inds[1] ]; 
            as := as * slp[ inds[1] ];
            tup := TupProduct(tup, tuple[ inds[1] ] :
                                gaut:=S`AutInfo`gaut, S:=S);
            assert tup[1] eq 0; //"Got 4";
            else //"Got 3";
          end if;
        end if;
      end if;
    end if;
    vprint LMG,3: "adjusted";
  end if;

//deal with level 4 component
  f := tup[2];
  if f gt 0 then
    vprint LMG,3: "level 4 component";
    inds := [i : i in [1..#gen] | level[i] eq 4 ];
    A<x> := AbelianGroup([e]);
    SA := sub< A | [ tuple[i][2]*x : i in inds ] >;
    if not f*x in SA then
      Append(~S`AutInfo`gen, ag);
      Append(~S`AutInfo`slp, as);
      Append(~S`AutInfo`tuple, tup);
      Append(~S`AutInfo`level, 4);
      vprint LMG,3: "stored - field auto order is now", #sub< A | SA, f*x >;
      return false, ag, as, _;
    end if;
    
    if #SA eq 2 then //must have #inds=1
      ag := ag * gen[ inds[1] ]; 
      as := as * slp[ inds[1] ];
      tup := TupProduct(tup, tuple[ inds[1] ]); 
      vprint LMG,3: "adjusted";
    else
    //we need to write g as word in existing generators at level 4
      F := FreeAbelianGroup(#inds);
      h := hom< F->A | [ tuple[i][2] * x : i in inds ] >; 
      w := Eltseq( (-f*x) @@ h );
      for i in [1..#w] do if w[i] ne 0 then
        ptup := tuple[ inds[i] ];
        if w[i] lt 0 then ptup := TupInverse(ptup); end if;
        ag := ag * gen[inds[i]]^w[i];
        as := as * slp[inds[i]]^w[i];
        for k in [ 1..Abs(w[i]) ] do
          tup := TupProduct(tup, ptup);
        end for;
      end if; end for;
      vprint LMG,3: "adjusted";
    end if;
  end if;

//deal with level 3 component in relevant cases
  if type ne "L" then
    formim := type eq "U" select
         tup[3] * form * MatToQ(Transpose(tup[3]), rtq)
    else tup[3] * form * Transpose(tup[3]);
    if (type eq "O+" or type eq "O-") and p eq 2 then
       formim:= UT(formim);
    end if;
    for i in [1..d] do if form[1][i] ne 0 then
      scal := formim[1][i]/form[1][i];
      assert formim eq scal * form;
      break;
    end if; end for;
    if type eq "U" then
      isp, scalrt := IsPower(scal,rtq + 1);
      assert isp;
      tup[3] *:= ScalarMatrix(d, scalrt^-1);
    else
      if not IsSquare(scal) then
         assert IsOdd(p) and type in { "S", "O+", "O-" };
        vprint LMG,3: "level 3 component";
        inds := [i : i in [1..#gen] | level[i] eq 3 ];
        if #inds eq 0 then
          Append(~S`AutInfo`gen, ag);
          Append(~S`AutInfo`slp, as);
          Append(~S`AutInfo`tuple, tup);
          Append(~S`AutInfo`level, 3);
          vprint LMG,3: "stored";
          return false, ag, as, _;
        end if;
        ag := ag * gen[ inds[1] ]; 
        as := as * slp[ inds[1] ];
        tup := TupProduct(tup, tuple[ inds[1] ]); 
        vprint LMG,3: "adjusted";
        formim := tup[3] * form * Transpose(tup[3]);
        if (type eq "O+" or type eq "O-") and p eq 2 then
           formim:= UT(formim);
        end if;
        for i in [1..d] do if form[1][i] ne 0 then
          scal := formim[1][i]/form[1][i];
          assert formim eq scal * form;
          break;
        end if; end for;
      end if;
      //now scal should be square!
      isp, scalrt := IsSquare(scal); assert isp;
      tup[3] *:= ScalarMatrix(d, scalrt^-1);
    //now tup[3] should fix the form
    end if; //type = "U"
  end if;

//deal with level 2 component in relevant cases
  diag :=  type eq "L" select GCD(q-1,d)
      else type eq "U" select GCD(rtq+1,d)
      else type in { "O+", "O-" } select GCD(q-1,2)
      else 1; 
    if type in { "O+", "O-" } then
      f := Determinant(tup[3]) eq 1 select 0 else 1;
    else
      w := PrimitiveElement(GF(q));
      lg := Log(w, Determinant(tup[3]));
      if type eq "U" then
        assert lg mod (rtq-1) eq 0;
        lg := lg div (rtq-1);
      end if;
      f := lg mod diag;
    end if;
    if f ne 0 then
      inds := [i : i in [1..#gen] | level[i] eq 2 ];
      if diag eq 2 then //worth dealing with this separately!
        vprint LMG,3: "level 2 component";
        if #inds eq 0 then
          Append(~S`AutInfo`gen, ag);
          Append(~S`AutInfo`slp, as);
          Append(~S`AutInfo`tuple, tup);
          Append(~S`AutInfo`level, 2);
          vprint LMG,3: "stored - order 2";
          return false, ag, as, _;
        end if;
        ag := ag * gen[ inds[1] ];
        as := as * slp[ inds[1] ];
        tup := TupProduct(tup, tuple[ inds[1] ]);
        vprint LMG,3: "adjusted";
      else
assert diag ne 1;
        vprint LMG,3: "level 2 component";
        detpows := [ ];
        for i in inds do
          lg := Log(w, Determinant(tuple[i][3]));
          if type eq "U" then
            assert lg mod (rtq-1) eq 0;
            lg := lg div (rtq-1);
          end if;
          detpows[i] := lg mod diag;
        end for;
        A<x> := AbelianGroup([diag]);
        SA := sub< A | [ detpows[i]*x : i in inds ] >;
        if not f*x in SA then
          Append(~S`AutInfo`gen, ag);
          Append(~S`AutInfo`slp, as);
          Append(~S`AutInfo`tuple, tup);
          Append(~S`AutInfo`level, 2);
      vprint LMG,3: "stored - diagonal auto order is now", #sub< A | SA, f*x >;
          return false, ag, as, _;
        end if;
        
        //we need to write g as word in existing generators at level 2
        F := FreeAbelianGroup(#inds);
        h := hom< F->A | [ detpows[i] * x : i in inds ] >; 
        w := Eltseq( (-f*x) @@ h );
        for i in [1..#w] do if w[i] ne 0 then
          ag := ag * gen[inds[i]]^w[i];
          as := as * slp[inds[i]]^w[i];
          tup[3] := tup[3] * tuple[inds[i]][3]^w[i];
        end if; end for;
        vprint LMG,3: "adjusted";
      end if; //diag = 2
    end if; //f ne 0
// now should lie in quasisimple group mod scalars - adjust by scalar
    w := PrimitiveElement(GF(q));
    lg := Log(w, Determinant(tup[3]));
    if type eq "L" then
      diag, c1, c2 := ExtendedGreatestCommonDivisor(d, q-1);
      assert lg mod diag eq 0;
      pow := c1 * (lg div diag);
      tup[3] := tup[3] * ScalarMatrix(d, w^(-pow));
    elif type eq "U" then
      assert lg mod (rtq-1) eq 0;
      lg := lg div (rtq-1);
      diag, c1, c2 := ExtendedGreatestCommonDivisor(d, rtq+1);
      assert lg mod diag eq 0;
      pow := (rtq-1) * c1 * (lg div diag);
      tup[3] := tup[3] * ScalarMatrix(d, w^(-pow));
    elif type eq "O" and Determinant(tup[3]) eq -1 then
      tup[3] := tup[3] * ScalarMatrix(d, -1);
    end if;
  assert Determinant(tup[3]) eq 1;

//deal with level 1 component in relevant cases
  if type eq "O" or (type eq "O+" and (d mod 4 eq 0 or q mod 4 ne 3)) or
         (type eq "O-" and (p eq 2 or (d mod 4 eq 2 and q mod 4 eq 3))) then
    if SpinorNorm(GL(d,q)!tup[3], form) eq 1 then
      vprint LMG,3: "level 1 component";
      inds := [i : i in [1..#gen] | level[i] eq 1 ];
      if #inds eq 0 then
        Append(~S`AutInfo`gen, ag);
        Append(~S`AutInfo`slp, as);
        Append(~S`AutInfo`tuple, tup);
        Append(~S`AutInfo`level, 1);
        vprint LMG,3: "stored";
        return false, ag, as, _;
      end if;
      ag := ag * gen[ inds[1] ];
      as := as * slp[ inds[1] ];
      tup[3] := tup[3] * tuple[ inds[1] ][3];
      vprint LMG,3: "adjusted";
    end if;
  elif (type eq "O+" and (d mod 4 eq 2 and q mod 4 eq 3)) or
       (type eq "O-" and p ne 2 and (d mod 4 eq 0 or q mod 4 eq 1)) then
     if SpinorNorm(GL(d,q)!tup[3], form) eq 1 then
       tup[3] := tup[3] * ScalarMatrix(d,-1);
     end if;
  end if;
  vprint LMG,3: "Automorphism is now inner!";

  return true, ag, as, GL(d,q)!(S`AutInfo`fmat * tup[3] * (S`AutInfo`fmat)^-1);
end function;

//Now some functions for doing the same thing with general
//groups that are not too large.

IdentifyEmbeddedAut := function(SS, A, genims)
//identify automorphism of group SS < A = Aut(SS) defined by genims
  local aut, cg, C;
   C := A; aut := Id(A);
   for i in [1..#genims] do
      isc, cgi := IsConjugate(C,SS.i^aut,genims[i]); assert isc;
      C := C meet Centraliser(A,genims[i]);
      aut *:= cgi;
   end for;
  return  aut;
end function;

PermRepAutGp := function(G)
//an alternative method of getting a permutation representation of
//the automorphism group of a permutation group with trivial centre and
//relatively small //outer automorphism group. Particularly suitable for
//sporadic groups.
//returns aut gp A, perm gp PA isomorphic to A, map G->PA, map A->PA
   local A, ng, nga, im, GG, imi, FA, FAtoA, OA, FAtoOA, OAtoPOA, POA, PA, H, N,
         gpai;
   assert Type(G) eq GrpPerm;
   assert #Centre(G) eq 1;
   vprint LMG,3: "new method for general automorphism group";
   A := AutomorphismGroup(G);
   ng := Ngens(G); nga := Ngens(A);
   if #A eq #G then
     im := function(aut)
       return IdentifyEmbeddedAut(G,G,[G.i @ aut : i in [1..ng]]);
     end function;
     GG := sub< G | [ im(A.i) : i in [1..nga] ] >;
     imi := hom< GG->A | [A.i : i in [1..nga] ] >;
     return A, G, IdentityHomomorphism(G),
                            hom< A->G | a:->im(a), g:->imi(g) >;
   end if;
   FA, FAtoA := FPGroup(A);
   OA, FAtoOA := OuterFPGroup(A);
   OAtoPOA, POA := CosetAction(OA,sub<OA|>); 
   T := [ Id(FA) ];
   for i in [2..#POA] do
      isc, g := IsConjugate(POA, 1, i);
      T[i] := g @@ OAtoPOA @@ FAtoOA;
   end for;
   imgp, injb, injt := WreathProduct(G, POA);
   im := function(fa) //image of an element fa in FA under map to imgp
      local im, el, g;
      im := fa @ FAtoOA @ OAtoPOA @ injt;
      for i in [1..#POA] do
        el := (T[i] * fa^-1) @ FAtoOA @ OAtoPOA;
        el := T[ 1^el ] * fa * T[i]^-1; //should be inner
        g := IdentifyEmbeddedAut(G,G,[G.i @ FAtoA(el) : i in [1..ng]]);
        im *:= g @ injb[i];
      end for;
      return im;
   end function;
   //get perm rep of aut gp
   PA := sub<imgp|[im(FA.i): i in [1..nga]]>;
   H := Stabiliser(PA,1); N := Normaliser(PA,H);
   //try reducing degree
   if N ne H then PA := CosetImage(PA,N); end if;
   //now have to work out which elements of G the inner generators are
   //inner generator numbers are actually 1,2,3,... but we won't assume that
   ig :=  [ IdentifyEmbeddedAut(G,G,[G.j @ A.i : j in [1..ng]]) :
                                      i in [1..#InnerGenerators(A)] ];
   GG := sub< G | ig >;
   GtoPA := hom< GG -> PA | [PA.i : i in [1..#ig]] >;
   IPA := sub< PA | [PA.i : i in [1..#ig]] >;
   gpai := hom< IPA->G | [GG.i : i in [1..#ig]] >;
   //Now can construct A -> PA
   im := function(aut)
     return IdentifyEmbeddedAut(IPA, PA,
                                       [GG.i @ aut @ GtoPA : i in [1..#ig]]);
   end function;
   imi := hom< PA->A | [A.i : i in [1..Ngens(A)] ] >;
   return A, PA, hom< G->PA | g:->GtoPA(g), g:->gpai(g) >,
                                  hom< A->PA | a:->im(a), g:->imi(g) >;
end function;

InitialiseAutInfoG := procedure(S)
  local AutInfoRFG, A, IG, rep, P, Q, OA, rho, e;

  AutInfoRFG := recformat<
    radquot: GrpPerm,              //radical quotient when matrix group
    radhom: HomGrp,                //radical projection when matrix group
    autgp: Grp,                    //Aut(S)
    outautgp: GrpPerm,             //Out(S)
    atoo: Map,                     //Aut(S) -> Out(S)
    pgp: GrpPerm,                  //GrpPerm isom to Aut(S)
    gtopgp: Map,                //embedding S -> pgp
    atopgp: Map,                //embedding Aut(S) -> pgp
    autos: SeqEnum,  //automorphism mapping onto generators of subgp of autautgp
    gen: SeqEnum,   //generators of overgroup inducing stored automorphisms
    slp: SeqEnum    //SLPs describing these generators.
  /**/ >;

  if Type(S) eq GrpMat then
    SS, rq := RadicalQuotient(S);
  else
    SS := S;
  end if;
    
  vprint LMG, 3: "getting aut grp";
  if IsAlternating(SS) and Degree(SS) ne 6 then
    vprint LMG, 3: "alternating", Degree(SS);
    A := Sym(Degree(SS));
    rep := IdentityHomomorphism(A);
    OA, rho := quo< A | SS>;
    S`AutInfo :=  rec< AutInfoRFG | autgp:=A, outautgp:=OA, atopgp:=rep,
            pgp:=A, gtopgp:=hom<SS->A|x:->x, x:->x>, atoo:=rep*rho,
            autos:=[], gen:=[], slp:=[] >;
  else
    _, A, e := PermRepAutGp(SS);
    rep := IdentityHomomorphism(A);
    OA, rho := quo< A | Image(e)  >;
    //OA, rho := quo< A | sub<A|[e(SS.i):i in [1..Ngens(SS)]]>  >;
    S`AutInfo :=  rec< AutInfoRFG | autgp:=A, outautgp:=OA, atopgp:=rep,
            pgp:=A, gtopgp:=e, atoo:=rep*rho, autos:=[], gen:=[], slp:=[] >;
/*
    A := AutomorphismGroup(SS);
    IG := InnerGenerators(A);
    vprint LMG, 3: "getting perm rep";
    rep, P := PermutationRepresentation(A);
    Q := sub < P | [rep(a): a in IG] >;
    OA, rho := quo< P | Q >;
    S`AutInfo := rec< AutInfoRFG | autgp:=A, outautgp:=OA, atopgp:=rep, 
                             atoo:=rep*rho, autos:=[], gen:=[], slp:=[] >;
*/
  end if;
  if Type(S) eq GrpMat then
     S`AutInfo`radquot := SS;
     S`AutInfo`radhom := rq;
  end if;
  
end procedure;


IdentifyOuterAutG := function(S, genims)
  local SS, rq, e, P;
  if Type(S) eq GrpMat then
    SS := S`AutInfo`radquot;
    rq := S`AutInfo`radhom;
    genims := [ x@rq : x in genims ];
  else
    SS := S;
  end if;

  A := S`AutInfo`autgp;
  atoo := S`AutInfo`atoo;
  if assigned S`AutInfo`gtopgp then
    e := S`AutInfo`gtopgp;
    P := S`AutInfo`pgp;
    aut := IdentifyEmbeddedAut( sub< P | [SS.i @ e : i in [1..Ngens(SS)]] >,
                         P, [g@e : g in genims]);
  else aut := A!hom< SS -> SS | genims >;
  end if;
  imaut := atoo(aut);
  return imaut;
end function;

ProcessAutG := function(S, genims, g, s)
//S is a general (quasi)simple permutation or matrix group.
//genims, g, s are as in ProcessAutC
  local A, OA, atoo, subgp, gen, slp, ag, as, aut, imaut, F, phi, w, ws, x,
        SS, rq, e, P;

  if Type(S) eq GrpMat then
    SS := S`AutInfo`radquot;
    rq := S`AutInfo`radhom;
    genims := [ x@rq : x in genims ];
  else
    SS := S;
  end if;

  A := S`AutInfo`autgp;
  OA := S`AutInfo`outautgp;
  atoo := S`AutInfo`atoo;
  autos := S`AutInfo`autos;
  gen := S`AutInfo`gen;
  slp := S`AutInfo`slp;
  ag := g; as := s;

  subautos := [ atoo(a): a in autos ];
  subgp := sub< OA | subautos >;

  if assigned S`AutInfo`gtopgp then
    e := S`AutInfo`gtopgp;
    P := S`AutInfo`pgp;
    aut := IdentifyEmbeddedAut( sub< P | [SS.i @ e : i in [1..Ngens(SS)]] >,
                         P, [g@e : g in genims]);
  else aut := A!hom< SS -> SS | genims >;
  end if;
  imaut := atoo(aut);

  if not imaut in subgp then
    Append(~S`AutInfo`autos, aut);
    Append(~S`AutInfo`gen, ag);
    Append(~S`AutInfo`slp, as);
    vprint LMG, 2: 
        "Appended - stored subgroup now has order", #sub< OA | subgp, imaut >;
    return false, ag, as, _;
  end if;

  F, phi := FPGroup(subgp);
  w := imaut @@ phi;
  ws := Eltseq(w^-1);
  for t in ws do
    if t gt 0 then
      ag := ag * gen[t];
      as := as * slp[t];
      aut := aut * autos[t];
    else
      ag := ag * gen[-t]^-1;
      as := as * slp[-t]^-1;
      aut := aut * autos[-t]^-1;
    end if;
  end for;
  vprint LMG, 3: "adjusted - automorphism is now inner";
  if assigned S`AutInfo`gtopgp then
    isi := aut in Image(e); x := aut @@ e;
  else
    isi, x := IsInner(aut);
  end if;
  assert isi;
  if Type(S) eq GrpMat then
    x := x @@ rq;
  end if;

  return true, ag, as, x;

end function;
