freeze;

///////////////////////////////////////////////////////////////////////////////////////////////

intrinsic HasPRoot(R::RngPad) -> BoolElt
{True if the local ring L contains a primitive p-th root of unity where p is 
 the prime of R.}
  p := Prime(R);
  if p eq 2 then return true; end if;
  
  Zp := PrimeRing(R);
  e := RamificationIndex(R,Zp);
  f := InertiaDegree(R,Zp);
  pi := UniformizingElement(R);
//"e",e;
  if not e mod (p-1) eq 0 then return false; end if;
//"noch da"; 
  
  F := ResidueClassField(R);
  Fy := PolynomialRing(F); y := Fy.1;
  
  g := y^(p-1)+F!(p/pi^e);
  
  return HasRoot(g);
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////

    
function absolute_totally_ramified_extension(R)

    f := 1;
    e := 1;
    C := R;
    repeat 
	cf := InertiaDegree(C);
	ce := RamificationDegree(C);
	C := CoefficientRing(C);
	f *:= cf;
	e *:= ce;
    until (cf eq 1 and ce eq 1) or Type(C) ne Type(R);

    assert2 f eq AbsoluteInertiaDegree(R);
    assert2 e eq AbsoluteRamificationDegree(R);
    assert2 Type(C) ne RngPad or C eq PrimeRing(R);

    if f gt 1 then
	res := ResidueClassField(C);
	res_ext := ext<res | f>;

	B := UnramifiedExtension(C, DefiningPolynomial(res_ext, res));
    else 
	B := C;
    end if;

if true then
  resext :=PolynomialRing(Integers())!
    MinimalPolynomial(PrimitiveElement(ResidueClassField(B)));
  rB :=Roots(resext,B)[1,1];
  rR :=Roots(resext,R)[1,1];
  piR :=UniformizingElement(R);

  piRp := [1, piR];
  for i in [2..e] do
    Append(~piRp, piRp[#piRp]*piR);
  end for;
  l :=Matrix([Flat(piR^i*rR^j) : j in [0..f-1], i in [0..e-1] ]
       cat [Flat(piR^e)]);
  n :=NullspaceMatrix(l);

  assert Nrows(n) eq 1;
  assert IsUnit(n[1][e*f+1]);

  n :=n/n[1][e*f+1];
  M :=Matrix(e,f,Prune(Eltseq(n)));
  n :=[Evaluate(Polynomial(Eltseq(M[i])),rB): i in [1..e]] cat [B|1];
  S :=TotallyRamifiedExtension(B, Polynomial(n));
else

  piR := UniformizingElement(R);

  piRp := [1, piR];
  for i in [2..e] do
    Append(~piRp, piRp[#piRp]*piR);
  end for;
  l := Matrix([Flat(x) : x in piRp]);
  n := NullspaceMatrix(l);
  assert Nrows(n) eq 1;
  assert IsUnit(n[1][e+1]);
  n := n/n[1][e+1];
  S := TotallyRamifiedExtension(B, Polynomial(B, Eltseq(n[1])));
end if;

  // OK, at this point we have the ring, now the embeddings.
  // one direction is not too hard:
  // S -> R: S.1 -> piR, and B can be lifted (hopefully)
  // The other direction will require solving of equations again.
  fl, r := HasRoot(Polynomial(R, DefiningPolynomial(B)));
  assert fl;
  up := [1, r];
  for i in [2..f-1] do
    Append(~up, up[2]*up[#up]);
  end for;
  basis_for_S_in_R := [i*j : i in up, j in piRp];
  m := Matrix([Flat(x) : x in basis_for_S_in_R]);
  fl, mi := IsConsistent(m, IdentityMatrix(PrimeRing(R), e*f));
  assert fl;
  basis_for_R_in_S := [S| [B!Eltseq(mi[j])[(i-1)*f+1..i*f] : i in [1..e]] : j in [1..e*f]];

  m := map< R -> S | 
     a:-> &+ [x[i]*basis_for_R_in_S[i] : i in [1..e*f]] where x := Flat(a),
     b:-> &+ [x[i]*basis_for_S_in_R[i] : i in [1..e*f]] where x := Flat(b)>;

  return S, m;

end function;

intrinsic AbsoluteTotallyRamifiedExtension(R::RngPad) -> RngPad, Map
{Compute a more efficient representation of R.  
All relative totally ramified subextensions (with no intermidiate unramified extensions)
are combined into one totally ramified extension S.  
In addition the isomorphism from R to S is returned}
    return absolute_totally_ramified_extension(R);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////////////////////

function residue_system(R)

  F := ResidueClassField(R);
  b := Basis(F);
  p := Characteristic(F);
  L := [0..p-1];
  C := CartesianPower(L,#b);

  res_sys := [ ];
  for c in C do
    Append(~res_sys,R!&+[c[i]*b[i]: i in [1..#b]]);
  end for;
  return res_sys;

end function;

intrinsic ResidueSystem(R::RngPad) -> SeqEnum
{}
  return residue_system(R);
end intrinsic;

intrinsic ResidueSystem(R::RngPadRes) -> SeqEnum
{}
  return residue_system(R);
end intrinsic;

intrinsic ResidueSystem(R::RngPadResExt) -> SeqEnum
{}
  return residue_system(R);
end intrinsic;

intrinsic ResidueSystem(R::FldPad) -> SeqEnum
{A set of representatives of the elements of the residue class field of R in R}
  return residue_system(Integers(R));
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/*
intrinsic HasRootOfUnity(L::RngPad, n) -> .
{Return whether the local ring or field L contains the n-th roots of unity}
 
  p := Prime(L);
  if p eq n then 
    return HasPRoot(L);
  end if;
  
  error "sorry not implemented yet";
end intrinsic;
*/
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
// UNITS
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

declare verbose PrincipalUnitGroup, 4;

intrinsic PrimeRing(R::FldPad) -> .
{The PrimeField of R.}
  if IsField(R) then 
    return PrimeField(R);
  else
    return PrimeRing(R);
  end if;
end intrinsic;

//--------------

function residue_system_basis(R)

  F := ResidueClassField(R);
  b := Basis(F);

  return [R!b[i] : i in [1..#b]]; 

end function;

//------------

function h2_is_isomorphism(R)

  p := Prime(R);
  pi := UniformizingElement(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := -p div pi^e;
  rcf := ResidueClassField(R);
  rcfy := PolynomialRing(rcf); y := rcfy.1;
  h22 := y^(p-1)-rcf!eps;
//"h22",Factorization(h22);
//Degree(h22);
//HasPRoot(R); IsIrreducible(h22);
  return not HasRoot(h22) and not Degree(h22) eq 1;
//  return IsIrreducible(h22) and not Degree(h22) eq 1;
end function;



function find_w1(R)
// subroutine for residue_system_basis_II(
  rf := ResidueClassField(R);
  w := Basis(rf);
  pi := UniformizingElement(R);
  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := rf!(p div (-pi^e));
  mu0 := Valuation(e,p)+1;
  e0 := e/(p^(mu0-1)*(p-1));
//"mu0",mu0; 
//"eps",eps;
  ex_p := p^mu0;
  ex_1 := p^(mu0-1);
//h2_is_isomorphism(R);
  C := CartesianPower([0..p-1],#w);
  for c in C do
//"c",c;
    if not &+[c[i]:i in [1..#c]] eq 0 then
      w1 := &+[w[i]*c[i]: i in [1..#w ]];
//"w1",w1;
//"w1^ex_p-eps*w1^ex_1",w1^ex_p-eps*w1^ex_1;
      if w1^ex_p-eps*w1^ex_1 eq 0 then
        return c;
      end if;
    end if;
  end for;
  error "PrincipalUnitGroupGenerators: Fatal error in computation of w_1.";
end function;

function residue_system_basis_II(R)

  F := ResidueClassField(R);
  w := Basis(F);
//"w",w;
  c := find_w1(R);
//"c",c;
  max, pos := Maximum([c[i]:i in [1..#c]]);
//[w[i]^c[i]: i in [1..#w ]];
  w1 := &+[w[i]*c[i]: i in [1..#w ]];
//"w1",w1;
 if pos ne 1 then 
    w[pos] := w[1];
  end if;
  w[1] := w1;

  return [R!w[i] : i in [1..#w]]; 
end function;

//------------

function wstar(R)

  p := Prime(R);
  pi := UniformizingElement(R);
  e := RamificationIndex(R,PrimeRing(R));
  eps := -p div pi^e;
  rf := ResidueClassField(R);
  w := Basis(rf);
  rfy := PolynomialRing(rf); y := rfy.1;
  
  C := CartesianPower([0..p-1],#w);
  for c in C do
    w_star := &+[w[i]*c[i]: i in [1..#w ]];
    h := y^p-rf!eps*y-w_star;
    if IsIrreducible(h) then
      return R!w_star;
    end if;
  end for;
  error "PrincipalUnitGroupGenerators: Fatal error in computation of w_star.";
end function;

// -----------

function Fe(R)

  p := Prime(R);
  e := RamificationIndex(R,PrimeRing(R));

  F := [];
  for i := 1 to Floor(p*e/(p-1)) do 
    if i mod p ne 0 then 
      Append(~F,i);
    end if;
  end for;

  return F;

end function;
  
function principal_units_generators_I(R)
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: case I";
   
//p := Prime(R);  
  pi := UniformizingElement(R);  
  m := Precision(R);  
    
  resy := residue_system_basis(R);  
//"resy",resy;   
    
  gens := [];
  
  F := Fe(R);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Fundamental levels:", F;
//"Fe",F;
  for nu in F do
    if nu lt m then
      for r in resy do
        Append(~gens, 1+r*pi^nu);
      end for;
    end if;
  end for;
//"gens",gens;
  return gens;
  
end function;


function principal_units_generators_II(R);

  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: case II";

  e := RamificationIndex(R,PrimeRing(R));
  p := Integers()!Prime(R);
  mu0 := Valuation(e,p)+1;
//(e/(p^(mu0-1)*(p-1)));
  e0 := Integers()!(e/(p^(mu0-1)*(p-1)));
   
  pi := UniformizingElement(R);  
  m := Precision(R);  
    
  resy := residue_system_basis_II(R);  
//"resy",resy;    
  gens := [];

  F := Fe(R);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Fundamental levels:", F;
  for nu in F do
    if nu lt m then
      for r in resy do
        Append(~gens, 1+r*pi^nu);
      end for;
    end if;
  end for;
  Append(~gens, 1+wstar(R)*pi^(p^mu0*e0));

  return gens;

end function;


function principal_units_generators(R)

  e := RamificationIndex(R,PrimeRing(R));
  p := Prime(R);
        
  if e mod (p-1) ne 0 or h2_is_isomorphism(R) or Precision(R) lt e/(p-1) then
     gens :=  principal_units_generators_I(R);
  else
     gens := principal_units_generators_II(R);
  end if;
 
  gens := Reverse(gens);
  //vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators: Generators:", gens;
  return gens;
end function;


intrinsic PrincipalUnitGroupGenerators(R::RngPad) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(R);
end intrinsic;

intrinsic PrincipalUnitGroupGenerators(R::RngPadRes) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(R);
end intrinsic;

intrinsic PrincipalUnitGroupGenerators(R::FldPad) -> SeqEnum
{A set of generators of the group of principal units of R.}
  return principal_units_generators(Integers(R));
end intrinsic;



/////////////////////////////////////////////////////////////////////////////
// UNITS cohen
//--------------------------------------------------------------------------
// principal untit functions for quadratic representation

function basis(R)
//{absolute basis of a local ring}
  
  T := R;
  L := [1];
  repeat
    S := T;
    M := [ [S.1^ex*l: ex in [0..Degree(S)-1]] : l in L];
    L := Flat(M);
    T :=  BaseRing(S);
  until BaseRing(S) eq PrimeRing(S);
  return L;

end function;

function pi_rep_mat(R) //-> .
//{representation matrix of pi*R}

  n := Degree(R, PrimeRing(R));
  bas := basis(R);
  pi := UniformizingElement(R);
 
  L := [];
  for b in bas do
    Append(~L,Flat(pi*b));
  end for;
  
  M := Matrix(L);
  ZM := MatrixAlgebra(Integers(),n);
  M := (ZM!M);
  return M;

end function;




function list_mat_reduce(L,M) //-> .
//{M must be in HNF}

  n := #L;
  for i := 1 to n do
    if Abs(L[i]) ge Abs(M[i][i]) then
      f := Floor(L[i]/M[i][i]);
      L := [ Integers()!(L[j]-f*M[i][j]): j in [1..n]];
    end if;  
  end for;

  return L;

end function;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


function principal_unit_group_quad_disc_log_level_k_l(punits, s, eta)// -> .
//{for eta with eta-1 in (pi^(2^(s-1))) compute a representation 
// of eta-1 in (pi^(2^(s-1)))/(pi^l),  2^(s-1) lt l le 2*2^(s-1).
//for eta in 1+(pi^quadlog)/1+(pi^m) compute a representation
// in (pi^quadlog)/(pi^m)}
  
  n := punits`n;
//"s:",s;
  Q := Rationals();
  p := Prime(punits`R);
  RR := pAdicRing(p,3*punits`prec);

  if s lt punits`quadlogexp then
    eta1 := eta - 1;
    if Valuation(eta1) gt 2^s then
      return [0: i in [1..n]];
    end if;
    if Valuation(eta1) lt 2^(s-1) then
      error "PrincipalUnitGroup: ERROR in discrete logarithm (quadratic).";
    end if;
  else
    eta1 := Log(eta);
    assert Exp(eta1) eq eta;
//"val(Log(eta))",Valuation(eta1);
    if Valuation(eta1) lt punits`quadlog then
      error "PrincipalUnitGroup: ERROR in discrete logarithm (logaritmic).";
    end if;
  end if;
//"val(eta1)",Valuation(eta1);
//"eta1",eta1;
  b := Flat(eta1);
//"b:",b;
  c := [Integers()!(RR!cc) : 
        cc in Eltseq(((Matrix([[Q!bb: bb in b]]))*punits`AA_inv[s])[1])];
//"1c:",c;
  c := list_mat_reduce(c,punits`level_rels[s]);    
//"level_rels",punits`level_rels[s];
//"2c:",c;
//"in: 1+pi^",2^(s-1),"/1+pi^",2^(s);
  return c;
end function;


function principal_unit_group_quad_disc_log(punits, eta) //-> .
//{discrete log in the principal units of R}
//"disc log ============================================";
  n := punits`n;
    
  k := 1; s := 1;
  a := [];
    
  while k ne punits`prec do
    l := Minimum(2*k,punits`prec);
    if k eq punits`quadlog then
      "truncating at k=", k, punits`quadlog, punits`prec;
      l := punits`prec;    // p-adic log/exp can handle the remaining steps
    end if;
//"disc log levels",k," to ", l,"--------------------";
//"eta:",eta;
//"val1:",Valuation(eta-1);
    c := principal_unit_group_quad_disc_log_level_k_l(punits, s, eta);
//"c:",c;//Parent(c);
//"hoch1",n;
    //eta := eta/&*[(punits`level_gens[s][i])^c[i] : i in [1..n]];
    if l ne punits`prec then // we do not need eta anymore 
                            //if we are at the highest level
//punits`level_gens[s];
      eta := eta div PowerProduct(punits`level_gens[s],c);
//"val2:",Valuation(eta-1);
//if Valuation(eta-1) lt l then
//"prec", punits`prec;
//"eta",eta;
//"val",Valuation(eta-1);
//error "ALARM disc log";
//end if;
    end if;
    if a eq [] then a := c; else a := Flat([a,c]); end if;
    k := l; s := s+1;
  end while;
//"a",a;
//"eta-1 val", Valuation(eta-1);
//"disclogminval",  Minimum([Valuation(aa,Prime(punits`R)):aa in a]);
//([Valuation(aa,Prime(punits`R)):aa in a]);
  return a;

end function;

/*
 * CF: bad example for the logarithmic method:
 <example>
   K := CyclotomicField(5);
   M := MaximalOrder(K);
   P := Decomposition(M, 5)[1][1];
   C, mC := Completion(M, P);
   C`DefaultPrecision := 12;
   B := BaseRing(C);
   B`DefaultPrecision := 3;

   CC := ChangePrecision(C, 12);
   U, mU := UnitGroup(CC);
   // if log method is used at precision 12 then
   [U.i @mU@@mU eq U.i : i in [1..Ngens(U)]];
   // does not always work. The quad-mehtod is fine.
 </example>
*/
function principal_unit_group_quad(R,prec) //-> .,.
//{the group of principal units of R together with a map}


  PUNITS := recformat<
            R,              // valuation ring
            n,              // absolute degree of R over Qp 
            basis,          // absolute basis of the valuation ring
            prec,           // (pi^prec) is the modulus
            AA,             // list of powers of the representation matrix of (pi)
            AA_inv,         // list of the inverses
            AA_exps,        // AA[i] = (pi)^AA_exps[i]
            level_gens,     // generators
            level_rels,     // step_rels[s] := AA[s+1]*AA_inv[s]
            generators,     // list of generators 
            relations,      // relation matrix
            basis_generators,//
            P_elts,
            quadlog,
            quadlogexp,
            group           // principal units as an abelian group 
            >;
//prec; 
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup: using precision",prec;
  vprintf PrincipalUnitGroup,3: "PrincipalUnitGroup: initializing";
  n := Degree(R,PrimeRing(R));
  e := RamificationIndex(R,PrimeRing(R));
  p := Prime(R);
  QM := MatrixAlgebra(Rationals(),n);
  ZM := MatrixAlgebra(Integers(),n);
  punits := rec<PUNITS| R := R, n := n, basis := basis(R), prec := prec>;
  
  if true or (p eq 2 or prec eq Precision(R)) then
    /* CF: SWITCH HERE */
    logmin := prec; // do not use logarithmic method, there is a bug in the 2-adic log
    // see above example for a p=5 problem as well.
  else
    logmin := 1+Floor(e/(p-1));  
  end if;
  l:=1; ls:=0;
  vprintf PrincipalUnitGroup,3: " %o",l;
  PI := pi_rep_mat(R);
  AA := PI;
  punits`AA := [AA]; 
  punits`AA_inv := [(QM!AA)^-1];
  punits`AA_exps := [1];
  punits`P_elts := [];
//logmin := Maximum(2,1+Floor(p*e/(p-1)));  
//logmin := Maximum(2,1+Floor(e/(p-1)));  
  // for levels over logmin we can use the p-adic 
  // logarithm/exponential
  // 2^(ls-1) < logmin <= 2^ls
//"e",e;
//"logmin",logmin;
//while l ne m do
  while l lt Minimum(logmin,prec) do
    ls := ls+1;
    l := Minimum(2^ls,prec);
//"l",l;
    vprintf PrincipalUnitGroup,3: " %o",l;
    AA := PI^l;
    Append(~punits`AA, AA);
    Append(~punits`AA_inv, (QM!AA)^-1);
    Append(~punits`AA_exps, l);
  end while;
  punits`quadlogexp := ls+1;   // up to level quadlog we use the quadratic method 
  punits`quadlog := Minimum(2^ls,prec);    // for higher levels the p-adic log/exp
  if l ne prec then
    vprintf PrincipalUnitGroup,3: " finally: %o",prec;
    AA := PI^prec;
    Append(~punits`AA, AA);
    Append(~punits`AA_inv, (QM!AA)^-1);
    Append(~punits`AA_exps, prec);
  end if;
  vprintf PrincipalUnitGroup,3: "\n";
//"AA",punits`AA;
//"AA",punits`AA_exps;

  ////////////////////////////////////////////////////////////
  // if quadlog=1: generators and relations of 1+(pi)/1+(pi^prec)
  ////////////////////////////////////////////////////////////
  if punits`quadlog eq 1 then
    k := 1; s := 1; // k=2^(s-1)
    l := Minimum(2,prec); t := 1;
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- p-adic log method";
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels 1 to",prec;
    punits`level_gens :=   
        [ [Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]):j in [1..n]] ];
    punits`generators := punits`level_gens[1];
    punits`level_rels := [HermiteForm(ZM!(punits`AA_inv[s]*punits`AA[s+1]))];
    punits`relations := punits`level_rels[1];
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- done";
    return punits;
  end if;
  ////////////////////////////////////////////////////
  // generators and relations of 1+(pi)/1+(pi^2)
  ////////////////////////////////////////////////////
  k := 1; s := 1; // k=2^(s-1)
  l := Minimum(2,prec); t := 1;
  vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- quadratic method";
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels 1 to 2";
  punits`level_gens :=   
        [ [1+&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]:j in [1..n]] ];
  punits`generators := punits`level_gens[1];
  special_hnf := function(A, pr)
    B := VerticalJoin(A, p^pr*IdentityMatrix(Integers(), Ncols(A)));
    B := HermiteForm(B);
    B := Submatrix(B, 1, 1, Rank(B), Ncols(B));
    return B;
  end function;
  punits`level_rels := [special_hnf(punits`AA[s], prec)];
  punits`relations := punits`level_rels[1];
  //////////////////////////////////////////////////////
  // generators and relations of 1+(pi^2)/1+(pi^quadlog)
  //////////////////////////////////////////////////////
  k := 2; s := 2; // k=2^(s-1)
  while l lt Minimum(punits`quadlog,prec) do
//"M:",punits`relations;
//"g:",punits`generators;
    l := Minimum(2^s,prec);
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels",k,"to",l;
    ///////////////////////////////////////////////////
    // generators and relations of 1+(pi^k)/1+(pi^l)
    ///////////////////////////////////////////////////
    Append(~punits`level_rels,special_hnf(ZM!(punits`AA_inv[s]*punits`AA[s+1]), prec));
    h := [1+&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]:j in [1..n]];
    Append(~punits`level_gens,h);
    punits`P_elts cat:= [1: i in [1..n]];
    punits`P_elts := [ punits`P_elts[i]* 
                       PowerProduct([punits`generators[(s-2)*n+j]:j in [1..n] ],
                                    [punits`relations[i][(s-2)*n+j]:j in [1..n]])
                       : i in [1..#punits`generators]];
    P := [ principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i])
          : i in [1..#punits`generators]];
    punits`generators := Flat([punits`generators,h]);
    dim := NumberOfRows(punits`relations);
    new := IdentityMatrix(Integers(),dim+n);
    InsertBlock(~new,punits`relations,1,1);
    InsertBlock(~new,-Matrix(P),1,dim+1);
    InsertBlock(~new,punits`level_rels[s],dim+1,dim+1);
    punits`relations := new;
    k := l; s := s+1;
  end while;
  //vprint PrincipalUnitGroup,4: "PrincipalUnitGroup: Generators:",punits`generators;
  //////////////////////////////////////////////////////
  // generators and relations of 1+(pi^quadlog)/1+(pi^prec)
  //////////////////////////////////////////////////////
  if punits`quadlog lt prec then 
    vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- p-adic log method";
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    levels",punits`quadlog,"to",prec;
//2^(s-1),"=",punits`quadlog,"=",punits`AA_exps[s]; 
    Append(~punits`level_rels,HermiteForm(ZM!(punits`AA_inv[s]*punits`AA[s+1])));
    h := [];
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    taking exps";
    for j in [1..n] do
      Append(~h, Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]));
      vprint PrincipalUnitGroup,3: j;
    end for;
    //h := [Exp(&+[punits`basis[i]*punits`AA[s][j][i]:i in [1..n]]):j in [1..n]];
    Append(~punits`level_gens,h);
    punits`P_elts cat:= [1: i in [1..n]];
    //vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    power products";
    //newP_elts := [];
    //for i in  [1..#punits`generators] do
    //  Append(~newP_elts,  punits`P_elts[i]*
    //                      PowerProduct([punits`generators[(s-2)*n+j]:j in [1..n] ],
    //                                   [punits`relations[i][(s-2)*n+j]:j in [1..n]]));
    //  vprint PrincipalUnitGroup,3: i;
    //end for;
    //punits`P_elts:=newP_elts;
    punits`P_elts := [ punits`P_elts[i]* 
                     PowerProduct([punits`generators[(s-2)*n+j]:j in [1..n] ],
                                  [punits`relations[i][(s-2)*n+j]:j in [1..n]])
                     : i in [1..#punits`generators]];
    vprint PrincipalUnitGroup,3: "PrincipalUnitGroup:    taking logs";
    P :=[];
    for i in  [1..#punits`generators] do
      Append(~P, principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i]));
      vprint PrincipalUnitGroup,3: i;
    //P := [ principal_unit_group_quad_disc_log_level_k_l(punits, s, punits`P_elts[i])
    //   : i in [1..#punits`generators]];
    end for;
    punits`generators := Flat([punits`generators,h]);
    dim := NumberOfRows(punits`relations);
    new := IdentityMatrix(Integers(),dim+n);
    InsertBlock(~new,punits`relations,1,1);
    InsertBlock(~new,-Matrix(P),1,dim+1);
    InsertBlock(~new,punits`level_rels[s],dim+1,dim+1);
    punits`relations := new;
//"M:",punits`relations;
//"g:",punits`generators;
  end if; 
  vprint PrincipalUnitGroup,2: "PrincipalUnitGroup: -- done";
  return punits;

end function;



//------------------------------------------------------------------------------
// principal units group for SNF representation

function principal_unit_group_disc_log(Zp, E_inv, new_rels, freegroup, punits, mgroup, b)
  quad_rep := principal_unit_group_quad_disc_log(punits,b);
  new_rep := [Integers()! r : r in RowSequence(Matrix(Zp,[quad_rep])*E_inv)[1]];
  free_rep := list_mat_reduce(new_rep,new_rels)[(#new_rep-#Generators(freegroup)+1)..#new_rep];
  return mgroup(freegroup!free_rep);
end function;


function principal_unit_embedding(R, punits, rep) 
  L := Eltseq(rep);
//"L",L;
//"hoch4",#L;
  return R!&*[punits`basis_generators[i]^L[i]: i in [1..#L]];
//[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//&*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//R!&*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
//return &*[punits`SNF_generators[i]^L[i]: i in [1..#L]];
end function;


function principal_unit_group(R, prec)
//{The group of principal units of R as an Abelian group G and the map G -> R*}
  //"principal_unit_group",prec;
  S := R;
  // S := ChangePrecision(R,Maximum(Precision(R),prec+Ceiling(prec/10))); 
  // beware of precision loss in log and exp
  Z := Integers();
  Zp := ChangePrecision(PrimeRing(R),2*Precision(PrimeRing(R)));
  //Zp := ChangePrecision(PrimeRing(R),1+Precision(PrimeRing(R)));
  //Zp := PrimeRing(R);
  p := Prime(R);
  f := InertiaDegree(R,PrimeRing(R));
  e := RamificationIndex(R,PrimeRing(R));
  //Precision(S);
  punits := principal_unit_group_quad(S, prec);
  //"punits done";  
  purank := #punits`generators;
  ///////////////////////////////////////////////////////////////
  // determine which generators will be needed for this precision
  gens := principal_units_generators(S);
  F :=  Fe(S);
  fund_levs := [f : f in F | f lt prec]; 
  if #gens gt #F*f and p*e/(p-1) lt prec then 
    // case II and high precision
    nrgens := f*#F+1; 
  else
    nrgens := f*#fund_levs;
  end if;
  gens := Reverse(Reverse(gens)[1..nrgens]);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroupGenerators:",gens;
  ///////////////////////////////////////////////////////////////
  //"gens",#gens,gens;
  //"rels", punits`relations;
  //"computing gens_reps";  
  vprint PrincipalUnitGroup,3: "PrincipalUnitGroup: computing relations";
  gens_reps := [principal_unit_group_quad_disc_log(punits,gens[i]): i in [1..#gens]];

  //CF: careful: the relations are incomplete - they include
  //contributions at the units (everything coprime to p) that need
  //removed. My guess is that this is due to the use of Integers() and
  //Rationals() in the principal_unit_group_quad function instead of
  //the p-adics.
  //So we remove the spurious parts here...
  H := FreeAbelianGroup(#punits`generators);
  H, mH := quo<H|RowSequence(punits`relations)>;
  G := FreeAbelianGroup(#gens);
  h := hom<G -> H | [mH(Domain(mH)!x) : x in gens_reps]>;
  assert IsSurjective(h);
  q, mq := quo<G|Kernel(h)>;
  hq := p^Valuation(#q, p);
  q, mmq := quo<q|hq*q>;
  mq := mq*mmq;

  ff := function(y)
    y := Domain(mH)!principal_unit_group_quad_disc_log(punits, y);
    y := y@mH;
    y := y@@h;
    y := y@mq;
    return y;
  end function;
  gf := function(x)
    return PowerProduct(gens, Eltseq(x@@mq));
  end function;

  return q, map<q -> R | x:->gf(x),
                         y:-> ff(y)>;

  /* CF: I have no idea what is happening here... */
  /* but Nils' kindly produced a counter-example where in low precision
   * (mathematically large enought!!) the relation matrix contained a free
   * part.
   */
  E_seq := [];
  //gens_reps_HNF := EchelonForm(Matrix(FiniteField(3),gens_reps));
  //gens_reps_HNF := EchelonForm(Matrix(Z,gens_reps));
  gens_reps_HNF := EchelonForm(Matrix(FiniteField(p),gens_reps));
  //"gens_reps",gens_reps;
  //"gens_reps_HNF",gens_reps_HNF,Rank(gens_reps_HNF);
  //"E_herm",E_herm;  
  j := 0;
  if #gens ne Rank(gens_reps_HNF) then
    error "PrincipalUnitGroup: ERROR, insufficient precision.";
  end if;
  
  for i in [1..#gens] do // we need a matrix E of full rank
    j+:=1;               // which contains the rows of gens_reps
    while gens_reps_HNF[i][j] eq 0 do
      newline := [0 : l in [1..purank]];
      newline[j] := 1;
      Append(~E_seq, newline);
      j +:=1;
    end while;
  end for;
  for i in [j+1..purank] do
    newline := [0 : l in [1..purank]];
    newline[i] := 1;
    Append(~E_seq, newline);
  end for;  
  E_seq cat:= gens_reps;
  //"E_seq",E_seq;  
  E := Matrix(Zp ,E_seq);
  //E := Matrix(Z ,E_seq);
  //"E",E;
  ZM :=  MatrixAlgebra(Z,#E_seq); 
  ZpM :=  MatrixAlgebra(Zp,#E_seq); 
  QM :=  MatrixAlgebra(Rationals(),#E_seq); 
  E_hnf, E_trans := HermiteForm(E);
  E_inv := E_trans;
  new_rels := ZM!HermiteForm(((ZpM!punits`relations)*E_inv));
  
  group_rels := RowSequence(Submatrix(new_rels,purank-#gens+1,purank-#gens+1,#gens,#gens));
  assert Determinant(Matrix(group_rels)) ne 0;
  freegroup := FreeAbelianGroup(#gens);
  vprint PrincipalUnitGroup,4: "PrincipalUnitGroup: relations:",group_rels;
  group, mgroup := quo<freegroup | group_rels>;
  punits`group := group;
  punits`basis_generators := [];
  for i in [1..#Generators(group)] do
    ex := Eltseq(group.i@@mgroup);
    Append(~punits`basis_generators,&*[ gens[i]^ex[i]:i in [1..#gens]]);
  end for;
            
  map :=  hom<punits`group -> S | a :-> principal_unit_embedding(S, punits, a),
                                  b :-> principal_unit_group_disc_log
                                        (Zp, E_inv, new_rels, freegroup, punits, mgroup, S!b)>;                                  
 
  if IsVerbose("PrincipalUnitGroup",3) then
    vprint PrincipalUnitGroup,3: 
           "PrincipalUnitGroup: -- testing discrete logarithm...";
    if not &and([map(group.i)@@map eq group.i:i in [1..#Generators(group)]]) then
[<group.i,map(group.i)@@map>:i in [1..#Generators(group)]];
//S;
      error "PrincipalUnitGroup: -- failed, aborting...";
    else
        vprint PrincipalUnitGroup,3:  "PrincipalUnitGroup: -- passed";
    end if;
  end if;
                                        
  return group,map;                                                                         

end function;

intrinsic PrincipalUnitGroup(R::RngPad:Prec := false) -> GrpAb, Map
{The group of principal units of R as an Abelian group G and the map G -> R*}
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  principal_unit_group(R,prec);
  return U,m;
end intrinsic;

intrinsic PrincipalUnitGroup(R::RngPadResExt) -> .,.
{"} // "
  prec := Precision(R);
  A, map := principal_unit_group(R,prec);
  return A,map;
end intrinsic;

intrinsic PrincipalUnitGroup(R::RngPadRes) -> .,.
{"} // "
  prec := Precision(R);
  A, map := principal_unit_group(R,prec);
  return A, map;
end intrinsic;
  
/////////////////////////////////////////////////////////////////////////////
// precision 1
function unit_group_disc_log_1(R,mrf,mrfu,b)
  rfurep := mrf(b)@@mrfu;
  return rfurep;
end function;
// precision 1
function unit_group_map_1(R,cycgen,a)
  return cycgen^Eltseq(a)[1];
end function;


function unit_group_disc_log(R,cycgen,mrf,mrfu,irfu,mpu,ipu,b)
  assert b in R and Valuation(b) eq 0;
  rfurep := mrf(b)@@mrfu;
//"rfurep",rfurep,Eltseq(rfurep);
  eta := b div cycgen^Eltseq(rfurep)[1];
//"eta",eta;
//"valeta",  Valuation(eta-1);
  purep := eta@@mpu;
  return irfu(rfurep)+ipu(purep);
end function;


function unit_group_map(R,cycgen,prfu,mpu,ppu,a)
  return cycgen^Eltseq(prfu(a))[1]*mpu(ppu(a));
end function;


function  unit_group(R,prec) //-> .
//{The unit group of a local ring or field R}
//"unit group",prec;
  p := Prime(R);
  rf, mrf := ResidueClassField(R);
  rfu, mrfu := UnitGroup(rf);
//"rfu",rfu;
  if prec eq 1 then
    cycgen := (R!mrf(mrfu(rfu.1)));
    group := rfu;
    map := hom<group -> R | a :-> unit_group_map_1(R,cycgen,a),
                            b :-> unit_group_disc_log_1(R,mrf,mrfu,b)>;
    return group, map; 
  end if;

  pu, mpu := principal_unit_group(R,prec);
//"pu",pu;
//#rf;
//"hi",((Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  cycgenexp := #rf^(Ceiling(Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  cycgen := (R!mrf(mrfu(rfu.1)))^cycgenexp;
//"cycgen",(mrf(cycgen))@@mrfu;
//"cycgen",cycgen;

  group, irfu, ipu, prfu, ppu := DirectSum(rfu,pu); 
  map :=  hom<group -> R | a :-> unit_group_map(R,cycgen,prfu,mpu,ppu,a),
                                  b :-> unit_group_disc_log(R,cycgen,mrf,mrfu,irfu,mpu,ipu,b)>;
  return group, map; 
end function;

intrinsic UnitGroup(R::RngPad:Prec := false) -> GrpAb, Map
{The group of units of R as an Abelian group A and the map A -> R*.}
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group(R,prec);
  return U,m;
end intrinsic;

intrinsic UnitGroup(R::RngPadRes:Prec := false) -> GrpAb, Map
{"} // "
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group(R,prec);
  return U,m;
end intrinsic;

intrinsic UnitGroup(R::RngPadResExt:Prec := false) -> GrpAb, Map
{"} // "
  if Prec cmpeq false then
    prec := Precision(R);
  else
    prec := Prec;
  end if;
  require Type(prec) eq RngIntElt:
    "The ring must be of finite precision";

  U, m :=  unit_group(R,prec);
  return U,m;
end intrinsic;



///// unit groups of fields /////////////////////////////////////////////////////////////

function unit_group_fld_disc_log(pi,R,map_rng,fg,ifg, iur,b)
  v := Valuation(b);
  b := b/pi^v;
  rng_rep := (R!b)@@map_rng;
  rep := ifg(fg!v)+iur(rng_rep);
  return rep;
end function;

function unit_group_fld_map(pi,map_rng, pfg, pur, a)
  return pi^Eltseq(pfg(a))[1]*map_rng(pur(a));
end function;


function unit_group_fld(L,prec)
  pi := UniformizingElement(L);
  R := Integers(L);
  units_rng, map_rng := unit_group(R,prec);
  fg := FreeAbelianGroup(1);
  group, ifg, iur, pfg, pur := DirectSum(fg, units_rng);
  map :=  hom<group -> L | a :-> unit_group_fld_map(pi,map_rng, pfg, pur, a),
                           b :-> unit_group_fld_disc_log(pi,R,map_rng,fg,ifg, iur,b)>;

  return group, map; 
end function;

intrinsic UnitGroup(L::FldPad: Prec := false) -> GrpAb, Map
{The unit group of the local field L}
  if Prec cmpeq false then
    prec := Precision(L);
  else
    prec := Prec;
  end if;
  group, map :=  unit_group_fld(L, prec);
  return group, map;
end intrinsic;

intrinsic pSelmerGroup(p::RngIntElt,F::FldPad)->GrpAb,Map
{Computes the group F^*/F^*p}
  require IsPrime(p): "p must be prime";
  R:=IntegerRing(F);
  pi:=UniformizingElement(R);
  vp:=Valuation(R!p);
  k,Rtok:=ResidueClassField(R);
  if p eq 2 and vp eq 0 then
    S:=AbelianGroup([2,2]);
    function toS(a)
      error if RelativePrecision(a) lt 1,"Insufficient precision";
      va:=Valuation(a);
      i:=IsSquare(Rtok(a*(F!pi)^(-va))) select 0 else 1;
      return S![va,i];
    end function;
    bl:=exists(u){u:u in k | not(IsSquare(u))};
    assert bl;
    fromS:=func<b|pi^v[1]*(u^v[2])@@Rtok where v:=Eltseq(b)>;
  elif (#k-1) mod p eq 0 then
    idx:=(#k-1) div p;
    u:=PrimitiveElement(k);
    uidx:=u^idx;
    lookup:=[uidx^i: i in [1..p]];
    S:=AbelianGroup([p,p]);
    function toS(a)
      error if RelativePrecision(a) lt 1,"Insufficient precision";
      va:=Valuation(a);
      i:=Index(lookup,Rtok(R!(a*(F!pi)^(-va)))^idx);
      assert i ne 0;
      return S![va,i];
    end function;
    fromS:=func<b|pi^v[1]*(u^v[2])@@Rtok where v:=Eltseq(b)>;
  elif vp gt 0 then
    r:=Floor(p/(p-1)*vp+1);
    Rr:=ChangePrecision(R,r);
    U,Um:=PrincipalUnitGroup(Rr);
    Uq,toUq:=quo<U|[p*u:u in Generators(U)]>;
    S:=AbelianGroup([p] cat Invariants(Uq));
    corr:=RamificationDegree(F,PrimeField(F));
    function toS(a)
      error if RelativePrecision(a) lt r,"Insufficient precision";
      va:=Valuation(a);
      return S!([va] cat Eltseq(toUq(((Rr!(a*(F!pi)^(-va)))^(1-#k))@@Um)));
    end function;
    function fromS(b)
      va:=Eltseq(b)[1];
      e:=(F!pi)^va*F!Um((Uq!(Eltseq(b)[2..Ngens(S)]))@@toUq);
      return ChangePrecision(e,Precision(e)+3*corr);
    end function;  
  else
    S:=AbelianGroup([p]);
    function toS(a)
      error if RelativePrecision(a) lt 1,"Insufficient precision";
      return S![Valuation(a)];
    end function;
    fromS:=func<b|pi^(Eltseq(b)[1])>;
  end if;
  return S,map<F->S| a:->toS(a), b:->fromS(b)>;
end intrinsic;

/* not ready for export
intrinsic UnitGroup(L::FldPad, m::RngIntElt) -> GrpAb, Map
{The unit group of the local field L up to a precision of m}
  group, map :=  unit_group_fld(L,m);
  return group, map;
end intrinsic;
*/
////////////////////////////////////////////////////////////////////////////////
// generators of unit groups without group structure
////////////////////////////////////////////////////////////////////////////////

function unit_group_generators(R,raw)

  gens := PrincipalUnitGroupGenerators(R);
  p := Prime(R);
  rf, mrf := ResidueClassField(R);
  rfu, mrfu := UnitGroup(rf);
//"rfu",rfu;
//"pu",pu;
//#rf;
//"hi",((Valuation(Exponent(pu),p)/Valuation(#rf,p)));
  if raw then
    cycgen := R!mrf(mrfu(rfu.1));
  else
    cycgenexp := #rf^(Ceiling(Precision(R)/Valuation(#rf,p)));
    cycgen := (R!mrf(mrfu(rfu.1)))^cycgenexp;
  end if;

  Append(~gens, cycgen);
  //R!mrf(mrfu(rfu.1)));
  vprint PrincipalUnitGroup,4: "UnitGroupGenerators:",gens;
  
  return gens;    

end function;

intrinsic UnitGroupGenerators(R::RngPad:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local ring R.  
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(R)): "The ring must be of finite precision";
  return unit_group_generators(R,Raw);
end intrinsic;

intrinsic UnitGroupGenerators(R::RngPadRes:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local ring R.
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(R)): "The ring must be of finite precision";
  return unit_group_generators(R,Raw);
end intrinsic;

intrinsic UnitGroupGenerators(F::FldPad:Raw:=false) -> SeqEnum
{A set of generators of the unit group of the local field F.
If Raw is false the generator of the torsion part is a root of unity.}
  require IsFinite(Precision(F)): "The field must be of finite precision";
  gens := [UniformizingElement(F)]; 
  return ([F!g: g in unit_group_generators(Integers(F),Raw)] cat gens);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

