freeze;

/*
 Function names in this file:
 ConjElts(C, C_over)
 GammaL1(s, q)
 GammaL(d, q, s)
 IsGLConjugateSemilinear(H, K: Print)
*/

ConjElts:= function(C, C_over)
  centralisers_conj:= false;
  o1:= Order(C);
  o_cent:= Order(C_over);
  gcd:= Gcd(o1, o_cent);
  C:= C^(o1 div gcd);
  C_over:= C_over^(o_cent div gcd); 
  assert Order(C_over) eq Order(C);
  for i in [1..gcd] do
    if Order(C_over^i) eq Order(C) then
      centralisers_conj, x:= IsSimilar(C_over^i, C);
      if centralisers_conj then
        return true, x;
      end if;
    end if;
  end for;
  return false, _;
end function;
/*****************************************************************/

//This produces GammaL(1, p^s) \leq GL(s, p)
function GammaL1(s, q)
 
  fac:= Factorisation(q);
  assert #fac eq 1;

  //"making singer cycle for GL(1, q) in GL(s, q)";
  pol:= PrimitivePolynomial(GF(q), s);
  x:= Parent(pol).1;
  coeffs:= Coefficients(pol);
  mat:= GL(s, q)!Matrix(GF(q), s, s, [<i, i+1, 1>: i in [1..s-1]] cat 
                      [<s, i, -coeffs[i]>: i in [1..s]]);

  //find field automorphism - the reason that x^s has been added to the
  //argument below is to ensure that cxp[i] and cxp2[i] are always defined!
  //The basis of the field is [1, x, x^2, \ldots, x^(s-1)]
  cxp:= [Coefficients(x^s + x^(i*q) mod pol) : i in [1..s-1]];
  field_auto := GL(s, q)!Matrix(GF(q), s, s, [<1, 1, 1>] cat &cat[[<i+1,
                   j, cxp[i][j]>:i in [1..s-1] ] : j in [1..s]]);

  grp:= sub<GL(s, q)|mat, field_auto>;
  return grp;
end function;


/**************************************************************/

function GammaL(d, q, s)

  fac:= Factorisation(q);
  assert #fac eq 1;
  assert d mod s eq 0;
  dim:= d div s;

  gammal1:= GammaL1(s, q);
  if dim eq 1 then return sub<GL(d, q)|gammal1>; end if;

  singer:= gammal1.1;
  frob:= gammal1.2;
  gens4:= GL(dim, q^s).2;

  //"putting singer cycle as block into gens for GL(dim, p)";
  newmat1:= Matrix(GF(q), d, d,
                [<i, j, singer[i][j]> : i, j in [1..s]] cat [<i, i,
                GF(q)!1> : i in [s+1..d]]);
  newmat2:= Matrix(GF(q), d, d,
                &cat[[<k + i*s, k+ j*s, gens4[i+1][j+1]> : i, j in
                [0..dim-1]] : k in [1..s]]);

  //"putting frobenius aut as block into gens for GL(dim, p)";
  newmat3:= Matrix(GF(q), d, d,
                &cat[[<i+k*s, j+k*s, frob[i][j]> : i, j in [1..s]]
                 : k in [0..dim-1]] );

  return sub<GL(d, q)|newmat1, newmat2, newmat3>;
end function;

/**********************************************************************/
  
//The main function. Takes as input two matrix groups. If they can be
//shown to be conjugate in a GammaL(d, q) then return true and a conjugating
//element. If they can be shown not to be conjugate in GL then return
//false. O/wise return "unknown". If print > 0 we give information as to
//progress, and a reason why "unknown" or "false" are returned.

intrinsic IsGLConjugateSemilinear(H::GrpMat, K::GrpMat: Print:=0)
-> BoolElt, GrpMatElt 
{If conjugates of H and K can be shown to be conjugate in a maximal
superfield subgroup of the general linear group then returns true and
a matrix conjugating H to K. If H and K are shown not to be conjugate
in the general linear group then returns false. Otherwise
returns "unknown".}  
 
  n:= Degree(H);
  require n eq Degree(K): "Groups must have same dimension";
  p:= #BaseRing(H); 
  require p eq #BaseRing(K): "Groups must be over same field";

  if Print gt 0 then "testing absolute irreduciblility"; end if;
  H_abs_irred, C1, ext_h:= IsAbsolutelyIrreducible(H);
  K_abs_irred, C2, ext_k:= IsAbsolutelyIrreducible(K);

  if not (H_abs_irred eq K_abs_irred) then
    if Print gt 0 then
      "One group is absolutely irreducible and the other is not";
    end if;
    return false, _;
  end if;
  if not H_abs_irred then
    if not ext_h eq ext_k then
      if Print gt 0 then "Different field extensions"; end if; 
      //if groups aren't absolutely
      //irreducible then should get largest possible value for ext_h, 
      //ext_k.  
      return false, _; 
    end if;
    C1:= GL(n, p)!C1; 
    C2:= GL(n, p)!C2;
  end if;

  //"testing for remaining semilinear cases";
  H_semilin:= IsSemiLinear(H); K_semilin:= IsSemiLinear(K);
  if not ((H_semilin cmpeq true) and (K_semilin cmpeq true)) then 
    if Print gt 0 then "One group may not be semilinear"; end if;   
    return "unknown", _; 
  end if;
  
  if H_abs_irred then
    C1:= GL(n, p)!CentralisingMatrix(H);
    C2:= GL(n, p)!CentralisingMatrix(K);
    ext_h:= DegreeOfFieldExtension(H);
    if not ext_h eq DegreeOfFieldExtension(K) then
      if Print gt 0 then "Different field extensions"; end if;
      return "unknown", _;
    end if;			     
  end if;

  if not IsPrime(ext_h) then
    fac:= Factorisation(ext_h);
    ext_h:= fac[#fac][1];
  end if;

  if Print gt 0 then "Constructing overgroup"; end if;
  overgroup:= GammaL(n, p, ext_h);
  assert IsSemiLinear(overgroup);
  C_over:= GL(n, p)!CentralisingMatrix(overgroup);

  if Print gt 0 then 
    "Conjugating centraliser matrix of group 1 to overgroup"; 
  end if; 
  centralisers_conj, x1:= ConjElts(C1, C_over);
  if not centralisers_conj then    
    if Print gt 0 then "centralisers not conjugate"; end if;
    return "unknown", _;
  end if;
  x1:= GL(n, p)!x1; 
  temp_h:= H^x1;
  for i in [1..Ngens(temp_h)] do
    if not temp_h.i in overgroup then
      if Print gt 0 then "failed to standardise group 1 correctly"; end if;
      return "unknown", _;
    end if;
  end for;

  if Print gt 0 then 
    "Conjugating centraliser matrix of group 2 to overgroup"; 
  end if;
  centralisers_conj, x2:= ConjElts(C2, C_over);
  if not centralisers_conj then    
    if Print gt 0 then "centralisers not conjugate for second group"; end if;
    return "unknown", _;
  end if;
  x2:= GL(n, p)!x2;  

  //this next bit is probably overcautious. depends on 
  //how reliable IsSemiLinear is being.  
  for i in [1..Ngens(K)] do
    if not (K^x2).i in overgroup then
      K:= sub<GL(n, p)|K>;
      if not (IsSemiLinear(K) cmpeq true) then
        return "unknown", _;
      end if;
      C2:= CentralisingMatrix(K);
      if C2 cmpeq "unknown" then
        return "unknown", _;
      end if;
      centralisers_conj, x2:= ConjElts(C2, C_over);
      if not centralisers_conj then
        return "unknown", _;
      end if;
      x2:= GL(n, p)!x2;  
      for i in [1..Ngens(K)] do
        if not (K^x2).i in overgroup then
          return "unknown", _;
        end if;
      end for;
    end if;
  end for;
  
  if Print gt 0 then "final conj check"; end if;
  phi, ov_p:= OrbitAction(overgroup, RSpace(overgroup).1);  
  conj_in_gaml, y:= IsConjugate(ov_p, (H^x1)@phi, (K^x2)@phi);
  if not conj_in_gaml then
    if Print gt 0 then "not conj in GammaL"; end if;
    return "unknown", _;
  else
    conj_elt:= x1*(y@@phi)*x2^-1;
    return true, conj_elt;
  end if;
end intrinsic;













