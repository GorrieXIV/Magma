freeze;
 
/*
function names:
ImprimsMeetSL(d, p, t)
GammaL1(s,p)
GammaL(d, p, s)
GammaLMeetSL(d, p, s)
*/
/*****************************************************************/
//to construct SL(d/t, p)^t.(p-1)^(t-1).\Sym(t)
function ImprimsMeetSL(d, p, t : general:=false )
  assert #Factorisation(p) eq 1;
  assert d mod t eq 0;
  assert t gt 1;
  if general then
    return WreathProduct(GL(d div t, p), Sym(t));
  end if;
  subgroup:= WreathProduct(SL(d div t, p), Sym(t));
  gens:= [subgroup.i : i in [1..Ngens(subgroup)]];
  newgens:= [];
  for i in [1..#gens] do
    det:= Determinant(gens[i]);
    assert ((det eq 1) or (det eq -1));
    if det eq 1 then
      Append(~newgens, GL(d, p)!gens[i]);
    else
      new_gen:=  gens[i]*GL(d, p)!DiagonalMatrix([-1]cat[1:i in[2..d]]);
      Append(~newgens, new_gen);
    end if;
  end for;
  subgroup:= sub<SL(d, p)|newgens>;
  z:= PrimitiveElement(GF(p));
  detmat:= DiagonalMatrix([z] cat [1 : i in [2..(d div t)]] cat [z^-1] cat
                   [1 : i in [(d div t)+2..d]]);
  return sub<SL(d, p)|subgroup, detmat>;
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
  xq := Modexp(x, q, pol);
  //cxp:= [Coefficients(x^s + x^(i*q) mod pol) : i in [1..s-1]];
  cxp:= [Coefficients(x^s + xq^i mod pol) : i in [1..s-1]];
  field_auto := GL(s, q)!Matrix(GF(q), s, s, [<1, 1, 1>] cat &cat[[<i+1,
                   j, cxp[i][j]>:i in [1..s-1] ] : j in [1..s]]);

  grp:= sub<GL(s, q)|mat, field_auto>;
  return grp;
end function;


/**********************************************************************/
//This uses previous function to produce GammaL(d/s, q^s) \leq GL(d, q)
//take singer cycle from gammal1(s, q). take gens from gl(d/s,
//p). make block matrices with singer as blocks inside gens from 
//gl. if entry is in GF(q) then have a block of identity. else
//take that power. make blocks with id as blocks inside field aut
//entries. 

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
  
/*
 * This final function returns only the part of the group which
 * intersects with SL.
 */

function GammaLMeetSL(d, q, s)  
  fac:= Factorisation(q);
  assert #fac eq 1;
  assert d mod s eq 0;
  if not IsPrime(s) then
    "warning: this function was designed for PRIME field extensions:";
    "results may be inaccurate";
  end if;
  
  dim:= d div s;

  gammal1:= GammaL1(s, q);
  singer:= gammal1.1;
  singer_inv:= singer^-1;
  singerSL:= singer^(q-1);
  frob:= d eq 2 and q mod 2 eq 1 select singer^((q-1) div 2)*gammal1.2
                                   else gammal1.2;
  //"determinant frob =", Determinant(frob);

  if dim eq 1 then return sub<GL(d, q)|singerSL, frob>; end if;

  gl2:= GL(dim, q^s).2;
  //"putting singer cycle as block into gens for SL(dim, q)";
  newmat1:= Matrix(GF(q), d, d,
                [<i, j, singer[i][j]> : i, j in [1..s]] cat [<i, i,
                1> : i in [s+1..d-1]] cat[<i + (d - s), j+(d-s), 
                singer_inv[i][j]> : i, j in [1..s] ] );
  newmat2:= Matrix(GF(q), d, d,
                &cat[[<k + i*s, k+ j*s, gl2[i+1][j+1]> : i, j in
                [0..(dim-1)]] : k in [1..s]]);   
  detmat:= Matrix(GF(q), d, d,
                [<i, j, singerSL[i][j]> : i, j in [1..s]] cat [<i, i,
                1> : i in [s+1..d]]);

  //"putting frobenius aut as block into gens for GL(dim, q)";
  newmat3:= Matrix(GF(q), d, d,
                &cat[[<i+k*s, j+k*s, frob[i][j]> : i, j in [1..s]]
                 : k in [0..dim-1]] );
  if IsEven(s) and IsOdd(dim) and IsOdd(q) then
    assert Determinant(frob) eq -1;
    fac:= Factorisation(q-1);
    two_part:= 2^fac[1][2];
    scal:= singer^((q-1) div 2);
    assert Determinant(scal) eq -1;
    newmat3:= DiagonalJoin([scal*frob: i in [1..dim]]);
  end if;

  grp:=  sub<SL(d, q)|newmat1, newmat2, newmat3, detmat>;
  assert IsSemiLinear(grp);
  return grp;
end function;

