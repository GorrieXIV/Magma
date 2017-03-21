freeze;

import  "psl2p.m": FindThreeElement;
import  "normes.m": NormaliserOfExtraSpecialGroupMinus;

/*
Constructively recognise and find maximal subgroups  of S(4,p).
Recognition by Derek Holt.
Maximals by Colva Roney-Dougal.
*/

SymplecticForm := function(G)

//G should be matrix group acting (absolutely?) irreducibly.
//Decide whether G preserves symplectic form.
  
local M, D, bool, mat;
M:=GModule(G);
if not IsAbsolutelyIrreducible(G) then
    "group is not absolutely irreducible";
end if;
D:=Dual(M);
bool, mat:= IsIsomorphic(M,D);
if bool then
    if mat eq -Transpose(mat) then
        return bool, mat;
    end if;
end if;
return false, _;
end function;


ListMatToQ:= function(a, q)
// raise every element of matrix A to q-th power. 
list:= Eltseq(a);
for i in [1..#list] do
    list[i]:= list[i]^q;
end for;
return list;
end function;

/**********************************************************************/

function ChangeMat(mat, type, d, p)
if type cmpeq "unitary" then
    return Transpose(GL(d, p^2)!ListMatToQ(mat, p));
else
    return Transpose(mat);
end if;
end function;



/**********************************************************************
 * GetCoords returns the column number in which row i of the form must 
 * be nonzero for conjugation.
 */

function GetCoords(i, d, q, type)
case type:
    when "unitary": return i;
    when "symplectic": return d-i+1;
    when "orth+": if IsOdd(q) then return i; else return d-i+1; end if;
    when "orth-": if IsOdd(q) then return i; else return d-i+1; end if;
    when "orth": if IsOdd(q) then return i; else return d-i+1; end if;
end case;
return 0;
end function;


/**********************************************************************
 * CorrectInTorus takes a (diagonal or antidiagonal) 
 * form matrix, and the type of form that
 * it is supposed to represent, and finds a conjugating element such
 * that the group will now preserve a form matrix consisting of all 
 * +1s and -1s.
 * In the case of an orthogonal form of type "oplus" it turns
 * everything into 1s and zs, where z is a primitive element of the
 * field. 
 * q is a prime power.
 */


function CorrectDiag(form, d, q, type)
if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
    return GL(d, q)!DiagonalMatrix([Root(form[i][i], p+1)^-1 : i in
                                        [1..d]]);
elif type cmpeq "symplectic" or IsEven(q) then 
    list:= [(form[i][d-i+1])^-1 : i in [1..Quotrem(d, 2)]];
    return GL(d, q)!DiagonalMatrix(list cat [GF(q)!1 : i in 
                                         [1..Quotrem(d, 2)]]); 
else
    z:= PrimitiveElement(GF(q));
    
    list:= [];
    nonsquares:= [];
    for i in [1..d] do
         a, b:= IsSquare(form[i][i]);
         if a then Append(~list, (b^-1));
         else a, b:= IsSquare(form[i][i]*(z^-1));
              Append(~list, (b^-1));
              Append(~nonsquares, i);
         end if;
    end for;
    mat1:= GL(d, q)!DiagonalMatrix(list);
    
    //"checking for nonsquare entries";
    ns:= #nonsquares;
    if ns eq 0 then
        return mat1;
    end if;
    
    if type eq "orth" and IsOdd(ns) then
         temp:= [x : x in [1..d] | not x in nonsquares];
         nonsquares:= temp;
         ns:= #nonsquares;
    end if;
         
    //"turning pairs of nonsquares into squares";
    x:= false; 
    while not x do
        b:= Random(GF(q));
        x, a:= IsSquare(z^-1 - b^2);
        if type cmpeq "orth" and x then
             a:= a^-1;
        end if;
    end while;         
    quot, rem:= Quotrem(ns, 2); 
    list:= [];
    //nonsquares;
    //mat1*form*Transpose(mat1);
    for i in [1..d] do
        if not i in nonsquares then
            Append(~list, <i, i, 1>);
        end if;
    end for;
    for i in [1..quot] do
         Append(~list, <nonsquares[2*i-1], nonsquares[2*i-1], a>);
         Append(~list, <nonsquares[2*i-1], nonsquares[2*i], b>);
         Append(~list, <nonsquares[2*i], nonsquares[2*i-1], b>);
         Append(~list, <nonsquares[2*i], nonsquares[2*i], -a>);
    end for;
    if rem eq 1 then 
        final:= nonsquares[ns];
        Append(~list, <nonsquares[ns], nonsquares[ns], 1>);
    end if;
    mat2:= GL(d, q)!Matrix(GF(q), d, d, list);
    //"after mat2 form is", mat2*mat1*form*Transpose(mat1)*Transpose(mat2);    

    //"moving final nonsquare entry to (d, d) position";
    mat3:= Identity(GL(d, q));
    if rem eq 1 then
        if not final eq d then
            newlist:= [<i, i, 1> : i in [1..d] | not i eq final and
        	    not i eq d] cat [<final, d, 1>, <d, final, 1>];
            mat3:= GL(d, q)!Matrix(GF(q), d, d, newlist);
        end if;
    end if;
    //"after mat3 form is";
    newform:= 
       mat3*mat2*mat1*form*Transpose(mat1)*Transpose(mat2)*Transpose(mat3); 
    //newform;

 //"converting matrix into 1s and primitives";
    list:= [];
    for i in [1..d] do
         a, b:= IsSquare(newform[i][i]);
         if a then Append(~list, (b^-1));
         else a, b:= IsSquare(newform[i][i]*(z^-1));
              Append(~list, (b^-1));
         end if;
    end for;
    mat4:= GL(d, q)!DiagonalMatrix(list);

    
    return mat4*mat3*mat2*mat1;

end if; 
end function;

/****************************************************************/

/*
 * This function returns a matrix that is the identity on the
 * first i rows and columns, and a random (invertible) matrix on 
 * the bottom d \times d block.
 * in the symplectic case, or orthogonals over even fields, 
 * it's the first rows and final columns that are zero.
 */

function GetRandomConj(i, d, q, type)
startelt:= Random(GL(d-i, q));
newelt:= DiagonalMatrix([GF(q)!1 : j in [1..d]]);
if type cmpeq "unitary" or (not (type cmpeq "symplectic") and IsOdd(q))
       then 
    for j in [1..d-i] do
        for k in [1..d-i] do
            newelt[i+j][i+k]:= startelt[j][k];
        end for;
    end for;
else
    for j in [1..d-i] do
        for k in [1..d-i] do
              newelt[i+j][k] := startelt[j][k];
        end for;
    end for;
end if;
return newelt;
end function;


/****************************************************************/

function GetConjMat(form, col, d, q, type)
conjmat:= DiagonalMatrix([GF(q)!1 : i in [1..d]]);
vec:= form[col];
if type cmpeq "unitary" or (not type cmpeq "symplectic"  and IsOdd(q))
         then
    for i in [(col+1)..d] do
         conjmat[i][col]:= -form[i][col]*(form[col][col]^-1);
    end for;
elif type cmpeq "symplectic" or IsEven(q) then
    for i in [1..(d-col)]cat[(d-col+2)..d] do
         conjmat[i][d-col+1]:= -form[i][col]*(form[d-col+1][col]^-1);
    end for;
end if;
return GL(d, q)!conjmat;
end function;    


/***********************************************************************/
/*
 * finds a matrix that will conjugate group1 (preserving form1) to 
 * group2 (preserving form2). group1 and group2 are not currently 
 * used by the function, but have been left in for testing purposes.
 * q is a prime power. 
 */

function ChangeForm(form1, form2, d, q, type, group1, group2)
//"at beginning of ChangeForm, form1 is", form1:Magma;
//"At beginning of ChangeForm, form2 is", form2:Magma;
//"type is", type;

if type cmpeq "unitary" then
    bool, p:= IsSquare(q);
else
    p:= q;
end if;

conj1:= Identity(GL(d, q));
conj2:= Identity(GL(d, q));
for i in [1..d-1] do
   /* First we have to deal with the problem that the relevant matrix
    * entry (entry [coords][i]) may be zero.
    * In the unitary case this is entry [i][i].
    * In the symplectic case it's entry [d-i+1][i].
    * In orth+ case it's also [d-i+1][i]. We also need [i][i] to be zero.
    */

   temp1:= form1;
   temp2:= form2;
   mat1:= Identity(GL(d, q));
   mat2:= Identity(GL(d, q));
   coords:= GetCoords(i, d, q, type);
   if type cmpeq "unitary" or type cmpeq "symplectic" or type cmpeq
              "orth+" or type cmpeq "orth-"  or type eq "orth" then
       while temp1[coords][i] eq 0 do
           mat1:= GetRandomConj(i-1, d, q, type);
           //"mat1 is", mat1;
           temp1:= mat1*form1*ChangeMat(mat1, type, d, p);
           //"at step ", i, "temp1 is ", temp1;
       end while;
   end if;     
   form1:= temp1;
   //"after removing zeros, form1 is", form1;
   conj1:= mat1*conj1;
   if type cmpeq "unitary" or type cmpeq "symplectic" or type cmpeq
   "orth+" or type cmpeq "orth-" or type cmpeq "orth" then
       while temp2[coords][i] eq 0 do
           mat2:= GetRandomConj(i-1, d, q, type);
           temp2:= mat2*form2*ChangeMat(mat2, type, d, p);
           //"temp2 is ", temp2;
       end while;
   end if;
   form2:= temp2;
   //"after removing zeros, form2 is", form2:Magma;
   conj2:= mat2*conj2;
     
   /* So by this stage the relevant entry is guaranteed to be nonzero 
    */

   conjmat1:= GetConjMat(form1, i, d, q, type);
   conjmat2:= GetConjMat(form2, i, d, q, type);
   form1:= conjmat1*form1*ChangeMat(conjmat1, type, d, p);
   form2:= conjmat2*form2*ChangeMat(conjmat2, type, d, p);
   conj1:= conjmat1*conj1;
   conj2:= conjmat2*conj2;
   
   //"conjmat1 = ", conjmat1;
   //"conjmat2 = ", conjmat2;
   //"form1 after step", i, "is ", form1;
   //"form2 after step", i, "is ", form2;
end for;

/* By now the matrix should either be diagonal or antidiagonal.
 */
 
if type cmpeq "unitary" or (IsOdd(q) and (type cmpeq "orth+" or type
    cmpeq "orth-" or type cmpeq "orth")) then
    assert IsDiagonal(form1);
    assert IsDiagonal(form2);
elif type cmpeq "symplectic" or IsEven(q) then
    for i in [1..d] do
        for j in [1..d] do
             if not i eq (d - j +1) then
                  assert form1[i][j] eq 0;
                  assert form2[i][j] eq 0;
             end if;
        end for;
    end for;
end if;

//"before conj_torus, form1 is", form1;
//"before conj_torus, form2 is", form2;
conj_torus1:= CorrectDiag(form1, d, p, type);
conj_torus2:= CorrectDiag(form2, d, p, type);

//"conj_torus1 is", conj_torus1;
//"conj_torus2 is", conj_torus2;

form1:= conj_torus1*form1*ChangeMat(conj_torus1, type, d, p);
form2:= conj_torus2*form2*ChangeMat(conj_torus2, type, d, p);

conj1:= conj_torus1*conj1;
conj2:= conj_torus2*conj2;

/* conj1 maps group preserving form1 to the group preserving
 * identity (in unitary case) or AntiDiag([1..1-1..-1]) (in symplectic
 * case). conj2 does the same to the group preserving form2.
 * so conj2(-1)conj1 should map group preserving form1 to group
 * preserving form2.
 */

return (conj1^-1)*conj2;

end function;

//tested on primes up to about 100.

//REQUIRE P>3.

//point stab isomorphic to p^3:(p-1) \times Sp(2, p).
function GetPointStab(p)
    z:= PrimitiveElement(GF(p));
    
    //act as scalar on stabilised point [1, 0, 0, 0]
    a:= GL(4, p)!DiagonalMatrix([z, 1, 1, z^-1]);
    
    //Sp(2, q) on <[0, 1, 0, 0], [0, 0, 1, 0]>
    b:= GL(4, p)![1, 0, 0, 0,
                  0, z, 0, 0, 
                  0, 0, z^-1, 0,
                  0, 0, 0, 1];
    c:= GL(4, p)![1, 0, 0, 0,
                  0, -1, 1, 0,
                  0, -1, 0, 0,
                  0, 0, 0, 1];
    
    //and the p-gunk, fixed so preserves symplectic form.
    d:= GL(4, p)![1, 0, 0, 0,
                  1, 1, 0, 0,
                  0, 0, 1, 0,
                  0, 0, -1, 1];
    e:= GL(4, p)![1, 0, 0, 0,
                  0, 1, 0, 0,
                  1, 0, 1, 0,
                  0, 1, 0, 1];
    f:= GL(4, p)! [1, 0, 0, 0,
                   0, 1, 0, 0,
                   0, 0, 1, 0,
                   1, 0, 0, 1];
    return sub<GL(4, p)|a, b, c, d, e, f>;
end function;

//line stab isomorphic to p^3:GL(2, p). Stabilise a totally isotropic
//2-space. <[1, 0, 0,0], [0, 1, 0, 0]>
function GetLineStab(p);
    z:= PrimitiveElement(GF(p));
    //torus
    a:= DiagonalMatrix([z, 1, 1, z^-1]);
    b:= DiagonalMatrix([1, z, z^-1, 1]);
    //p-gunk.
    c:= GL(4, p)![1, 0, 0, 0, 
                  0, 1, 0, 0,
                  1, 0, 1, 0,
                  0, 1, 0, 1];
    d:= GL(4, p)![1, 0, 0, 0,
                  0, 1, 0, 0,
                  0, 1, 1, 0,
                  0, 0, 0, 1];
    e:= GL(4, p)![1, 0, 0, 0,
                  0, 1, 0, 0,
                  0, 0, 1, 0,
                  1, 0, 0, 1];
    //remaining required generator for GL (this+torus=gl); 
    f:= GL(4, p)![-1, 1, 0, 0, 
                  -1, 0, 0, 0,
                   0, 0, -1, -1,
                   0, 0, 1, 0];
    return sub<GL(4, p)|a, b, c, d, e, f>;
end function; 

function GetReducibles(p)
    assert p gt 3 and IsPrime(p);
    return GetPointStab(p), GetLineStab(p);
end function;

/*
 * To make the 2nd group we use the fact that
 * GL(2, q) = <Diag[gamma, 1], [-1, 1, -1, 0]>;
 * idea is to act as gens of gl on (e1, e2) and compensate on f1, f2, 
 * or swap the subspaces over. 
 */

function GetImprims(q)
    gamma:= PrimitiveElement(GF(q));
    e:= GF(q)!1;

    g:= WreathProduct(Sp(2, q), Sym(2));
    bool, form:= SymplecticForm(g);
    //"form_g = ", form;
    standard_form:= GL(4, q)![0, 0, 0, e, 
                          0, 0, e, 0, 
                          0, -e, 0, 0, 
                         -e, 0, 0, 0];  
    x:= GL(4, q)!ChangeForm(form, 
         standard_form, 4, q, "symplectic", g, Sp(4, q));
    imprim1:= g^x;

    
    newmat1:= GL(4, q)!DiagonalMatrix([gamma, e, e, gamma^-1]);
    newmat2:= GL(4, q)![-e, e, 0, 0,
                    -e, 0, 0, 0, 
                     0, 0, -e, -e,
                     0, 0, e, 0];
    newmat3:= GL(4, q)![0, 0, -e, 0,
                    0, 0, 0, -e,
                    e, 0, 0, 0,   
                    0, e, 0, 0];

    imprim2:= sub<GL(4, q)|newmat1, newmat2, newmat3>;

    return imprim1, imprim2;
end function;

//This produces GammaL(1, p^s) \leq GL(s, p)

function GammaL1(s, p)

    //"making singer cycle for GL(1, p^s) in GL(s, p)";
    pol:= DefiningPolynomial(GF(p^s));
    x:= Parent(pol).1;
    coeffs:= Coefficients(pol);
    mat:= GL(s, p)!Matrix(GF(p), s, s, [<i, i+1, 1>: i in [1..s-1]] cat 
                                   [<s, i, -coeffs[i]>: i in [1..s]]);

/* 
 * find field automorphism - the reason that x^s has been added to the
 * argument below is to ensured that cxp[i] and cxp2[i] are always defined!
 * The basis of the field is [1, x, x^2, \ldots, x^(s-1)]
 */

    cxp:= [Coefficients(x^s + x^(i*p) mod pol) : i in [1..s-1]];

    field_auto := GL(s, p)!Matrix(GF(p), s, s, [<1, 1, 1>] cat &cat[[<i+1,
                          j, cxp[i][j]>:i in [1..s-1] ] : j in [1..s]]);


    grp:= sub<GL(s, p)|mat, field_auto>;
    return grp;

end function;


/* This uses previous function to produce Sp(d/2, p^2).2 \leq Sp(d, p)
 * take singer cycle from gammal1(s, p). use known generators for
 * Sp(d/2, p^2).  make block matrices with singer as blocks inside gens from 
 * gl. 
 */

/* We use the fact that Sp(d, q).1 = DiagonalMatrix([z, 1, \ldots,
 * z^-1]), where z is a primitive element of GF(q), and that entries
 * of Sp(d, q).2 all lie in the base field. 
 */

/******************************************************************/
function GammaSpMeetSp(d, s, p)
 
    assert d mod s eq 0;

    dim:= d div s;
    assert IsEven(dim);

    gammal1:= GammaL1(s, p);
    g1:= gammal1.1;
    o:= Order(Determinant(g1));

    gens1:= g1^o;
    gens1_inv:= gens1^-1;
    gens2:= gammal1.2;

    gens4:= Sp(dim, p^s).2;


// "putting singer cycle as block into gens for GL(dim, p)";
 
    newmat1:= Matrix(GF(p), d, d,
                [<i, j, gens1[i][j]> : i, j in [1..s]] cat [<i, i,
                GF(p)!1> : i in [s+1..(d-s)]] cat
                [<i+d-s, j+d-s, gens1_inv[i][j]> : i, j in [1..s]]);
    newmat2:= Matrix(GF(p), d, d,
                &cat[[<k + i*s, k+ j*s, gens4[i+1][j+1]> : i, j in
                [0..s-1]] : k in [1..dim]]);

// "putting frobenius aut as block into gens for GL(dim, p)";

    newmat3:= Matrix(GF(p), d, d,
                &cat[[<i+k*s, j+k*s, gens2[i][j]> : i, j in [1..s]]
                 : k in [0..dim-1]] );

    return sub<GL(d, p)|newmat1, newmat2, newmat3>;
end function;

/*******************************************************************/

/*
 * This makes GU(d/2, p).2 \leq Sp(d, p).
 * we take the description of generators for GU from Don's paper -
 * "Pairs of generators for Matrix groups, I".
 * Submatrices are named accordingly.
 */

function GammaUMeetSp(d, p)

    half:= d div 2;

    gammal1:= GammaL1(2, p);
    epsilon:= gammal1.1;

/* 
 * to be substitued into first generator of GU;
 */

  epsilon_conj_inv:= epsilon^(-p);


/*
 * to be substituted into second generatror of GU if half is even;
 */

    if half eq 2 then
        beta:= epsilon^((p+1) div 2);
        minus_beta_inv:= -(beta^-1);
    elif IsEven(half) then
        power:= epsilon^(p-1);
        temp:= GL(2, p)![power[1][1]+1, power[1][2], power[2][1],
                         power[2][2]+1]^-1;
        beta:= -temp;
    end if;    

/*
 * to be substituted into second generator of GU if half is odd.
 */
    
    if not IsEven(half) then
        nu:= epsilon^((p+1) div 2);
        nu_inv:= nu^(-1);
        minus_nu_inv:= -(nu^(-1));
    end if;

/*
 * putting powers of the singer cycle as blocks into the 
 * generators for GU(half, p);
 */

    if half eq 2 then
        newmat1:= GL(4, p)![epsilon[1][1], epsilon[1][2], 0, 0,
                        epsilon[2][1], epsilon[2][2], 0, 0,
                        0, 0, epsilon_conj_inv[1][1], epsilon_conj_inv[1][2],
                        0, 0, epsilon_conj_inv[2][1], epsilon_conj_inv[2][2]];
        newmat2:= GL(4, p)!
                [ -1,   0, beta[1][1], beta[1][2],
                   0,  -1, beta[2][1], beta[2][2],
                 minus_beta_inv[1][1], minus_beta_inv[1][2], 0, 0,
                 minus_beta_inv[2][1], minus_beta_inv[2][2], 0, 0];
    
    elif half eq 4 then 
        newmat1:= Matrix(GF(p), 8, 8,
                [<i, j, epsilon[i][j]> : i, j in [1,2]] cat
                [<i, i, 1> : i in [3..6]] cat
                [<6+i, 6+j, epsilon_conj_inv[i][j]> : i, j in [1..2]]);
        newmat2:= Matrix(GF(p), 8, 8, 
                &cat[[<i+s, i, 1> : i in [1, 2]]: s in [0,2]] cat
                [<i, j+4, nu[i][j]> : i,j in [1, 2]] cat
                [<i+4, j+2, nu_inv[i][j]> : i, j in [1,2]] cat
                [<i+4, i+6, 1> : i in [1,2]] cat 
                [<i+6, j+2, minus_nu_inv[i][j]> : i, j in [1,2]]); 
    
    elif IsOdd(half) then
        newmat1:= Matrix(GF(p), d, d,
                [<i + half-3, j+half-3, epsilon[i][j]> : i, j in [1, 2]] 
                cat [<i, i, GF(p)!1> : i in [1..(half-3)] cat [half,
                                       half+1] cat [half+4..d]] cat
                [<i+half+1, j+half+1, epsilon_conj_inv[i][j]> : i, j in
		[1, 2]]);
        newmat2_list:= [<i, i+2, 1> : i in [1..half-3]] cat
               [<half -2, d-1, 1>, <half-1, d, 1>, <half+2, 1, 1>,
                <half +3, 2, 1>, <half-2, half, -1>, <half-1, half+1,
                -1>, <half, half, -1>, <half+1, half+1, -1>, <half, 1,
                -1>, <half+1, 2, -1>] cat
               [<i, i-2, 1> : i in [half+4..d]] cat
               [<half-3+i, j, beta[i][j]> : i, j in [1, 2]];
        newmat2:= Matrix(GF(p), d, d, newmat2_list);

    else //half is even and > 4.
        newmat1:= Matrix(GF(p), d, d,
                [<i, j, epsilon[i][j]> : i, j in [1, 2]] cat [<i, i,
                GF(p)!1> : i in [3..(d-2)]] cat
                [<i+d-2, j+d-2, epsilon_conj_inv[i][j]> : i, j in
		[1, 2]]);
        newmat2:= Matrix(GF(p), d, d,
               [<1, 1, GF(p)!1>, <2, 2, GF(p)!1>] cat
               [<i, i-2, GF(p)!1> : i in [3..half]] cat
               [<i, i+2, GF(p)!1> : i in [(half+1)..d-2]] cat
               [<i, j+half, nu[i][j]> : i, j in [1,2]] cat
               [<i + d-4, j+half-2, nu_inv[i][j]>: i, j in [1,2]] cat
               [<i+d-2, j+half-2, minus_nu_inv[i][j]> : i, j in [1,2]]);
    end if;


/*
 * Now we substitute the (2 \times 2) matrix representing the
 * frobenius automorphism as blocks down the diagonal, and then
 * multiply it by the matrix representing a 2-power scalar in GL(2,
 * p^2)\setminusGU(2, p) whose square lies in GU(2, p).
 */

    frob_aut:= gammal1.2;

/*
 * "putting frobenius aut as block into identity matris";
 */

    frobmat1:= Matrix(GF(p), d, d,
                &cat[[<i+k*2, j+k*2, frob_aut[i][j]> : i, j in [1..2]]
                 : k in [0..half-1]] );

/*
 * "finding highest 2-power order of a scalar in GU(2, p)";
 */
    two_power:= 1;
    temp:= p+1;
    while IsEven(temp) do
	temp:= temp div 2;
	two_power:= two_power*2;
    end while;

/*
 * "finding a scalar in GL(2, p^2) of twice this order2-power order";
 */

    power:= (p^2 - 1) div (two_power*2);
    gens1_power4:= epsilon^power;
    frobmat2:= Matrix(GF(p), d, d,
                &cat[[<i+k*2, j+k*2, gens1_power4[i][j]>: i, j in
		[1..2]] : k in [0..half-1]]);

/*
 * the product is now our third generator.
 */
    newmat3:= frobmat1*frobmat2;

    //"newmat1="; GL(d, p)!newmat1;
    //"newmat2="; GL(d, p)!newmat2;
    //"newmat3="; GL(d, p)!newmat3;
    return sub<GL(d, p)|newmat1, newmat2, newmat3>;
end function;


/*******************************************************************/

/*
 * and now the main function for Sp(4, p). This has maximal subgroups 
 * Sp(2, p^2).2 and GU(2, p).2
 */

function GetSemilins(p)
    assert IsPrime(p);
    standard_form:= GL(4, p)![0, 0, 0, 1, 
                          0, 0, 1, 0, 
                          0, -1, 0, 0, 
                         -1, 0, 0, 0];  

    g1:= GammaSpMeetSp(4, 2, p);
    bool, form:= SymplecticForm(g1);
    assert bool;
    x:= GL(4, p)!ChangeForm(form, standard_form, 4, p, 
                                     "symplectic", g1, Sp(4, p));
    semilin1:= g1^x;


    g2:= GammaUMeetSp(4, p);
    bool, form:= SymplecticForm(g2);
    assert bool;
    x:= GL(4, p)!ChangeForm(form, standard_form, 4, p, 
                                     "symplectic", g2, Sp(4, p));
    semilin2:= g2^x;

    return semilin1, semilin2;

end function;

function GetExtraSpec(p)

    group:= NormaliserOfExtraSpecialGroupMinus(4, p);
    dergroup:= DerivedSubgroup(group);

    if p mod 8 eq 1 or p mod 8 eq 7 then
         power_two:= 1;
         power_odd:= p-1;
         while IsEven(power_odd) do
             power_two:= 2*power_two;
             power_odd:= power_odd div 2;
         end while;
         newgens:= [x^(power_odd): x in Generators(group)];
         tripgens:= [x^Order(Determinant(x)): x in newgens];
         newgroup:= sub<GL(4, p)|dergroup, tripgens>;
         //"group ="; ChiefFactors(group);
         //"newgroup ="; ChiefFactors(newgroup);
    else
         newgroup:= dergroup;
    end if;


    // The derived subgroup is guaranteed to preserve a form; newgroup
    // may be too big if p mod 8 eq 1.
    bool, form1:= SymplecticForm(dergroup);
    assert bool;
    form2:= GL(4, p)![0, 0, 0, 1,
             0, 0, 1, 0,
             0, -1, 0,0,
             -1, 0, 0,0];
    x:= GL(4, p)!ChangeForm(form1, form2, 4, p, "symplectic", dergroup,
                   Sp(4, p));
    overgroup:= newgroup^x;
    newder:= dergroup^x;

    if ((p mod 8 eq 3) or (p mod 8 eq 5) or (p mod 8 eq 7) or
                SymplecticForm(overgroup)) then 
        return overgroup; 
    end if;

 /* 
  * we are now in the situation where we have a subgroup of SL that
  * is twice as big as what we want. we need to find an element that
  * does *not* lie in the derived subgroup (which is of index 4) but
  * *does* lie in this subgroup (index 2).
  */
    found:= false;
    runs:= 0;
    while not found do
        x:= Random(overgroup);
        if not (x in newder) then
             fullgroup:= sub<GL(4, p)|newder, x>;
             if SymplecticForm(fullgroup) then
                 found:= true;
             end if;
        end if;
        //"runs =", runs;
        runs:= runs+1;
    end while;
    return fullgroup;
end function;

//tested on i in [5..1000]

function GetL2p(p)
    g:= SL(2, p);
    module:= GModule(g);	
    power:= TensorPower(module, 3);
    indecs:= IndecomposableSummands(power);
    assert exists(newmod){x: x in indecs | Dimension(x) eq 4};
    group:= sub<GL(4, p)|ActionGenerators(newmod)>;

    bool, form1:= SymplecticForm(group);
    assert bool;
    form2:= GL(4, p)![0, 0, 0, 1,
             0, 0, 1, 0,
             0, -1, 0,0,
             -1, 0, 0,0];
    x:= GL(4, p)!ChangeForm(form1, form2, 4, p, "symplectic", group,
                   Sp(4, p));
    newgroup:= group^x;

    return newgroup;
end function;

/* This function makes a matrix group isomorphic to 2.Sym(6) 
 * whenever 3 is square in GF(p). Tested on all suitable p in range 
 * [10..1000];
 */ 

function GetSym6(p)

assert IsPrime(p);

M:= GModule(PermutationGroup<80 |  
    \[ 1, 5, 3, 8, 2, 13, 11, 4, 16, 17, 7, 21, 6, 24, 22, 9, 
    10, 30, 28, 31, 12, 15, 34, 14, 38, 27, 26, 19, 42, 18, 20, 
    45, 33, 23, 52, 50, 54, 25, 58, 59, 60, 29, 64, 65, 32, 46, 
    68, 69, 67, 36, 62, 35, 71, 37, 72, 73, 66, 39, 40, 41, 77, 
    51, 76, 43, 44, 57, 49, 47, 48, 80, 53, 55, 56, 74, 75, 63, 
    61, 78, 79, 70 ],
    \[ 2, 6, 7, 1, 10, 9, 14, 3, 4, 18, 19, 5, 23, 15, 8, 20, 
    27, 22, 26, 11, 32, 12, 35, 36, 13, 16, 40, 30, 17, 44, 45, 
    47, 21, 49, 39, 53, 24, 56, 25, 43, 28, 62, 29, 61, 66, 31, 
    48, 33, 68, 69, 34, 70, 55, 51, 37, 50, 38, 71, 75, 73, 41, 
    65, 42, 79, 78, 67, 46, 54, 57, 64, 80, 52, 59, 58, 76, 60, 
    74, 63, 72, 77 ]
        /* order = 1440 = 2^5 * 3^2 * 5 */ >, [ 
MatrixAlgebra(IntegerRing(), 16) |
\[ 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 
-1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
0, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 
0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 
1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 
0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, -1, 2, 1, 0, 0, 0, 0, 0, 0, 
0, -1, 0, -1, -1, 0, 0 ],
\[ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 3, 1, 1, 0, 0, 0, 0, 0, 
0, -1, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1,
-1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 
0, 0, 0, -1, 0, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 
0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0,
0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 
0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
0, -1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 
0, 0, 0, 0, 0, 0, 1, -1 ]]);

comp_factors:= CompositionFactors(ChangeRing(M, GF(p)));
if not #comp_factors eq 4 then
    "unable to decompose module";
    return false, _;
end if;

grp:= MatrixGroup<4, GF(p)|ActionGenerators(comp_factors[1])>;
bool, form1:= SymplecticForm(grp);
assert bool;
form2:= GL(4, p)![0, 0, 0, 1,
                 0, 0, 1, 0,
                0, -1, 0,0,
               -1, 0, 0,0];
x:= GL(4, p)!ChangeForm(form1, form2, 4, p, "symplectic", grp,
                   Sp(4, p));
return true, grp^x;
end function;


/*****************************************************************/

/*
 * The following function finds the 4 dimensional symplectic
 * representation of 2.Alt6 that is maximal whenever 2.Sym6 doesn't
 * exist. 
 */

function GetAltSix(p)

assert IsPrime(p);

M:= GModule(PermutationGroup<80 |  
    \[ 49, 30, 69, 12, 24, 65, 27, 20, 21, 62, 13, 41, 70, 59, 
    31, 1, 6, 66, 73, 29, 25, 3, 60, 80, 10, 47, 72, 14, 56, 58,
    37, 22, 8, 7, 68, 42, 19, 28, 45, 63, 51, 26, 5, 76, 16, 4, 
    71, 50, 55, 2, 33, 36, 57, 17, 32, 46, 74, 67, 77, 18, 11, 
    15, 35, 38, 64, 52, 34, 79, 39, 75, 23, 48, 9, 40, 43, 53, 
    54, 61, 44, 78 ],
    \[ 38, 53, 54, 36, 11, 4, 35, 23, 15, 79, 5, 10, 1, 8, 9, 
    58, 32, 33, 74, 19, 30, 72, 6, 3, 56, 46, 80, 45, 41, 70, 
    27, 61, 64, 73, 68, 14, 51, 24, 42, 47, 29, 49, 17, 66, 43, 
    77, 71, 16, 55, 62, 76, 40, 57, 13, 60, 63, 7, 67, 65, 69, 
    28, 78, 37, 26, 59, 52, 22, 2, 39, 31, 44, 48, 75, 12, 50, 
    25, 18, 34, 20, 21 ]
        /* order = 720 = 2^4 * 3^2 * 5 */ >, [ 
MatrixAlgebra(IntegerRing(), 16) |
\[ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 2, -3, -1, 
-1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 2, 0, 1, 0, 0, 0, 0,
0, 0, -1, 0, 1, 0, 0, 0, -2, 4, 2, 1, 0, 0, 0, 0, 0, 0, -1, -1, 
0, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 
0, 0, 0, 0, 1, -1, -1, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 
-1, 1, 0, 1, 1, -2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, -1, 
-1, 2, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1, -1, 0, -1, 0, 2, 0, 0,
0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, -2, -1, 2, 0, 0, 0, 0, -1, -1,
1, -2, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, -3, -1, 0, 
0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1, 2, 0, 1, 0, 0, 0, 0, 0, 
0, 0, 0, 1, 0, 0, 0, 1, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
0, 1, 0, 1, -1, -1, 1, 0, 0, 0, 0, -1, 0 ],
\[ 1, -3, -1, -1, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, -1, 1, 0,
0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
0, 0, 0, 1, -1, 1, 1, 0, 0, 2, -3, -1, -1, 0, 0, 0, 0, 0, 0, 1, 
1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 1, -2, 0, 0, 0, 0, 1, 
1, 0, 0, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
1, 0, 0, -2, -1, 2, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, -1, -1, 
1, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 0, -1, 0, 
0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 
0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, 0, -1, 1, 0, 0, 
0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1, -2, 0, 0, 0, 0, 0, 0, 
0, 0, 1, 0, 0, 1, 0, 0, -2, 3, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 
0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 1, 0, 0, 0, 0, -2, 0, 
0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ]]);


comp_factors:= CompositionFactors(ChangeRing(M, GF(p)));
if not #comp_factors eq 4 then
    "unable to decompose module";
    return false, _;
end if;

grp:= MatrixGroup<4, GF(p)|ActionGenerators(comp_factors[1])>;
bool, form1:= SymplecticForm(grp);
assert bool;
form2:= GL(4, p)![0, 0, 0, 1,
             0, 0, 1, 0,
             0, -1, 0,0,
             -1, 0, 0,0];
x:= GL(4, p)!ChangeForm(form1, form2, 4, p, "symplectic", grp,
                   Sp(4, p));
return true, grp^x;
end function;

/*******************************************************************/

/*
 * main function. tested on 5 \leq p \leq 1000.
 */

function GetAlt6(p)

if p mod 12 eq 1 or p mod 12 eq 11 then
     bool, grp:= GetSym6(p);
     if not bool then
         "error making sym 6";
         return 0;
     end if;
     return grp;
elif p mod 12 eq 5 or p mod 12 eq 7 then
     bool, grp:= GetAltSix(p);
     if not bool then
         "error making alt 6";
         return 0;
     end if;
     return grp;
else
    "incorrectly called get alt6";
    return 0; 
end if;
 
end function;    

/*******************************************************************
*                   The main function                              *
********************************************************************/

forward MakeSpHomomGeneral;
function Sp4pMaximals(group, p : max:= true, Print:=0)

    //out eq  2;
    assert IsPrime(p);
    assert p gt 3;
    
    if Print gt 1 then "Making standard sp.2"; end if;
    sp:= Sp(4, p);
    w := PrimitiveElement(GF(p));
    gsp:= sub< GL(4,p) | sp.1, sp.2, DiagonalMatrix(GF(p),[w,w,1,1]) >;
    factor, pgsp:= OrbitAction(gsp, Orbit(gsp, sub<RSpace(gsp)|[1,0,0,0]>));
    
    psp:= sp@factor;
    AssertAttribute(psp, "Order", #PSp(4, p));
    
    conj_invol := pgsp.3;
    
    o:= #group;
    IsPSp := o eq #psp;
    //dgroup :=  DerivedSubgroup(group);
    
    if Print gt 1 then "Setting up homomorphism"; end if;
    homom, soc, group:=
      MakeSpHomomGeneral(group, 4, p, 1, psp, pgsp, factor : Print:=0);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psp | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

    //homom, F, phi:= MakeHomom(dgroup, group, p, psp, pgsp:Print:=Print);
    dh := Domain(homom);
    pgsp := sub<pgsp | homom(dh.1), homom(dh.2), conj_invol >;
    AssertAttribute(pgsp, "Order", #psp * 2);
    
    maximals:=[];
    if not max then
      return homom, pgsp, maximals, F, phi;
    end if;

/*
 * Reducibles. We need the stabiliser of a point and of a totally
 * isotropic subspace <e_1, e_2>.
 */

    if Print gt 1 then print "Getting reducibles"; end if;
    a, b:= GetReducibles(p);
    Append(~maximals, a@factor);
    Append(~maximals, b@factor);

/* 
 * There are two maximal imprimitives - one is sp(2, p) \wreath 2; the
 * other is GL(2, p).2., where we act freely as GL on <e_1, e_2> and
 * then correct as required by the form on <f_1, f_2>.
 */

    if Print gt 1 then print "Getting imprimitives"; end if;
    a, b:= GetImprims(p);
    Append(~maximals, a@factor);
    Append(~maximals, b@factor);

/*
 * There are two maximal semilinears. Sp(2, p^2).2 and GU(2, p).2,
 * where in the symplectic case the .2 is simply a field automorphism,
 * and in the unitary case the .2 is field aut*scalar from GL(2, p^2)
 * of 2-power order that squares into GU(2, p).
 */

    if Print gt 1 then print "Getting semilinears"; end if;
    a, b:= GetSemilins(p);
    Append(~maximals, a@factor);
    Append(~maximals, b@factor);

/*
 * Now the extraspecials - if p mod 8 = 1 or -1 and we're in case 
 * IsPSp then there are 2 conjugacy classes of
 * extraspecials. If p mod 8 eq 1 or -1 and we're not in case IsPSp
 * then there are no extraspecials. 
 */

    if Print gt 1 then print "Getting extraspecs"; end if;
    a:= GetExtraSpec(p);
    if p mod 8 eq 3 or p mod 8 eq 5 then
        Append(~maximals, a@factor);
    elif IsPSp then
        Append(~maximals, a@factor);
        Append(~maximals, (a@factor)^conj_invol);
    end if;

/*
 * There is a maximal C_9 subgroup isomorphic to PSL(2, p) whenever
 * p \geq 7. 
  */

    if p gt 7 or (p eq 7 and not IsPSp) then
        if Print gt 1 then print "Getting L(2, p)"; end if;
        a:= GetL2p(p);
        Append(~maximals, a@factor);
    end if;


/*
 * There is a maximal C_9 subgroup isomorphic to Alt(6) when p = \pm 5
 * mod 12. There is a pair of maximal C_9 subgroups isomorphic to
 * Sym(6) when p = \pm 1 mod 12. 
 */

    if (p mod 12 eq 1 or p mod 12 eq 11) and IsPSp then
        if Print gt 1 then print "Getting Sym(6)"; end if;
        a:= GetAlt6(p);
        Append(~maximals, a@factor);
        Append(~maximals, (a@factor)^conj_invol);
    elif (p mod 12 eq 5 or p mod 12 eq 7) and p ne 7 then
        if Print gt 1 then print "Getting Alt(6)"; end if;
        a:= GetAlt6(p);
        Append(~maximals, a@factor);
    end if;


//only for p=7.

    if p eq 7 then
        if Print gt 1 then print "Getting Alt(7)"; end if;
        alt_7:= MatrixGroup<4, GF(7) |
           \[ 0, 0, 2, 1, 3, 2, 1, 2, 0, 0, 4, 0, 6, 0, 4, 6 ],
           \[ 0, 3, 1, 2, 0, 6, 2, 1, 5, 1, 6, 5, 4, 2, 6, 1 ]
                  /* order = 5040 = 2^4 * 3^2 * 5 * 7 */ >;
        Append(~maximals, alt_7@factor);
    end if;

    
    if Print gt 1 then print "Found maximals in standard copy"; end if;
    
    return homom, pgsp, maximals, F, phi;
end function;

function PSp4pIdentify(group, p: max:=true, Print:=0)
    assert p gt 3;
    return Sp4pMaximals(group, p: max:=max, Print:=Print);
end function;


/* This function uses the black-box Sp recognition code to set up an
 * isomorphism between an unknown group isomorphic to PSp(d,p^e) and
 * the standard copy - curerently it only works for odd p.
 * Input parameters:
 * group is the almost simple group, where it is  known that
 * Socle(group) ~= PSp(d,p^e).
 * psp < apsp where apsp is the standard copy of Aut(PSp(d,p^e)).
 * factor is a homomorphism from the standard copy of GSp(d,p^e) to apsp.
 * homom, socle and group are returned, where group is the same
 * group but with generators redefined to make those of socle come first.
 * group is
 */
// the Black-Box constructive recognition code.
MakeSpHomomGeneral := function(group, d, p, e, psp, apsp, factor : Print:=0)
  local works, GtoSp, SptoG, mat, homom, ims,
    g, newgens, subsoc, subgp, pspgens, imgens, CG, ce, isc, h, socle;

  soc := Socle(group);
  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */

  repeat
    newgens := [ group | Random(soc), Random(soc) ];
    subsoc := sub<soc|newgens>; RandomSchreier(subsoc);
  until subsoc eq soc;
  soc := subsoc;
  subgp := subsoc;
  for g in Generators(group) do
   if not g in subgp then Append(~newgens,g);
   subgp := sub< group | newgens >; RandomSchreier(subgp);
   end if;
  end for;
  group := subgp;

  works := false;
  if d eq 4 then
    //use Eamonn's new function
    while not works do works, GtoSp, SptoG := RecogniseSp4(soc,p^e);
    end while;
  else
    while not works do works, GtoSp, SptoG := RecogniseSpOdd(soc,d,p^e);
    end while;
  end if;

  pspgens := [];
  for  i in [1..Ngens(soc)] do
      mat := GtoSp(soc.i);
      Append(~pspgens,mat@factor);
    end for;
    //Now identify images of all generators of group in apsp.
    ims := pspgens;
    for i in [Ngens(soc)+1..Ngens(group)] do
      g := group.i;
      CG := apsp; ce := Id(apsp);
      for j in [1.. #pspgens] do
        mat := GtoSp(soc.j^g);
        isc, h := IsConjugate(CG,pspgens[j]^ce,mat@factor);
        if not isc then error "Conjugation error in Aut(PSp(d,q))"; end if;
        CG := Centraliser(CG,mat@factor);
        ce := ce*h;
      end for;
      Append(~ims,ce);
    end for;
  return hom< group -> apsp | ims >, soc, group;
end function;
