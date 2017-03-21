freeze;
 
/*
 * This the implemention of  the algorithm described in Derek's
 * email, combined with my own algorithm for the final (2 \times 2)
 * block.
 * The algorithm reduces a quadratic form to the standard one, over
 * GF(2^m) for some m.
 */

function Iden(d, q)
return GL(d, q).0;
end function;

/*****************************************************************/

/*
 * This takes a quadratic form $F$ and a conjugating matrix $C$ and
 * returns the form that a group preserving $F$ would preserve 
 * after conjugation by $C$.
 */
 
function RenormaliseForm(form, conj, n, q)
form:= conj^-1*form*Transpose(conj^-1);
newform:= [GF(q)!0 : i in [1..n^2]];
for i in [1..n] do
  for j in [i..n] do
    if not i eq j then
      newform[(i-1)*n+j]:= form[i][j] + form[j][i];
    else
      newform[(i-1)*n+j]:= form[i][j];
    end if;
  end for;
end for;
return Matrix(GF(q), n, n, newform);
end function;

/******************************************************************/
//this returns a matrix which swaps a[i][i] and a[j][j]

function Swapmat(i, j, q, n)
  diag:= [<i,i,1> : i in [1..n]];
  swapmat:= GL(n, q)!Matrix(GF(q), n, n, 
               diag cat [<i,i,0>, <j, j,0>, <i, j, 1>, <j, i, 1>]);  
  return swapmat;
end function;

/******************************************************************/

function Correct2dimQuadForm(form, n, q, type)

  /*
   * The orthogonal groups of minus type in 2 dimensions have 
   * a different form than the central 2 \times 2 block of the form
   * for the orthgonals in > 2 dimensions.
   */
  if n gt 2 and type cmpeq "orth-" then
    bool, form_4:= QuadraticForm(GOMinus(4, q));
    goal:= [[form_4[2][2], form_4[2][3]], [0, form_4[3][3]]];
  elif n eq 2 and type cmpeq "orth-" then
    bool, goal:= QuadraticForm(GOMinus(2, q));
  end if;

  a:= form[1][1]; b:= form[1][2]; c:= form[2][2];
  p := PolynomialRing(GF(q)); x := p.1;

  if type cmpeq "orth+" then
    if a eq 0 and c eq 0 then
      sqrt:= Root(b, 2);
      return GL(2, q)!DiagonalMatrix([sqrt, sqrt]);
    elif c eq 0 then // so a is not zero, and neither is b.
      mat:= GL(2, q)![0, a*b^-2, b*a^-1, 1];
      return mat^-1;
    elif b eq 0 then // so c is not zero, and neither is b.
      mat:= GL(2, q)![b^-1, 0, b^-1*c, 1];
      return mat^-1;
    else
      //roots exist since form is of plus type.
      roots:= Roots(form[1][1]*x^2 + form[1][2]*x + form[2][2]);
      z:= roots[1][1];
      mat:= GL(2, q)![z, 1, b^-1+z*a*b^-2, a*b^-2]; 
      return mat^-1;
    end if;
  end if;
                 

  /*
   * The remaining code is for orth-. Sadly, I don't know exactly what
   * the form will be, so I've done it for a general form.. 
   */

  //we have matrix [a, b, 0, c] and are aiming for [X, Y, 0,
  //Z]. We will get there by multiplying by [A, B, C, D]. We know 
  //that b and Y are nonzero, and that ax^2+bx+c is irreducible.

  X:= goal[1][1]; Y:= goal[1][2]; Z:= goal[2][2];  

  p := PolynomialRing(GF(q)); x := p.1;

  for A in GF(q) do
    poly:= a*A^2 + x*A*b + x^2*c - X;
    roots:= Roots(poly);
    //roots;
    for root in roots do
      B:= root[1];
      if not (A eq 0 or B eq 0) then
        roots2:= Roots(x^2*B^-2*X + x*B^-1*Y + a*b^-2*B^-2*Y^2 + Z); 
        if #roots2 gt 0 then //it seems that this is always the case
                             //but I can't quite see why.
          D:= roots2[1][1];
          C:= B^-1*(Y*b^-1 + A*D);
          mat:= GL(2, q)![A, B, C, D];
          return mat^-1;
        end if;
      elif not B eq 0 then //so A = 0.
        C:= Y*B^-1*b^-1;
        roots2:= Roots(x^2*c + x*C*b + C^2*a + Z);
        if #roots2 gt 0 then //again, this is always the case.
          mat:= GL(2, q)![A, B, C, roots2[1][1]];
          return mat^-1;
        end if;
      elif not A eq 0 then //so B eq 0.
        D:= Y*b^-1*A^-1;
        roots2:= Roots(x^2*a + x*D*b + D^2*c + Z);
        if #roots2 gt 0 then //and so is this. 
          mat:= GL(2, q)![A, B, roots2[1][1], D];
          return mat^-1;
        end if;
      end if;
    end for;
  end for;
  //"error: form =", form, "goal =", goal;
  return false;
end function;

/*********************************************************************/
      
//this is the main function to standardise a quadratic form.

function CorrectQuadForm(form, n, q, type)
  
  diag:= [<i,i,1> : i in [1..n]];
  s:= 1; f:= n;
  conj:= Identity(GL(n, q));

  while (f - s) gt 1 do

    //if there exists a diagonal entry which is zero
    if exists(t){i : i in [s..f] | form[i][i] eq 0} then

      // move it to row s
      mat:= Swapmat(t, s, q, n);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      //if there is an entry in row start which is nonzero
      if exists(t){i : i in [s..f-1] | not form[s][i] eq 0} then  
        mat:= Swapmat(t, f, q, n);
        form:= RenormaliseForm(form, mat, n, q); 
        conj:= conj*mat;
      end if;

      //new x_f -> sum _{j=s,f} form_{s j} old x_j
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
        [<s+j, f, form[s][s+j]> : j in [0..(f-s)]]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      // new x_s = sum _{i=s,f} form_{i f} old x_i
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
          [<s+j, s, form[s+j][f]> : j in [0..(f-s)]]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

      s:= s+1; f:= f-1;

    elif exists(t){i : i in [s..f] | exists(u){j: j in [i+1..f] |
                    form[i][j] eq 0}} then
      ri:= Root(form[t][t], 2);
      rj:= Root(form[u][u], 2);
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat [<t,t,ri>, <u,t,rj>]);
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

    else
      mat:= GL(n, q)!Matrix(GF(q), n, n, diag cat
         [<s+1, s+1, form[s][s+1]>, <s+2, s+1, form[s][s+2]>]);    
      form:= RenormaliseForm(form, mat, n, q);
      conj:= conj*mat;

    end if;
  end while;

  //the final 2 \times 2 block in the centre.
  h:= n div 2;
  centre:= Submatrix(form, h, h, 2, 2);
  mat:= Correct2dimQuadForm(centre, n, q, type);
  if n gt 2 then
    mat:= GL(n,q)!DiagonalJoin(<Iden(h-1, q), mat, Iden(h-1, q)>);
  end if;
  form:= RenormaliseForm(form, mat, n, q);

  return form, conj*mat;
end function;



/*
 * Some tests.

pairs:= [<2, 8>, <2, 16>, <2, 32>, <2, 64>, <2, 128>, <2,
256>,
 <4, 2>, <4, 4>, <4, 8>, <4, 16>, 
 <6, 2>, <6, 4>, <6, 8>, <6, 16>,
 <8, 2>, <8, 4>, <8, 8>,
 <10, 2>, <10, 4>,
 <12, 2>,
 <14, 2>];

for p in pairs do
  p;
  for y in [1..100] do
    z:= Random(GL(p[1], p[2]));
    qf:= QuadraticForm(GOMinus(p[1], p[2])^z);
    a, b:= CorrectQuadForm(qf, p[1], p[2], "orth-");
    QuadraticForm(GOMinus(p[1], p[2])^(z*b)) eq
        QuadraticForm(GOMinus(p[1], p[2]));
    qf:= QuadraticForm(GOPlus(p[1], p[2])^z);
    a, b:= CorrectQuadForm(qf, p[1], p[2], "orth+");
    QuadraticForm(GOPlus(p[1], p[2])^(z*b)) eq
      QuadraticForm(GOPlus(p[1], p[2]));
  end for;
end for; 
    

*/

