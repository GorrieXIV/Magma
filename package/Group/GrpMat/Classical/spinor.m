freeze;
import "group.m" : GetAandB;


/*
form should be bilinear, g is an element of the orthogonal group preserving
that form.  Even q uses the paper by Dye "the special orthogonal groups and
the Dickson invariant".  Odd q following Zassenhaus "on the  spinor norm"
returns 0 if g is in Omega, 1 if g is in SO \ Omega.
*/
intrinsic SpinorNorm(g::GrpMatElt, form::AlgMatElt) -> RngIntElt
{The spinor norm of the element in the special orthogonal group fixing 
 the specified form}

  d:= NumberOfRows(g);
  q:= #BaseRing(g);
  K := GF(q);

  A := IdentityMatrix(K,d) - g;

  // test from Dye paper 
  // -- this is the Dickson invariant *not* the spinor norm
  if IsEven(q) then
    return IsEven(Rank(A)) select 0 else 1;
  end if;

  // assert IsOdd(q);
  require g*form*Transpose(g) eq form : "Not an element of the orthogonal group";

  ns := Nullspace(A);
  bs := Basis(Complement(VectorSpace(K, d), ns));
  new_d := #bs;
  m1 := Matrix(K, new_d, d, bs);
  newmat := m1*form*Transpose(A)*Transpose(m1);

  // Why is this next line needed? If 2 is not a square in K, nothing changes
  a := (Determinant(g) eq K!(-1)) select K!2 else K!1;
  return IsSquare(Determinant(newmat)*a) select 0 else 1;

end intrinsic;

intrinsic SpinorNorm(g::GrpMatElt, form::GrpMatElt) -> RngIntElt
{The spinor norm of the element in the special orthogonal group fixing 
 the specified form}
 return SpinorNorm(g, Matrix(form));
end intrinsic;



/****************************************************************************/

//function to compute the map tau as given in Kleidman and Liebeck
// - measures how much an element of the conformal group warps the form. 
// returns a nonzero field element lambda such that f(xg, yg) = lambda*f(x, y)
// for all vectors x, y. if lambda = 1 then g is in the orthogonal group. 
// NB: This function does not check if g is in the conformal group.

function tmap(g, f, d, q : Unitary:=false)
  // find a pair of vectors e_x and e_y s.t. f(e_x, e_y) \neq 0. 
  // if the form is nondegenerate, the first value of x will work for some y.
  _ := exists(i,j){ <i,j> : i,j in [1..d] | f[i,j] ne 0 };
  V := VectorSpace(BaseRing(g),d);
  v1 := V.i;  v2 := V.j;

  //find images of e_x, e_y under g.
  v1:= v1*g;
  v2:= v2*g;
  if Unitary then
    v2 := V![ x^q : x in Eltseq(v2) ];
  end if;
 
  return (v1*f,v2) * f[i,j]^-1;
end function;


/*
Only used for symplectic groups -- see symplectic.m/RecogniseExtendedSp

intrinsic ClassicalMultiplierMap( F::Mtrx, type::MonStgElt : Group:=false ) -> Map
{The multiplier map from the conformal group of the form F}
  require type in ["unitary","symplectic","orthogonal"] : "Invalid type";
  G := (Group cmpeq false) select ConformalClassicalGroup(F,type) else Group;
  d := Degree(G);
  K := BaseRing(G);  q := #K;  
  if type eq "unitary" then  _,q:= IsSquare(q);  end if;
  return hom< G -> GL(1,K) | 
    g :-> Matrix(1,1,[tmap(g, F, d, q : Unitary:=(type eq "unitary"))]) >;
end intrinsic;
*/

//function to compute the coset of an element of the conformal group, odd dimension odd field.
//returns a scalar matrix, a spinor norm value, and an element g1 of SO, such that g1*scalar
//is the original element, and the spinor norm value is the norm on g1. 

function ExtendedSpinorNormOddOdd(g, f, d, q)
  //fixing the tmap with a scalar gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  rt:= Root(t, 2);
  scal1:= ScalarMatrix(d, rt);
  
  //now fix determinant +/-1 to get into SO
  if Determinant(g)*Determinant(scal1)^-1 eq GF(q)!-1 then
    scal2:= ScalarMatrix(d, GF(q)!-1);
  else 
    scal2:= GL(d, q).0;
  end if;

  //finally do spinor norm on the elt of GO. elements can be described by spinor norm and a 
  //pair of scalars.
  g1:= scal1^-1 * scal2^-1 * g;

  return scal1, scal1[1][1], scal2, scal2[1][1], g1, SpinorNorm(g1*scal2, f);
end function;

function ExtendedSpinorNormEvenEven(g, f, d, q)
  //fixing the tmap with a scalar gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  rt:= Root(t, 2);
  scal1:= ScalarMatrix(d, rt);
  
  //finally do spinor norm on the result. elements can be described by spinor norm and a scalar.
  g1:= scal1^-1 * g;

  return scal1, scal1[1][1], GL(d, q).0, GF(q)!1, g1, SpinorNorm(g1, f);
end function;
  

function ExtendedSpinorNormEvenOdd(g, f, d, q, sign)
 //K&L need the form to be diagonal. our input form may not be, AND the one preserved by 
 //magma is not, but the form mapped to by CorrectForm is (although it has final entry a 
 //primitive field element rather than first one.
  if sign eq "orthogonalplus" then
    matfplus:= CorrectForm(f, d, q, "orth+");
    b, f1:= SymmetricBilinearForm(GOPlus(d, q));
    matcoplus:= CorrectForm(f1, d, q, "orth+");
  else
    matfminus:= CorrectForm(f, d, q, "orth-");
    b, f1:= SymmetricBilinearForm(GOMinus(d, q));
    matcominus:= CorrectForm(f1, d, q, "orth-");
    b, newform:= SymmetricBilinearForm(GOMinus(d, q)^matcominus);
    //"newform =", newform;
  end if;

  //fixing the tmap with a power of delta gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  if t eq 1 then
    delta:= GL(d, q).0;
    g1:= g;
  elif sign eq "orthogonalplus" then
    //this version of delta works for GOPlus as in magma.
    delta:= GL(d, q)!DiagonalMatrix([t : i in [1..d div 2]] cat [1 : i in [1..d div 2]]);
    delta:= delta^(matcoplus*matfplus^-1);
    g1:= delta^-1 * g;
  else //minus type is more complicated
    bool, b:= IsSquare(t);
    if bool then //discriminant square or nonsquare comes out the same if t is square.
      //"t square";
      delta:= ScalarMatrix(d, b);
      t1:= tmap(delta, GL(d, q).0, d, q);
      if not (t1 eq t) then //taken wrong square root
        delta:= delta*ScalarMatrix(d, GF(q)!-1);
        assert tmap(delta, GL(d, q).0, d, q) eq t;
      end if;
    else 
      //"t nonsquare, t is", t;
      z:= PrimitiveElement(GF(q));
      bool, c:= IsSquare(t*z^-1);
      assert bool;
      a, b:= GetAandB(q);
      if IsEven((d*(q-1)) div 4) then //discriminant nonsquare
        //"disc nonsquare";
        delta1:= GL(d, q)!Matrix(GF(q),d,d, &cat[[<2*i+1, 2*i+1, a*c>, <2*i+1, 2*i+2, b*c>,
         <2*i+2, 2*i+1, b*c>, <2*i+2, 2*i+2, -a*c>] : i in [0..((d div 2)-2)]]  
          cat [<d-1, d, c>, <d, d-1, z*c>]);
        t1:= tmap(delta1^(matcominus^-1), f1, d, q);
        //"t1 is", t1;
        if not (t1 eq t) then //found wrong square root
          delta1:= delta1*ScalarMatrix(d, GF(q)!-1);
          //"new delta1 =", delta1; 
        end if;
        //assert delta1^(matcominus^-1)*f1*Transpose(delta1^(matcominus^-1)) eq ScalarMatrix(d, t)*f1;
     else 
        delta1:= GL(d, q)!Matrix(GF(q), d,d, &cat[[<2*i+1, 2*i+1, a*c>, <2*i+1, 2*i+2, b*c>,
         <2*i+2, 2*i+1, b*c>, <2*i+2, 2*i+2, -a*c>] : i in [0..((d div 2)-1)]]);  
         t1:= tmap(delta1, GL(d, q).0, d, q);
        if not (t1 eq t) then //found wrong square root
          delta1:= delta1*ScalarMatrix(d, GF(q)!-1); 
        end if;
      end if;
      //assert tmap(delta1, newform, d, q) eq t;
      delta:= delta1^(matfminus^-1);
      //assert delta*f*Transpose(delta) eq ScalarMatrix(d, t)*f;
    end if;
    //assert tmap(delta, f, d, q) eq t;
    g1:= delta^-1 * g;
  end if;

  //assert tmap(g1, f, d, q) eq GF(q)!1;
 
  spin:= SpinorNorm(g1, f);

  if Determinant(g1) eq 1 then
    g2:= GL(d, q).0;
  else
    g2:= GL(d, q)!Matrix(GF(q), d, d, [<1, d, -2>, <d, 1, -1*GF(q)!(2^-1)>] cat [<i,i,1> : i in [2..d-1]]);
    if sign eq "orthogonalminus" then
      g2:= g2^(matcominus*matfminus^-1);
    else
      g2:= g2^(matcoplus*matfplus^-1);
    end if;
  end if;

  g3:= g2^-1 * g1;

  //assert Determinant(g3) eq 1 and g3*f*Transpose(g3) eq f;
  //assert delta*g2*g3 eq g;

  return delta, t, g2, Determinant(g1), g3, spin;
end function;


//the extended spinor norm decomposes the matrix g into: a diagonal element, an element of GO but 
//not SO, and an element of SO. returns up to 6 things: the diagonal elt, the field element
//describing it (see the t-map for more details when the diagonal is not scalar), a reflection
//(or the identity), a flag +/- 1 to indicate whether the preceding elt is the identity, an elt 
//of SO and the (standard) spinor norm of the product of the reflection and the elt of SO 
//sometimes the reflection is never needed 
//(whenever q is even or d is odd), in which case the middle two values are placeholders.
//sign only needs to be completed for even dimension odd field, should be "orthogonalplus" or
//"orthgonalminus"
function ExtendedSpinorNorm(g, f, sign)
  d:= NumberOfRows(g);
  q:= #BaseRing(g);

  if IsOdd(d) then
    assert IsOdd(q);
    return ExtendedSpinorNormOddOdd(g, f, d, q);
  elif IsEven(d) and IsEven(q) then
    return ExtendedSpinorNormEvenEven(g, f, d, q);
  else
    return ExtendedSpinorNormEvenOdd(g, f, d, q, sign);
  end if;
end function;



// We can pass the group to the function to avoid element testing
intrinsic ClassicalGroupQuotient( type::MonStgElt, d::RngIntElt, q::RngIntElt : Group:=false ) -> GrpMat
{The standard quotient group for the conformal classical group preserving the form F up to scalars}

  case type :
  when "linear", "symplectic" :
    Q := PolycyclicGroup< a | a^(q-1)=1 >;
  when "unitary" :
    Q := PolycyclicGroup< a, b | b^a=b, b^(q+1)=1, a^(q-1)= b^d >;
  when "orthogonal" :
    if IsEven( q ) then
      Q := PolycyclicGroup< r0, c | r0^2=1, c^r0=c, c^(q-1)=1 >;
    else
      if IsOdd( d ) then
        Q := PolycyclicGroup< c, r0, r1 | r0^2=1, r1^2=1, r1^r0=r1,
          c^((q-1) div 2)=1, r0^c=r0, r1^c=r1 >;
      else
        // THIS IS WRONG
        Q := PolycyclicGroup< c, r0, r1 | r0^2=1, r1^2=1, r1^r0=r1,
          c^(q-1)=1, r0^c=r1, r1^c=r0 >;
      end if;
    end if;
  end case;

  return Q;
end intrinsic;

/*
  d := Nrows(F);  K := BaseRing(F);  eta := PrimitiveElement(K);  
  q := #K;
  G := (Group cmpeq false) select ConformalClassicalGroup(F,type) else Group;
  case type :
  when "linear" : 
    Q<a> := AbelianGroup( [#K-1] );
    return hom< G -> Q | 
      g :-> Log(Determinant(g)) * a,
      x :-> G!DiagonalMatrix( [eta^(Eltseq(x)[1])] cat [K|1:i in [1..d-1]] ) >;
  when "symplectic" :
    q := #K;
    Q<a> := AbelianGroup( [q-1] );
    m := d div 2;  I := IdentityMatrix(K,m);
    return hom< G -> Q | 
      g :-> Log(tmap(g,F,d,q)) * a,
      x :-> G!DiagonalJoin( eta^(Eltseq(x)[1]) * I, I ) >;
  when "unitary" :
    _, q := IsSquare(#K);
    F<a,b> := FreeAbelianGroup(2);
    Q, h := quo<F|[a*(q-1) = b*d, b*(q+1)=0]>;
    return hom< G -> Q | 
      g :-> Log(tmap(g,F,d,q)) * a,
      x :-> G!DiagonalJoin( eta^(Eltseq(x)[1]) * I, I ) >;
  when "orthogonal" : return CO(F);
  end case;
*/


