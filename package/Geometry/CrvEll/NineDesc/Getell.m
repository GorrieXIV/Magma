freeze;

/********************************************
Getell.m
Brendan Creutz
version July 2011


Given a plane cubic C, this computes the etale
algebras F,L and M corresponding to the Galois sets of 
the 9 flex points, the 12 lines passing through 3 distinct flexes,
and the set of 36 pairs consisting of a line and a point
on that line.

This is used for doing 9-descents.

Notation:
C - a plane cubic.
K - the flex algebra (associated to the 9 flexes on C)
T - linear form with coefficients in K defining the tangent to C at a generic flex
L - the line algebra
ell - linear form with coefficients in L defining a generic line through 3 flexes
M - the algebra of pairs (P,ell) where P is a flex on the line ell
Np - induced norm from F to L
c - constant in Q s.t. N_{K/Q}(t) = c*cube
beta - constant in L s.t. Np(t) = beta*ell^3

********************************************/

declare verbose ComputeL, 2;

QQ := Rationals();
ZZ := Integers();

/*
FlexPoints := function(C);
  //
  //Input:	C - The plane cubic C.
  //Output: Points - A tup containing one flex point in each Galois orbit.
  //  Fields - A tup containing the field of definition of each point.
  //
  
  f := DefiningEquation(C);
  Hess := Determinant(HessianMatrix(C));
  P := PolynomialRing(Rationals(),3);
  I := ideal<P | f,Hess>;
  B := Reverse(GroebnerBasis(I));
  FlexPoints := <>;
  Fields := [];
  Q := Rationals();
  FB1 := Factorization(B[1]);
  P1 := PolynomialRing(CoefficientRing(P));
  for p in FB1 do
      g := p[1];
      if g eq P.3 then
          gcd := GCD([Evaluate(B[i], [P1.1,1,0]) : i in [2..#B]]);
          Fgcd := Factorization(gcd);
          for s in Fgcd do
              K := ext<QQ | s[1]>;
              if Evaluate(gcd, K.1) ne 0 then
                  root := Roots(gcd, K)[1,1];
              else
                  root := K.1;
              end if;
              NewFlex := C(K)![root,1,0];
              error if K eq QQ, "Has rational flex point: P = %o\n   Use ThreeDescent(EllipticCurve(C,P)).\n", NewFlex;
              FlexPoints := Append(FlexPoints,NewFlex);
              Fields cat:= [K];
          end for;
      else g := Evaluate(g, [0,P1.1,1]); // g eq P.3
          if Degree(g) eq 1 then
              root1 := -Coefficient(g, 0);
              gcd := GCD([Evaluate(B[i], [P1.1, root1, 1]) : i in [2..#B]]);
              Fgcd := Factorization(gcd);
              for s in Fgcd do
                  K := ext<QQ | s[1]>;
                  if Evaluate(gcd, K.1) ne 0 then
                      root2 := Roots(gcd, K)[1,1];
                  else
                      root2 := K.1;
                  end if;
                  NewFlex := C(K)![root2,root1,1];
                  error if K eq QQ, "Has rational flex point: P = %o\n   Use ThreeDescent(EllipticCurve(C,P)).\n", NewFlex;
                  FlexPoints := Append(FlexPoints,NewFlex);
                  Fields cat:= [K];
              end for; // s in Fgcd
          else // Degree(g) eq 1
              Fg := Factorization(g);
              for factor in Fg do
                  h := factor[1];
                  K := ext<QQ | h>;
                  P2 := PolynomialRing(K);
                  gcd := GCD([Evaluate(B[i], [P2.1, K.1,1]) : i in [2..#B]]);
                  Fgcd := Factorization(gcd);
                  for s in Fgcd do
                      K2 := AbsoluteField(ext<K | s[1]>);
                      if Evaluate(s[1], K2.1) ne 0 then
                          root := Roots(s[1], K2)[1,1];
                      else
                          root := K2.1;
                      end if;
                      NewFlex := C(K2)![root,K.1,1];
                      error if K eq QQ, "Has rational flex point: P = %o\n   Use ThreeDescent(EllipticCurve(C,P)).\n", NewFlex;              
                      FlexPoints := Append(FlexPoints,NewFlex);
                      Fields cat:= [K2];
                  end for; // s in Fgcd
              end for; // factor in Fg
          end if; // Degree(g) eq 1
      end if; // g eq P.3
  end for; // p in FB1
  // We want to choose defining polynomials to be monic.
  NewFields := [];
  NewPoints := <>;
  for i in [1..#Fields] do
    Pt := FlexPoints[i];
    K := Fields[i];
    O := Integers(K);
    Knew := ext<Rationals()|MinimalPolynomial(O.2)>;
    bool,map := IsIsomorphic(K,Knew);
    if bool then
      NewFields cat:= [Knew];
      NewPoints := Append(NewPoints,C(Knew)![map(Pt[s]) : s in [1..3]]);
    else
      error "Problem computing maximal orders in the flex algebra.";
    end if; 
  end for; // i in [1..#Fields]
  return NewPoints, NewFields;
end function; //FlexPoints
*/


FlexPoints := function(C);
  X := Flexes(C);
  Rp := RepresentativePoints(X);
  Ks := [ Ring(Parent(P)) : P in Rp ];
  Knews := [];
  Rpnews := <>;
  for u in [1..#Ks] do
    //get better representations;
    Knew,toKnew := OptimisedRepresentation(Ks[u]);
    Knews cat:= [ Knew ];
    Append(~Rpnews,C(Knew) ! [ toKnew(Rp[u][i]) : i in [1..3] ]);
  end for;
  K<theta> := Knews[1];
  return Rpnews,[K];
end function;

DescentMapForm := function(C,PT)
  /*
  Input:	C - The cubic curve
    PT- a flex point on C.
  
  Output: T - a linear form over the field of definition of PT.
    S - the set of rational primes which are bad for T.
  
  T defines the tangent line to C at P. This gives the descent map.
  */
  K := Ring(Parent(PT));
  O := MaximalOrder(K);
  R := PolynomialRing(K,3);
  T:=[Evaluate(Derivative(DefiningEquation(C),i),Eltseq(PT)) : i in [1..3]];
  // Now ensure that the coefficients are integral.
  n := Degree(K);
  M := KMatrixSpace(K,n,n)!BasisMatrix(O);
  Kvsp, map := KSpace(K,QQ);
  // Write out coefficients in terms of the Power basis for F
  Tv:= [map(T[i]) : i in [1..3]];
  // Write out coefficients in terms of the integral basis
  ITv := [Tv[i]*M^(-1) : i in [1..3]];
  // Determine scaling factor
  d := LeastCommonMultiple([Denominator(ITv[i][j]) : j in [1..n], i in [1..3]]);
  T := &+[d*T[i]*R.i : i in [1..3]];
  //We also want to remove common factors from the coefficients if possible.
  Opol := PolynomialRing(O,3);
  T1:=Opol!T;
  d := &cat[ Eltseq(Evaluate(T1,[KroneckerDelta(i,j) : i in [1..3]])) : j in [1..3 ]];
  d := GCD([ ZZ!a : a in d]);
  T := T/d;
  //We need to compute bad primes as well.
  cs := Coefficients(T);
  fact := [ Factorization(ideal<O|a>) : a in { b : b in cs | not IsZero(b)} ];
  badprimesK := &meet{ { pid[1] : pid in fact[i] } : i in [1..#fact] };
  badprimesZ := { Characteristic(ResidueClassField(pid)) : pid in badprimesK};
  //At this point one could check if the pids in badprimesK are principal, then use this to remove more common factors, but this is slow and leads to coefficients which will involve very large units.
  //Now compute the constant coming from the norm condition.
  Kx := Parent(T);
  _,m := SwapExtension(Kx);
  NT := Norm(m(T));
  R := Parent(NT);
  IC := ideal<R|DefiningEquation(C)>;
  H3 := NormalForm(R!Determinant(HessianMatrix(C))^3,IC);
  NT := NormalForm(NT,IC);
  c := QQ ! (NT/H3);
  return T,badprimesZ,c;
end function;//DescentMapForm


NewPoint := function(Indicies,P,Fld,Ob,Ob2);
  if Type(Ob) eq FldNumElt then
    extra := Ob;
  else
    FldPol := PolynomialRing(Fld);
    extra := FldPol.1;
  end if;
  if Type(Ob2) ne FldNumElt then
    Ob2 := Fld.1;
  end if;
  Sequ := [];
  for i in [1..3] do
    if Indicies[1] eq i then
      Sequ cat:= [1];
    end if;
    if Indicies[2] eq i then
      entry := Parent(Ob2)!0;
      tosum := [ Eltseq(P[Indicies[2]])[i]*Ob2^(i-1) : i in [1..#Eltseq(P[Indicies[2]])] ];
      for i in [1..#Eltseq(P[Indicies[2]])] do
        entry +:= tosum[i];
      end for;
      Sequ cat:= [entry];
    end if;
    if Indicies[3] eq i then
      Sequ cat:= [extra];
    end if;
  end for;
  return Sequ;
end function; //NewPoint()

IndiciesOfPt := function(P)
  // Up to some permutation of the coordinates, a generic point defined over F will look like (a,c*F.1,1) where a in F and c in Q. This determines what the order is.
  Primitive := "";
  for i in [1..3] do
    if P[i] eq 1 then
      One := i; 
    end if;
    if P[i]/Parent(P[i]).1 in QQ then
      Primitive := i;
    end if;
  end for;
  if Type(Primitive) eq MonStgElt then
    //We look for an almost primitive.
    for i in ({@ 1,2,3 @} diff {One}) do
      bools := [ Eltseq(P[i])[j] eq 0 : j in [3..#Eltseq(P[i])] ];
      if bools eq [ true : j in [3..#Eltseq(P[i])] ] then
        Primitive := i;
      end if;
    end for;
  end if;
  if Type(Primitive) eq MonStgElt then
    return [One,({@ 1,2,3 @} diff {One})[1],({@ 1,2,3 @} diff {One})[2]], "no primitive";
  else 
    return [One,Primitive,({@ 1,2,3 @} diff {Primitive,One})[1]], "has primitive";
  end if;
end function; //IndiciesOfPt()


FieldOfDefOfSlope := function(P,Q,F);
/*
P and Q are flex points of C defined over some some extension F'/F (here F is really one of the components of F). This computes the slope of the line through P and Q, and its minimal field of definition over F. This gives a field F(Slope) over F which should be one of the components of M. We then compute the minimal polynomial of Slope over Q, and obtain Q(Slope) which should be one of the components of L. We also compute F(Slope) as a relative extension of Q(Slope) and the equation of ell.
*/
vprintf ComputeL, 1 :" Entering FieldOfDefOfSlope.\n"; 
//For now we assume the Slope is not in Q.
Slope := (Q[2]-P[2])/(Q[1]-P[1]);
  //The two cases below correspond to whether Slope in F or in some extension of F.
  if Slope in F then
    vprintf ComputeL, 1: "  Slope is defined over F\n     ==> easy method.\n";
    MoverF := F;
    M := F;
    SlopeInMoverF := F!Slope;
    SlopeInM := M!Slope;
    vprintf ComputeL, 1: "  Computing minimal polynomial for slope : ";
    vtime ComputeL, 1:
    Lslp := ext<QQ|MinimalPolynomial(SlopeInM)>;
    vprintf ComputeL, 1: "  Minimal polynomial has degree %o.\n", Degree(Lslp);
    L,toL := OptimizedRepresentation(Lslp);
    vprintf ComputeL,2: "  Optimised L.\n";
    Embed(L,Lslp,Inverse(toL)(L.1));
    slpL := toL(Lslp.1);
    // This is the field of definition of the slope over Q. Its primitive element is the slope (assuming the slope was not in Q to begin with).
    Embed(Lslp,M,SlopeInM);
    vprintf ComputeL,1: "  Computing relative field M over L.\n";
    MoverL := RelativeField(L,M);
  else
    vprintf ComputeL, 1: "  Computing minimal polynomial for slope relative to degrees %o, %o : ", 
                         AbsoluteDegree(Parent(Slope)), AbsoluteDegree(BaseRing(Parent(Slope)));
    vtime ComputeL, 1:
    f_slp := MinimalPolynomial(Slope);
    //This is the minimal polynomial over F (when Slope in F, this may give the min poly over Q, or the (linear) min poly over F depending on where P and Q are coming from. It is for this reason we have the if statement above).
    MoverF := ext<F|f_slp : Check:=false >;
    SlopeInMoverF := MoverF.1;
    vprintf ComputeL, 1: "  Computing absolute field for M\n";
    if Degree(MoverF) eq 2 then
      vprintf ComputeL, 2: "    M/F is quadratic ==> complete the square method.\n";
      MoverF2 := MoverF;
      // We can find the absolute field smarter than the general routine...
      // first complete the square:
      b := Coefficients(f_slp)[2];
      d := -Coefficients(f_slp)[1] + 1/4*b^2;
      // f2 := x^2 - d;
      // f_slp(x) = f2(x+1/2b)
      D,m := NiceRepresentativeModuloPowers(d,2);
      //dm^2 = D 
      f := Parent(f_slp).1^2 - D;
      // f(m(x+1/2b)) = m^2*f2(x+1/2b) = m^2*f_slp(x);
      MoverF := ext< F | f >;
      // next step is dangerous? 
      Embed(MoverF2,MoverF,m*(MoverF.1+b/2));
      
      M := AbsoluteField(MoverF);
      rts := Roots(f_slp,M);
      vprintf ComputeL, 1: "    ==> Component of M of degree %o.\n", Degree(M);
      assert #rts gt 0;
      SlopeInM := M ! rts[1][1];
      SlopeInMoverF := MoverF ! SlopeInM;
    
    else
      vprintf ComputeL, 1: "    Degree of M/F is %o ==> using general method.\n", Degree(MoverF);
      M := AbsoluteField(MoverF);
      vprintf ComputeL, 1: "    ==> Component of M of degree %o.\n", Degree(M);
      SlopeInM := M ! SlopeInMoverF;
    end if;
    // To get the Field of Definition over Q, we take the minimal polynomial of Slope in M.
    vprintf ComputeL, 1: "  Computing minimal polynomial for slope in M of degree %o over Q : ", Degree(M);
    vtime ComputeL, 1:
    f_slp2 := MinimalPolynomial(SlopeInM);
    Lslp := ext<QQ|f_slp2>;
    vprintf ComputeL, 2: "  Optimizing L : ";
    vtime ComputeL, 2:
    L,toL := OptimizedRepresentation(Lslp);
    Embed(L,Lslp,Inverse(toL)(L.1));
    slpL := toL(Lslp.1);
    // This is the field of definition of the slope over Q. Its primitive element is the slope (assuming the slope was not in Q to begin with).
    vprintf ComputeL, 1: "  Factoring f_F over L : ";
    vtime ComputeL, 1:
    factf_F := Factorization(DefiningPolynomial(F),L);
    D3s := { f[1] : f in factf_F | Degree(f[1]) eq 3 };
    vprintf ComputeL, 1 : "  f_F has %o factor(s) of degree 3 over L.\n", #D3s;
    // if there is more than one, we need to check which is the correct one:
    if #D3s gt 1 then
      Embed(Lslp,M,SlopeInM);
      vprintf ComputeL, 1 : "    ==> using relative field method :";
      vtime ComputeL, 1: 
      MoverL := RelativeField(L,M);
      M2 := AbsoluteField(MoverL);
      assert DefiningPolynomial(M2) eq DefiningPolynomial(M);
      // This should be equal to M. MAGMA will know this.
    else
      vprintf ComputeL, 1 : "    ==> using factorization method.\n";
      MoverL := ext<L|Random(D3s)>;
      M2 := AbsoluteField(MoverL);
      vprintf ComputeL, 1: "  Factoring f_L over F : ";
      vtime ComputeL, 1:
      factf_L := Factorization(DefiningPolynomial(L),F);
      MoverFdeg := Integers()! (Degree(M)/9);
      D4s := { f[1] : f in factf_L | Degree(f[1]) eq MoverFdeg };
      vprintf ComputeL, 1 : "  f_L has %o factor(s) of degree %o over K.\n", #D4s,MoverFdeg;
      if #D4s gt 1 then
        Embed(Lslp,M,SlopeInM);
        vprintf ComputeL, 1 : "   ==> using relative field method :";
        vtime ComputeL, 1: 
        MoverL := RelativeField(L,M);
        M2 := AbsoluteField(MoverL);
        assert DefiningPolynomial(M2) eq DefiningPolynomial(M);
      // This should be equal to M. MAGMA will know this.
      else
        vprintf ComputeL, 1 : "    ==> using factorization method.\n";
        MoverF := ext<F|Random(D4s)>;
        M3 := AbsoluteField(MoverF);
        assert DefiningPolynomial(M2) eq DefiningPolynomial(M3);
        Embed(M2,M3,M3.1);
        Embed(M3,M2,M2.1);
        M := M2;
        SlopeInMoverF := MoverF ! M ! slpL;
      end if;
    end if;
  end if;
  // Now to write down the equation of ell.
  L3Pol<u,v,w> := PolynomialRing(L,3);
  yIntercept := L!( MoverL ! M ! (MoverF!P[2] - SlopeInMoverF*(MoverF ! P[1])));
  ell := v - slpL*u - yIntercept*w;
  FactorToClearDenom := LCM([ Denominator(Eltseq(Coefficients(ell)[3])[i]) : i in [1..#Eltseq(Coefficients(ell)[3])] ]);
  ell := ell*FactorToClearDenom;
  coeffs := [ Eltseq(L ! Coefficients(ell)[3])[i] : i in [1..#Eltseq(L! Coefficients(ell)[3])] ];
  coeffs := [ ZZ!coeffs[i] : i in [1..#coeffs] ];
  Remove := GCD(coeffs);
  ell := ell/Remove;
  return MoverF,M,MoverL,L,ell;
end function;


ComputeL_TransitiveCase := function(C,Points,Fields,t);
// This appears to be working for Galois type of X an extension by F_3^2.

// Since F_3^2 < G, the action on F is transitive. In this case M and L have split into the same number of factors, each factor of M being a degree 3 extension of some factor of L. In this case the Norm M -> L is given by taking the norms component wise.
vprintf ComputeL, 1 : "\nComputing the algebra of lines.\n";

F := Fields[1];
pt := Points[1];
f_F := DefiningPolynomial(F);
vprintf ComputeL, 1: " Factoring f_F over F : ";
vtime ComputeL, 1:
Ff := Factorization(f_F, F);
//There will be a linear factor corresponding to the primitive element of F. We throw this out.
//It should be the first factor, but lets check...
for i in [1..#Ff] do
	if Degree(Ff[i][1]) eq 1 then
		if Roots(Ff[i][1])[1][1] eq Fields[1].1 then
			ind := i; 
		end if;
	end if;
end for;
Fg := [ Ff[j][1] : j in [1..ind-1] ];
Fg cat:= [ Ff[j][1] : j in [ind+1..#Ff] ];
TYPE := ThreeTorsionType(Jacobian(C));

// Generic or 2Sylow 
// M is of type (36)
// L is of type (12)
// f_F/(Fpol.1 - F.1) is irreducible.

// Generic3Isogeny or mu_3-nonsplit
// M is of type (9,27)
// L is of type (3,9)
// // f_F/(Fpol.1 - F.1) factors as:
	// for Gen3Isog :  a quadric and a sextic.
	// for mu_3-nonsplit : quadric * cubic * cubic, with the two cubics leading to the same extensions. We should only take one in this case.

// Dihedral
// M is of type (18,18)
// L is of type (6,6)
// f_F/(Fpol.1 - F.1) factors as a product of two irreducible quartics.

// mu3+Z/3Z
// M is of type (9,9,18) 
// L is of type (3,3,6)
// f_F/(Fpol.1-F.1) factors as:
	//for mu3+Z/3Z (1,1,2,2,2): We only want to take one of the linear factors. Two of the quadratic factors lead to lines defined over a degree 9 n.f. (we only want to take one of these) the third leads to a line defined over a degree 3 n.f. We only want one of the. 
	//for Z/3Z-nonsplit (1,1,6): We only need to take one of the linear factors.

/*
Z/3Z-nonsplit (there are unresolved issues with case 2)
case 1	 	2
M ~ (9,27) or	(9,9,18)	In case 2 the norm is (a,b,c) :-> (N(a),b*N(c)).
L ~ (3,9)  or	(3,9)		(the second case is the only X-transitive F_3 extension).
One detects the difference by factoring the defining polynomial of F over F: f_F factors as:
case1: (1,1,6)
case2: (1,1,2,2,2) (There is something seriously wrong in this case)
*/

// For certain types, there may be 'repeated factors' that we want to throw out.	
if TYPE eq "mu3-nonsplit" then
	Fg := [ Fg[1], Fg[2] ];
end if;
if TYPE eq "Z/3Z-nonsplit" then
	if #Fg eq 3 then
		//This is case1 above.
		Fg := [ Fg[1],Fg[3] ];
	else
	  error "Not yet implemented in this case.\n";
		//This is case2 above. (There is something dodgy in this case)
		Fg := [Fg[1],Fg[3],Fg[4],Fg[5]];
	end if;
end if;
if TYPE eq "mu3+Z/3Z" then
	if Degree(Fg[2]) eq 1 then
		Fg := [Fg[1],Fg[3],Fg[4],Fg[5]];
	//This throws out one of the two linear factors.
	//We still need to throw out one of the quadratic factors, but we won't know which until after we have computed the corresponding extensions.
	else
		error "Problems computing ell.\n";
	end if;
end if;


Fis := < ext<F|Fg[i]> : i in [1..#Fg] >;

Ms := <>;
MoverFs := <>;
MoverLs := <>;
Ls := <>;
ell := <>;

// pts := GetMoreFlexesInOrbit(C,pt,F);

vprintf ComputeL, 1: " Adjoining a second flex gives %o extensions of F of relative degrees %o.\n", #Fis, [ Degree(f) : f in Fg ];

ind := IndiciesOfPt(pt);
pts := <>;

for i in [1..#Fg] do
	if Degree(Fg[i]) eq 1 then
		//in this case there should be 3 flex points defined over F, and we don't need to take an extension to find them. They lie on a line, so finding a second is sufficient.
		Y := Roots(Fg[i])[1][1];
		nP := NewPoint(ind,pt,F,"",Y);
		g := Evaluate(DefiningPolynomial(C),nP);
		xcoord := Roots(g,F);
		//mu3+Z/3Z and Z/3Z-nonsplit: we should get two roots, only one of which corresponds to a flex point (so choice matters).
		pt1 := "";
		j := 0;
		while Type(pt1) eq MonStgElt do
			j +:= 1;
			P := NewPoint(ind,pt,F,xcoord[j][1],Y);
			if Evaluate(Determinant(HessianMatrix(C)),P) eq 0 then
				pt1 := P;
			end if;
      error if j gt #xcoord, "Could not find second flex point to compute ell.\n";
		end while;
		pts := Append(pts,pt1);
	else

    if true then
    // we just want a conjugate of point...
      newpoint := [];
      for j in [1..3] do
        elt := Eltseq(pt[j]);
        coord := &+[ Fis[i].1^(s-1)*elt[s] : s in [1..9] ];
        newpoint cat:= [coord];
      end for;
      assert Evaluate(DefiningEquation(C),newpoint) eq 0;
      Append(~pts,newpoint);
    else
      F1 := Fis[i];
      nP := NewPoint(ind,pt,F1,"","");
      g := Evaluate(DefiningEquation(C),nP);
      vprintf ComputeL, 1: "Calling Roots() to get additional flex point : ";
      vtime ComputeL, 1:
      
      xcoord := Roots(g,F1);
      printf "Number of roots = %o.\n", #xcoord;
      //Generic, 3Isog : we get a single root.
      //Dihedral : we get two roots, but choice doesn't matter.
      //mu3-nonsplit, we get multiple roots, choice matters.
      pt1 := "";
      j := 0;
      while Type(pt1) eq MonStgElt do
        j +:= 1;
        P := NewPoint(ind,pt,F1,xcoord[j][1],"");
        if Evaluate(Determinant(HessianMatrix(C)),P) eq 0 then
          pt1 := P;
        end if;
        error if j gt #xcoord, "Could not find second flex point to compute ell.\n";
      end while;
      pts := Append(pts,pt1);
    end if;
	end if;
end for;



for pt1 in pts do
  vprintf ComputeL, 1: "\n";
	MoverF1,M1,MoverL1,L1,ell1 := FieldOfDefOfSlope(pt,pt1,F);
	vprintf ComputeL, 1: "\n";
	Ms := Append(Ms,M1);
	MoverFs := Append(MoverFs,MoverF1);
	MoverLs := Append(MoverLs,MoverL1);
	Ls := Append(Ls,L1);
	ell := Append(ell,ell1);
end for;

if TYPE eq "mu3+Z/3Z" then
	//We have 2 copies of the extension of the form M -3- L -9- Q. We get rid of it now.
	Done := "no";
	k := 3;
	while Done eq "no" do
		error if k gt #Ms, "Problem in computing L!\n";
		if Degree(Ms[k]) eq 18 then
			Indicies := [1..k-1];
			Indicies cat:= [k+1..#Ms];
			Ms := <Ms[i] : i in Indicies >;
			MoverFs := <MoverFs[i] : i in Indicies>;
			MoverLs := <MoverLs[i] : i in Indicies>;
			Ls := <Ls[i] : i in Indicies>;
			ell := <ell[i] : i in Indicies>;
			Done := "yes";
		end if;
		k +:= 1;
	end while;
end if;

Fc := CartesianProduct([F]);
Mc := CartesianProduct(Ms);
MoverFc := CartesianProduct(MoverFs);
MoverLc := CartesianProduct(MoverLs);
Lc := CartesianProduct(Ls);
n := NumberOfComponents(Lc);
MoverKc := MoverFc;
M2c := < AbsoluteField(MoverLc[j]) : j in [1..NumberOfComponents(MoverLc)] >;

/*
if TYPE eq "Z/3Z-nonsplit-strange" then
	N1 := map< Fc -> Lc | x :-> Lc!< Norm(MoverLc[1]!x[1]) , (Lc[2]!MoverLc[2]!x[1])*(Lc[2]!(Norm(MoverLc[3]!x[1]))) > >;
*/

vprintf ComputeL, 1: " Computing beta and finishing up...\n";
N1 := map< Fc -> Lc | x :-> Lc!< Norm(MoverLc[i] ! x[1]) : i in [1..n] > >;
toverL := < PolynomialRing(MoverLc[i],3) ! t[1] : i in [1..NumberOfComponents(Lc)] >;
m := [];
for i in [1..NumberOfComponents(Lc)] do
	_,mapa := SwapExtension(Parent(toverL[i]));
	m cat:= [mapa];
end for;
N1t := < Parent(ell[i]) ! Norm(m[i](toverL[i])) : i in [1..#toverL] >;
IdealofC := < ideal<Parent(ell[i])|Parent(ell[i])!DefiningEquation(C)> : i in [1..#toverL] >;
beta := Lc ! < Lc[i]!(NormalForm(N1t[i],IdealofC[i])/NormalForm(ell[i]^3,IdealofC[i])) : i in [1..#toverL] >;

nL := n;
K := Fields[1];
K_9Pol := PolynomialRing(K,9);
MoverKc_9Pol := < PolynomialRing(MoverKc[j],9) : j in [1..nL]>;
MoverLc_9Pol := < PolynomialRing(MoverLc[j],9) : j in [1..nL]>;
MoverKc_3Pol := < PolynomialRing(MoverKc[j],3) : j in [1..nL] >;

//Now we need to write N'(z) for a generic element z in K, factor it as N'(z) = z*\tilde{N}(z), and then write \tilde{N}(z) as a form with coefficeints in MoverK.
O_K := LLL(Integers(K));
GenEltK := &+[ O_K.i*K_9Pol.i : i in [1..9] ];
// z = GenEltK is a generic element of K
GenEltKinMoverL := < MoverLc_9Pol[j] ! GenEltK : j in [1..nL] >;
// now written in a basis for M over L
MoLswap := <>;
for j in [1..nL] do
	_,mpa := SwapExtension(MoverLc_9Pol[j]);
	Append(~MoLswap,mpa);
end for;
NprimeGenElt := < Norm(MoLswap[j](GenEltKinMoverL[j])) : j in [1..nL] >;
// N'(z) as a cubic form over L
// N'(z) = \tilde{N}(z)*z for some quadratic form \tilde{N}(z) with coefficients in M
NtildeMoL := < MoverLc_9Pol[j]! ( (MoverLc_9Pol[j] ! NprimeGenElt[j])/GenEltKinMoverL[j] ) : j in [1..nL] >;
NtildeMoK := < MoverKc_9Pol[j]! NtildeMoL[j] : j in [1..nL] >;
// Now written in the basis for M over K
// We also want ell in this basis.
ellInMoverK := < MoverKc_3Pol[j] ! ell[j] : j in [1..nL] >;
vprintf ComputeL, 1 : "Finished computing algebras.\n\n";

return Fc,Mc,MoverKc,MoverLc,Lc,ell,N1,beta,ellInMoverK,NtildeMoK,GenEltK;
end function;
