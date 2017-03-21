freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   CANONICAL LIFT TRACE ALGORITHMS                  //
//			[X0(p)] GENUS 0 CASE			      //
//                             Mike Harrison                          //
//                   Adapted from some original code                  //
//                          by P. Gaudry                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "canonliftgen.m" : SatohNorm;

/* limits only used for p = 2 */
LERCIER_LIM := 600;
RECURSE_LIM := 1000;

/* limits for p > 2 */
GNB2_LIM := 131;
CYCLO_LIM_7 := 520;
CYCLO_LIM_13 := 1500; // guestimate!


function E(X,Y,p)
  case p:
    when 2:   //Y - (X*(4*Y+1))^2
        return  Y - (X*(ShiftValuation(Y,2)+1))^2;
    when 3:  //U(X)U(Y)Y-X^3 where U(x) is 27x^2+9x+1
	X2 := X^2;
	Ux := 1+ShiftValuation(X,2)+ShiftValuation(X2,3);
	Uy := 1+ShiftValuation(Y,2)+ShiftValuation(Y^2,3);	
  	return  Ux*Uy*Y-X*X2;
    when 5: //U(X)U(Y)Y-X^5 where U(x) is 25x^4+25x^3+15x^2+5x+1
	X2 := X^2;
	X4 := X2^2;
	Ux := 1+ShiftValuation(X,1)+ShiftValuation(X2+X2+X2,1)+
		ShiftValuation(X*X2,2)+ShiftValuation(X4,2);
	Uy := 1+ShiftValuation(Y*
		(1+Y*(3+ShiftValuation(Y*(Y+1),1))),1);
	return Ux*Uy*Y-X*X4;
    when 7: //YV(X)U(X)^3-X^7V(Y)U(49Y)^3 where
 	    // V(x)=49x^2+13x+1 & U(x)=x^2+5x+1
	X_2 := X^2;
	X2 := X+X;
	Ux := 1+ShiftValuation(X,1)-X2+X_2;
	Vx := 1-X+ShiftValuation(X2+ShiftValuation(X_2,1),1);
	YS := ShiftValuation(Y,1);
	Y2 := YS^2;
	Vy := 1+YS+YS-Y+Y2;
	Uy := 1-E-E+ShiftValuation(YS+Y2,2) where
		E is ShiftValuation(Y,2);
	return Y*Vx*Ux^3-X*Vy*(X_2*Uy)^3;
    when 13: //YV(X)U(X)^3-X^13V(Y)U1(13Y)^3 where
 	    // V(x)=13x^2+5x+1 & U(x)=x^4+19x^3+20x^2+7x+1
	    // U1(x) := x^4U(1/x)
	X2 := X^2;
	X4 := X2^2;
	Vx := 1+5*X+ShiftValuation(X2,1);
	Ux := 1+7*X+20*X2+19*X*X2+X4;
	Y2 := Y^2;
	Vy := 1+5*Y+ShiftValuation(Y2,1);
	YS := ShiftValuation(Y,1);
	Y2 := ShiftValuation(Y2,2);
	Uy := 1+19*YS+20*Y2+(7+YS)*YS*Y2;
	return Y*Vx*Ux^3-X*Vy*(X4*Uy)^3;
  end case;
end function;

function Ex(X,Y,p)
// NB: actually computes Ex(X,Y)/p !
  case p:
    when 2:   //defn. of E(X,Y) above
        return  -X*(ShiftValuation(Y,2)+1)^2;
    when 3:  //defn. of E(X,Y) above
	Uy := 1+ShiftValuation(Y,2)+ShiftValuation(Y^2,3);	
  	return  Uy*Y*ShiftValuation(1+E+E,1)-X^2
			where E is ShiftValuation(X,1);
    when 5: //defn. of E(X,Y) above
	X2 := X^2;
	X4 := X2^2;
	Uy := 1+ShiftValuation(Y*
		(1+Y*(3+ShiftValuation(Y*(Y+1),1))),1);
	Vx := 1+X+ShiftValuation(X,1)+ShiftValuation(X2+X2+X2,1)+
	  ShiftValuation(X3,2)-ShiftValuation(X3,1) where X3 is X*X2;
	return Uy*Y*Vx-X4;
    when 7: //defn. of E(X,Y) above
	X_2 := X^2;
	X2 := X+X;
	Ux := 1+ShiftValuation(X,1)-X2+X_2;
	Wx := 4+26*X2-E-E+ShiftValuation(E,2)+ShiftValuation(E*X2,1)
		where E is 4*X_2;
	YS := ShiftValuation(Y,1);
	Y2 := YS^2;
	Vy := 1+YS+YS-Y+Y2;
	Uy := 1-E-E+ShiftValuation(YS+Y2,2) where
		E is ShiftValuation(Y,2);
	return Y*Wx*Ux^2-Vy*(X_2*Uy)^3;
    when 13: //defn. of E(X,Y) above
	X2 := X^2;
	X3 := X*X2;
	X4 := X2^2;
	Ux := 1+7*X+20*X2+19*X3+X4;
	Wx := 2+22*X+102*X2+234*X3+214*X4+14*(X*X4);
	Y2 := Y^2;
	Vy := 1+5*Y+ShiftValuation(Y2,1);
	YS := ShiftValuation(Y,1);
	Y2 := ShiftValuation(Y2,2);
	Uy := 1+19*YS+20*Y2+(7+YS)*YS*Y2;
	return Y*Wx*Ux^2-Vy*(X4*Uy)^3;
  end case;
end function;

function Ey(X,Y,p)
  case p:
    when 2:   //defn. of E(X,Y) above
        return  1-ShiftValuation((ShiftValuation(Y,2)+1)*X^2,3);
    when 3:  //defn. of E(X,Y) above
	return (1+ShiftValuation(X,2)+ShiftValuation(X^2,3))*
			(1+ShiftValuation(Y,2))^2;	
    when 5: //defn. of E(X,Y) above
	Ux := 1+ShiftValuation(X*
		(1+X*(3+ShiftValuation(X*(X+1),1))),1);
	Vy := E^2+ShiftValuation((Y*(1+E))^2,1) where
		E is 1+ShiftValuation(Y,1);
	return Ux*Vy;
    when 7: //defn. of E(X,Y) above
	X_2 := X^2;
	X2 := X+X;
	Ux := 1+ShiftValuation(X,1)-X2+X_2;
	Vx := 1-X+ShiftValuation(X2+ShiftValuation(X_2,1),1);
	YS := ShiftValuation(Y,2);
	Y2 := YS^2;
	Uy := 1-YS-YS+ShiftValuation(YS,1)+Y2;
	Wy := 748+556*YS+(116+YS+ShiftValuation(YS,1))*Y2;
	return Vx*Ux^3-Wy*X*(X_2*X*Uy)^2;
    when 13: //defn. of E(X,Y) above
	X2 := X^2;
	X4 := X2^2;
	Vx := 1+5*X+ShiftValuation(X2,1);
	Ux := 1+7*X+20*X2+19*X2*X+X4;
	YS := ShiftValuation(Y,1);
	Y2 := YS^2;
	Y3 := YS*Y2;
	Y4 := Y2^2;
	Uy := 1+19*YS+20*Y2+7*Y3+Y4;
	Wy := 746+1942*YS+1614*Y2+666*Y3+142*Y4+14*(YS*Y4);
	return Vx*Ux^3-Wy*X*(X4*X2*Uy)^2;
  end case;
end function;


/* X and Y are input at a cetain precision (p_big, say)
   and R1 has precision  >= p_big-p_div.
   The function E3 efficiently computes each of
   R1!(E(X,Y)/p^p_div), Ex(R1!X,R1!Y), Ey(R1!X,R1!Y).
   Used by Lercier lift and Harley's recursive method. */
 
function E3(X,Y,R1,p_div)
  p := Prime(R1);
  case p:
    when 2:
	v := ShiftValuation(Y,2)+1; //4*Y+1
	w := X*v;
	Eval := R1!ShiftValuation(Y-w^2,-p_div);
	w := R1!w;
	Ex := ShiftValuation(-w*(R1!v),1); //-2*(w*(R1!v))
	Ey := R1!1 - ShiftValuation(w*(R1!X),3); //R1!1 - 8*(w*(R1!X))
	return Eval,Ex,Ey;
    when 3:  //defn. of E(X,Y) above
	X2 := X^2;
	Y2 := Y^2;
	Ux := 1+ShiftValuation(X,2)+ShiftValuation(X2,3);
	Uy := 1+ShiftValuation(Y,2)+ShiftValuation(Y2,3);
	yUy := Uy*Y;
	Eval := R1!ShiftValuation(Ux*yUy-X*X2,-p_div);
	Ex := ShiftValuation(ShiftValuation((1+xR1+xR1)*R1!yUy,1)-
		R1!X2,1) where xR1 is ShiftValuation(R1!X,1);
	Ey := (R1!Ux)*(1+yR1+yR1+ShiftValuation(R1!Y2,4))
		where yR1 is ShiftValuation(R1!Y,2);
    when 5: //defn. of E(X,Y) above
	X2 := X^2;
	X3 := X*X2;
	X4 := X2^2;
	Y2 := Y^2;
	Y3 := Y*Y2;
	Y4 := Y2^2;
	Ux := 1+ShiftValuation(X,1)+ShiftValuation(X2+X2+X2,1)+
		ShiftValuation(X3,2)+ShiftValuation(X4,2);
	Uy := 1+ShiftValuation(Y,1)+ShiftValuation(Y2+Y2+Y2,1)+
		ShiftValuation(Y3,2)+ShiftValuation(Y4,2);
	yUy := Uy*Y;
	Eval := R1!ShiftValuation(Ux*yUy-X*X4,-p_div);
	Ex := ShiftValuation(
	  (1+R1!X+ShiftValuation(R1!X,1)+xR2+xR2+xR2+
	    ShiftValuation(xR3,1)-xR3)*R1!yUy - R1!X4,1) 
		where xR2 is ShiftValuation(R1!X2,1)
		where xR3 is ShiftValuation(R1!X3,1);
	Y2 := ShiftValuation(R1!Y2,1);
	Y3 := ShiftValuation(R1!Y3,2);
	Ey := (R1!Ux)*(1+yR1+yR1+yR2+yR2-Y2+ShiftValuation(Y3,1)
		-Y3+ShiftValuation(R1!Y4,3))
		where yR1 is ShiftValuation(R1!Y,1)
		where yR2 is ShiftValuation(Y2,1);
    when 7: //defn. of E(X,Y) above
	YS := ShiftValuation(Y,1);
	Y_2 := YS^2;
	Vy := 1+YS+YS-Y+Y_2;
	YS := ShiftValuation(Y,2);
	Y_2 := ShiftValuation(Y_2,2);
	Uy := 1+ShiftValuation(YS,1)-YS-YS+Y_2;
	X_2 := X^2;
	X2 := X+X;
	Ux := 1+ShiftValuation(X,1)-X2+X_2;
	Ux2 := Ux^2;
	Vx := 1-X+ShiftValuation(X2+ShiftValuation(X_2,1),1);

	yUx2 := Y*Ux2;
	UxVx := Ux*Vx;
	x2Uy := X_2*Uy;
	x4Uy2 := x2Uy^2;
	x6Uy3Vy := x4Uy2*x2Uy*Vy;
	Eval := R1!ShiftValuation(yUx2*UxVx-X*x6Uy3Vy,-p_div);
	YS := R1!YS;
	Wy := 748+556*YS+(116+YS+ShiftValuation(YS,1))*(R1!Y_2);
	X_2 := R1!X_2;
	X_3 := X_2*R1!X; 
	Wx := 4+26*R1!X2+188*X_2+ShiftValuation(X_3,1)+
				ShiftValuation(X_3,2);
	Ex := ShiftValuation((R1!yUx2)*Wx-R1!x6Uy3Vy,1);
	Ey := (R1!Ux2)*(R1!UxVx)-(R1!x4Uy2)*X_3*Wy;
    when 13: //defn. of E(X,Y) above
	X2 := X^2;
	X3 := X*X2;
	X4 := X2^2;
	Ux := 1+7*X+20*X2+19*X3+X4;
	Vx := 1+5*X+ShiftValuation(X2,1);
	Wx := 2+22*X+102*X2+234*X3+214*X4+14*(X*X4);
	Y2 := Y^2;
	Vy := 1+5*Y+ShiftValuation(Y2,1);
	YS := ShiftValuation(Y,1);
	Y2 := ShiftValuation(Y2,2);
	Y3 := YS*Y2;
	Y4 := Y2^2;
	Uy := 1+19*YS+20*Y2+7*Y3+Y4;

	Ux2 := Ux^2;
	yUx2 := Y*Ux2;
	UxVx := Ux*Vx;
	x4Uy := X4*Uy;
	x8Uy2 := x4Uy^2;
	x12Uy3Vy := x8Uy2*x4Uy*Vy;
	Eval := R1!ShiftValuation(yUx2*UxVx-X*x12Uy3Vy,-p_div);

	Wy := 746+1942*E+1614*R1!Y2+666*R1!Y3+142*F+14*(E*F)
		where E is R1!YS where F is R1!Y4;
	X5 := R1!X*R1!X4;
	Wx := 2+22*R1!X+102*R1!X2+234*R1!X3+214*R1!X4+14*X5;
	Ex := ShiftValuation((R1!yUx2)*Wx-R1!x12Uy3Vy,1);
	Ey := (R1!Ux2)*(R1!UxVx)-(R1!x8Uy2)*X5*Wy;	
  end case;

  return Eval,Ex,Ey;

end function;

function init_param_val(j,p)
  case p:
    when 7:   return 1/(j+1);
    when 13:  return 1/(j-5);
  end case;
  return 1/j; // p = 2,3,5
end function;

function NormParam(x,p,use_log)
  case p:
    when 2:  //norm(1+4x)
	c := 1+ShiftValuation(x,2);
	if use_log then
	    return Exp(Trace(Log(c)));
	else
	    return Norm(c);
	end if;
    when 3:  //norm((27x^2+9x+1)(9x+1)/x(3x+1))
	E := x*(1+ShiftValuation(x,1));
	c := ((1+ShiftValuation(E,2))*(1+ShiftValuation(x,2)))
		div E;
        //return (bGNB select Norm(c) else Exp(Trace(Log(c))));
	return (use_log select SatohNorm(c) else Norm(c));
    when 5: //norm( (U(x)/x^2) * Sqrt(
	// ((1+5x)^2+5x^2(2+5x)^2)/((1+2x)^2+5(1+x)^2) ) )
	Ux := 1+ShiftValuation(x*
		(1+x*(3+ShiftValuation(x*(x+1),1))),1);
	Vx := E^2+ShiftValuation((x*(1+E))^2,1) where
		E is 1+ShiftValuation(x,1);
	Wx := (x+E)^2+ShiftValuation((x*E)^2,1) where E is 1+x;
	c := (Ux div x^2)^2 * (Vx div Wx);
    when 7: // norm( (x^3*U(49x)/U(x)) * Sqrt(
	// ((1-5*49x)^2-(49x)^2*(34+98x+343x^2))/
	//  ((1+7x)^2+7x^2*(2+10x-x^2)) ) ) [U(x)=1+5x+x^2]
	//c := (-Ey(x,y,7) div Ex(x,y,7)) where y is GaloisImage(x,1);
	x_2 := x^2;
	x7 := ShiftValuation(x,1);
	x49 := ShiftValuation(x,2);
	x343 := ShiftValuation(x,3);
	Ux := 1-x-x+x7+x_2;
	U49x := 1-x49-x49+x343+ShiftValuation(x_2,4);
	Vx := (1+x49+x49-x343)^2 - ShiftValuation(x_2*
		(34+x49+x49+ShiftValuation(x_2,3)),4);
	Wx := 1+x7+x7+ShiftValuation(x_2*(9+10*x-x_2),1);
	c := ((x*x_2*U49x) div Ux)^2 * (Vx div Wx);
    when 13: // norm( (x^6*U1(X)/U(x)) * Sqrt(
	// (1-38X-122X^2-108X^3-46X^4-10X^5-X^6)/
	//  (1+10x+46x^2+108x^3+122x^4+38x^5-x^6) ) [X=13x]
	X2 := x^2;
	X3 := x*X2;
	X4 := X2^2;
	X5 := x*X4;
	X6 := X3^2;
	Ux := 1+7*x+20*X2+19*X3+X4;
	Wx := 1+10*x+46*X2+108*X3+122*X4+38*X5-X6;
	XS := ShiftValuation(x,1);
	X2 := ShiftValuation(X2,2);
	X3 := ShiftValuation(X3,3);
	X4 := ShiftValuation(X4,4);
	X5 := ShiftValuation(X5,5);
	UX := 1+19*XS+20*X2+7*X3+X4;
	Vx := 1-38*XS-122*X2-108*X3-46*X4-10*X5-
		ShiftValuation(X6,6);
	c := ((X6*UX) div Ux)^2 * (Vx div Wx);
  end case;
  return SquareRoot(use_log select SatohNorm(c) else Norm(c));
end function;

procedure doSign(~t,E)
  p := Characteristic(BaseRing(E));
  case p:
    when 2:  //t=1+2*trace((a1a2+a3)/a1^3) mod 4
	a1,a2,a3 := Explode(aInvariants(E));
	if Trace((a1*a2+a3)/(a1^3)) ne 0 then
	    t := -t; // t = 1 mod 4 initially!
	end if;
    when 3:  //t = (b2(E)/q) mod 3
	boo := IsSquare(bInvariants(E)[1]);
	boo1 := IsDivisibleBy(t-1,3);
	if boo xor boo1 then
	    t := -t;
	end if;
    when 5: //t = norm(c4(E)) mod 5
	nc4 := Norm(cInvariants(E)[1]);
	if Parent(nc4)!t ne nc4 then
	    t := -t;
	end if;
	assert Parent(nc4)!t eq nc4;
    when 7: //t = norm(-c6(E)) mod 7
	nc6 := Norm(-cInvariants(E)[2]);
	if Parent(nc6)!t ne nc6 then
	    t := -t;
	end if;
	assert Parent(nc6)!t eq nc6;
    when 13: //t = norm(c4(E)^3-5*Delta(E)) mod 7
	nm := Norm(cInvariants(E)[1]^3-5*Discriminant(E));
	if Parent(nm)!t ne nm then
	    t := -t;
	end if;
	assert Parent(nm)!t eq nm;
  end case;
end procedure;


/*
    SST lifting suitable for use with Cyclotomic Unramified
    pAdic rings. The inverse Frobenius map is effected mod p
    in the finite field and lifted.
*/
function SSTLift(c, W, finalprec)

  K := Parent(c);
  p := Prime(K);
  n := Degree(K);
  
  R := ChangePrecision(K,W);
  _, red := ResidueClassField(R);
  x := R!c;

  vprintf SEA,4: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  for i := 1 to W-1 do
    y := GaloisImage(x,1);
    x := y - E(x, y, p);
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;

  numloops := Ceiling(finalprec/W)-1;
  inner_lim := W;

  y := GaloisImage(x,1);
  Dx := ShiftValuation(Ex(x, y, p),1);
  Dy := Ey(x, y, p);

  for m := 1 to numloops do
    if m eq numloops then
        inner_lim := finalprec-numloops*W;
    end if;
    vprintf SEA,4: "Increasing precision from %o to %o.. ",m*W,m*W+inner_lim;
    tyme := Cputime();
    x := ChangePrecision(K,m*W+inner_lim)!x;
    y := GaloisImage(x,1);
    V := E(x, y, p);
    v := R!ShiftValuation(V,-m*W);

    for i := 0 to inner_lim - 1 do
      r := -red(v);
      dx := R!Root(r,p);
      dy := GaloisImage(dx,1);
      x +:= ShiftValuation(Parent(x)!dx,m*W+i);
      v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
    end for;
    vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
    
  end for;

  return x;

end function;

/*********** Harley's recursive version of SST ********************
* used instead of straight SST with cyclotomic bases for n large */

DIRECT_LIM := 7;

function recurseA(Eval,Dx,Dy)

  R := Parent(Eval);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    v := Eval;
    inc_x := R!0;
    for i := 0 to prec - 1 do
      dx := R!Root(-red(v),p);
      dy := GaloisImage(dx,1);
      inc_x +:= ShiftValuation(dx,i);
      if i lt prec-1 then
          v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
      end if;
    end for;
    return inc_x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // firest recursion
    inc_x := R!recurseA(R1!Eval,R1!Dx,R1!Dy);
    inc_y := GaloisImage(inc_x,1);
    //update Eval
    tmp := ShiftValuation(Eval+Dx*inc_x+Dy*inc_y,-prec3);
    //second recursion
    ChangePrecision(~R1,prec2);
    inc_x1 := R!recurseA(R1!tmp,R1!Dx,R1!Dy);

    return inc_x+ShiftValuation(inc_x1,prec3);
  end if;

end function;

function recurse(a6l)

  R := Parent(a6l);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    x := a6l;
    for i := 1 to prec - 1 do
      tmp := ShiftValuation(E(x,GaloisImage(x,1),p),-i);
      dx := R!Root(-red(tmp),p);
      x +:= ShiftValuation(dx,i);
    end for;
    return x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // first recursion
    x := R!recurse(R1!a6l);
    y := GaloisImage(x,1);
    //compute E(x,y), Ex(x,y), Ey(x,y) to half precision
    ChangePrecision(~R1,prec2);
    Eval,Dx,Dy := E3(x,y,R1,prec3);
    //second recursion
    x1 := R!recurseA(Eval,Dx,Dy);
    return x+ShiftValuation(x1,prec3);
  end if;

end function;

/************* END OF RECURSIVE HARLEY FUNCTIONS *****************/


/* 
   ADAPTED VERSION OF LERCIER/LUBITZ USED TO GET TO MODERATE PRECISION
   WHEN USING GAUSSIAN NORMAL BASIS.
   The lift function takes a p-adic c [(c,p) = 1] and returns c1 where
      c1 = x mod p^((prec+1)*W),   x the root of
        E(x,GaloisImage(x,1)) = 0 with x=c mod p.
   Only used for p=2 (for p>2 its faster to use straight L/L) and it
   is assumed that W <= 30 [currently: 24<=W<=30].
   
   The method used is Lercier's Newton lift method, adapted by me to
   increase precision by the fixed increment W as in MSST. This is
   faster than Lercier's direct method for precisions required in the
   usual cryptographic ranges (GF(p^n), 100<=n<=1000, say) but is worse
   asymptotically [O(n^(3+epsilon) as opposed to O(n^(2+epsilon)*logn)].
   
   Assume n>=W. The method rests on solving an equation of the form
       Fx = a1*x + b1 mod p^W where F is Frobenius and a1=0 mod p.
   Iterating gives (F^r)x = ar*x+br mod p^W with ar=0 mod p^r so
     x = (F^(n-W))bW mod p^W.
   The ar,br up to r=W are calculated following the binary expansion of W
   and the obvious relations between the as,bs for increasing s.
   For W fixed, the a1 mod p^W is independant of iterations, so all the
   ar needed to get from b1 to bW are precomputed at the beginning and
   reused.
   
   There are 2 fixed precision increment stages: the first to get to
   c1 mod p^W using (precisional) increments of 6, and the second
   with increments of W to get to c1.
   
   It is assumed that n>=6 and if n<W then prec <=0.
*/
function LercierSSTLift(c, W, prec)

  K := Parent(c);
  p := Prime(K);
  n := Degree(K);

  R := ChangePrecision(K,6*Ceiling(W/6));
  y := R!c;//ChangePrecision(c,W);

  // first get to precision 30ish using the general method but
  // with a fixed precision increase of 6.
  vprintf SEA,4: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  for i := 1 to 5 do
    x := GaloisImage(y, n-1);
    y := y - E(x, y, p);
  end for;
    // make precomputes
  x := GaloisImage(y, n-1);// x,y correct to prec 6.
  Dyinv := (-Ey(x, y, p))^-1;
  a1 := ShiftValuation(Ex(x,y,p),1) * Dyinv;
  precomps := [a,GaloisImage(a*a1,1)] where a is GaloisImage(a1,1);
  Append(~precomps,GaloisImage(precomps[2]*a1,3));
    // precision increment loop
  for m in [1..Ceiling(W/6)-1] do
    b1 := ShiftValuation(E(x, GaloisImage(x,1), p),-6*m)*Dyinv;
    b := GaloisImage(b1,1) + precomps[1]*b1; //b=b2
    b := GaloisImage(b,1) + precomps[2]*b1;  //b=b3
    b := GaloisImage(b,3) + precomps[3]*b;   //b=b6
    x +:= ShiftValuation(GaloisImage(b,n-6),6*m);
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;

  R := ChangePrecision(K,W);
  x := R!x;

  if prec le 0 then return x; end if;

  //now use precisional increments of W
    // make precomputes
  vprint SEA,4: "Making precomputes.. ";
  tyme := Cputime();
  y := GaloisImage(x,1);
  Dyinv := (-Ey(x, y, p))^-1;
  a1 := ShiftValuation(Ex(x,y,p),1) * Dyinv;
  seq := Prune(Intseq(W,2)); // binary expansion of W
  precomps := [R|];
  exp := 1;
  a := a1;
  for i := #seq to 1 by -1 do
    tmp := GaloisImage(a,exp);
    Append(~precomps,tmp);
    a := a *tmp;
    exp *:= 2;
    if seq[i] eq 1 then
      tmp := GaloisImage(a,1);
      Append(~precomps,tmp);
      a := a1*tmp;
      exp +:= 1;
    end if;
  end for;
  vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
    //precision incremental loop
  for m := 1 to prec do
    vprintf SEA,4: "Increasing precision from %o to %o.. ",m*W,(m+1)*W;
    tyme := Cputime();
    x := ChangePrecision(K,(m+1)*W)!x;
    b1 := (R!ShiftValuation(E(x, GaloisImage(x,1), p),-m*W))*Dyinv;
    b := b1;
    exp := 1;
    ind := 1;

    for i := #seq to 1 by -1 do
      b := GaloisImage(b,exp) + precomps[ind]*b;
      exp *:= 2; ind +:= 1;
      if seq[i] eq 1 then
        b := GaloisImage(b,1) + precomps[ind]*b1;
        exp +:= 1; ind +:= 1;
      end if;
    end for;
    x +:= ShiftValuation(Parent(x)!GaloisImage(b,n-W),m*W);
    vprintf SEA,4 : "Time %o\n",Cputime()-tyme;
  end for;

  return x;

end function;

/*
   used for p>2 to get to an initial small precision before the
   Lercier/Lubicz lift. Actually computes a lift of Frob^-1(c).
*/
function BasicGNBLift(c,W)
  K := Parent(c);
  p := Prime(K);
  n := Degree(K);

  y := ChangePrecision(K,W)!c;

  vprintf SEA,3: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
  for i := 1 to W-1 do
    x := GaloisImage(y, n-1);
    y := y - E(x, y, p);
  end for;
  vprintf SEA,3 : "Time %o\n",Cputime()-tyme;

  return y;
end function;

/* 
   LERCIER/LUBITZ NEWTON LIFT METHOD. Used with GNB when
   high precision is required.
   prec0 is the precision that the input a6 is correct to.
   precAdjs is the boolean list of adjustments to get to
   the final precision exactly:
   ie if precAdjs = [boo1,boo2,...], the precision sequence
      is  prec1 := 2*prec0 - (1 if boo1 else 0)
          prec2 := 2*prec1 - (1 if boo2 else 0)  ....
*/
function LercierLift(a6,prec0,precAdjs)

  K := Parent(a6);
  p := Prime(K);
  n := Degree(K);

  prec := prec0;
  R := ChangePrecision(K,prec);
  x := R!a6;
  for boo in precAdjs do

    precinc := prec - (boo select 1 else 0);
    vprintf SEA,4: "Increasing precision from %o to %o.. ",prec,prec+precinc;
    tyme := Cputime();
    R := ChangePrecision(K,prec+precinc);
    x1 := R!x;
    y := GaloisImage(x1,1);
    Eval,Ex,Ey := E3(x1,y,Parent(x),prec);
    Dyinv := (-Ey)^-1;
    a1 := Ex * Dyinv;
    b1 := Eval * Dyinv;
    
    exp := 1;
    seq := Prune(Intseq(precinc,2));
    a := a1;
    b := b1;

    for i := #seq to 1 by -1 do
      tmp := GaloisImage(a,exp);
      b := GaloisImage(b,exp) + tmp*b;
      a *:= tmp;
      exp *:= 2;
      if seq[i] eq 1 then
        tmp := GaloisImage(a,1);
        b := GaloisImage(b,1) + tmp*b1;
        a := a1*tmp;
        exp +:= 1;
      end if;
    end for;
    
    x := x1 + ShiftValuation(R!GaloisImage(b,n-precinc),prec);
    prec +:= precinc;
    vprintf SEA,4 : "Time: %o\n",Cputime()-tyme;
    
  end for;

  return x;
  
end function;


function CanonicalLiftTraceMain(j)

  // j a non-supersingular jInv in GF(p^n), p odd. n>=3 is assumed!
  // The function returns +/- the trace of Frobenius on an ordinary
  // elliptic curve/GF(p^n) with that j invariant.

  vprint SEA, 1: "Computing trace via canonical lift.";
  tracetime := Cputime();
  n := Degree(Parent(j));
  p := Characteristic(Parent(j));
  a6 := init_param_val(j,p);
  precfin := Ceiling(n/2)+1;
  if (p eq 2) then 
    precfin -:= 1; pfadj := 2; 
  elif (p eq 3) and IsEven(n) then 
    precfin +:= 1; pfadj := 0;
  else
    pfadj := 0;
  end if;

  // choose type of pAdic basis: normal, cyclotomic,
  //   gnb type 1 or gnb type 2
  if n ge 6 then
    gnb_type := 1;
    R := pAdicQuotientRing(p,1);
    while gnb_type le 2 do //possible GNB types
     booGNB := HasGNB(R,n,gnb_type);
     if booGNB then break; end if;
     gnb_type +:= 1;
    end while;
  else
    booGNB := false;
  end if;
  if booGNB and (gnb_type eq 2) and (p ne 2) then
    if n gt GNB2_LIM then booGNB := false; end if;
    /* if n is too large, the time taken to embed Parent(j)
       into the residue class field of a type 2 gnb unram
       extension of Qp render the gnb extn unhelpful.    */
  end if;
  if not booGNB then
    if p lt 7 then 
	booCyclo := true;
    elif p eq 7 then
	booCyclo := (n ge CYCLO_LIM_7);
    else // p = 13
	booCyclo := (n ge CYCLO_LIM_13);
    end if;
  end if;

  // compute Norm(x) as exp(trace(log(x))) ?
  use_log := (not booGNB) and ((p le 3) or ((p eq 5) and (n ge 340))
		or ((p gt 5) and booCyclo)); 


  if booGNB then  // will use GNB basis for local ring
    vprintf SEA, 1: "Working with Gaussian normal basis type %o\n",gnb_type;
    precmid := precfin;
    bAdjs := [Booleans()|];
    lerc_lim := ((p eq 2) select LERCIER_LIM else 3);
    while precmid gt lerc_lim do
      Append(~bAdjs,IsOdd(precmid));
      precmid := Ceiling(precmid/2);
    end while;
    // choose best precision increment W (24 <= W <= 30)
    // for the "adapted" Lercier stage.
    if precmid le 30 then
      W := precmid; n_its := 1;
    else
      valarr := [5,6,6,7,6,7,7];
      bestval := Infinity();
      for w in [24..30] do
        p0 := Ceiling((precmid)/w);
        val := 4*p0+valarr[w-23];
        if val lt bestval then
           bestval := val;
           W := w; n_its := p0;
        end if;
      end for;
    end if;
    Rprec := Max(W*n_its,precfin+pfadj);
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    R := UnramifiedExtension(
	pAdicQuotientRing(p, Rprec), n : GNBType := gnb_type
    );
    Embed(Parent(a6),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;
    if GetVerbose("SEA") ge 3 then
      if W gt 6 then
	printf "\nLifting by ArtinSchreier at fixed precision %o\n",W;
      else
	printf "\nPerforming basic GNB lift\n";
      end if;
      if #bAdjs gt 0 then printf "to reach precision %o.\n",precmid; end if;
      tyme := Cputime();
    end if;
    c := ((W le 6) select BasicGNBLift(R!a6,W) else LercierSSTLift(R!a6,W,n_its-1));
    if #bAdjs gt 0 then
      vprint SEA, 3: "Beginning full NewtonLift phase.\n";
      Reverse(~bAdjs);
      c := LercierLift(R!c,precmid,bAdjs);
    end if;
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
  else // will use Cyclotomic basis for local ring
    vprint SEA, 1: "Working with",str,"basis." where str is
	(booCyclo select "Cyclotomic" else "simple pAdic");

    // First, create R to precision log_prec -- this is the precision required
    // to compute the Log.  Doing this here saves creating the higher
    // precision in the Log() call.
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    if p eq 2 then
      log_prec := precfin+2;
      if use_log then log_prec := log_prec + Isqrt(log_prec div 2); end if;
      R := UnramifiedExtension(
	pAdicQuotientRing(p, log_prec), n : Cyclotomic := booCyclo
      );
      R := ChangePrecision(R, precfin);
    else
      R := UnramifiedExtension(
	pAdicQuotientRing(p, precfin), n : Cyclotomic := booCyclo
      );
    end if;
    Embed(Parent(a6),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;

    if (p eq 2) and (n le RECURSE_LIM) then //use straight MSST
       tyme := Cputime();
       W := Min(precfin,Floor(30*Log(2)/Log(p)));
       c := SSTLift(R!a6,W,precfin);
       vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
    else //use recursive Harley MSST
       vprintf SEA, 3: "Using Harley's recursive method.\n";
            //"Using MSST with precision increment of %o.\n",W;
       tyme := Cputime();
       c := recurse(R!a6);//MSSTLift(R!a6,W,precfin);
       vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
     end if;
  end if;

  if pfadj gt 0 then
    c := ChangePrecision(R,precfin+pfadj)!c;
  end if;

  vprint SEA,3 : "Computing norm.. ";
  tyme := Cputime();
  c := NormParam(c,p,use_log);
  vprintf SEA, 3: "Time: %o.\n",Cputime()-tyme;
  c := Integers()!c;
  if c gt Isqrt(4*p^n) then
    c := c - p^(precfin+pfadj);
  end if;

  vprintf SEA,1 : "Total trace time: %o\n",Cputime(tracetime);
  return c;
  
end function;

intrinsic ECCanonicalLiftTraceGenus0(E::CrvEll) -> RngIntElt
{}
    t := CanonicalLiftTraceMain(jInvariant(E));
    doSign(~t,E);
    return t;
end intrinsic;

