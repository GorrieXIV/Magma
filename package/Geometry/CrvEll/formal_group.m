freeze;

/****************************************************************************

  FormalLog, FormalGroupLaw and FormalGroupHomomorphism 

  Steve Donnelly

****************************************************************************/

declare attributes CrvEll : FormalLog; 

debug := false;

intrinsic FormalLog(E::CrvEll : Precision:=10, ReturnPoint:=true) 
       -> RngSerPowElt, PtEll[RngSerLaur]
{Returns the formal logarithm on E as a power series log(T), 
 where the parameter T is the function -x/y on E.  
 Also returns a point P(T) whose coordinates are Laurent series x(T) and y(T).}

   if assigned E`FormalLog then
     if ReturnPoint and #E`FormalLog eq 2 then
       log, pt := Explode(E`FormalLog);
       if AbsolutePrecision(log) ge Precision then
         return log, pt;
       end if;
     elif not ReturnPoint then 
       log := E`FormalLog[1];
       if AbsolutePrecision(log) ge Precision then
         return log;
       end if;
     end if;
   end if;

   R := BaseRing(E);
   a1,a2,a3,a4,a6 := Explode(aInvariants(E));
   Rz := LaurentSeriesRing(R:Precision:=Precision+10); // DefaultPrecision (shouldn't matter here)
   z := Rz.1;  

   A := a1*z+a2*z^2-1;
   B := a3+a4*z;           
   C := a6;

   w := z^3;
   while true do
     w2 := w^2;
     w3 := w*w2;
     f := C*w3 + B*w2 + A*w + z^3;
     df := 3*C*w2 + 2*B*w + A;
     delta := -f/df;
     if not IsExact(R) then
       error if Min([Valuation(c) + Precision(c) : c in Coefficients(delta)])
                lt R`DefaultPrecision/2, "Too much precision loss";
     end if;
     vdelta := [i : i in [0..Precision+10] | not IsWeaklyZero(Coefficient(delta,i))];
     if IsEmpty(vdelta) then
       break;
     end if;
     w +:= delta;
   end while;

   if debug and IsExact(R) then
     // old method
     Rzw:=PolynomialRing(Rz);  
     ww:=Rzw.1;
     pol:=ww-(z^3+a1*z*ww+a2*z^2*ww+a3*ww^2+a4*z*ww^2+a6*ww^3);
     rt:=[r: r in Roots(pol) | Valuation(r[1]) eq 3];
     Wz:=rt[1][1];
     assert #rt eq 1 and rt[1][2] eq 1;
     assert Valuation(Wz) eq 3;
     assert Valuation(Evaluate(pol,Wz)) ge Precision/2;
     assert Valuation(Evaluate(pol,w)) ge Precision/2;
     assert Valuation(w - Wz) ge Precision; // agrees with Newton
   end if;

   omega := (w-z*Derivative(w)) / (w*(a1*z+a3*w-2));
   log := PowerSeriesRing(R:Precision:=Precision+10)! Integral(omega);

   if ReturnPoint then
     e := O(z^Precision);
     Pz := E(Rz)! [z*u+e,-u+e] where u is 1/w;
     E`FormalLog := <log, Pz>;
     return log, Pz;
   else
     E`FormalLog := <log>;
     return log;
   end if;
end intrinsic;


// Here we consider a generic point (x:1:z) in a neighbourhood of 0 on E,
// and calculate a power series z = x^3 + ... + O(x^(prec+1))

function z_as_series_in_x(E, prec)  
//                        CrvEll, RngIntElt -> RngUPolElt

   a1,a2,a3,a4,a6 := Explode(Coefficients(E));
   _<x,z> := PolynomialRing(BaseRing(E),2); 
   z_eq := - a1*x*z - a3*z^2 + x^3 + a2*x^2*z + a4*x*z^2 + a6*z^3;
   ans := z_eq;
   while Degree(ans, z) gt 0 do
      // discard monomial terms where deg_x > prec or 3*deg_z > prec
      mons := Monomials(ans);
      coeffs := Coefficients(ans);
      for i := 1 to #mons do 
         if Degree(mons[i],x) + 3*Degree(mons[i],z) gt prec then
            ans -:= coeffs[i]*mons[i]; end if;
      end for;

      // subst z_eq for one factor z
      // TO DO: truncate z_eq getting rid of terms that won't contribute
      pure_x_part := Evaluate(ans, [x,0]);
      ans := pure_x_part + ((ans - pure_x_part) div z) * z_eq;
   end while;
   if debug then
      PSR := PowerSeriesRing(BaseRing(E));
      xtest := PSR.1;
      ztest := Evaluate(ans, [xtest,0]);
      err := Evaluate(z - z_eq, [xtest,ztest]);
      assert Valuation(err) ge prec; 
   end if;
   if debug and Characteristic(BaseRing(E)) eq 0 then
      _,Pz := FormalLog(E : Precision:=prec+1);
      assert IsWeaklyZero( Evaluate(1/Pz[2], -PSR.1) - Evaluate(ans,[PSR.1,0]) + O(PSR.1^(prec+1)) );
   end if;
   PSR := PowerSeriesRing(BaseRing(E));
   return Evaluate(ans, [PSR.1,0]) + O(PSR.1^(prec+1));
end function;


intrinsic FormalGroupLaw(E::CrvEll, prec::RngIntElt) -> RngMPolElt
{A polynomial in 2 variables T1 + T2 + ... expressing  
the formal group law associated to addition on E, 
up to precision 'prec' (up to terms of total degree 'prec').
This formal group law is with respect to the variable -x/y 
(where x and y are the standard affine coordinates on E).}
 
   require prec ge 2 : "The second argument should be an integer at least 2";

   a1,a2,a3,a4,a6 := Explode(Coefficients(E));
   _<x1,x2,z1,z2> := PolynomialRing(BaseRing(E), 4);
   
   // addition formula for (x1:1:z1) + (x2:1:z2)
   xsum_times_xdiffsquared := (z1-z2)^2*z1*z2 + a1*(z1-z2)*(x2*z1-x1*z2)*z1*z2
                              - (a2*z1*z2+x1*z2+x2*z1)*(x2*z1-x1*z2)^2;
   sum := [ xsum_times_xdiffsquared*(x2*z1-x1*z2), 
            - xsum_times_xdiffsquared*(z1-z2 + a1*(x2*z1-x1*z2)) 
              - (x2-x1)*(x2*z1-x1*z2)^2*z1*z2 - a3*(x2*z1-x1*z2)^3*z1*z2,
            (x2*z1-x1*z2)^3*z1*z2 ];

   SeriesRing1 := PowerSeriesRing(BaseRing(E));  xx1 := SeriesRing1.1;
   SeriesRing2 := PowerSeriesRing(SeriesRing1);  xx2 := SeriesRing2.1;
   working_prec := prec + 1;
   while true do
      zz := z_as_series_in_x(E, working_prec);
      zz1 := Evaluate(zz, xx1);
      zz2 := Evaluate(zz, xx2);
 
      xsum := Evaluate( sum[1], [xx1,xx2,zz1,zz2]);
      ysum := Evaluate( sum[2], [xx1,xx2,zz1,zz2]);
      // remove leading coefficients of ysum that are big O of something:
      while true do 
         coeffs, l := Coefficients(ysum);
         if #coeffs gt 0 and Valuation(coeffs[1]) gt working_prec then  
            // remove the leading term
            ysum := &+[SeriesRing2| coeffs[i]*xx2^(i+l-1) : i in [2..#coeffs] ];
         else break; end if; 
      end while;
      loss := Valuation(ysum);
      if ysum ne 0 then loss := Max(loss, Valuation(Coefficients(ysum)[1])); end if;
      if ysum eq 0 then 
         working_prec +:= 2;
      elif working_prec lt prec + loss then 
         working_prec := prec + loss;
      else break; end if;
   end while;
   ans := (xsum/ysum);
   coeffs, l := Coefficients(ans);
   assert &and[ IsWeaklyZero(coeffs[i]) : i in [1..-l]];
   assert #coeffs+l-1 ge prec;
   _<T1,T2> := PolynomialRing(BaseRing(E), 2, "Glex");
   ans := 0;
   for i := 1-l to prec+1-l do 
     if Valuation(coeffs[i]) le prec then
       ci := Evaluate(coeffs[i], -T1);
       if ci ne 0 then
         ans -:= ci * (-T2)^(i+l-1);
       end if;
     end if;
   end for;
 //ans := &+[ Evaluate(coeffs[i],T1) * T2^(i+l-1) : i in [1-l .. prec+1-l]
 //         | Valuation(coeffs[i]) le prec and Evaluate(coeffs[i],T1) ne 0];
   coeffs_ans, mons_ans := CoefficientsAndMonomials(ans);
   ans := &+[ coeffs_ans[i] * mons_ans[i] : i in [1..#mons_ans] 
                                          | TotalDegree(mons_ans[i]) le prec ];

   if debug then
      assert ans eq Evaluate(ans, [T2,T1]); // check commutativity
      P3 := PolynomialRing(BaseRing(E), 3);
      P3_prec := quo< P3 | ideal< P3 | MonomialsOfDegree(P3,prec+1) > >;
      t1 := P3_prec! P3.1;  t2 := P3_prec! P3.2;  t3 := P3_prec! P3.3;
      assoc := Evaluate(ans, [t1, Evaluate(ans, [t2,t3]) ])
               - Evaluate(ans, [Evaluate(ans, [t1,t2]), t3]);
      assert assoc eq 0;  print "Checked associativity";
   end if;

   return ans;
end intrinsic;


intrinsic FormalGroupHomomorphism(phi::MapSch, prec::RngIntElt) 
       -> RngSerPowElt
{A power series in one variable (to precision 'prec') giving a 
homomorphism between formal groups, associated to the given isogeny phi. 
(The corresponding formal groups can be obtained by calling FormalGroupLaw 
for the domain and codomain of phi; they use the parameter T = -x/y on each 
elliptic curve).}

   require Type(Domain(phi)) eq CrvEll and Type(Codomain(phi)) eq CrvEll :
          "The given map phi must be an isogeny between elliptic curves";

   comps := Components(phi);
   if #comps gt 1 and &and [Type(Domain(comp)) eq CrvEll : comp in comps] then  
     // work step by step (cheaper to compose power series than map eqns)
     f := FormalGroupHomomorphism(comps[1], prec);
     for i in [2..#comps] do 
       fi := FormalGroupHomomorphism(comps[i], prec);
       f := Evaluate(fi, f);
     end for;
     return f;
   end if; 

   // Change affine patch: re-de-homogenise the formula for the map, 
   // with the new affine variables x and z on the first curve
   _<x,z> := PolynomialRing(BaseRing(Domain(phi)), 2);
   eqns := [ Evaluate(eqn, [x,1,z]) : eqn in DefiningEquations(phi)];

   // Let T = -x/y = -x
   // Get the formala for z(T) = -T^3 + ... + O(T^prec) and plug it in,
   zx := z_as_series_in_x(Domain(phi), prec+2);
   T := Parent(zx).1; 
   zT := Evaluate(zx, -T);
   assert Valuation(zT + T^3) ge 4;
   num := Evaluate(eqns[1], [-T,zT]);
   den := Evaluate(eqns[2], [-T,zT]);
   ans := Parent(T)! (-num/den) + O(T^(prec+1));

   if debug then   // check the homomorphism property
      P2 := PolynomialRing(BaseRing(Domain(phi)), 2);
      P2_quo, qm := quo< P2 | ideal< P2 | MonomialsOfDegree(P2,prec+1) > >;
      T1 := qm(P2.1);  T2 := qm(P2.2);
      FG1 := Evaluate( FormalGroupLaw(Domain(phi),prec), [T1,T2]);
      FG2 := Evaluate( FormalGroupLaw(Codomain(phi),prec), [T1,T2]);
      hom_diff := Evaluate(ans, FG1) - 
                  Evaluate(FG2, [Evaluate(ans,T1), Evaluate(ans,T2)]);
      assert hom_diff eq 0;  print "Checked the homomorphism property.";      
   end if;
   
   return ans;
end intrinsic;
