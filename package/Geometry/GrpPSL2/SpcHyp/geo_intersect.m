freeze;


/////////////////////////////////////////
//                                     // 
//   functions related to              //
//    Fundemantal domains              //
//  and points in the upper half plane //
//                                     //
/////////////////////////////////////////

// intersection of geodesics

function complexintersection(x,y,H)
   x1  := Real(x[1]);
   x1i := Imaginary(x[1]);
   x2  := Real(x[2]);
   x2i := Imaginary(x[2]);
   y1  := Real(y[1]);
   y1i := Imaginary(y[1]);
   y2  := Real(y[2]);
   y2i := Imaginary(y[2]);
   // assume imaginary values 0.
   // assume no infinities
   x1,x2:=Explode(Sort([x1,x2]));
   y1,y2:=Explode(Sort([y1,y2]));
   if x2 eq y1 then return [H!x2];
   end if;
   if y2 eq x1 then return [H!x1];
   end if;
   if x2 lt y1 or
      y2 lt x1 or
      (x1 lt y1 and y2 lt x2) or
      (y1 lt x1 and x2 lt y2) then
      return [];
   end if;
   // assume x comes first:
   if y1 lt x1 then
      t := x1; x1 := y1; y1 := t;
      t := x2; x2 := y2; y2 := t;
   end if;
   centerx := (x1+x2)/2;
   radiusx := (x2-x1)/2;
   centery := (y1+y2)/2;
   radiusy := (y2-y1)/2;
   d := centery - centerx;
   if d eq 0 then return []; end if;
   X := ((radiusx^2 - radiusy^2)/d + d)/2;
   realZ := centerx + X;
   ImZ := (radiusx^2 - X^2)^(0.5);   
   return [H!(realZ + (-1)^(0.5)*ImZ)];
end function;



function complexintersectionInfinity(real,edge,H)
   // this function  is used if one of the edges has a vertex at infinity;
   if edge[1] eq H!Infinity() then return [H|]; end if;
   if edge[2] eq H!Infinity() then return [H|]; end if;
   e1:=Real(edge[1]);
   e2:=Real(edge[2]);
   if real lt e1 or real gt e2 then return []; end if;
   if real eq e1 then return [H!edge[1]]; end if;
   if real eq e2 then return [H!edge[2]]; end if;
   i := ComplexValue(H.1); 
   radius := (e2 - e1)/2;
   center := (e2 + e1)/2;
   b := AbsoluteValue(SquareRoot(radius^2 - (center-real)^2));
   return [H!(real+i*b)];
end function;
   

intrinsic GeodesicsIntersection(x::[SetCspElt],y::[SetCspElt],H::SpcHyp)
   -> SeqEnum
   {computes the intersection in the upper
   half plane of the two geodesics x, y,
   where x and y are specified by their end points, given as cusps.
   If the geodesics intersect along a line the empty sequence is returned.}
   translated := false;
   if x[1] eq x[2] then 
      if Eltseq(x[1]) in [Eltseq(u) : u in y] then
	 return [H!x[1]];
      else return [];
      end if;
   end if;
   if y[1] eq y[2] then 
      if Eltseq(y[1]) in [Eltseq(u) : u in x] then
	 return [H!y[1]];
      else return [];
      end if;
   end if;
   if #Set([Eltseq(u) : u in [x[1],y[1],x[2],y[2]]]) eq 3 then
      if Eltseq(y[1]) in [Eltseq(u) : u in x] then
	 return [H!y[1]];
      else
	 return [H!y[2]];
      end if;
   end if;
   if #Set([Eltseq(u) : u in [x[1],y[1],x[2],y[2]]]) eq 2 then
      return [];
   end if;
   // want to assume x[1] eq Infinity:
   if [1,0] in [Eltseq(u) : u in [y[1],y[2]]] then
      t := x;
      x := y;
      y := t;
   end if;
   if x[2] eq Cusps()![1,0] then
      x[2] := x[1];
      x[1] := Cusps()![1,0];
   end if;
   if [1,0] notin [Eltseq(u) : u in [x[1],x[2]]] then
      translated := true;
      a,b := Explode(Eltseq(x[1]));
      g,r,s := Xgcd(a,b);
      a := a/g; b:= b/g;
      G := PSL2(Integers());
      M := G![r,s,-b,a];
      Minv := G![a,-s,b,r];
      x[1] := Cusps()![1,0];
      x[2] := M*x[2];
      y[1] := M*y[1];
      y[2] := M*y[2];
   end if;
   frac := func<T | T[1]/T[2]>;
   y1 := frac(Eltseq(y[1]));
   y2 := frac(Eltseq(y[2]));
   x2 := frac(Eltseq(x[2]));
   radius := Abs(y1-y2)/2;
   center := (y1+y2)/2;
   b := Abs(center-x2);
   hsq := radius^2 - b^2;
   if hsq lt 0 then return [];
   end if;
   hn := Numerator(hsq);
   hd := Denominator(hsq);
   hf,hs := SquarefreeFactorization(hn*hd);
   K := QuadraticField(-hf);
   int := H!((K.1)*hs/hd + x2);
   if translated then
      int := Minv*int;
   end if;
   return [int];
end intrinsic;

// ExtendedGeodesic
// given a geodesic (x1,x2), finds points (y1,y2) in R such
// that (y1,y2) extends (x1,x2) to the real axis. 

intrinsic ExtendGeodesic(z::[SpcHypElt],H::SpcHyp) -> SeqEnum
   {returns a geodesic with end points in R which extends the
   geodesic given by the first argument}
   // note that if any end point is infinity, it is the first
   // component of the returned sequence.
   // note also that if the end points are real, they are
   // returned in ascending order (this is used in the function below).
   a := ComplexValue(z[1]);
   b := ComplexValue(z[2]);
   if Imaginary(a) eq Infinity() then
      return [H|Infinity(),Real(b)];
   end if;
   if Imaginary(b) eq Infinity() then
      return [H|Infinity(),Real(a)];
   end if;
   x := Real(a);
   y := Imaginary(a);
   u := Real(b);
   v := Imaginary(b);
   c := (v^2 + u^2 - x^2 - y^2)/(u-x)/2;
   c := ComplexField()!c;
   r := AbsoluteValue(SquareRoot((x-c)^2 + y^2));
   return [H!(c-r),H!(c+r)];
end intrinsic;

intrinsic GeodesicsIntersection(x::[SpcHypElt],y::[SpcHypElt],H::SpcHyp) -> SeqEnum
   {computes the intersection in the upper
   half plane of the two geodesics x, y,
   where x and y are specified by their end points.
   If the geodesics intersect along a line the empty sequence is returned.}
   if &and[IsCusp(u) : u in x cat y] then
      return
      GeodesicsIntersection
      ([ExactValue(u) : u in x],[ExactValue(u) : u in y],H);
   else
      xe := ExtendGeodesic(x,H);
      ye := ExtendGeodesic(y,H);
      if xe[1] eq H!Infinity() then
	 return complexintersectionInfinity(Real(xe[2]),ye,H);
      end if;
      if ye[1] eq H!Infinity() then
	 return complexintersectionInfinity(Real(ye[2]),xe,H);
      end if;      
      xc := [ComplexValue(u) : u in xe];
      yc := [ComplexValue(u) : u in ye];      
      z := complexintersection(xc,yc,H);
      if #z eq 0 then return []; end if;
      zr := Real(z[1]);
      x1, x2 := Explode(Sort([Real(u) : u in x]));
      y1, y2 := Explode(Sort([Real(u) : u in y]));
      if zr ge x1 and zr le x2 and
	 zr ge y1 and zr le y2 then
	 return z;
      else
	 return [H|];
      end if;      
   end if;
end intrinsic;





