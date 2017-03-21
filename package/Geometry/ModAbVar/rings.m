freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: rings.m
   DESC: standard-ish rings 

   Creation: 06/16/03 -- initial creation
      
 ***************************************************************************/

ZZ := IntegerRing();
QQ := RationalField();
Qbar := AlgebraicClosure(QQ);
CC := ComplexField();
RR := RealField();

forward
   ApproximateRational,
   CommonBaseRing,
   CommonFieldOfDefinition,
   IsDefnField,
   IsNumberField,
   IsReal,
   OverCompositum,
   OverField,
   OverRing,
   RingName;


// really dumb for now.
function OverCompositum(K1, K2)
   if Type(K1) eq BoolElt or Type(K2) eq BoolElt or  
      (Characteristic(K1) ne Characteristic(K2)) then
      return false;
   end if;
   if K1 cmpeq K2 then
      return K1;
   end if;
   if K1 cmpeq RR or K2 cmpeq RR then
      return CC;
   end if;
   if K1 cmpeq QQ then 
      return K2;
   end if;
   if K2 cmpeq QQ then
      return K1;
   end if;
   if Type(K1) eq FldCyc and Type(K2) eq FldCyc then
      return CyclotomicField(LCM(CyclotomicOrder(K1),CyclotomicOrder(K2)));
   end if;
   return Qbar;
end function;

function OverField(fields)
   if #fields eq 0 then
      return QQ;
   end if;
   K := fields[1];
   for i in [2..#fields] do
      K := OverCompositum(K,fields[i]);
   end for;
   return K;
end function;

function OverRing(rings)
   return OverField(rings);  // good enough for testing.
end function;

function IsReal(F)
   if Characteristic(F) ne 0 then
      return false;
   end if;
   print "Warning -- IsReal: not yet written";
   return true;
end function;

function IsNumberField(F)  // careful, because mine doesn't agree with MAGMA's.
   return Type(F) in {RngInt, FldRat, FldNum, FldQuad, FldCyc};
end function;

function IsDefnField(F)
   return true;  // allow anything at first.
   //return Type(F) in {RngInt, FldRat, FldNum, FldQuad, FldCyc};
end function;

function CommonFieldOfDefinition(X)
   S := [* *];
   for A in X do
      Append(~S, FieldOfDefinition(A));
   end for;
   return OverField(S);
end function;

function CommonBaseRing(X)
   S := [* *];
   for A in X do
      Append(~S, BaseRing(A));
   end for;
   return OverRing(S);
end function;

function RingName(F)
   case Type(F):
      when FldRat:
         return "Q";
      when RngInt:
         return "Z";
      when FldRe:
         return "R";
      when FldCom:
         return "C";
      when FldCyc:
         return Sprintf("Q(zeta_%o)",CyclotomicOrder(F));
      when FldAC: 
         return "Qbar";
      when FldFin:
         return Sprintf("GF(%o)",#F);
      else:
         return Sprintf("%o",F);
   end case;
end function;


function ApproximateRational(x, Cutoff)   // Cutoff = 1000 is good.
   assert Type(x) eq FldReElt;
   cf := ContinuedFraction(Real(x));
   for i in [2..#cf] do
      if cf[i] gt Cutoff then
         v := Convergents([cf[j] : j in [1..i-1]]);
         return v[1,1]/v[2,1];
      end if;
   end for;
   v := Convergents(cf);
   p := v[1,1]/v[2,1];
   return p;
end function;
