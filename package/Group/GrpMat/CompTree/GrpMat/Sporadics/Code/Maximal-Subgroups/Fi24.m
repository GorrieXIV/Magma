freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Fi24' */

"Note: No generators are known";

GeneratorsFi24Max1 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max2 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max3 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max4 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max5 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max6 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max7 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max9 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max10 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max11 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max12 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max13 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max14 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max15 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max16 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max17 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max18 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max19 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max20 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max21 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max22 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max23 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max24 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi24Max25 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

/* list of subgroups of Fi24' */

DataFi24 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Fi24", generators := [a, b], order := 1255205709190661721292800>,

   rec <SporadicRF | name := "Fi23", parent := "Fi24", generators := 
   GeneratorsFi24Max1(a,b), order := 4089470473293004800, index := 306936>,

   rec <SporadicRF | name := "2.Fi22:2", parent := "Fi24", generators := 
   GeneratorsFi24Max2(a,b), order := 258247006617600, index := 4860485028>,

   rec <SporadicRF | name := "(3x(O8+(3):3)):2", parent := "Fi24", generators := 
   GeneratorsFi24Max3(a,b), order := 89139236659200, index := 14081405184>,

   rec <SporadicRF | name := "O10-(2)", parent := "Fi24", generators := 
   GeneratorsFi24Max4(a,b), order := 25015379558400, index := 50177360142>,

   rec <SporadicRF | name := "3^7.O7(3)", parent := "Fi24", generators := 
   GeneratorsFi24Max5(a,b), order := 10028164124160, index := 125168046080>,

   rec <SporadicRF | name := "3^(1+10):U5(2):2", parent := "Fi24", generators := 
   GeneratorsFi24Max6(a,b), order := 4848782653440, index := 258870277120>,

   rec <SporadicRF | name := "2^11.M24", parent := "Fi24", generators := 
   GeneratorsFi24Max7(a,b), order := 501397585920, index := 2503413946215>,

   rec <SporadicRF | name := "2^2.U6(2):S3", parent := "Fi24", generators := 
   GeneratorsFi24Max8(a,b), order := 220723937280, index := 5686767482760>,

   rec <SporadicRF | name := "2^(1+12):3.U4(3).2", parent := "Fi24", generators := 
   GeneratorsFi24Max9(a,b), order := 160526499840, index := 7819305288795>,

   rec <SporadicRF | name := "3^(2+4+8).(A5x2A4).2", parent := "Fi24", generators := 
   GeneratorsFi24Max10(a,b), order := 68874753600, index := 18224467509248>,

   rec <SporadicRF | name := "[3^13]:(L3(3)x2)", parent := "Fi24", generators := 
   GeneratorsFi24Max11(a,b), order := 17907435936, index := 70094105804800>,

   rec <SporadicRF | name := "(A4x(O8+(2):3)):2", parent := "Fi24", generators := 
   GeneratorsFi24Max12(a,b), order := 12541132800, index := 100087107696576>,

   rec <SporadicRF | name := "He:2", parent := "Fi24", generators := 
   GeneratorsFi24Max13(a,b), order := 8060774400, index := 155717756992512>,

   rec <SporadicRF | name := "He:2b", parent := "Fi24", generators := 
   GeneratorsFi24Max14(a,b), order := 8060774400, index := 155717756992512>,

   rec <SporadicRF | name := "2^(3+12).(L3(2)xA6)", parent := "Fi24", generators := 
   GeneratorsFi24Max15(a,b), order := 1981808640, index := 633363728392395>,

   rec <SporadicRF | name := "2^(6+8).(S3xA8)", parent := "Fi24", generators := 
   GeneratorsFi24Max16(a,b), order := 1981808640, index := 633363728392395>,

   rec <SporadicRF | name := "(G2(3)x(3^2:2)).2", parent := "Fi24", generators := 
   GeneratorsFi24Max17(a,b), order := 152845056, index := 8212275503308800>,

   rec <SporadicRF | name := "(A9xA5):2", parent := "Fi24", generators := 
   GeneratorsFi24Max18(a,b), order := 21772800, index := 57650174033227776>,

   rec <SporadicRF | name := "(L2(8):3)xA6", parent := "Fi24", generators := 
   GeneratorsFi24Max19(a,b), order := 544320, index := 2306006961329111040>,

   rec <SporadicRF | name := "A7x(7:6)", parent := "Fi24", generators := 
   GeneratorsFi24Max20(a,b), order := 105840, index := 11859464372549713920>,

   rec <SporadicRF | name := "U3(3):2", parent := "Fi24", generators := 
   GeneratorsFi24Max21(a,b), order := 12096, index := 103770313259809996800>,

   rec <SporadicRF | name := "U3(3):2b", parent := "Fi24", generators := 
   GeneratorsFi24Max22(a,b), order := 12096, index := 103770313259809996800>,

   rec <SporadicRF | name := "L2(13):2", parent := "Fi24", generators := 
   GeneratorsFi24Max23(a,b), order := 2184, index := 574727888823563059200>,

   rec <SporadicRF | name := "L2(13):2b", parent := "Fi24", generators := 
   GeneratorsFi24Max24(a,b), order := 2184, index := 574727888823563059200>,

   rec <SporadicRF | name := "29:14", parent := "Fi24", generators := 
   GeneratorsFi24Max25(a,b), order := 406, index := 3091639677809511628800>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Fi24' and produce listing of maximal subgroups */

/* 
MaximalsFi24 := function (G)

   x, y := StandardGeneratorsFi24(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Fi24", DataFi24());

end function;
*/
