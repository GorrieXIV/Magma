freeze;


//datatypes:

declare attributes Map : deg;  //degree of an inclusion

//stores the information about a place P of F1
place_rec := recformat<
		P, //place of F1
		pi, //special local uniformizer of P
		x_1, //the element that belongs to pi
		n1, //-v_P(x_1)
		d1, //scalar to normalize x_1
		m,   //precision for local uniformizer no big influence on 
            //running time
		pre, //precision for pi (not used??)
		B1,   //k[x_1] basis for Cl(k[x_1],F1)
        n, //valuations of the elements in B1
        place_case, //0 if everything is fine
                    //1 if there is no place of deg 1 s.t.
                    //the char does not div the min pole
                    //-n if there is no place of deg 1
                    // and n is the min with #places of deg
                    // n is ge 1
        const_fld_ext_map //s.b.
>;

//stores the information about a divisior D of F2
//for every interesting divisor there will be such a rec
div_rec := recformat<
		D, //Divisor
		S, //supp(D) as a list of places
		e, //list of rammificationindicies
		m, //precision for local uniformizers does not have much influence 
            //on the running time
		pre, //precision for the image of pi for all places in the
                     //support of D
		pi1, //list of the special local uniformizers of P_i in S
        wild, //list of indecies where due to char divides valuation we cant
              //use special local uniformizer
		b_1, //the elements whose roots form the pi1
		B2, //the reduced riemann roch basis as a basis of OS
		d2,    //list of coefficents that were needed to normalize
		       //the b_1
		SR,    //field of laurent series that depende on the
			//parameter
		Kab,	//rational function field in which the 
			//coefficients of the parameter depending
			//series lie
		b_is,	//the function field elements that belong to
			//the other parameters
		phi_pi, //the images of the special local uniformizer
			//of P as series in pi1 with coefficients
			//in Kab kann vielleicht noch raus
		anzpara, //the number of parameter
        	n1, //s.o.
        	const_fld_ext_map //map into the constant
                      //field extension
			 
>;

//rec to store the information about the parameter.
para_rec := recformat<
		Pmod,	//rec of type place_rec with the informations
			//about P
		Dmod,	//same with div_rec
		gleichungen,  //the equations for the parameter
		I,	//ideal defined by the gleichungen
		R,	//k[co1,co2,..,b1,..,br,coiinv] ring in which
			//I lies
                r2kab,  //function to coerce from R to k(...)
		tups,	//tupel of parameter solving the equations
		phi_pi, //phi(pi) image of the local uniformizer as a
                //serie with coefs depending on the parameter
        beta0, //infos about the coeffs of the b_1 as series in 
		       //pi
        phi_x	//coefficients of the images of the x_i as a
			//k[z]-kombination of a basis of O^S
                        //depending on some parameter
>;

declare verbose emb, 2;
//SetVerbose("emb",1);

declare verbose embpre, 2;
//SetVerbose("embpre",1);
/////////////////////////////////////////////////////////////////////////
//begin methods to check if the input is correct
//////////////////////////////////////////////////////////////////////////



//main method to check the input
//input: F1,F2 function fields
//output: true if everything is ok, false and error message otherwise
input_test := function(F1,F2)
 g1 := Genus(F1);
 g2 := Genus(F2);
 check := [];
 check[1] :=  g1 ge 2 and g2 ge 2;
 check[2] := g2 gt g1;
 check[3] := ConstantField(F1) cmpeq ConstantField(F2);
 check[4] := IsGlobal(F1);
 check[5] := IsRationalFunctionField(BaseField(F1));
 check[6] := IsRationalFunctionField(BaseField(F2));
 case Position(check,false):
        when 0: 
            return true, "ok";
        when 1:
            
            return false, "The genera have to be larger than 1";
        when 2:
            
            return false ,"The genus of F1 has to be larger than the genus of F2";
        when 3:
            mess := "The function fields have to be defined over the same constant field";
            return false, mess;
        when 4:
            mess := "The algorithm only works for global function fields";
            return false,mess;
        when 5:
            mess := "The first argument must not be relative";
            return false,mess;
        when 6:
            mess := "The seccond argument must not be relative";
            return false,mess;
 end case;
end function;

//method to check the rest of the input
//input: classgrp, strat, pre
//output: true if everything is fine
input_test_2 := function(classgrp,strat,pre)
 if not Type(classgrp) cmpeq BoolElt then
    mess := "classgrp musst be of type BoolElt";
    return false,mess;
 end if;

 if Type(strat) cmpeq RngIntElt then
    if not strat ge 2 then
       mess := "strat should be at least 2";
       return false,mess;
    end if; 
 else if Type(strat) cmpeq MonStgElt then
         if not strat in ["all","some"] then
            mess := "no valid strategy";
             return false,mess;
         end if;
     else
         mess := "possible types for strat are RngIntElt or MonStgElt";
         return false ,mess;
     end if;
 end if;

 if Type(pre) cmpeq RngIntElt then
     if not pre ge 1 then
         mess := "The precision must be positiv";
         return false, mess;
     end if;
 else if not pre cmpeq "auto" then
         mess := "pre should be of Type RgnIntElt";
         return false, mess;
     end if;
 end if;
 return true, "ok";
end function;

/////////////////////////////////////////////////////////////////////////
//end methods to check the input
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
//begin combinatorics to construct set of divisors
/////////////////////////////////////////////////////////////////////////

//use hurwitz genus formula to calculate the maximal degree of an
//embedding
//input:F1,F2 function fields
//output: int max degree

hurwitzabschaetzer := function(F1,F2)
 g1 := Genus(F1);
 g2 := Genus(F2);
 maxgrad := Floor((2*g2 -2)/(2*g1 - 2));
 vprint emb,1 : "Upper bound for the degree of an inclusion:";
 vprint emb,1 : maxgrad;
 return maxgrad;
end function;


//use number of places of degree 1 of the function fields to
//determin the minimal degree of an embedding
//input:F1,F2 function fields
//output: int min degree

grad_untere_schranke := function(F1,F2) 
 m1 := #Places(F1,1);
 m2 := #Places(F2,1);
 nmin := Maximum([2,Ceiling(m2/m1)]);
 vprint emb,1 : "lower bound for the degree of an inclusion:";
 return nmin;
end function;



//using dedekinds defferenten crit to check which devisors are possible
//conorms
//input: g1, g2 the genera, D divisor, n degree of the extension
//output:false if D does not fulfill the dedekind different theorem

differentenkrit :=function(n,g1,g2,D)
 S := Support(D);
 diffdeg := &+ [(Valuation(D,P)-1)*Degree(P) : P in S ];
 k := (2*g2-2) - n*(2*g1-2) - diffdeg;
 return k ge 0;
end function;



//method that calculates the class numbers of F1 and F2 to, 
//deternim the possible degrees of an embedding
//input:  F1, F2, nmin nmax minimal and maxiaml degree
//output: sequence of possible degrees

klassenkrit := function(F1 ,F2,nmin,nmax)
 vprint emb,1 : "calculating the class numbers";
 fak1 := Factorisation(ClassNumber(F1));
 fak2 := Factorisation(ClassNumber(F2));
 prim1 := [a[1] : a in fak1];
 prim2 := [a[1] : a in fak2];
 exp1 := [a[2] : a in fak1];
 exp2 := [a[2] : a in fak2];
 nout:=[Integers() | ];
 for n in [nmin..nmax] do
    checker := true;
    for p in prim1 do
         if GCD(n,p) eq 1 then
             posi := Position(prim2,p);
             if posi eq 0 or exp1[Position(prim1,p)] gt exp2[posi] then
                 checker:=false;
                 break;
             end if;
         end if;
    end for;
    if checker then
         Append(~nout,n);
    end if;
 end for;
 vprint emb,1 : "possible degrees: ";
 vprint emb,1 : nout;
 return nout;
end function;



stellenzerlegung2 := function(n)
 partli := Partitions(n);
 outli := [];
 for part in partli do
     zerl := [];
     max := part[1];
     for i in [1..max] do
         if i in part then
             Append(~zerl ,[ #[j : j in [1..#part] | part[j] eq i ] , i]);
         end if;
     end for;
     Append(~outli,zerl);
 end for;
 return outli;
end function;




//function to construct the effective divisors of a fixed degree
//input: degree n, function field F2
//output: list of devisors

getmoeglicheconormen := function(n,F2)
 divliste := [DivisorGroup(F2) | ];
 gradlisten :=[];
 for i in [1..n] do
     gradlisten[i] := Places(F2,i);
 end for;
 posis:=[];
 for i in [1..#gradlisten] do
     posis[i] := [1..#gradlisten[i] ];
 end for;
 kombis := stellenzerlegung2(n);
 for kombi in kombis do
     temp :=[];
     checker := [];
     for j in [1..#kombi] do        
         for i in [1..kombi[j][1] ] do
             Append(~temp,posis[kombi[j][2]]);
             Append(~checker,kombi[j][2]);
         end for;        
     end for;
     cart := SetToSequence(Set(CartesianProduct(temp)));
     cart1 := [];
     for j in [1..#cart] do
         rein := true;
         for i in [1..#cart[1]-1] do
            if  (cart[j][i] gt cart[j][i+1] and checker[i] eq checker[i+1]) then
                 rein := false;
             end if;
         end for;
         if rein then
             Append(~cart1,cart[j]);
         end if;
     end for;
     for k in [1..#cart1] do
         D := Zero(DivisorGroup(F2));
         for l in [1..#cart1[k] ] do
             D +:= 1*gradlisten[checker[l]][cart1[k][l]];
         end for;
         Append(~divliste,D);
     end for;
 end for;
 return divliste;
end function;



//calculates the possible degrees for an inclusion
//input: the function fields F1,F2, strat and classgrp
//output: seq of possible degs

get_possible_degs := function(F1,F2,strat,kltest)
 maxgrad := hurwitzabschaetzer(F1,F2);
 mingrad := grad_untere_schranke(F1,F2);
 if Type(strat) cmpeq RngIntElt then
     return [strat];
 end if;
 if kltest then
     allegrade := klassenkrit(F1,F2,mingrad,maxgrad);
 else
     allegrade := [mingrad..maxgrad];
 end if;
 return allegrade;
end function;



//calculates the efficient divisors of a fixed degree
//input: the function field F2 and the dergee deg
//output: seq of degs

get_possible_divisors_deg := function(F2,deg)
    divli :=  getmoeglicheconormen(deg,F2);
    return divli;
end function;

forward dach;
forward eins_raus;




//function to check if the riemann roch space L(D) contains an
//element z with (z)_\infty eq D
//input: D divisor
//output: bool , the element

get_ele_with_polediv := function(D)
 ba := Basis(D);
 eins_raus(~ba);
 S , vielf := Support(D);
 q := #ConstantField(FunctionField(D));
 Kx := PolynomialAlgebra(ConstantField(FunctionField(D)),#ba+1);
 mali := [ [Coefficient(dach(a , S , 10)[i],-vielf[i]) 
 : i in [1 ..#S]] : a in ba ];
 mat := Matrix(Kx,mali);
 vec := Vector(Kx,[Kx.i : i in [1..#ba]] );
 poly := &* ElementToSequence(vec*mat);
 moli := Monomials(poly);
 coli := Coefficients(poly);
 for j in [1..#moli] do
     for i in [1..#ba] do
         while IsDivisibleBy(moli[j], Kx.i^q) do
             moli[j] := moli[j] div Kx.i^(q-1);
         end while;
     end for;
 end for;
 if #moli eq 0 then
     poly := 0; 
 else
     poly := &+ [coli[i]*moli[i] : i in [1..#coli] ];
 end if;
 if poly eq 0 then
     return false,false,false;
 end if;
 gl := [poly*Kx.(#ba+1) +1];
 I := ideal<Kx | gl>;
 maxnum_tups := q^Dimension(I);
 if maxnum_tups le 1000 then
     gl := [Kx.i^q - Kx.i : i in [1..#ba+1] ] cat [poly*Kx.(#ba+1) +1];
     I := ideal<Kx | gl>;
     tups := Variety(I);
     tup := tups[1];
 else
     tup := [1] cat [0 : a in [1..#ba]];
     flag := Evaluate(poly,tup) eq 0;
     while flag do
         tup := [];
         for j in [1..#ba+1] do
             Append(~tup,Random(CoefficientRing(Kx)));
         end for;
         flag := Evaluate(poly,tup) eq 0;
     end while;
 end if;
 z := &+ [tup[i]*ba[i] : i in [1..#ba] ];
 posi := Position([tup[i] eq 0 : i in [1..#ba]], false);
 Remove(~ba,posi);
 vprint emb,2 : "z in get_ele_with_polediv: ";
 vprint emb,2 : z;
 vprint emb,2 : "basis in get_ele_with_polediv: ";
 vprint emb,2 :  ba cat [1];
 return true, z , ba cat [1] ;
end function; 




//method to filter the list of divisors 
//input: list of divisors, Prec place_rec, G automorphism group of F2
//output: list of div_recs, list of the degrees of the constant field
//extensions

filter_divs := function(divli,Pmod)
 outdivli := [];
 outdegli := [1];
 g2 := Genus(FunctionField(divli[1]));
 g1 := Genus(FunctionField(Pmod`P));
 dede_tester := function(D)
    return differentenkrit(Degree(D),g1,g2,D);
 end function;
 n1 := Pmod`n1; 
 for D in divli do
 anzpara := Dimension(n1*D);
 if anzpara ge 2 and dede_tester(D) then
     Dmod := rec<div_rec | D := D , anzpara := anzpara, n1 := n1>;
 S,e := Support(D);
     Dmod`S := S;
     Dmod`e := e;
     Append(~outdivli,Dmod);
     const_deg := LCM([Degree(P) : P in Support(D)]);
     if not const_deg in outdegli then
         Append(~outdegli,const_deg);
     end if;
 end if; 
 end for;
 return outdivli, outdegli;
end function;


//sorts the divisors in a way that those for which the computation is likely
//to be faster are checked first. only used in the case where one is not
//interessted in calculating all inclusions
//input: sequence of divrecs of the same degree. with anzpara and e assigned
//output: the same sequence but ordered lex by first #e then anzpara

sort_divs := procedure(~zutesten)
  comp := function(D1,D2)
   if Maximum(D1`e) lt Maximum(D2`e) then 
     return -1;
   end if;
   if Maximum(D1`e) gt Maximum(D2`e) then
     return 1;
   end if;
   return D1`anzpara - D2`anzpara;
  end function;
 Sort(~zutesten,comp);
end procedure;



////////////////////////////////////////////////////////////////////////
//end construction of divisors
////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//begin constant field extension
//////////////////////////////////////////////////////////////////////

//method to calculate a constant field extension for F1
//input: Pmod place_rec, deg degree of the extension
//output: place_rec belonging to the extension

extend_F1 := function(Pmod,deg);
 F1 := FunctionField(Pmod`P);
 K := ConstantField(F1);
 Kstrich := ext< K | deg >;
 F1neu, schubs1 := ConstantFieldExtension(F1,Kstrich);
 x1 := Representative([a : a in Basis(Pmod`n1*Pmod`P) | not IsConstant(a) ]);
 S1 := Support(PoleDivisor(Divisor(schubs1(x1))));
 assert #S1 eq 1;
 return rec<place_rec | P := S1[1] , const_fld_ext_map := schubs1, 
 n1 := Pmod`n1, place_case := Pmod`place_case>;
end function;




//method to calculate a constant field extension for F2
//input: Dmod div_rec
//output: div_rec belonging to the extension

extend_F2 := procedure(~Dmod)
 F2 := FunctionField(Dmod`D);
 K := ConstantField(F2);
 S,es := Support(Dmod`D);
 grade := [Degree(Pi) : Pi in S ];
 //es := [Valuation(Dmod`D,Pi) :Pi in S ];
 erwgrad := LCM(grade);
 Kstrich := ext< K | erwgrad >;
 F2neu, schubs2 := ConstantFieldExtension(F2,Kstrich);
 D1 := Zero(DivisorGroup(F2neu));
 for i in [1..#S] do
     k := 0;
     Pi := S[i];
     repeat
         k +:=1;
     until Dimension(k*Pi) ge 2;
     x1 := Representative([a : a in Basis(k*Pi) | not IsConstant(a) ]);
     Si := Support(PoleDivisor(Divisor(schubs2(x1))));
     D1 +:= &+[ es[i]*Q : Q in Si ];
 end for;
 assert Degree(D1) eq  &+ [grade[i]*es[i] : i in [1..#grade] ];
 Dmod`D := D1;
 S1,es1 := Support(D1);
 Dmod`S := S1;
 Dmod`e := es1;
 Dmod`const_fld_ext_map := schubs2;
 Dmod`Kab := RationalFunctionField(ConstantField(FunctionField(D1)),
 #Dmod`S + Dmod`anzpara -1 );
end procedure;




//function to calculate a place_rec for any needed constant
//field extension
//input: Pmod place_rec for the not extended case, degli
//sequence of the extesion degrees
//output:sequence of place_recs

places_and_extensions := function(Pmod,degli)
 outli := [ ];
 for deg in degli do
     Append(~outli, extend_F1(Pmod,deg));
 end for;
 return outli;
end function;





//function to calculate a preimage for an element under a constent field
//extension map, does the same as haspreiamge but this method doesnt seem
//to work in my cases
//function only works for finite extensions of finite constant fields
//input: a element, f map
//output: ok bool  whether there existe a preimage, the preimage

urbild_konstantenkoerpererweit := function(a,f)
 F := Domain(f);
 Fneu := Codomain(f);
 Kx := CoefficientRing(F);
 assert Parent(a) eq Fneu;
 yba := ElementToSequence(a);
 out := [];
 for px in yba do
     num := Numerator(px);
     den := Denominator(px);
     numli := ElementToSequence(num);
     denli := ElementToSequence(den);    
     numok := [IsCoercible(ConstantField(F),ko) : ko in numli ];
     denok := [IsCoercible(ConstantField(F),ko) : ko in denli ];
     if &and numok and &and denok then
         if #numli ge 1 then
             temp1:= &+ [ConstantField(F)!numli[i]*F!Kx.1^(i-1) : i in [1..#numli] ];
         else
             temp1 := F!0;
         end if;
         temp2:= &+ [ConstantField(F)!denli[i]*F!Kx.1^(i-1) : i in [1..#denli] ];
         Append(~out,(temp1/temp2));
     else
         return false,false;
     end if;    
 end for;
 out := &+ [F!(out[i]*F.1^(i-1)) : i in [1..#out] ];
 return true,out;
end function;

///////////////////////////////////////////////////////////////////////
//end constant field extension
//////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//begin get infos concerning P
///////////////////////////////////////////////////////////////////////

//this function chooses a place P of F1 with a minimal pole number that 
//is not devided by the char 
//input: F1 function field
//output: Pmod place_rec with the palce P and the case

stellenwahl := function(F1)
 chara := Characteristic(F1); 
 pcandis := Places(F1,1);
 if #pcandis eq 0 then
         "this shouldnt happen. no place of deg 1";
         P:=false;
         i := 2;
         while #Places(F1,i) eq 0 do
             i +:=1;
         end while;
         place_case := -i;
 else
     miniindi := 0;
     minipol := Infinity();
     for Pi in pcandis do
         gaps := GapNumbers(F1,Pi);
         i := 1;
         while i in gaps or i mod chara eq 0 do
             i +:=1;
         end while;
         if i lt minipol and not (i mod chara eq 0) then
             minipol := i;
             miniindi := Pi;
         end if;
     end for;
     P := miniindi;
     gaps := GapNumbers(F1,P);
     i := 1;
     while i in gaps do
         i+:=1;
     end while;
     if i mod chara eq 0 then
         place_case := 1;
     else
         place_case := 0;
     end if;
     n1 := minipol;
 end if;
 if P cmpeq 0 then
     "something happend that shouldnt. no place of degree one chosen";
 end if;
 Pmod := rec<place_rec | P := P , place_case := place_case, n1 := n1>;
 vprint emb,2 : "P:";
 vprint emb,2 : P;
 vprint emb,1 : "first pole number for chosen place of F1: ";
 vprint emb,1 : n1;
 return Pmod;
end function;




forward getxundn;




//calculates a value for the precision for the local uniformizer. this
//precision doesnt have much influence on the running time. it has to be large
//enough, s.t. there are errors when changing for a representation in an
//arbitrary local uniformizer to the special local uni
//input: Pmod
//output:nat m

get_precision_for_P := function(Pmod,zutesten)
 e := Maximum([Maximum([ei : ei in a`e]) :a in zutesten ]);
 n := getxundn(Pmod`P);
 m := Maximum(30, 5 + (n[#n] + 1)*e);
 vprint embpre,2 : "precision for local uniformizer: ";
 vprint embpre,2 : m;
 return m;
end function;




//sets the precision for the special local uniformizer
//input: Pmod place_rec , int m
//output: sets Pmod`m to m

set_precision_for_P := procedure(~Pmod,m)
 Pmod`m := m;
end procedure;



//function to calculate the generaters of the pole sequence 
//and their valuations for a given place
//input: P the place
//output: n sequence of valuations, x sequence of generators

getxundn := function(P)
 //F1 := FunctionField(P);
 n1 := 0;
 repeat
     n1 := n1 + 1;
     E := n1 * P; 
 until Dimension(E) eq 2;
 n := [ n1 ];
 x1 := Representative( [ z : z in Basis(E) | Valuation(z, P) eq -n1 ] );
 x := [ x1 ];
 i := 1;
 nn := n1;
 while i lt n1 do
     i := i + 1;
     repeat
         nn := nn + 1;
         lastdim := Dimension(E);
         E := E + P;
     until &and [ not IsZero((nn - ni) mod n1) : ni in n ]
             and Dimension(E) gt lastdim;
     n[i] := nn;
     x[i] := Representative( [ z : z in Basis(E) | 
     Valuation(z, P) eq -nn ] );        
 end while;
 vprint emb,1 : "poles of the elements of F1";
 vprint emb,1 : n;
 return n,x;
end function;



//function to calculate a reduced k[x_1] basis of O^P where x_1 is not
//necessarily a representative for the first pole number but has pole of
//order n_1 at P  
//input: P the place, n_1 the pole order
//output: n sequence of valusations, x sequence of generators

getxundn2 := function(P,n1)
 n := [ n1 ];
 x1 := Representative( [ z : z in Basis(n1*P) | Valuation(z, P) eq -n1 ] );
 x := [ x1 ];
 i := 1;
 nn := 1;
 E := 1*P;
 while i lt n1 do
     i := i + 1;
     repeat
         nn := nn + 1;
         lastdim := Dimension(E);
         E := E + P;
     until &and [ not IsZero((nn - ni) mod n1) : ni in n ]
             and Dimension(E) gt lastdim;
     n[i] := nn;
     x[i] := Representative( [ z : z in Basis(E) | 
     Valuation(z, P) eq -nn ] );        
 end while;
 vprint emb,1 : "poles of the elements of F1";
 vprint emb,1 : n;
 return n,x;
end function;



//function to calculate a reduced basis for O^P
//input: place_rec Pmod
//output: x s.t. [1,x[2] ,.., x[n]] is an x[1] basis of O^S

get_x1_for_P := procedure(~Pmod)
 if Pmod`place_case eq 0 then
    n,x := getxundn(Pmod`P);
 else
    n,x := getxundn2(Pmod`P,Pmod`n1);
 end if;
 Pmod`x_1 := x[1];
 Pmod`B1 := x;
 Pmod`B1[1] := 1;
 Pmod`n := n;
end procedure; 



//function that calculates several information concernig
//the special local uniformizer at P
//input: Pmod the place_rec with the place P and the precision m
//output:x_1, n1, d1, pi

getLUx1 := procedure (~Pmod)
 m := Pmod`m;
 x_1 := Pmod`x_1;
 x_1 := 1/x_1;
 n1 := Valuation(x_1,Pmod`P);
 assert n1 eq Pmod`n[1];
 x := LocalUniformizer(Pmod`P);
 d := Evaluate(x_1/x^n1,Pmod`P);
 x_1 := x_1/d;
 res,_ := Expand(x_1,Pmod`P : RelPrec := m);
 R := PolynomialAlgebra(Parent(res));
 f := (R.1)^n1 - res;
 pi := Representative(Roots(f,m))[1];
 //M`n1 := n1;
 Pmod`d1 := d;
 Pmod`pi := pi;
 //"d1:  ", M`d1;
 vprint embpre,2 : "special local uniformizer for P: ";
 vprint embpre,2 : pi;
end procedure;




//main method to collect the informations concerning P the palce of F1
//for a sequence of place_recs the special local uniformizer are
//calculated
//input: Pmods a sequence of place_rec
//output: same sequence updated

get_P_infos := procedure(~Pmods)
 for i in [1 ..#Pmods] do
     get_x1_for_P(~Pmods[i]);
     getLUx1(~Pmods[i]);
 end for;

end procedure;

///////////////////////////////////////////////////////////////////////
//end infos concerning P
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
//begin get infos concerning D
///////////////////////////////////////////////////////////////////////


//function to modify the basis of a riemann roch space st there is 1 
//as a basis element and removing 1
//input:rr basis as a sequence of elements
//output: sequence with 1 element less. replacing the missing element
//by 1 yields a basis

eins_raus := procedure(~rb)
 if true in [IsConstant(a) : a in rb] then
    rb := [a : a in rb | not IsConstant(a) ];
 else
    K := ConstantField(Parent(rb[1]));
    rel := Representative(Basis(Relations(rb cat [One(Parent(rb[1]))],K)));
    for i in [1..NumberOfColumns(rel)] do
         if not rel[i] eq 0 then
             Remove(~rb,i);
             break;
         end if;
    end for;
 end if;
end procedure;







//function to calculate an element as above
//in a stupid way

dummes_z := procedure(~Dmod)
 bcand := Basis(Dmod`n1*Dmod`D);
 eins_raus(~bcand);
 fertig := false;
 count := 1;
 tester :=[];
 K := ConstantField(Parent(bcand[1]));
 repeat 
 for i in [1..#bcand] do
     tester[i]:= (K!Random([1..#K]));
 end for;
 z := &+ [tester[j]*bcand[j] : j in [1..#bcand] ];
 fertig := &and [Valuation(z,P) + Valuation(Dmod`n1*Dmod`D,P) eq 0 
 : P in Support(Dmod`D)];
 until count gt 100 or fertig;
 if fertig then
     Dmod`b_1 := z;
     posi := Position([IsZero(a) : a in tester],false);
     Remove(~bcand,posi);
     Dmod`b_is := Append(bcand,1);
 end if;
end procedure;





//function to calculate a representation of b_1^-e*n_1 as a serie
//in a local uni of P_i
//input:Dmod div_rec
//output:special local uniformizer

getLUb1 := procedure(~Dmod)
 m := Dmod`m;
 b_1 := Dmod`b_1;
 b_1 := 1/b_1;
 x := [LocalUniformizer(P) : P in Dmod`S ];
 n1 := [Valuation(b_1,P) : P in Dmod`S];
 wild := [i : i in [1..#Dmod`S] | n1[i] mod Characteristic(FunctionField(Dmod`D)) eq 0];
 normal := [i : i in [1..#Dmod`S] | not i in wild ];
 d := [Evaluate(b_1/x[i]^n1[i],Dmod`S[i]) : i in [1..#n1] ];
 b_1 := [b_1/t : t in d];
 res := [Expand(b_1[i],Dmod`S[i] : RelPrec := m) : i in [1..#Dmod`S] | not i in wild ];
 R := [PolynomialAlgebra(Parent(res[i])) : i in [1..#res] ];
 f := [(R[i].1)^n1[i] - res[i] : i in [1..#res] ];
 pit := [Representative(Roots(f[i],m))[1] : i in [1..#res] ];
 pi := [];
 for i in wild do
     d[i] := 1;
     pi[i] := Expand(x[i],Dmod`S[i] : RelPrec := m);
 end for;
 for i in [1..#normal] do
     pi[normal[i]] := pit[i];
 end for;
 Dmod`d2 := d;
 Dmod`pi1 := pi;
 Dmod`wild := wild;
 vprint embpre,2 : "special local uniformizer for D:";
 vprint embpre,2 : pi;
end procedure;



//function that calculates how much precision is needed for schritt1 to work
//correctly
//input: Dmod and Pmod, we will need to know the rammification index e,
//the valuations at P of the x_i
//output: a vector of valuations

get_precision := function(Pmod,Dmod)
 n := Pmod`n[#Pmod`n];
 e := Dmod`e;
 pre :=[ 3 + (n+1)*e[i] : i in [1..#Dmod`S] ];
 pre := [Maximum([a,17-Dmod`anzpara]) : a in pre ];  //15 seems to be quite a
                                                 //good value for anzpara=2
                                                 //and small genera
                                              //but sometimes it takes to
                                            //long when anzpara=3
 vprint emb,1 : "chosen value for pre:";
 vprint emb,1 : pre;
 return pre;
end function;



//function to set the precision of a divmod
//input: Dmod div_rec, m precision for the special local uniformizer
//pre precision for the image of pi
//output: set Dmod`m

set_precision_for_D := procedure(~Dmod,m,pre)
   Dmod`m := m;
   Dmod`pre := pre;
end procedure;


forward get_reduced_mod_basis;


//main function to calculate the neccessary information about D
//calculates 
//input: Dmod div_rec
//output: div_rec with infos or false if there is no element z
//with (z)_\infty = n1*D

get_D_infos := function(Dmod)
 test , b_1 , b_is := get_ele_with_polediv(Dmod`n1*Dmod`D);
 if not test then 
     return false,false;
 end if;
 Dmod`b_1 := b_1;
 Dmod`b_is := b_is;
 getLUb1(~Dmod);
 get_reduced_mod_basis(~Dmod);
 return true, Dmod;
end function;

///////////////////////////////////////////////////////////////////////
//end infos concerning D
///////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//begin lattice reduction
//////////////////////////////////////////////////////////////////////


//function to calculate the valuation of a vector of series 
//without respecting the rammification/identification with a lattice
//input: a sequence of series
//output: min v_pi (a)

vektorbewert2 := function (a)
 bew := [Valuation(i) : i in a];
 mini := bew[1];
 for i in [2..#bew] do
     if bew[i] lt mini then
         mini := bew[i];
     end if;
 end for;
 return mini;
end function;



//function to determin the degree of the divisor one has to reduce
//to get a basis of O^S
//input: element z with supp((z)_\infty) = S, D divisor, n1 
//output: nat r st reduction of basis(r*D) yields k[z]
//basis of O^S

get_dim_for_red := function(D,z,n)
 zunendlich := PoleDivisor(Divisor(z));
 //assert zunendlich eq n*D;
 deg := Degree(zunendlich);
 m := Dimension(D);
 i :=0;
 repeat
 k1 := Dimension(D);
 D := D + zunendlich;
 i +:=1;
 k2 := Dimension(D);
 until k2 - k1 eq deg;

 return i*n + 1;
end function; 


//function to estimate the needed precision for the lattice reduction
//input: Divisor D, rrdim st reduction is applied to rrdim*D
//output: nat m 

praezi_schaetz_fuer_kzred := function(D,rrdim)
 max := Maximum([Valuation(D,Pi) : Pi in Support(D) ]);
 return max*rrdim;
end function;
 


//calculates a vector of the series expansions of an element a
//to the preciosn m with respect to the local uniformizers of
//the places in S
//input:function field element a, nat precision m, S set of places
//output:sequence of series

dach := function (a,S,m)
 L := [Expand(a,P : RelPrec := m) : P in S];
 return L;
end function;




//function to calculate the valuation of an element with respect
//to the embedding in a z^-1/e lattice
//input: vektor of series L, einfo
//output: minimal valuation

vau := function (L,einfo)
 //assert #einfo eq #L;
 e := LCM(einfo);
 bew := [Valuation(i) : i in L];
 bew := [bew[i]*e/einfo[i] : i in [1..#L]];
 mini := bew[1];
 for i in [2..#bew] do
     if bew[i] lt mini then
         mini := bew[i];
     end if;
 end for;
 return mini;
end function;


//does the same as vau but for an element of a function field
//input:a element, M rec
//output: valuation wrt a lattice 

vau2 := function(a,M)
 einfo := M`Dmod`e;
 e := LCM(einfo);
 bew := [Valuation(a,P) : P in M`Dmod`S];
 bew := [bew[i]*e/einfo[i] : i in [1..#bew] ];
 mini := bew[1];
 for i in [2..#bew] do
     if bew[i] lt mini then
         mini := bew[i];
     end if;
 end for;
 return mini;
end function;



//elements will be sorted with respect to this function
//it compares the vau valuation 
//input: a,b vectors of series, einfo
//output: lt 0  if a lt b, gt 0 if a gt b  

vauvergl := function (a,b,einfo)
 if vau(a,einfo) eq vau(b,einfo) then
         return 0;
 end if; 
 return (vau(a,einfo)- vau(b,einfo));
end function;



//calculates the vector of the leading coefficients with respect
//to vau
//input: vector of sereis, einfo
//vector: over the field
//auch das aus rel

teta2 := function (a, einfo)
 e := LCM(einfo);
 k := vau(a, einfo);
 bew := [Valuation(i) : i in a];
 bew := [bew[i]*e/einfo[i] : i in [1..#a]];
 out := [];
 for i in [1..#a] do
     if not bew[i] eq k then 
         out[i] := Zero(BaseRing(Universe(a)));
     else out[i] := Coefficient(a[i], Integers()!(k*einfo[i]/e) );
     end if;
 end for;
 return Vector(CoefficientRing(Parent(a[1])),out);
end function;



//adds two vectors
//input: a,b
//output: a + b

reihenadd := function(a,b)
 assert #a eq #b;
 out := [];
 ChangeUniverse(~a,Universe(b));
 for i in [1..#a] do
   out[i] := a[i] + b[i];
 end for;
 return out;
end function;



//function to multiply two vectors
//input: a,b sa
//outout: a*b

reihenmulti := function(a,b)
 assert #a eq #b;
 out := [];
 for i in [1..#a] do
   out[i] := a[i] * b[i];
 end for;
 return out;
end function;



//scalar multiplication
//input: alpha skalar,a vector of series
//outout: alpha*a

reihenskalar_kz := function(alpha,a)
 alpha := CoefficientRing(Parent(a[1]))!alpha;
 out := [];
 for i in [1..#a] do
   out[i] :=  alpha * a[i];
 end for;
 return out;
end function;




//scalar multiplication 
//input: alpha scalar,a list of series
//outout: alpha*a

reihenskalar := function(alpha,a)
 LSR := LaurentSeriesRing(Parent(alpha));
 out := [];
 for i in [1..#a] do
   temp := ElementToSequence(a[i]);
   temp := ChangeUniverse(temp,Parent(alpha));
   temp := LSR!temp;
   temp := temp * LSR.1^Valuation(a[i]);
   out[i] :=  alpha * temp;
 end for;
 return out;
end function;



//n th power of a vector
//input: a vektor, n exponent
//output: a^n

reihenpot := function(a,n)
 out := [];
 for i in [1..#a] do
   out[i] := a[i]^n;
 end for;
 return out;
end function;



//function to create the basis out of the transformation matrix
//input: z, T reductionsmatrix, B unmodified basis.
//basis as a list of function field elements
//output: reduced basis = T applied to B

getreducedbasis := function(z,T,B)
 assert Parent(z) eq Universe(B);
 out := [Parent(z) | ];
 for i in [1..#B] do
     temp := 0;
     for j in [1..#B] do
         temp :=temp +  Evaluate(T[j][i],z)*B[j];
     end for;
     out[i] := temp;
 end for;
 return out;
end function;




//main function of this section. it calculates a k[z] basis of
//an holomorphic ring O^S, it is neccessary to call this function
//with a precision m larger than the absolute value of the minimal
//valuation of the series
//input:z, B the basis that will be reduced, m the precision for the
//series
//a k[z] basis of O^S

kzreduktion_pre := function(z,B,m)
 entwickeln := true;
 zusammenfassen := false;
 S := Support (PoleDivisor(Divisor(z)));
 zstrich := dach(z,S,m);
 einfo := [ -Valuation(Divisor(z),P) : P in S];
 e := LCM(einfo);
 //"e,einfo ",e,einfo;
 Kz := PolynomialAlgebra(ConstantField(Parent(z))); Z := Kz.1;
 cmp := function (a,b)
   return vauvergl(a,b,einfo);
 end function;
 //fehlercount:=0;
 repeat
 //fehlercount +:=1;
 //fehlercount;
    b := 0;
    if entwickeln then
      b := 1;
      entwickeln := false;
      T := ScalarMatrix(Kz, #B, 1);
      phi := [dach (b,S,m) : b in B];
    else 
      if zusammenfassen then
        b := 1;
        entwickeln := true;
        zusammenfassen := false;
        B := getreducedbasis(z,T,B);
        B := [a : a in B | not IsZero(a) ];

      else
        for kappa in [0..e-1] do      
            phi, T_0 := Sort(phi,cmp);
            T_0 := Transpose(PermutationMatrix(Kz,T_0));
            T :=T * T_0;
            ind := [Integers() | ];
            for i in [1..#B] do
                if not vau(phi[i],einfo) eq Infinity() and Integers()!vau(phi[i],einfo) mod e eq kappa then
                    Append(~ind,i);
                end if;
            end for;
            //"ind: ", ind;
            if #ind gt 1 then
                phitemp1 := [phi[i] : i in ind];
                phitemp1 := [reihenmulti(reihenpot(zstrich,-((vau(phitemp1[1],einfo) - vau(a,einfo))/e)),a) : a in phitemp1];
              //  "phitemp1 hier: ", phitemp1;
                mat1 := [teta2 (a,einfo) : a in phitemp1];
                ker1 := Kernel(Matrix(mat1));
                if Dimension(ker1) ge 1 then
                rel1 := Representative(Basis(ker1));
                ind1 := [ind[i] : i in [1..#ind] | not rel1[i] eq 0];
                //"ind1: ",ind1;
                j:=1;
                while rel1[j] eq 0 do
                   j+:=1;
                end while;
                j:=ind[j];
                phitemp := [phi[i] : i in ind1 ];
                phitemp := [reihenmulti(reihenpot(zstrich,-((vau(phitemp[1],einfo) - vau(a,einfo))/e)),a) : a in phitemp];
              //  "phitemp: ", phitemp;
                mat2 := [teta2 (a,einfo) : a in phitemp];
                ker := Kernel(Matrix(mat2));
                assert Dimension(ker) eq 1;
                rel := Representative(Basis(ker));
                rel := 1/rel[1]*rel;
                rest := [0 : i in [1..#S]];
                for m in [2..NumberOfColumns(rel)] do
                    rest := reihenadd(rest,reihenskalar_kz(rel[m],phitemp[m]));
                end for;
                xi := reihenadd(phitemp[1], rest);
                //"xi: ", xi;
                if &and[Valuation(a) gt 0 : a in xi]
                    then xi := [0 : a in xi];
                end if;

                b := 1;
                T_1 := ScalarMatrix(Kz, #B, 1);
                for m in [s : s in ind1 | not s eq j] do 
                   // if m in ind1 then
                       T_1[m][j] :=rel[Position(ind1,m)]*Z^Integers()!(-((vau(phi[j],einfo)-vau(phi[m],einfo))/e));
                   // end if;
                end for;
                phi[j] := xi;
                T := T * T_1;
                //"modifizierte basis: ", phi;
              //  "trafomatix: ", T;
                end if;
           end if;
           // end if;
        //end for;
            for j in [1..#phi] do
                for k in [1..#S] do
                    if AbsolutePrecision(phi[j][k]) lt 1 then
                        zusammenfassen := true;
                    end if;
                end for;
            end for;
        if zusammenfassen then
            break;
        end if;
        end for;

        
      end if;
    end if;
 until b eq 0;
 B := getreducedbasis(z,T,B);
 B := [a : a in B | not IsZero(a) ];
 return B;
end function;



//adds the reduced basis to a div_rec
//input: Dmod div_rec
//output: s.a.

get_reduced_mod_basis := procedure(~Dmod)
 vprint emb,1 : "calculating a reduced basis in F2";
 z := Dmod`b_1;
 D := Dmod`D;
 n1 := Dmod`n1;
 S := Dmod`S;
 rrdim := get_dim_for_red(D,z,n1);
 m := praezi_schaetz_fuer_kzred (D,rrdim)+4*Degree(PoleDivisor(Divisor(z)));  
 rb := Basis(rrdim*D);
 B2 := kzreduktion_pre(z,rb,m);
 Dmod`B2 := B2;
end procedure;


/////////////////////////////////////////////////////////////////////
//end lattice reduction
////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////
//begin series expansios
////////////////////////////////////////////////////////////////////


//function to set the precision for the image of the special
//local uniformizer
//input:Dmod div_rec, precision pre nat
//output: set Dmod`pre

set_image_of_lu_pre := procedure(~Dmod,pre)
 Dmod`pre := pre;
end procedure;

//function to expend an element into a laurent serie with respect to a
//special local uniformizer
//input: a function field element, pi the special local uniformizer 
//as a serie in the normal lu, P the place, m the precision

getReiheInSpecialLU := function (a,pi,P,m)
 a_in_x := Expand(a,P : RelPrec := m);
 x_in_pi := Reverse(pi);
 a_in_pi := Evaluate(a_in_x, x_in_pi);
 return a_in_pi;
end function;



//function to calculate the image of pi depending on the parameter
//
//input:Dmod div_rec
//output:Dmod`phi_pi

getphi_mehr_para := function(Dmod,Pmod,i)
 vprint emb,1 : "calculating special local uniformizer";
 bs := Dmod`b_is; 
 pre := Dmod`pre[i];
 s := #Dmod`S;
 Kabc := Dmod`Kab; 
 Rabc := PolynomialAlgebra(BaseRing(Kabc),Rank(Kabc));
 SR := LaurentSeriesRing(Rabc);
 S := PolynomialAlgebra(Kabc,pre-1);
 n := Dmod`n1;
 St := PolynomialAlgebra(S); T := St.1;
 phipi :=  &+ [S.(j)*T^(Dmod`e[i]+j) : j in [1..pre-1] ];
 phipi +:= Kabc.i*T^Dmod`e[i];
 b2reihe := [getReiheInSpecialLU(bi,Dmod`pi1[i],Dmod`S[i],pre+5) : bi in bs];
 stopper := Minimum([pre] cat [AbsolutePrecision(a)-1 : a in b2reihe]);
 b2poly :=[ St!( &+[(Kabc!Coefficient(b2,j))*T^(j+ n*Dmod`e[i]) : j in [Valuation(b2)..stopper]]) : b2 in b2reihe] ;
 beta0 := [ElementToSequence(b2r)[1] : b2r in b2poly ];
 rest := &+ [ Dmod`d2[i]*Kabc.(s + j)*beta0[j] : j in [1..#beta0] ];
 erster_koef :=  Dmod`d2[i]/Pmod`d1*Kabc.i^-n - rest; 
 im := St!(erster_koef*Pmod`d1/Dmod`d2[i]*phipi^n) + St!( &+ [Pmod`d1*Kabc.(s+j)
 *b2poly[j]*phipi^n : j in [1..#b2poly] ] ) - St!( T^(n*Dmod`e[i])) ;
 li := ElementToSequence(im);
 la := [li[j] : j in [1..Dmod`e[i]*n+pre] ];
 I := ideal<S| la>;
gb := GroebnerBasis(I : HomogeneousWeights := false);//???faster???
//gb := GroebnerBasis(I);
 R := quo<S | I>;
 koefs := [Kabc!(R.i) : i in [1..pre-2] ];
 assert &and [Denominator(a) eq 1 : a in koefs];
 koefs := [Rabc!Numerator(a) : a in koefs];
 out := &+ [koefs[j]*SR.1^(Dmod`e[i] + j) : j in [1..#koefs] ];
 out :=(Rabc.i)*SR.1^Dmod`e[i] + out + BigO(SR.1^(Dmod`e[i] + pre-2));
 return out,ChangeUniverse(beta0,CoefficientField(Kabc) );
end function;


//does the same as the method above but in the case of a wildly rammified 
//conorm. this means that you dont work with the special local uniformizer
//but with a normal
getphi_mehr_parawild := function(Dmod,Pmod,i)
 vprint emb,1 : "calculating spacial local uniformizer wild case";
 assert assigned(Dmod`wild);
 assert i in Dmod`wild;
 bs := Dmod`b_is; 
 pre := Dmod`pre[i];
 s := #Dmod`S;
 Kabc := Dmod`Kab; 
 Rabc := PolynomialAlgebra(BaseRing(Kabc),Rank(Kabc));
 SR := LaurentSeriesRing(Rabc);
 S := PolynomialAlgebra(Kabc,pre-1);
 n := Dmod`n1;
 St := PolynomialAlgebra(S); T := St.1;
 phipi :=  &+ [S.(j)*T^(Dmod`e[i]+j) : j in [1..pre-1] ];
 phipi +:= Kabc.i*T^Dmod`e[i];
 b2reihe := [getReiheInSpecialLU(bi,Dmod`pi1[i],Dmod`S[i],pre+5) : bi in bs];
 b1reihe := getReiheInSpecialLU(Dmod`b_1,Dmod`pi1[i],Dmod`S[i],pre+5);
 stopper := Minimum([pre] cat [AbsolutePrecision(a)-1 : a in b2reihe] cat [AbsolutePrecision(b1reihe)-1]);
 b2poly :=[ St!( &+[(Kabc!Coefficient(b2,j))*T^(j+ n*Dmod`e[i]) : j in [Valuation(b2)..stopper]]) : b2 in b2reihe] ;
 b1poly := St!( &+[(Kabc!Coefficient(b1reihe,j))*T^(j+ n*Dmod`e[i]) : j in [Valuation(b1reihe)..stopper]]) ;
 beta0 := [ElementToSequence(b2r)[1] : b2r in b2poly ];
 beta1 := ElementToSequence(b1poly)[1];
 rest := &+ [ Dmod`d2[i]*Kabc.(s + j)*beta0[j] : j in [1..#beta0] ];
 erster_koef :=  (Dmod`d2[i]/Pmod`d1*Kabc.i^-n - rest)/beta1; 
 im := St!(erster_koef*Pmod`d1/Dmod`d2[i]*phipi^n*b1poly) + St!( &+ [Pmod`d1*Kabc.(s+j)
 *b2poly[j]*phipi^n : j in [1..#b2poly] ] ) - St!( T^(n*Dmod`e[i])) ;
 li := ElementToSequence(im);
 la := [li[j] : j in [1..Dmod`e[i]*n+pre] ];
 I := ideal<S| la>;
//gb := GroebnerBasis(I);
 gb := GroebnerBasis(I : HomogeneousWeights := false);
 R := quo<S | I>;
 koefs := [Kabc!(R.i) : i in [1..pre-2] ];
 assert &and [Denominator(a) eq 1 : a in koefs];
 koefs := [Rabc!Numerator(a) : a in koefs];
 out := &+ [koefs[j]*SR.1^(Dmod`e[i] + j) : j in [1..#koefs] ];
 out :=(Rabc.i)*SR.1^Dmod`e[i] + out + BigO(SR.1^(Dmod`e[i] + pre-2));
 return out,ChangeUniverse(beta0,CoefficientField(Kabc) );
end function;




//function to construct a para_rec
//input:Pmod place_rec, Dmod div_rec with several values
//output:M para_rec

make_para_rec := function(Pmod,Dmod)
 M := rec<para_rec | Pmod := Pmod, Dmod := Dmod >;
 phi_pi := [];
 beta0 := [];
 for i in [1..#Dmod`S] do
     if not i in Dmod`wild then
     phi_pii,beta0i := getphi_mehr_para(Dmod,Pmod,i);
     else
     phi_pii,beta0i := getphi_mehr_parawild(Dmod,Pmod,i);
     end if;
     Append(~phi_pi,phi_pii);
     Append(~beta0,beta0i);
 end for;
 M`phi_pi := phi_pi;
 M`beta0 := beta0;
 return M;
end function;




//function to calculate the series expandsion of an element with respect 
//to a special local uniformizer
//input: ele the element as a serie in pi, phi_von_pi the new local unifom
//M para_rec, i in [1..#M`phi_pi] 
//output:element as a serie in phi_von_pi

getReiheInParaLU := function (ele,M,i)
 R := PolynomialAlgebra(CoefficientRing(Parent(ele)),
 #M`Dmod`S + M`Dmod`anzpara - 1);
 SR := LaurentSeriesRing(R);
 ele := SR!ele;
 phi_von_pi := SR!M`phi_pi[i];
 out := Evaluate(ele,phi_von_pi);
 return out;
end function;



//function to calculate a vector of series expansions for an element
//of F1 or F2
//for elements of F1, the entries of the vector consists of series
//in phi(pi), for elements of F2 the entries does not depend on
//any parameter
//input:M para_rec with M`phi_pi assigned, a element of F1 of F2,
//output: vector of series

getReihenVektor := function(a,M)
 case Parent(a) :
     when FunctionField(M`Pmod`P):
         temp := getReiheInSpecialLU(a,M`Pmod`pi,M`Pmod`P,M`Pmod`m);
         out := [getReiheInParaLU(temp,M,i) : i in [1..#M`Dmod`S] ];
     when FunctionField(M`Dmod`D):
         out := [getReiheInSpecialLU(a,M`Dmod`pi1[i],M`Dmod`S[i],M`Dmod`m) : i in [1..#M`Dmod`S] ];
     else
         "a has to be in one of the function fields";
 end case;
 return out;
end function; 

////////////////////////////////////////////////////////////////////
//end series expansions
///////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////
//begin calcuating the parameter pt1
//////////////////////////////////////////////////////////////////////


//function to update the ideal
//ideal is in R = k[co1,..,cos,invco1,..,invcos,b,c,..]
//input: I the ideal that is going to be updated, gl the set of
//equations that define the ideal (every equation, not only the new ones)
//R the ring in which the ideal lives, M para_rec
//output: I is changed.

updateideal := procedure(~I,gl,R,M)
 d2 := M`Dmod`d2;
 d1 := M`Pmod`d1;
 beta0 := M`beta0;
 m := Rank(R) - M`Dmod`anzpara +1 ;
 s := m div 2;
 assert s eq #d2;
 id := [R | R.i * R.(s + i) -1 : i in [1..s] ];
 nume := [R.i : i in [1..s] ];
 dene := [R.(s+i) : i in [1..s] ];
 for i in [M`Dmod`anzpara - 1..1 by -1] do
     nume cat:= [R.(Rank(R)-i+1)];
     dene cat:= [R.(Rank(R)-i+1)];
 end for;
 for i in [1..#gl] do
     num := Numerator(gl[i]);
     den := Denominator(gl[i]);
     temp := Evaluate(num,nume)*Evaluate(den,dene);
     Append(~id,temp);
 end for;
 for j in [2..#d2] do
     rest1 := 0;
     restj := 0;
     for k in [1..#beta0[j]] do
         rest1 +:= d2[1]*beta0[1][k]*R.(2*s+k);
         restj +:= d2[j]*beta0[j][k]*R.(2*s+k);
     end for;
     temp := (d2[1]/d1*R.(s+1)^M`Dmod`n1 - rest1) - (d2[j]/d1*R.(s+j)^M`Dmod`n1
     - restj);
     Append(~id,temp);
 end for;
 I := ideal<R| id>;
end procedure;




//function to update the ideal shall replace updateidal, because this may
//be faster
//ideal is in R = k[co1,..,cos,invco1,..,invcos,b,c,..]
//input: I the ideal that is going to be updated, gl the set of
//new equations that define the ideal 
//R the ring in which the ideal lives, M para_rec
//output: I is changed.

updateideal2 := procedure(~I,gl,R,M)
 d2 := M`Dmod`d2;
 d1 := M`Pmod`d1;
 beta0 := M`beta0;
 m := Rank(R) - M`Dmod`anzpara +1 ;
 s := m div 2;
 assert s eq #d2;
 id := [R |  ];
 nume := [R.i : i in [1..s] ];
 dene := [R.(s+i) : i in [1..s] ];
 for i in [M`Dmod`anzpara - 1..1 by -1] do
     nume cat:= [R.(Rank(R)-i+1)];
     dene cat:= [R.(Rank(R)-i+1)];
 end for;
 for i in [1..#gl] do
     num := Numerator(gl[i]);
     den := Denominator(gl[i]);
     temp := Evaluate(num,nume)*Evaluate(den,dene);
     Append(~id,temp);
 end for;
 I := ideal<R|I, id>;
end procedure;


//function to coerce an elemten of the multivariat rational function field
//into the ring
//input: a element of M`Dmod`Kab, M
//output: element of M`R
kab2r := function(a,M)
 m := Rank(M`R) - M`Dmod`anzpara +1 ;
 s := m div 2;
 nume := [M`R.i : i in [1..s] ];
 dene := [M`R.(s+i) : i in [1..s] ];
 for i in [M`Dmod`anzpara - 1..1 by -1] do
     nume cat:= [M`R.(Rank(M`R)-i+1)];
     dene cat:= [M`R.(Rank(M`R)-i+1)];
 end for;
 num := Numerator(a);
 den := Denominator(a);
 a := Evaluate(num,nume)*Evaluate(den,dene);
 return a;
end function;

//and vice versa
//input: a element of M`R, M
//output: function for the coercion

r2kabfunc := function(M)
 K := M`Dmod`Kab;
 s := Rank(K);
 r := M`Dmod`anzpara - 1;
 genim := [K.i : i in [1..s-r] ] cat [1/K.i : i in [1..s-r] ];
 for m in [r..1 by -1] do
     genim cat:= [K.(s-m+1)];
 end for;
 f := hom<M`R -> K | genim>;
 return f;
end function;


//function to coerce a matrix
//input: mat matrix over k(co1,..,cos,b), 
//R = k[co1,..,cos,invco1,..,invcos,b,c,..]
//output:matrix over k[co1,..,cos,invco1,..,invcos,b,c,..]/(coi*invcoic-1)

mattrafo1 := function(mat,R,M)
 m := Rank(R) - M`Dmod`anzpara +1;
 s := m div 2;
 J := ideal<R | >;
 nume := [R.i : i in [1..s] ];
 dene := [R.(s+i) : i in [1..s] ];
 for j in [M`Dmod`anzpara-1..1 by -1] do
     nume cat:= [R.(Rank(R)-j+1)];
     dene cat:= [R.(Rank(R)-j+1)];
 end for;
 updateideal(~J,[],R,M);
 Rr := quo<R | J>;
 N := ZeroMatrix(Rr,NumberOfRows(mat),NumberOfColumns(mat));
 for i in [1..NumberOfRows(mat)] do
     for j in [1..NumberOfColumns(mat)] do
         num := Numerator(mat[i][j]);
         den := Denominator(mat[i][j]);
        // "nenner: ",den;
         N[i][j] := Rr!(Evaluate(num,nume)*Evaluate(den,dene));
     end for;
 end for;
 return N;
end function;



//function that gets a matrix over k[...]/(ci*invci-1) and transforms it 
//into a matrix over k[....]/I macht
//input: matrix M, ideal I, R= k[co1,..cos,invs..,,b..]
//output matrix over R/I

mattrafo2 := function(M,I,R)
 // "I in mattrafo2: ", I;
 Rr := quo<R | I>;
 m := Rank(R);
 s := m div 2;
 genim := [Rr.i : i in [1..m] ];
 f := hom<BaseRing(M) -> Rr | genim >;
 N := ZeroMatrix(Rr,NumberOfRows(M),NumberOfColumns(M));
 for i in [1..NumberOfRows(M)] do
     for j in [1..NumberOfColumns(M)] do
         N[i][j] := f(M[i][j]);
     end for;
 end for;
 return N;
end function;


//function that lifts a matix over k[co1,..cos,invs.b,...]/I to a matrix 
//over k(co1,..cos,b,...) liftet
//input: mat matrix M para_rec, K := k(co1,..cos,b,...)
//output: the lifted matrix

mattrafo3 := function(mat,M,K)
 s := Rank(K);
 r := M`Dmod`anzpara - 1;
 genim := [K.i : i in [1..s-r] ] cat [1/K.i : i in [1..s-r] ];
 for m in [r..1 by -1] do
     genim cat:= [K.(s-m+1)];
 end for;
 f := hom<BaseRing(mat) -> K | genim>;
 N := ZeroMatrix(K,NumberOfRows(mat),NumberOfColumns(mat));
 for i in [1..NumberOfRows(mat)] do
     for j in [1..NumberOfColumns(mat)] do
         N[i][j] := f(mat[i][j]);
     end for;
 end for;
 return N;
end function;



//function to calculate a vector of the leading (with respect
//to vau) coefficients of a vector of series
//input: series vector a, einfo , K1 base ring
//output: vector of elements of K1

teta5 := function(a,einfo,K1)
 e := LCM(einfo);
 k := vau(a,einfo);
 bew := [Valuation(i) : i in a];
 bew := [bew[i]*e/einfo[i] : i in [1..#a]];
 out := [K1| ];
 for i in [1..#a] do
     if not bew[i] eq k then 
         out[i] := 0;
     else 
        //"seine eltern: ",Parent(Coefficient(a[i], Integers()!(k*einfo[i]/e)));
         out[i] := Coefficient(a[i], Integers()!(k*einfo[i]/e) );
     end if;
 end for;
 return Vector(K1,out);
end function;




//function to execute one reduction step and change the 
//variables
//input: T  matrix that discribes the steps that have been done
//L the intergral basis which is used for the reduction, x 
//element which will be reduced, 
//gleichungen sequence of equations,
// M para_rec 
//output: several velues possibly changed

reduktionsschritt := procedure(~x,L,~Ls,~T,~gleichungen,~I,z,M,e,einfo,null,Kz,R,bound)
 Kz<Z> := Kz;
 mini := Integers()!vau(x,einfo);
 if mini lt bound-1 then
     ind := [Integers() | ];
     for i in [1..#L] do
         if (Integers()!vau(L[i],einfo) - mini) mod e eq 0 and vau(L[i],einfo) ge mini then
             Append(~ind,i);
         end if;
     end for;
     Ltemp := [L[i] : i in ind];
     Ltemp := [reihenmulti(reihenpot(z,-((vau(x,einfo) - vau(a,einfo))/e)),a) : a in Ltemp ];
     mat := Matrix([teta5(a,einfo,CoefficientRing(Parent(x[1]))) : a in (Ltemp cat [x]) ]);
     ker := Kernel(mat);
     if Dimension(ker) ge 1 then
         rel := Representative(Basis(ker));
         assert not rel[#Ltemp+1] eq 0;
         rel := 1/rel[#Ltemp+1] * rel;
         rest := null;
         for m in [1..NumberOfColumns(rel)-1] do
             rest := reihenadd(rest,reihenskalar(rel[m],Ltemp[m]));
         end for;
         xi := reihenadd(x,rest);
         T_1 := ScalarMatrix(Kz,#Ls,1);
         for m in [s : s in ind | not s eq #Ls] do
             T_1[m][#Ls] := rel[Position(ind,m)] * Z^Integers()!(-((vau(x,einfo)-vau(Ls[m],einfo))/e));
         end for;
         x := xi;
         Ls[#Ls] := xi;
         T := T * T_1;       
     else
         xaktiv := [i : i in [1..#x] | Valuation(x[i])*e/einfo[i] eq mini ];
         yaktiv := &cat [[i : i in [1..#x] | Valuation(a[i])*e/einfo[i] eq mini ] : a in Ltemp ];
         raus := [i : i in xaktiv | not i in yaktiv];
         if #raus ge 1 then
             for i in raus do
                 Append(~gleichungen,LeadingCoefficient(x[i]));
                 updateideal2(~I,[LeadingCoefficient(x[i])],R,M);
                 x[i] := x[i] - LeadingTerm(x[i]);
             end for;
             Ls[#Ls] := x;
         else
             n := Minimum([NumberOfRows(mat),NumberOfColumns(mat)]);
             gl := Minors(mat,n);
             gleichungen := gleichungen cat gl;
             updateideal2(~I,gl,R,M);
             if Dimension(I) ge 0 then
               // "vor erster trafo: ", mat;
                 mattemp := mattrafo1(mat,R,M);
               //  "vor zweiter trafo: ", mattemp;
                 mattemp := mattrafo2(mattemp,I,R);
               //  "vor dritter trafo: ", mattemp;
                 mattemp := mattrafo3(mattemp,M,BaseRing(mat));
               //  "die hinundherumgewandelte matrix:  ", mattemp;
                 ker := Kernel(mattemp);
                 rel := Basis(ker);
                 if Dimension(ker) ge 1 then
                     pos_x := NumberOfColumns(rel[1]);   
                     if pos_x ge 1 then
                         rel1 := [k : k in rel | not k[pos_x] eq 0 ];
                     else
                         rel1 := [];
                         "something happend that shouldnt..";
                     end if;
                     if #rel1 ge 1 then
                         rel := Representative(rel1);
                         rel := 1/rel[pos_x]*rel;
                         //"relation die benutzt wird:  ", rel;
                         x_neu := null;
                         assert #ind eq NumberOfColumns(rel)-1;
                         for j in [1..NumberOfColumns(rel)-1] do
                             x_neu := reihenadd(x_neu ,reihenskalar(rel[j],reihenmulti(reihenpot(z,-((vau(x,einfo) - vau(Ls[ind[j]],einfo))/e)),Ls[ind[j]])));
                         end for;
                         x_neu := reihenadd(x_neu,Ls[#Ls]);
                         if vektorbewert2(x_neu) eq mini then
                             for j in [1..#x_neu] do
                                 if Valuation(x_neu[j]) eq mini then
                                     x_neu[j] := x_neu[j] - LeadingTerm(x_neu[j]);
                                 end if;
                             end for;
                         end if;
                         T_1 := ScalarMatrix(Kz,#Ls,1);
                         for m in [1..NumberOfColumns(rel)-1] do
                             T_1[ind[m]][#Ls] := rel[m]*Z^Integers()!(-((vau(x,einfo)-vau(Ls[ind[m]],einfo))/e));
                         end for;
                         T := T * T_1;
                         Ls[#Ls] := x_neu;
                         x := x_neu;
                     else
                         "something happend that shouldnt";
                     end if;
                 else
                     "something happend that shouldnt";
                 end if;
             end if;
         end if;
     end if;
 end if;
end procedure;



//function to calculate the images of the xi by doing some lattice reduction
//input: xli seq of vectors over a laurent series field with some parameter,
// L basis of lattice 
//z s.t  o^s is a k[z] modul 
//M para_rec 
//output:das ideal generated by the equations for the parameter and
//the images of the xi

paraberech_kz_red_alle := function(xli,L,z,M,bound)
 Lsli :=[L cat [x] : x in xli ];
 Kz := PolynomialAlgebra(CoefficientRing(Parent(xli[1][1]))); Z := Kz.1;
 Tli := [ScalarMatrix(Kz,#L+1,1) : j in [1..#xli] ];
 R := M`R;
 //R := PolynomialAlgebra(CoefficientRing(Parent(L[1][1])),2*Rank(CoefficientRing(Parent(x[1])))-1);
 I := ideal<R | >;
 updateideal(~I,[],R,M);
 null := [ Parent(xli[1][1]) | 0 : i in [1..#xli[1]] ];
 gleichungen := [ CoefficientRing(Parent(xli[1][1])) | ];
 einfo := [-Valuation(z[i]) : i in [1..#z] ];
 e := LCM(einfo);
 count :=1;
 repeat
     bewert := [Integers() | vektorbewert2(x) : x in xli ];
     //"bewert: ",bewert;
     //mini,k := Minimum(bewert);
     redbar := [i : i in [1..#xli] | vektorbewert2(xli[i]) lt bound[i] ];
     if #redbar eq 0 then
         break;
     end if;
     mini,k := Minimum([Integers() | vektorbewert2(xli[i]) : i in redbar]);
     k := redbar[k];
     reduktionsschritt(~xli[k],L,~Lsli[k],~Tli[k],~gleichungen,~I,z,M,e,einfo,null,Kz,R,bound[k]);
     //updateideal(~I,gleichungen,R,M);
         count +:=1;
     //"dim: ", Dimension(I);
     bewertneu := [Integers() | vektorbewert2(x) : x in xli ];
 until (Dimension(I) le 0 and mini gt 0 ) or Dimension(I) lt 0
  or bewertneu eq bewert;

 return gleichungen,Tli,I;
end function;



//main method for the first part of calculating the parameter
//the elements of the basis of o^p and of o^s are identified with
//elements of a lattice and its is calculated for which parameter one 
//can approximate some by the other..
//input: M para_rec
//output: M`gleichungen, M`phi_x

schritt1 := procedure(~M)
 vprint emb,1 : "starting step 1";
 s := #M`Dmod`S;
 x := [M`Pmod`x_1] cat [M`Pmod`B1[i] : i in [2..#M`Pmod`B1 ] ];
 xli := [getReihenVektor(a,M) : a in x];
 L := [getReihenVektor(a,M) : a in M`Dmod`B2];
 zr := getReihenVektor(M`Dmod`b_1,M);
 R := PolynomialAlgebra(ConstantField(FunctionField(M`Pmod`P))
 ,2*s + M`Dmod`anzpara -1 );
 M`R := R;
 M`r2kab := r2kabfunc(M);
 I1 := ideal<R| >;
 prezis := [[AbsolutePrecision(a) : a in xv] : xv in xli];
 prezis := [Minimum(a) : a in prezis];
 bound := [Minimum([ a : a in M`Dmod`pre])  -1 - M`Pmod`n[#M`Pmod`n],Minimum(prezis)-1];   //theoretically the minimum should be taken by the 
                   //min of prezis but i am not absolutly sure about this
 bound := [Minimum( [Minimum([ a : a in M`Dmod`pre])  -1 - M`Pmod`n[i], prezis[i] ]) : i in [1..#prezis] ];
 vprint embpre,1 :"bound: ";
 vprint embpre,1 : bound;
 gleichungen,Tli,I:=paraberech_kz_red_alle(xli,L,zr,M,bound);
 phi_x := [];
 for T in Tli do    
     Append(~phi_x,-1*Transpose(T)[NumberOfColumns(T)]);
 end for;
 M`gleichungen := gleichungen;
 updateideal(~I1,gleichungen,R,M);
 M`phi_x := phi_x;
 M`I := I1;
 vprint emb,1 : "dimension of the ideal after step 1";
 vprint emb,1 : Dimension(I1);
end procedure;


//////////////////////////////////////////////////////////////////////
//end calculating parameter pt.1
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//begin parameter calculation pt.2
//////////////////////////////////////////////////////////////////////


//function to calculate the k basis of a k[z] module up to a certain
//degree
//input: z , B k[z] basis of o^s, d maximal degree
//output: k basis  z^i*B[j] with i le deg 

gradbasis := function(z,B,d)
 out := [Parent(z) |  z^j*b : j in [0..d], b in B | j le d ];
 return out;
end function;


//calculates the k basis of a k[z] module up to a certain valuation
//input: z, B k[z] basis of O^S, M rec, d maximal valuation
//output: k basis z^i B[j] and sequence of polynomials with the information
//about the representation of each k basis element

gradbasis_val := function(z,B,M,d)
 out := [ [* z^j*B[i] ,[j,i] *] : j in [0..d] , i in [1..#B] | -vau2(z^j*B[i],M) le d ];
 ba := [a[1] : a in out ];
 rep := [a[2] : a in out ];
 return ba,rep;
end function;


gradbasis_val_F1 := function(z,B,M,d)
 out := [ [* z^j*B[i] ,[j,i] *] : j in [0..d] , i in [1..#B] | -Valuation(z^j*B[i],M`Pmod`P) le d ];
 ba := [a[1] : a in out ];
 rep := [a[2] : a in out ];
 return ba,rep;
end function;


// replaced by the version below that is maybe faster
//function to calculate a representation of an element of F1 in 
//the k[x1] basis of o^p
//input: a element of F_1, para_rec M
//output:list of polynomials [p1,..,pn] st a = p1(x1)*b1+..+pn(x1)bn

getRepresentationInF_1old := function(a,M)
 x_1 := M`Pmod`x_1;
 assert Parent(x_1) eq Parent(a);
 B := M`Pmod`B1;
 K := ConstantField(Parent(x_1));
 //Kp := PolynomialAlgebra(K,#B + 1);
 Kp := PolynomialAlgebra(K);
 out := 0;
 i := -1;
 repeat
     i +:=1;
     //i;
     kBasis := gradbasis(x_1,B,i);
     rel := Relations(kBasis cat [a],K);
 until Dimension(rel) ge 1;
 rel := Representative(Basis(rel));
 rel := -1/rel[NumberOfColumns(rel)]*rel;
 out := [Kp | 0 : i in [1..#B] ];
 for j in [1..NumberOfColumns(rel)-1 ] do
     out[Ceiling(j/(i+1))] := out[Ceiling(j/(i+1))] + rel[j]*Kp.1^(((j-1) mod (i+1)));
 end for;
 // out := &+ [ out[i]*Kp.(i+1) : i in [1..#out] ];
 return out;
end function; 



//function to calculate a representation of an element of F1 in 
//the k[x1] basis of o^p
//input: a element of F_1, para_rec M
//output:list of polynomials [p1,..,pn] st a = p1(x1)*b1+..+pn(x1)bn

getRepresentationInF_1 := function(a,M)
 x_1 := M`Pmod`x_1;
 assert Parent(x_1) eq Parent(a);
 B := M`Pmod`B1;
 K := ConstantField(Parent(x_1));
 //Kp := PolynomialAlgebra(K,#B + 1);
 Kp := PolynomialAlgebra(K);
 out := 0;
 i := -Valuation(a,M`Pmod`P) - 1;
 repeat
     //i;
     i +:=1;
     kBasis,rep := gradbasis_val_F1(x_1,B,M,i);
     rel := Relations(kBasis cat [a],K);
 until Dimension(rel) ge 1;
 rel := Representative(Basis(rel));
 rel := -1/rel[NumberOfColumns(rel)]*rel;
 out := [Kp | 0 : i in [1..#B] ];
 for j in [1..NumberOfColumns(rel)-1 ] do
     out[rep[j][2]] +:= rel[j]*Kp.1^(rep[j][1]);
 end for;
 //out;
 //getRepresentationInF_1old(a,M);
 return out;
end function; 


//replace this by the faster? version below
//function that does the same as the function above but will work
//also for elements that are not in o^p
//input: a an element of F_1, para_rec M
//output: two sequences of polynomials [p1,..,pn], [q1,..,qn] st.
//a = p1(x1)/q1(x1)*b1+..+pn(x1)/qn(xn)*bn

getRepresentationInF_1_neub := function(a,M)
 x_1 := M`Pmod`x_1;
 //assert Parent(x_1) eq Parent(a);
 B := M`Pmod`B1;
 K := ConstantField(Parent(x_1));
 Kp := PolynomialAlgebra(K);
 numout := 0;
 denout := 0;
 i := -1;
 repeat
     i +:=1;
     kBasisnum := gradbasis(x_1,B,i);
     kBasisden := gradbasis(x_1,B,i);
     L := [b : b in kBasisnum ] cat [-a*b : b in kBasisden ];
     rel := Relations(L,K);
 until  Dimension(rel) ge 1;
 rel := ElementToSequence(Representative(Basis(rel)));
 rel := Partition(rel,#rel div 2);

 numout := [Kp | 0 : i in [1..#B] ];
 denout := [Kp | 0 : i in [1..#B] ];
 for j in [1..#rel[1]] do
    numout[Ceiling(j/(i+1))] := numout[Ceiling(j/(i+1))] + rel[1][j]*Kp.1^(((j-1) mod (i+1)));
 end for;
 for j in [1..#rel[2]] do
     denout[Ceiling(j/(i+1))] := denout[Ceiling(j/(i+1))] + rel[2][j]*Kp.1^(((j-1) mod (i+1)));
 end for;
 return numout, denout;
end function; 



//function that does the same as the function above but will work
//also for elements that are not in o^p
//input: a an element of F_1, para_rec M
//output: two sequences of polynomials [p1,..,pn], [q1,..,qn] st.
//a = p1(x1)/q1(x1)*b1+..+pn(x1)/qn(xn)*bn

getRepresentationInF_1_neu := function(a,M)
 x_1 := M`Pmod`x_1;
 //assert Parent(x_1) eq Parent(a);
 B := M`Pmod`B1;
 K := ConstantField(Parent(x_1));
 Kp := PolynomialAlgebra(K);
 numout := 0;
 denout := 0;
 d := -Valuation(a,M`Pmod`P);
 i := Maximum(0,-d) - 1;
 repeat
     i +:=1;
     kBasisnum,repnum := gradbasis_val_F1(x_1,B,M,d+i);
     kBasisden,repden := gradbasis_val_F1(x_1,B,M,i);
     L := [b : b in kBasisnum ] cat [-a*b : b in kBasisden ];
     rel := Relations(L,K);
 until  Dimension(rel) ge 1;
 rel := Representative(Basis(rel));
 //rel := Partition(rel,#rel div 2);

 numout := [Kp | 0 : i in [1..#B] ];
 denout := [Kp | 0 : i in [1..#B] ];
 for j in [1..#repnum] do
    numout[repnum[j][2]] +:=  rel[j]*Kp.1^(repnum[j][1]);
 end for;
 for j in [1..#repden] do
     denout[repden[j][2]] +:= rel[j+#repnum]*Kp.1^(repden[j][1]);
 end for;
 //vergl
// numoutb,denoutb := getRepresentationInF_1_neub(a,M);
// numout;
// numoutb;
// denout;
// denoutb;
 //vergl
 return numout, denout;
end function; 





//simplifies the representation of the images of the xi by reducing the
//coefficents that depend on the indeterminates in phi_x modulo the
//relations one has calculated in schritt1
//input:M
//output:M with M`phi_x modified

simple_rep := procedure(~M)
 Q := quo<M`R | M`I>;
 KabZ := Parent(M`phi_x[1][1]);
 phi_x := [[] : i in [1..#M`phi_x] ];
 for i in [1..#M`phi_x] do
    for j in [1..NumberOfColumns(M`phi_x[i]) ] do
       koefs := Eltseq(M`phi_x[i][j]);
       rkoefs := [Q!(M`R!(kab2r(a,M))) : a in koefs ];
       skoefs := [M`r2kab(M`R!a) : a in rkoefs];
       phi_x[i][j] := KabZ!skoefs;
    end for;
 end for;
 Vs :=Parent(M`phi_x[1]);
 M`phi_x := [Vs!a : a in phi_x];
end procedure;





//function to calculate a representation as a param. funcion field element
//input: vector phi_xi this is one that is calculated by the reduction algo 
//Basis B in which phi_xi shall be expressed, rr_oder_os bool if
//riemann roch basis (true) or reduced (allways used) 
//basis of o^s, z 
//output: element phi_xi  as a parametericed funktionen field
//element

getphi_von_x_i_inF2 := function(phi_xi,M,rr_oder_os)
 s := #M`Dmod`S;
 drueber := RationalFunctionField(Parent(M`Dmod`B2[1]),s+M`Dmod`anzpara - 1 );
 polyring := PolynomialAlgebra(RationalFunctionField(FunctionField(M`Dmod`D),
 s+M`Dmod`anzpara- 1 ));
 out := 0;
 n := M`Pmod`n;
 k := NumberOfColumns(phi_xi);
 posi := 0;
 if rr_oder_os then
     for j in [1..#M`phi_x] do
         if phi_xi cmpeq M`phi_x[j] then 
            posi := j;
         end if;
     end for;
     if posi eq 0 then
         "something happened that shouldnt";
     else
         B := Basis(n[posi]*M`Dmod`D);
     end if;
     for i in [1..k-1] do
         out +:=drueber!phi_xi[i]*drueber!B[i];
     end for;
 else
     B := M`Dmod`B2;
     z := M`Dmod`b_1;
     for i in [1..k-1] do       
         out +:= drueber!Evaluate(polyring!phi_xi[i],z)*drueber!B[i];
     end for;
 end if;
 return out;
end function;


forward simple_rep_pt2;

//replaced by a possibly faster version
//this function calculates a representation of an element of F2 that depends
//on the parameter as a k(parameter)[z] linear combination in the
//basis of o^s
//input:a  element given by getphi_von.. , this means a multi-
//variate polynomalring over F2, B the k[z] basis of o^s, z 
//M para_rec
//output:sequence of coeffs in k(para)

getRepresentationInF_2b := function(a,B,M,z)
 assert ConstantField(Parent(a)) eq Parent(z);
 //a := simple_rep_pt2(a,M);
 s := #Support(PoleDivisor(Divisor(z)));
 F := Parent(z);
 K := ConstantField(F);
 Kp := RationalFunctionField(K,s+M`Dmod`anzpara-1);
 Kpz := PolynomialAlgebra(Kp); Z := Kpz.1;
 Fneu ,einbett := ConstantFieldExtension(F,Kp);
 //assert Fneu eq M`Fneu;
 num := Numerator(a);
 den := Denominator(a);
 nummon := Monomials(num);
 denmon := Monomials(den);
 nummonFneu := [Kp!i : i in nummon];
 denmonFneu := [Kp!i : i in denmon];
 //coefs := [nummon[i]*denmon[i] : i in [1..#nummon] ];
 moncoefsnum := [einbett(MonomialCoefficient(num,a)) : a in nummon ];
 moncoefsden := [einbett(MonomialCoefficient(den,a)) : a in denmon ];
 numFneu := &+ [Fneu!(moncoefsnum[i]*nummonFneu[i]) : i in [1..#nummon] ];
 denFneu := &+ [Fneu!(moncoefsden[i]*denmonFneu[i]) : i in [1..#denmon] ];
 astrich := numFneu/denFneu;
 out := [Kpz | 0 : i in [1..#B] ];
 i := -1;
 repeat
     i +:=1;
     kcbbasis := gradbasis(z,B,i);
     kcbbasis := [einbett(b) : b in kcbbasis ];
     rel := Relations(kcbbasis cat [astrich], Kp);
     //if i ge 25 then
     //    "probleme beim relationen finden";
     //    break;
     //end if;
 until Dimension(rel) ge 1;
 if Dimension(rel) gt 1 then
     "zu viele relationen, das darf nicht passieren";
 else
     rel := Representative(Basis(rel));
     rel := -1/rel[NumberOfColumns(rel)]*rel;
     for j in [1..NumberOfColumns(rel)-1 ] do
         out[Ceiling(j/(i+1))] := out[Ceiling(j/(i+1))] + rel[j]*Z^(((j-1) mod (i+1)));
     end for;    
 end if;
 return out;
end function;





//this function calculates a representation of an element of F2 that depends
//on the parameter as a k(parameter)[z] linear combination in the
//basis of o^s
//input:a  element given by getphi_von.. , this means a multi-
//variate polynomalring over F2, B the k[z] basis of o^s, z 
//M para_rec,d an approximation for the degree of the element
//output:sequence of coeffs in k(para)

getRepresentationInF_2 := function(a,B,M,z,d)
 assert ConstantField(Parent(a)) eq Parent(z);
 //a := simple_rep_pt2(a,M);
 s := #Support(PoleDivisor(Divisor(z)));
 F := Parent(z);
 K := ConstantField(F);
 Kp := RationalFunctionField(K,s+M`Dmod`anzpara-1);
 Kpz := PolynomialAlgebra(Kp); Z := Kpz.1;
 Fneu ,einbett := ConstantFieldExtension(F,Kp);
 //assert Fneu eq M`Fneu;
 num := Numerator(a);
 den := Denominator(a);
 nummon := Monomials(num);
 denmon := Monomials(den);
 nummonFneu := [Kp!i : i in nummon];
 denmonFneu := [Kp!i : i in denmon];
 //coefs := [nummon[i]*denmon[i] : i in [1..#nummon] ];
 moncoefsnum := [einbett(MonomialCoefficient(num,a)) : a in nummon ];
 moncoefsden := [einbett(MonomialCoefficient(den,a)) : a in denmon ];
 numFneu := &+ [Fneu!(moncoefsnum[i]*nummonFneu[i]) : i in [1..#nummon] ];
 denFneu := &+ [Fneu!(moncoefsden[i]*denmonFneu[i]) : i in [1..#denmon] ];
 astrich := numFneu/denFneu;
 out := [Kpz | 0 : i in [1..#B] ];
 i := d-1;
 repeat
     i +:=1;
     kcbbasis,rep := gradbasis_val(z,B,M,i);
     kcbbasis := [einbett(b) : b in kcbbasis ];
     rel := Relations(kcbbasis cat [astrich], Kp);
     //if i ge 25 then
     //    "probleme beim relationen finden";
     //    break;
     //end if;
 until Dimension(rel) ge 1;
 if Dimension(rel) gt 1 then
     "this shouldnt happen";
 else
     rel := Representative(Basis(rel));
     rel := -1/rel[NumberOfColumns(rel)]*rel;
     for j in [1..NumberOfColumns(rel)-1 ] do
         out[rep[j][2]] +:=  rel[j]*Z^(rep[j][1]);
     end for;    
 end if;
 return out;
end function;






//simplifies the representation of an element that depends on some
//parameter by reducing modulo the relations
//input:an element that is produced by phi_von_xixj, this means an
//element of a multivariat rational function field over a function field, M
//output:the same element but in a hopefully simplified representation
//doesnt seem to speed things up.

simple_rep_pt2 := function(a,M)
 num := Numerator(a);
 den := Denominator(a);
 numco,nummo := CoefficientsAndMonomials(num);
 denco,denmo := CoefficientsAndMonomials(den);
 Q := quo<M`R | M`I>;
 nummo := [Q!(M`R!(kab2r(M`Dmod`Kab!i,M))) : i in nummo];
 denmo := [Q!(M`R!(kab2r(M`Dmod`Kab!i,M))) : i in denmo];
 nummo := [Parent(a)!(M`r2kab(M`R!i)) : i in nummo];
 denmo := [Parent(a)!(M`r2kab(M`R!i)) : i in denmo];
 num := &+ [numco[i]*nummo[i] : i in [1..#numco] ];
 den := &+ [denco[i]*denmo[i] : i in [1..#denco] ];
 return (num/den);
end function;



//this funktion calculates a representation of phi(x_i*x_j) 
//in the k[z] basis of o^s
//input:i,j st B1[i]=x_i and B1[j]=x_j, 
//z as an element of F2
//B1 the basis of o^p in F1, B2  basis of o^s in F2
//x_1 element that belongs to B1 
// rr_oder_os bool to decide which basis to use
//output: coefs of the representation of phi(x_i*x_j) in the k[z] basis B2 

phi_von_xixj := function(i,j,M,rr_oder_os)
 s := #M`Dmod`S;
 B1 := M`Pmod`B1;
 B2 := M`Dmod`B2;
 z := M`Dmod`b_1;
 b_is := M`Dmod`b_is;
 assert #b_is eq M`Dmod`anzpara-1;
 phi_x := M`phi_x;
 beta0 := M`beta0;
 //Fneu := M`Fneu;
 a := B1[i]*B1[j];
 vp := -Valuation(a,M`Pmod`P);
 d := LCM(M`Dmod`e)*vp;
 n := M`Pmod`n;
 Ftemp := RationalFunctionField(FunctionField(M`Dmod`D),s+M`Dmod`anzpara-1);
 Ftempx := PolynomialAlgebra(Ftemp);
 temp := getRepresentationInF_1(a,M);
 im_x := M`Dmod`d2[1]/M`Pmod`d1*Ftemp.1^(-n[1]);
 for i in [1..#beta0[1]] do
     im_x -:= M`Dmod`d2[1]*beta0[1][i]*Ftemp.(s+i);
 end for;
 im_x *:= z;
 for i in [1..#b_is] do
     im_x +:= Ftemp.(s+i)*b_is[i];
 end for; 
 out := Evaluate(Ftempx!temp[1],im_x);
 for l in [2..#temp] do
     q := Ftempx!temp[l];
     out +:=  Evaluate(q,im_x)*getphi_von_x_i_inF2(phi_x[l],M,rr_oder_os);
 end for;
 //"seine eltern:  ", Parent(out);
 return getRepresentationInF_2(out,B2,M,z,d);  //und das dauert
end function;



//calculate phi(x_i)*phi(x_j) represented in the k[z] basis of o^s
//input: i,j for x_i and x_j, M para_rec, rr_oder_os bool
//output: liste der koefs der darstellung von phi(x_i)*phi(x_j) so wie oben

phi_von_xi_phi_von_xj := function(i,j,M,rr_oder_os)
 phixi := getphi_von_x_i_inF2(M`phi_x[i],M,rr_oder_os);
 phixj := getphi_von_x_i_inF2(M`phi_x[j],M,rr_oder_os);
 a := phixi * phixj;
 e := LCM(M`Dmod`e);
 vp := -Valuation(M`Pmod`B1[i]*M`Pmod`B1[j], M`Pmod`P);
 d := e*vp;
 return getRepresentationInF_2(a,M`Dmod`B2,M,M`Dmod`b_1,d);
end function;



//compares the representations of phi(x_i*x_j) and phi(x_i)*phi(x_j) to find  
//equations for the parameter
//input: L1, L2 squences of param. polynomials over k(a,b,c..)
//output: seq. of equations

vergleich_der_koefs := function(L1,L2)
 //assert Universe(L1) eq Universe(L2);
 assert #L1 eq #L2;
 gleichungen := [];
 for k in [1..#L1] do
     temp := L1[k] - L2[k];
     li := ElementToSequence(temp);
     for coef in li do
         if not coef eq 0 then
             Append(~gleichungen,coef);
         end if;
     end for;
 end for;
 return gleichungen;
end function;



//main function of this section, checks if phi(x_i*x_j) = phi(x_i)*phi(x_j)
//input: para_rec M
//output: M`I and M`gleichungen updated

schritt2 := procedure(~M)
 gleichungen := M`gleichungen;
 I := M`I;
 simple_rep(~M);
 for i in [2..#M`Pmod`B1] do
     for j in [i..#M`Pmod`B1] do
         if Dimension(I) ge 1 then
             L1 := phi_von_xixj(i,j,M,false);
             L2 := phi_von_xi_phi_von_xj(i,j,M,false);
             gl := vergleich_der_koefs(L1,L2);
             gleichungen cat:= gl;
             updateideal2(~I,gl,M`R,M);
         end if;
     end for;
 end for;
 M`gleichungen := gleichungen;
 M`I := I;
end procedure;



forward getim;
forward getimofxi;
forward getim2;



//function that does the same as schritt2 but tests if for a specific parameter
//tuple the multiplicativity is fullfilled
schritt2tupeltest := procedure(~M)
 assert Dimension(M`I) le 0;
 if Dimension(M`I) eq 0 then
  tups := Variety(M`I);
  M`tups := tups;
  for tup in tups do
      phi_x_eval := getimofxi(M,tup);
      for i in [2 ..#M`Pmod`B1] do
          for j in [i..#M`Pmod`B1] do
              L1 := getRepresentationInF_1(M`Pmod`B1[i]*M`Pmod`B1[j],M);
              phi_xixj := getim2(L1,M,phi_x_eval);
              L2 := getRepresentationInF_1(M`Pmod`B1[i],M);
              L3 := getRepresentationInF_1(M`Pmod`B1[j],M);
              phi_xi_phi_xj := getim2(L2,M,phi_x_eval)*getim2(L3,M,phi_x_eval);
              rest := phi_xixj - phi_xi_phi_xj;
              if not IsZero(rest) then
                  Exclude(~M`tups,tup);
              end if;
          end for;
      end for;
  end for;
 end if;
end procedure;



//function to add some resanable equations to the ideal
//input:I ideal, gl equations, R ring in whcih I lives, M para_rec
//output: x_i^q - x_i added

add_equations := function(M)
 //gl := M`gleichungen;
 gl := [Universe(M`gleichungen) |  ];
 T := M`Dmod`Kab;
 I := M`I;
 q := #ConstantField(T);
 for i in [1..Rank(T)] do
     Append(~gl, T.i^q - T.i);
 end for;
 updateideal2(~I,gl,M`R,M);
 return I;
end function;;



/////////////////////////////////////////////////////////////////////
//end parameter calculation pt.2
/////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//begin construction the maps
////////////////////////////////////////////////////////////////////


//calculates the image of an element under the map that is given bei a 
//tupel of values for the parameter
//input: li sequence with the representation of the element as a k[x1]
//linear kombination, M para_rec, tup parameter tupel
//output: the image as an element of F2
 
getim := function(li,M,tup) 
 F1 := FunctionField(M`Pmod`P);
 F2 := FunctionField(M`Dmod`D);
 Kx := CoefficientRing(F2);
 x1 := M`Pmod`x_1;
 z := M`Dmod`b_1;
 B1 := M`Pmod`B1;
 B2 := M`Dmod`B2;
 phi_x := M`phi_x;
 s := #M`Dmod`S;
 beta0 := M`beta0;
 b_is := M`Dmod`b_is;
 Kab := M`Dmod`Kab;
 Fneu,schubs := ConstantFieldExtension(F2,Kab);
 drueber := PolynomialAlgebra(Fneu); T := drueber.1;
 out := Zero(F2);
 //pli := ElementToSequence(li[1]);
 im_x := M`Dmod`d2[1]/M`Pmod`d1*Kab.1^(-M`Pmod`n[1]);
 for i in [1..#beta0[1]] do
     im_x -:= M`Dmod`d2[1]*beta0[1][i]*Kab.(s+i);
 end for;
 im_x *:=schubs(z);
 for i in [1..#b_is] do
     im_x +:= Kab.(s+i)*schubs(b_is[i]);
 end for; 
     outtemp1 := Evaluate(drueber!li[1],Fneu!(im_x));
 for i in [2..#li] do   
     outtemp := Evaluate(drueber!li[i],Fneu!(im_x)); 
     xj := Zero(Fneu);
     for j in [1..NumberOfColumns(phi_x[i])-1 ] do
         pli := ElementToSequence(phi_x[i][j]);
         poli := Zero(drueber);
         for m in [1..#pli] do
             poli +:=Kab!pli[m]*T^(m-1); 
         end for;
         xj +:= Evaluate(poli,schubs(z))*schubs(M`Dmod`B2[j]);
    end for;
    outtemp *:= xj;
    outtemp1 +:= outtemp;
 end for;
 para := [tup[i] : i in [1..s]] cat [tup[j] : j in [Rank(M`R)-M`Dmod`anzpara+2..Rank(M`R) ] ];
 iny := ElementToSequence(outtemp1);
 inF2 := [];
 for i in [1..#iny] do
     xnumli := ElementToSequence(Numerator(iny[i]));
     for j in [1..#xnumli] do
         pnum :=Evaluate(Numerator(xnumli[j]),para);
         pden :=Evaluate(Denominator(xnumli[j]),para);
         assert not IsZero(pden);
         xnumli[j] := pnum/pden;        
     end for;
     xnumli := ChangeUniverse(xnumli,ConstantField(F2));
     if #xnumli ge 1 then 
         xnum := &+ [xnumli[m]*F2!(Kx.1^(m-1)) : m in [1..#xnumli] ];
     else 
         xnum := 0;
     end if;
     xdenli := ElementToSequence(Denominator(iny[i]));
     for j in [1..#xdenli] do
         pnum := Evaluate(Numerator(xdenli[j]),para);
         pden := Evaluate(Denominator(xdenli[j]),para);
         assert not IsZero(pden);
         xdenli[j] := pnum/pden;       
     end for;
     xdenli := ChangeUniverse(xdenli,ConstantField(F2));
     if #xdenli ge 1 then
         xden := &+ [xdenli[m]*F2!(Kx.1^(m-1)) : m in [1..#xdenli] ];
     else
         xden := 1;
     end if;
     inF2[i] := xnum/xden;
 end for;
 out := &+[inF2[i]*F2.1^(i-1) : i in [1..#iny] ];
 return out;
end function;

/*
try a new version for getim. faster?
*/
//calculates the images of the xi for a tupel of parameter as an element
//of F2
//input: M with M`phi_x assigned, tup a parameter tuple
//output: phi(xi) as elements of F2
 
getimofxi := function(M,tup)
 F1 := FunctionField(M`Pmod`P);
 F2 := FunctionField(M`Dmod`D);
 Kx := CoefficientRing(F2);
 x1 := M`Pmod`x_1;
 z := M`Dmod`b_1;
 B1 := M`Pmod`B1;
 B2 := M`Dmod`B2;
 phi_x := M`phi_x;
 s := #M`Dmod`S;
 beta0 := M`beta0;
 b_is := M`Dmod`b_is;
 para := [tup[i] : i in [1..s]] cat [tup[j] : j in [Rank(M`R)-M`Dmod`anzpara+2..Rank(M`R) ] ];
 im_x := M`Dmod`d2[1]/M`Pmod`d1*para[1]^(-M`Pmod`n[1]);
 for i in [1..#beta0[1]] do
     im_x -:= M`Dmod`d2[1]*beta0[1][i]*para[s+i];
 end for;
 im_x *:= z;
 for i in [1..#b_is] do
     im_x +:= para[s+i]*b_is[i];
 end for; 
 phi_x_eval := [];
 for k in [1..#phi_x] do
    a := phi_x[k];
    imxi := Zero(F2);
    for i in [1..NumberOfColumns(a)-1] do
        koefs := Eltseq(a[i]);
        imkoef := 0;
        //imxi := Zero(F2);
        for j in [1..#koefs] do
           num := Numerator(koefs[j]);
           den := Denominator(koefs[j]);
           imkoef +:= Evaluate(num,para)/Evaluate(den,para)*z^(j-1);
        end for;
        imxi +:= imkoef*M`Dmod`B2[i];
    end for;
    Append(~phi_x_eval,imxi);
 end for;
 phi_x_eval[1] := im_x;
 return phi_x_eval;
end function;




getim2 := function(li,M,phi_x_eval)
 F2 := FunctionField(M`Dmod`D);
 F2t := PolynomialAlgebra(F2);
 li := ChangeUniverse(li,F2t);
 out := Evaluate(li[1],phi_x_eval[1]);
 out +:= &+ [Evaluate(li[i],phi_x_eval[1])*phi_x_eval[i] : i in [2..#li] ];
 return out;
end function;


 


//main function that constructs the inclusions 
//input: M para_rec with phi_x and tups assigned
//output: sequence of maps

schritt3 := function(M)
 F1 := FunctionField(M`Pmod`P);
 F2 := FunctionField(M`Dmod`D); 
 Kx := CoefficientRing(F1);
 tups := M`tups;
 mappen := [];
  num1, den1 := getRepresentationInF_1_neu(Kx.1,M);
  num, den := getRepresentationInF_1_neu(F1.1,M);
 for i in [1..#tups] do
     phi_x_eval := getimofxi(M,tups[i]);   
     imx := getim2(num1,M,phi_x_eval)/getim2(den1,M,phi_x_eval);
     koefmap := hom<Kx -> F2 | imx>;   
     imy := getim2(num,M,phi_x_eval)/getim2(den,M,phi_x_eval);
     mappe := hom<F1 -> F2 | koefmap, imy>;
     Append(~mappen,mappe);
 end for;
 return mappen;
end function;



//main function that constructs the inclusions, schritt3 is used and after that
//the constant field extension is undone
//input: M para_rec with phi_x and tups assigned 

schritt3_cfx := function(M)
 if Dimension(M`I) le -1 then
     return [];
 end if;
 schubs1 := M`Pmod`const_fld_ext_map;
 schubs2 := M`Dmod`const_fld_ext_map;
 F1neu := FunctionField(M`Pmod`P);
 F2neu := FunctionField(M`Dmod`D);
 F1 := Domain(schubs1);
 F2 := Domain(schubs2);
 mappen := schritt3(M);
 outmappen :=[];
 for mappe in mappen do
     check1,imx := urbild_konstantenkoerpererweit(mappe(schubs1(CoefficientRing(F1).1)),schubs2);
     check2,imy := urbild_konstantenkoerpererweit(mappe(schubs1(F1.1)),schubs2);
     if check1 and check2 then
        koefmap := hom<CoefficientRing(F1) -> F2 | imx>;
         bmappe := hom<F1 -> F2 | koefmap, imy >;
         Append(~outmappen,bmappe);
     end if;
 end for;
 return outmappen;
end function;





//main function to construct the inclusions. does basically the same as
//schritt3 but uses the methods of autoiso.m by florian hess to construct
//the maps as elements of this category

schritt3cat := function(M)
 F1 := FunctionField(M`Pmod`P);
 F2 := FunctionField(M`Dmod`D); 
 Kx := CoefficientRing(F1);
 C := FieldCategory();
 E := FunctionFieldCategory();
 tups := M`tups;
 mappen := [];
 num1, den1 := getRepresentationInF_1_neu(Kx.1,M);
 num, den := getRepresentationInF_1_neu(F1.1,M);
 for i in [1..#tups] do
     phi_x_eval := getimofxi(M,tups[i]);   
     imx := getim2(num1,M,phi_x_eval)/getim2(den1,M,phi_x_eval);      
     imy := getim2(num,M,phi_x_eval)/getim2(den,M,phi_x_eval);
     I := [imy,imx];
     ok,mappe,mess := HasMorphismFromImages(E)(F1,F2,I);
     assert ok;
     Append(~mappen,mappe);
 end for;
 return mappen;
end function;




//same as above. generating morphisms in the category

schritt3_cfxcat := function(M)
 if Dimension(M`I) le -1 then
     return [];
 end if;
 C := FieldCategory();
 E := FunctionFieldCategory();
 schubs1 := M`Pmod`const_fld_ext_map;
 schubs2 := M`Dmod`const_fld_ext_map;
 F1neu := FunctionField(M`Pmod`P);
 F2neu := FunctionField(M`Dmod`D);
 F1 := Domain(schubs1);
 F2 := Domain(schubs2);
 mappen := schritt3cat(M);
 outmappen :=[];
 for mappe in mappen do
     check1,imx := urbild_konstantenkoerpererweit(mappe(schubs1(CoefficientRing(F1).1)),schubs2);
     check2,imy := urbild_konstantenkoerpererweit(mappe(schubs1(F1.1)),schubs2);
     if check1 and check2 then
         I := [imy,imx];
         ok,bmappe,mess := HasMorphismFromImages(E)(F1,F2,I); 
         assert ok;
         bmappe`deg := Degree(M`Dmod`D);
         Append(~outmappen,bmappe);
     end if;
 end for;
 return outmappen;
end function;



////////////////////////////////////////////////////////////////////
//end constructing the maps
////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////
//begin methods to handle some special cases
///////////////////////////////////////////////////////////////////

//function to check if there is at least one place of F1 fulfilling
//the necessary conditions
//input:F1,F2 function fields
//output: F1strich, F2strich constant field extensions of 
//F1, F2, ok bool true if an extension was naccessary
//ext1, ext2 the constent field extension maps  

no_places_of_deg1 := function(F1,F2)
 if #Places(F1,1) ge 1 then
      return false,F1,F2,false,false;
 end if;
 g1 := Genus(F1);
 q := #ConstantField(F1);
 d := Ceiling(2*(Log(q,(2*g1+1)/(q^(1/2) - 1)))) +1;
 for i in [2..d+1] do
     if #Places(F1,i) ge 1 then
         K := ConstantField(F1);
         Kstrich := ext< K | i >;
         F1neu, schubs1 := ConstantFieldExtension(F1,Kstrich);
         F2neu, schubs2 := ConstantFieldExtension(F2,Kstrich);
         return true, F1neu, F2neu, schubs1, schubs2;
     end if;
 end for;
 "this shouldt happen. no place found. d not large enough";
 return true, false, false, false, false;
end function;




//function that checks which maps are defined over the original 
//constant field in the case that the function above was applied
//input: maps sequence of maps F1strich -> F2strich, constant field
//extension maps exti: Fi -> Fistich
//output: sequence of maps F1 -> F2

undo_const_fld_ext := function(maps,schubs1,schubs2)
 outmappen := [];
 F1neu := Codomain(schubs1);
 F2neu := Codomain(schubs2);
 F1 := Domain(schubs1);
 F2 := Domain(schubs2);
 for f in maps do
     check1,imx := urbild_konstantenkoerpererweit(f(schubs1(CoefficientRing(F1).1)),schubs2);
     check2,imy := urbild_konstantenkoerpererweit(f(schubs1(F1.1)),schubs2);
     if check1 and check2 then
         koefmap := hom<CoefficientRing(F1) -> F2 | imx>;
         bmappe := hom<F1 -> F2 | koefmap, imy >;
         bmappe`deg := f`deg;
         Append(~outmappen,bmappe);
     end if;
 end for;
 return outmappen;
end function;


///////////////////////////////////////////////////////////////////
//end methods to handle some special cases
/////////////////////////////////////////////////////////////////////



/////////////////////////////////////////////////////////////////////
//begin methods to calculate induced map on divisor groups
////////////////////////////////////////////////////////////////////

//function to calculate the first pole element of a place P
//does the same as the magma intrinsic by hess but works also
//for places of higher degree
//input: place P
//output: first pole element

first_pole_ele := function(P)
 F := FunctionField(P);
 D := 1*P;     
 while not Dimension(D) ge 2 do
    D := D + P;
 end while;
 x := Representative( [ z : z in Basis(D) | not IsConstant(z) ] );
 return x, -Valuation(x,P);   
end function;





//calculates the image of a place under the mapping on the divisor
//groups that is induced by a function field homomorphism
//input: place P, hom f

induced_placemap := function(P,f)
 assert FunctionField(P) eq Domain(f);
 F := Codomain(f);
 x,n := first_pole_ele(P);
 D := DivisorGroup(F)!PoleDivisor(Divisor(f(x)));
 S,val := Support(D);
 out := &+ [(val[i] div n)*S[i] : i in [1..#S] ];
 return out;
end function;



//calculates the image of a divisor under the mapping on the divisor
//groups
//input: divisor D, hom f

induced_divmap := function(D,f)
 assert FunctionField(D) eq Domain(f);
 F := Codomain(f);
 S,val := Support(D);
 fD := &+ [DivisorGroup(F) | val[i]*induced_placemap(S[i],f) : i in [1..#S] ];
 return fD;
end function;


//faster version of the inducede divisor map

induced_divmap_id := function(D,f)
 i1,i2 := Ideals(D);
 a,b := TwoElement(i1);
 g1 := [a,b];
 a,b := TwoElement(i2);
 g2 := [a,b];
 g1 := [f(a) : a in g1];
 g2 := [f(a) : a in g2];
 Dt1 := -GCD(Divisor(g1[1]), Divisor(g1[2]));
 Dt2 := -GCD(Divisor(g2[1]), Divisor(g2[2]));
 D1 := -GCD(Dt1,Dt2);
 S,e := Support(D1);
 D1 := &+ [e[i]*S[i] : i in [1..#S] ];
 return D1;
end function;



//calculates the induced map on the divisor groups for a function field
//morphism, the old version seems to be a bit slower but i have not tested
//if the new one works allways correct..

intrinsic InducedDivisorMap_old(f::Map) -> Map
{Returns the induced map on the divisor group}
 divmap := map<DivisorGroup(Domain(f))-> DivisorGroup(Codomain(f)) | 
   D :-> induced_divmap(D,f) >;
 return divmap;
end intrinsic;

intrinsic InducedDivisorMap(f::Map) -> Map
{Returns the induced map on the divisor group}
 divmap := map<DivisorGroup(Domain(f))-> DivisorGroup(Codomain(f)) | 
   D :-> induced_divmap_id(D,f) >;
 return divmap;
end intrinsic;


//reduces the seq of divisors one has to check modulo the equirel ~
// D~D` <=> exist g in Aut(F2) s.t. D = g(D`)
//input: sequence of dmods
//output : sequence of dmods
 
reduce_mod_autos := function(zutesten,G)
 G := [InducedDivisorMap(g) : g in G ];
 autcl := [];
 divli := [a`D : a in zutesten ];
 bla := divli;
 while #divli ge 1 do
     D := divli[1];
     for i in [1..#G] do
        if i eq 1 then
          Append(~autcl,Position(bla,D));
        end if;
     Exclude(~divli,G[i](D));
     end for;
 end while;
 zutesten := [zutesten[i] : i in autcl ];
 return zutesten;
end function;

/////////////////////////////////////////////////////////////////////
//end induced maps on divisor group
////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////
//begin change representation wrt inclusion
///////////////////////////////////////////////////////////////////

/*

//not completed yet..
//calculates the norm of a polynomial as described by trager
//input: the minimal polynomial of y2 over F1(x2), F1(x2)
//output the minimal polynomial of a primitiv element for F1(x2,y2) over F1

getpolynorm := function(p,Fneu,F2)
 degu := Degree(Fneu);
 K := PolynomialAlgebra(BaseField(Fneu),degu);
 mipo := DefiningPolynomial(Fneu);
 mipo := mipo / LeadingCoefficient(mipo);
 mipokoefs := Eltseq(mipo);
 Kt := PolynomialAlgebra(K);
 pp := Eltseq(p);
 pp := [Eltseq(a) : a in pp ];
 for i in [1..#pp] do
    if #pp[i] eq 0 then
       pp[i] := [0];
    end if;
 end for;
 //pl := [ [0 : i in [1..#pp] ]: j in [1..degu] ];
 pl := [ [] : i in [1..degu] ];
 for k in [1..degu] do
    for i in [1..#pp] do
           pl[k][i] := &+ [ K.k^(j-1)*pp[i][j] : j in [1..#pp[i]] ];
    end for;
 end for;
 pl := [ &+ [Kt.1^(i-1) * pl[k][i] : i in [1..#pl[k] ] ] : k in [1..degu] ]; 
 poly := &* pl;
 pa := Eltseq(poly);
 //case degu=1:
 if degu eq 1 then
    x2 := - mipokoefs[1];
    pa := [Evaluate(a,<x2>) : a in pa ];
    F1y := PolynomialAlgebra(BaseField(Fneu));
    pripo :=  &+ [pa[i]*F1y.1^(i-1) : i in [1..#pa] ];
 else
   "case under construction"; //replace monomials by suitable ele in 
                              //mipokoefs
   return false;
 end if;
 return pripo,x2,F2.1;
end function;




//input: F1=k(x1,y1),F2=k(x2,y2),f s.t. f:F1->F2 is an embedding
//output: polynomial p over F1 with p(x2) = 0

getmipoforx := function(phi)
 F1 := Domain(phi);
 F2 := Codomain(phi);
 kx1 := CoefficientRing(F1);
 kx2 := CoefficientRing(F2);
 p := MinimalPolynomial(phi(F1!kx1.1));
 //F1t := PolynomialAlgebra(F1); t := F1t.1;
 den := LCM([Denominator(a) : a in Eltseq(p) ]);
 p := den*p;
 Fx := PolynomialAlgebra(F1);
 K := PolynomialAlgebra(Fx,2);
 pp := Eltseq(p);
 pp := [Eltseq(Numerator(a)) : a in pp ];
 for i in [1..#pp] do
    if #pp[i] eq 0 then 
       pp[i] := [0];
    end if;
 end for;
 pl := [];
 for i in [1..#pp] do 
     pl[i] := &+ [pp[i][j]*K.1^(j-1) : j in [1..#pp[i] ] ];
 end for; 
 pol := &+ [pl[i]*K.2^(i-1) : i in [1..#pl] ];
 out := Evaluate(pol,<Fx.1,kx1.1>);
 return out;
end function; 




//extends by y2 the primitive element of F2 over its rational function
//field
//input: Fneu the extension of F1, the inclusion
//output: extesion of Fneu
 
extendbyy := function(Fneu,phi)
 p := DefiningPolynomial(Codomain(phi)); 
 //F1t := PolynomialAlgebra(Fneu); t := F1t.1;
 den := LCM([Denominator(a) : a in Eltseq(p) ]);
 p := den*p;
 Fx := PolynomialAlgebra(Fneu);
 K := PolynomialAlgebra(Fx,2);
 pp := Eltseq(p);
 pp := [Eltseq(Numerator(a)) : a in pp ];
 for i in [1..#pp] do
    if #pp[i] eq 0 then 
       pp[i] := [0];
    end if;
 end for;
 pl := [];
 for i in [1..#pp] do 
     pl[i] := &+ [pp[i][j]*K.1^(j-1) : j in [1..#pp[i] ] ];
 end for; 
 pol := &+ [pl[i]*K.2^(i-1) : i in [1..#pl] ];
 out := Evaluate(pol,<Fneu.1,Fx.1>);
 return out;
end function;




//main method, calculates the representation of F2 as an extension
//of phi(F1) where phi is an embedding
//input: phi : F1 -> F2
//output: F2 as an extension of F1 an isos

changerepresentation := function(phi)
 F1 := Domain(phi);
 F2 := Codomain(phi);
 mip1 := getmipoforx(phi);
 mip1 := Factorisation(mip1)[1][1]; //does it matter which factor?
 Fneu := FunctionField(mip1);
 mip2 := extendbyy(Fneu,phi);
 mip2 := [fac[1] : fac in Factorisation(mip2) |phi`deg eq Degree(fac[1])*Degree(mip1)  ][1];
 mip2,x2,y2 := getpolynorm(mip2,Fneu,F2);
 Fout := FunctionField(mip2);
 kx1 := CoefficientRing(F2);
 Fint := BaseField(Fout);
 kx2 := CoefficientRing(Fint);
 f1 := hom<kx1 -> Fout |Fout!x2 >;
 f1 := hom<F2 -> Fout | f1, Fout.1 >;
 f2 := hom<kx2 -> F2 |phi(F1!CoefficientRing(F1).1) >;
 f2 := hom<Fint -> F2 | f2, phi(F1.1) >;
 f2 := hom<Fout -> F2 | f2, y2 >;
 return Fout,f1,f2;
end function; 

*/

///////////////////////////////////////////////////////////////////
//end change representation
///////////////////////////////////////////////////////////////////



//main method to calculate the embeddings
//input: F1, F2 function fields, strat, kltest bool
//strat: int n to calculate the embeddings of degree n
//       string all to calculate all
//       string some to calculate at leaste one
//kltest: bool wether to calculate the class  number or not
//output: list of function field homs F1 -> F2
//input: Ppre the precision for P, Dpre1 precision for D, Dpre2 imprtant
//precision for D 

inclusions_pre := function(F1,F2,strat,kltest,Ppre,Dpre1,Dpre2)
 check,F1,F2,schubs1,schubs2 := no_places_of_deg1(F1,F2);
 degs := get_possible_degs(F1,F2,strat,kltest);
 mappen := [];
 vprint emb,1 : "calculating the automorphisms of F2";
 G :=  Automorphisms(F2: BaseMorphism := IdentityFieldMorphism(ConstantField(F2)));
 for deg in degs do
 zutesten := get_possible_divisors_deg(F2,deg);
 //zutesten := get_moegliche_divs(F1,F2,strat,kltest);
 if #zutesten eq 0 then
     return [];
 end if;
 Pmod := stellenwahl(F1);
 zutesten, degli := filter_divs(zutesten,Pmod);
 if #zutesten eq 0 then
 break;
 end if;
 vprint emb,1: "number of divisors to check: ";
 vprint emb,1: #zutesten;
 Pmods := places_and_extensions(Pmod,degli);
 m := get_precision_for_P(Pmod,zutesten);
 for i in [1..#Pmods] do
     set_precision_for_P(~Pmods[i],m);
 end for;
 get_P_infos(~Pmods);
 mappen := [];
 vprint emb,1 : "reducing mod automorphisms of F2";
 zutesten := reduce_mod_autos(zutesten,G);
 vprint emb,1 : "number of divisors to check after reduction mod autos: ";
 vprint emb,1 : #zutesten;
 if strat cmpeq "some" then
     vprint emb,1 : "sorting the divisors";
     sort_divs(~zutesten);
 end if;
 while #zutesten ge 1 do
     Dmod := zutesten[1];
     Remove(~zutesten,1);
     Dd := Dmod`D;
     extend_F2(~Dmod);
     posi := Position([ConstantField(FunctionField(a`P)) eq 
     ConstantField(FunctionField(Dmod`D)) : a in Pmods],true);
     if Dpre2 cmpeq "auto" then
        pre := get_precision(Pmods[posi],Dmod);
     else
        pre := [Dpre2 : j in [1..#Dmod`S]];
     end if;
     set_precision_for_D(~Dmod,m,pre);
     test, Dmod := get_D_infos(Dmod);
     if not test then
         continue;
     end if; 
     vprint emb: "divisor: ";
     vprint emb :Dmod`D;
     vprint emb: "anzpara: ";
     vprint emb :Dmod`anzpara;
     //vprint emb : i;
     M := make_para_rec(Pmods[posi],Dmod);
     //"M`Pmod`B1: ", M`Pmod`B1; 
     //"M`Pmod`B2: ", M`Dmod`B2;
     //M`phi_pi;
     schritt1(~M);
     //i;
     vprint emb,1 : "starting step 2";
     case Dimension(M`I):
         when -1:
             continue;
         when 0:
             schritt2tupeltest(~M);
         else
             //schritt 2 faster than
             //adding x^q-x and schritt2tupeltest??
             maxnum_of_tups :=  #ConstantField(FunctionField(M`Pmod`P))^(
             Dimension(M`I)+1);
             if maxnum_of_tups gt 1000 then
                 schritt2(~M);
             end if;
             I := add_equations(M);
             M`I := I;
             schritt2tupeltest(~M);
     end case;
     vprint emb,1 : "starting construction of the maps";
     mappen cat:= schritt3_cfxcat(M);
     if #mappen ge 1 and strat cmpeq "some" then
        if check then
            mappen := undo_const_fld_ext(mappen,schubs1,schubs2);
        end if;
        if #mappen ge 1 then
           return mappen;
        end if;
     end if; 
 end while;
 if check then
     mappen := undo_const_fld_ext(mappen,schubs1,schubs2);
 end if;
 end for;
 outim := [];
 outmap := [];
 E := FunctionFieldCategory();
 for g in G do
     for f in mappen do
        _,m := HasComposition(E)(f,g);
        m`deg := f`deg;
        im := [m(F1.1), m(F1!CoefficientField(F1).1)];
        if not im in outim then 
           Append(~outim,im);
           Append(~outmap,m);
        end if;
     end for;
 end for;
 return outmap;
 end function; 




//function to calculate the inclusions that map a specific place to a 
//specific divisor
//input:F1,F2 function fields, kltest,P,D,pre a sequence of in of length = 
//#supp D

inclusionsP2D := function(F1,F2,P,D,pre)
 if Degree(P) gt 1 then
    P;
    Degree(P);
    "P must be of degree one";
    return false;
 end if;
 chara := Characteristic(F1); 
 gaps := GapNumbers(F1,P);
 i := 1;
 place_case := 0;
 while i in gaps or i mod chara eq 0 do
     if not i in gaps and i  mod chara eq 0 then
         place_case := 1;
     end if;
     i +:=1;
 end while; 
 Pmod := rec<place_rec | P := P , place_case := place_case, n1 := i>;
 zutesten := [D];
 zutesten, degli := filter_divs(zutesten,Pmod);
 Pmods := places_and_extensions(Pmod,degli);
 m := get_precision_for_P(Pmod,zutesten);
 for i in [1..#Pmods] do
     set_precision_for_P(~Pmods[i],m);
 end for;
 get_P_infos(~Pmods);
 mappen := [];
 for i in [1..#zutesten] do
     extend_F2(~zutesten[i]);
     posi := Position([ConstantField(FunctionField(a`P)) eq 
     ConstantField(FunctionField(zutesten[i]`D)) : a in Pmods],true);
     if pre cmpeq "auto" then
        pre := get_precision(Pmods[posi],zutesten[i]);
     else
        pre := [pre : j in [1..#zutesten[i]`S]];
     end if;
     set_precision_for_D(~zutesten[i],m,pre);
     //vprint emb : "needed precision for the local uniformizer: ", Pmods[posi]`n[#Pmods[posi]`n] + 5;
     test, Dmod := get_D_infos(zutesten[i]);
     if not test then
         continue;
     end if; 
     vprint emb : "anzpara: ";
     vprint emb : Dmod`anzpara;
     vprint emb : "generating para mod for:", i ;
     M := make_para_rec(Pmods[posi],Dmod);
     vprint emb : "starting schritt1";
     schritt1(~M);
     vprint emb : "dimension after schritt1: ", Dimension(M`I);
     vprint emb : "starting schritt2: ";
     case Dimension(M`I):
         when -1:
             continue;
         when 0:
             schritt2tupeltest(~M);
         else
             //dim of the ideal is gt 0
             //faster to do schritt2 or
             //to make it 0 dimensional by adding
             //euationas x^p - x 
             maxnum_of_tups :=  #ConstantField(FunctionField(M`Pmod`P))^(
             Dimension(M`I)+1);
             if maxnum_of_tups gt 1000 then
                 schritt2(~M);
             end if;
             I := add_equations(M);
             M`I := I;
             schritt2tupeltest(~M);
     end case;
     vprint emb : "starting construction of the maps";
     mappen cat:= schritt3_cfxcat(M); 
 end for;
 return mappen;
end function;



intrinsic Inclusions(F1::FldFunG, F2::FldFunG :classgrp := true, strat := "all",pre := "auto")-> SeqEnum {Returns a sequence of inclusions F1->F2}
 ok,mess := input_test(F1,F2);
 require ok : mess;
 ok, mess := input_test_2(classgrp,strat,pre);
 require ok : mess;
 return inclusions_pre(F1,F2,strat,classgrp,30,30,pre);
end intrinsic;

intrinsic Inclusions(F1::FldFunG, F2::FldFunG, P:: PlcFunElt, D::DivFunElt : pre := "auto")->SeqEnum {Returns a sequence of inclusions F1 -> F2 s.t. P |-> D }
 ok,mess := input_test(F1,F2);
 require ok : mess;
 ok, mess := input_test_2(false,2,pre);
 require ok : mess;
 return inclusionsP2D(F1,F2,P,D,pre);
end intrinsic;


intrinsic Inclusions(P::PlcFunElt, D::DivFunElt : pre := "auto")->SeqEnum {Returns a sequence of inclusions F1 -> F2 s.t. P |-> D }
 ok,mess := input_test_2(false,2,pre);
 require ok : mess;
 F1 := FunctionField(P);
 F2 := FunctionField(D);
 ok,mess := input_test(F1,F2);
 require ok : mess;
 return inclusionsP2D(F1,F2,P,D,pre);
end intrinsic;


intrinsic HasInclusion(F1::FldFunG, F2::FldFunG :classgrp := true, pre := "auto")->Bool,Map {Returns wether there is an inclusion and an inclusion}
 ok,mess := input_test(F1,F2);
 require ok : mess;
 ok,mess := input_test_2(classgrp,"some",pre);
 require ok : mess;
 mappen :=  inclusions_pre(F1,F2,"some",classgrp,30,30,pre);
 if #mappen eq 0 then
   return false,_;
 else
   return true, mappen[1];
 end if;
end intrinsic;
