freeze;

///////////////////////////////////////////////////////////////////////////////
//
//  Matrix package                                             Alice Niemeyer
//  Latest revision March 2011 
//  
//  Copyright (C)  1998  University of Western Australia 
//
//  This file contains  an implementation  of the recognition  algorithms for
//  classical groups by Niemeyer and Praeger.  A description  of them  can be 
//  found in 
//  
//  [1] Alice C. Niemeyer and  Cheryl E. Praeger 
//      "A Recognition Algorithm for Classical Groups over Finite Fields",
//      Proc. London Math. Soc (3) 77, 1998, 117-169.
// 
//  [2] Alice C. Niemeyer and  Cheryl E. Praeger 
//      "Implementing a Recognition Algorithm for Classical Groups"
//      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
//
//  [3] Alice C. Niemeyer and  Cheryl E. Praeger 
//      "A Recognition Algorithm for Non-Generic Classical Groups over
//       Finite Fields",  J. Austral. Math. Soc. (Series A)67 , 223-253, 1999.
//
//  This implementation uses some algorithms described elsewhere:
// 
//  [4] Frank Celler and C.R. Leedham-Green
//      "Calculating the order of an invertible matrix",
//      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
//
//  [5] Frank Celler and C.R. Leedham-Green
//      "A non-constructive recognition algorithm for the special linear
//      and other classical groups"
//      "Groups and Computation II", Amer. Math. Soc. DIMACS Series 28, 1997.
//
//    In this implementation we use the irreducibility test of the algorithm
//    described in [5], which can often avoid an application  of the Meataxe
//    algorithm.
//
//  [6] Frank Celler and Charles R. Leedham-Green and Scott H. Murray 
//      and Alice C. Niemeyer and E.A. O'Brien
//      "Generating random elements of a finite group"
//      Comm. Algebra 23,  4931--4948 (1995)
//
//  For an overview see also
//
//  [7] Cheryl E. Praeger, 
//      "Primitive prime divisor elements in finite classical groups",
//       Proc. of Groups St. Andrews in Bath 1997, Cambridge University
//      Press, to appear.
//
//  Input to RecogniseClassicalNP:
//
//  - a group <grp>, which is a subgroup of  GL(d,q) 
//  - an optional string <case>, one of "linear", "unitary", "symplectic", 
//           "orthogonalplus", "orthogonalminus", or "orthogonalcircle"
//  - an optional integer <NumberOfElements>
//
//
//
//  Output:
//
//  A boolean, i.e. either 'true' or 'false'.
//
//  Complexity:
//
//  For small fields (q < 2^16), the cost for a given value of <N> is
//  O( d^3 log d )$   bit operations.
//
//  The  algorithm  is designed  to test  whether a matrix group <grp> 
//  acting irreducibly on the underlying  vector spapce   contains the
//  corresponding classical group Omega and is contained in Delta (see
//  [1]). Omega and Delta are defined as follows:
//
//  Case "linear":           Delta = GL(d,q),  Omega = SL( d, q)
//  Case "symplectic":       Delta = GSp(d,q), Omega = Sp( d, q)
//  Case "orthogonalplus":   Delta = GO+(d,q), Omega = OmegaPlus(d,q)
//  Case "orthogonalminus":  Delta = GO-(d,q), Omega = OmegaMinus(d,q)
//  Case "orthogonalcircle": Delta = GO(d,q),  Omega = Omega(d,q)
//  Case "unitary":          Delta = GU(d,q),  Omega = SU(d,q)
//
//  If the algorithm returns 'true', then  we will know with certainty
//  that <grp>  contains Omega  and  is contained   in Delta.   If  it
//  returns 'false'  then either <grp>  does not contain Omega, or the
//  group is not contained  in Delta or there is  a small  chance that
//  <grp>  is contained in Delta  and contains Omega.  More precisely,
//  if <grp> really does contain Omega then the probability with which
//  the algorithm returns the  boolean  'false' is less than  epsilon,
//  where epsilon is some  real number  between 0  and 1  depending on
//  <NumberOfElements>. If "User1" is set to Verbose then, in the case
//  that RecongizeClassicalNP() returns   'true', it also   prints the
//  statement "Proved that  the group  contains  a classical group  of
//  type <Case> in <n>  random selections', where  <n>is the number of
//  selections needed.  In  case the function returns false  it prints 
//  a statement  giving some  indication of  why the algorithm reached 
//  this conclusion.
//  
//  
//  The  algorithm is  based  on Theorem  4.8  of [1].  It  relies  on
//  finding special elements, called ppd(d,q; e)-elements, in <grp> to
//  decide  whether <grp> satisfies the hypotheses of the theorem.  In
//  practice we attempt to find these ppd-elements by selecting up  to 
//  <N> random elements of the group see [6].  Then we test whether an
//  element g in <grp> has the ppd(d,q;e)-property for some d/2 <e<= d.
//  We also need to be able to decide whether <g> is a basic or a large 
//  ppd(d, q ;e)-element.  This  is done  by  a  modification  of  the
//  algorithm of Celler and Leedham-Green for determining the order of
//  a matrix, (see [4] and [2]).  Note that Theorem 4.8 requires <grp>
//  to act irreducibly on the underlying vector space, but this is not
//  one of the assumptions  on the input to our  algorithm. In fact we
//  use the irreducibility test based on the degrees of characteristic
//  polynomials described in [5].
//  
//  
//  

declare verbose Classical, 3;

import "ppd.m":IsPpdElement,IsPpdElementD2, IsPrimitivePrimeDivisor;

import "sld2.m": RecogniseDegree2, RecognizeOmega2;

forward IsTwoPowerMinusOne;

procedure InfoRecog(i,stg)
    vprint Classical, i: stg;
end procedure;

// Number of random elements: default seemed to be too small when
// the dimension or field is small
function ClassicalRecognitionElements(d, F)
    if d le 8 or #F le 9 then
	return 150;
    else
	return 30;
    end if;
end function;

// if we deduce that the group does not act (absolutely) irreducibly 
// then we unbind type flag and set certain of the flags to false
procedure SetNotAbsIrred(grp)
    grp`recognize`isLinearGroup     := false;
    grp`recognize`isSymplecticGroup := false;
    grp`recognize`isUnitaryGroup    := false;
end procedure;

// This function checks whether we found some evidence that the 
// case was wrong
CaseCheck := function(grp,Case)

    d := Degree(grp);
    if Case eq "symplectic" then
        for e in grp`recognize`E do
            if e gt d/2 and e mod 2 ne 0 then 
                InfoRecog(2,"The group does not preserve a symplectic form");
                grp`recognize`isGeneric               := false;
                grp`recognize`possibleOverLargerField := true;
                grp`recognize`possibleNearlySimple    := {};
                return false;
            end if;
        end for;
    elif Case eq "unitary" then
        for e in grp`recognize`E do
            if e gt d/2 and e mod 2 eq 0 then
                InfoRecog(2,"The group does not preserve a unitary form");
                grp`recognize`isGeneric               := false;
                grp`recognize`possibleOverLargerField := true;
                grp`recognize`possibleNearlySimple    := {};
                return false;
            end if;
        end for;
    elif Case eq "orthogonalminus" then
        for e in grp`recognize`E do
            if e gt d/2 and e  mod 2 ne 0 then
                InfoRecog(2,"The group does not preserve a quadratic form");
                grp`recognize`isGeneric               := false;
                grp`recognize`possibleOverLargerField := true;
                grp`recognize`possibleNearlySimple    := {};
                return false;
            end if;
        end for;
    elif Case in ["orthogonalplus","orthogonalcircle"] then
        for e in grp`recognize`E do
            if (e gt d/2 and e  mod 2 ne 0) or e eq Degree(grp) then
                InfoRecog(2,"The group does not preserve a quadratic form");
                grp`recognize`isGeneric               := false;
                grp`recognize`possibleOverLargerField := true;
                grp`recognize`possibleNearlySimple    := {};
                return false;
            end if;
        end for;
    end if;

    return true;

end function;

procedure InitRecog(grp,Case)
    if assigned grp`d eq false then grp`d := Degree(grp); end if;
    F := BaseRing (grp);
    if not assigned grp`p then grp`p := Characteristic(F); end if;
    if not assigned grp`k then grp`k := Degree(F); end if;
    if not assigned grp`q then grp`q := #F; end if;

    FF := recformat< formType, bilinearForm, quadraticForm, sesquilinearForm,
                    bilinFlag, sesquiFlag, scalars, bc, n >;
    RF := recformat< E, LE, basic, n, isReducible, isGeneric, 
                     possibleOverLargerField, possibleNearlySimple,
                     dimsReducible, noFormFound, orders,
                     isLinearGroup, isSymplecticGroup,
                     isOrthogonalPlusGroup, 
                     isOrthogonalMinusGroup, 
                     isOrthogonalCircleGroup, 
                     isUnitaryGroup, applies
                >;

        grp`recognize  := rec< RF |
                             E                       := [],
                             LE                      := [],
                             basic                   := [],
                             n                       := 0,
                             applies                 := true,
                             isReducible             := true,
                             isGeneric               := false,
                             possibleOverLargerField := true,
                             possibleNearlySimple    := {},
                             orders                  := {},
                             dimsReducible           := [] >;
        grp`forms    := rec< FF |
                             n                := 0,
                             bilinearForm     := false,
                             quadraticForm    := false,
                             sesquilinearForm := false,
                             bilinFlag        := true, 
                             sesquiFlag       := true,
                             formType         := "unknown">;

       grp`forms`sesquiFlag := Degree(BaseRing(grp)) mod 2 eq 0;
  
end procedure;
  

///////////////////////////////////////////////////////////////////////////////
//
//  StoreClassicalForms ( <grp>, <Case> )
//
//  This function tests whether an invariant form for <grp> is 
//  already known.
//  If so, it returns true if Case matches the form and false else.
//  If no form is known it will compute the invariant forms and 
//  again compare with Case.
//
StoreClassicalForms := function(grp, Case)

    
    // if no forms are known, compute them
    if not assigned grp`forms or
        grp`forms`formType eq "unknown" then
        n := grp`forms`n;
        grp`forms`n := 0;
        // derived group must act absolutely irreducibly 
        // or else function exits with error 
        try 
           tmp := ClassicalForms(grp:Scalars := true);
        catch e
           return false;
        end try;
        if tmp cmpeq false then return false; end if;
        grp`forms`n +:= n;
        grp`forms`formType := tmp`formType;
        grp`forms`bilinearForm := tmp`bilinearForm;
        grp`forms`quadraticForm := tmp`quadraticForm;
        grp`forms`sesquilinearForm := tmp`sesquilinearForm;
        grp`forms`scalars := tmp`scalars;
    end if;

    // if necessary, set Case
    if Case eq "unknown" then
	Case := grp`forms`formType;
        return true;
    end if;

    if grp`forms`formType eq "unknown" then
        if grp`recognize`isReducible eq true then
            if IsIrreducible( grp ) cmpeq false then
                InfoRecog(2,"The group is reducible.\n");
            else
                grp`recognize`isReducible := false;
            end if;
        else
            InfoRecog (2,"Cannot find invariant form.\n");
        end if;
        return false;
    end if;

    // now compare with case
    if grp`forms`formType ne Case then
	InfoRecog( 1, Case cat " is not the right case");
	InfoRecog( 1, "The case is " cat grp`forms`formType);
        return false;
    end if;

    return true;

end function;

// If Case is the correct answer, then set all the information in the
// record recognize
SetReturnNP := function(grp,Case)

    d := Degree(grp);

    // set the group type
    delete grp`recognize`dimsReducible;
    delete grp`recognize`possibleOverLargerField;
    delete grp`recognize`possibleNearlySimple;

    if grp`recognize`isReducible then
        if IsIrreducible( grp ) then
            grp`recognize`isReducible := false;
        else
            InfoRecog(2, "Group is reducible." );
            return false;
        end if;
    end if;

    form := StoreClassicalForms(grp, Case);
    if form eq false then return false; end if;


    grp`recognize`isSymplecticGroup := false;
    grp`recognize`isOrthogonalPlusGroup := false;
    grp`recognize`isOrthogonalMinusGroup := false;
    grp`recognize`isOrthogonalCircleGroup := false;
    grp`recognize`isUnitaryGroup    := false;
    grp`recognize`isLinearGroup     := false;
    if Case eq "linear" then
        grp`recognize`isLinearGroup     := true;
    elif Case eq "symplectic" then
        grp`recognize`isSymplecticGroup := true;
     elif Case eq "unitary" then
        grp`recognize`isUnitaryGroup    := true;
     elif Case eq "orthogonalminus" then
        grp`recognize`isOrthogonalMinusGroup := true;
     elif Case eq "orthogonalplus" then
        grp`recognize`isOrthogonalPlusGroup := true;
     elif Case eq "orthogonalcircle" then
        grp`recognize`isOrthogonalCircleGroup := true;
     end if;

    return true;

end function;



/////////////////////////////////////////////////////////////////////////////
//
//  IsReducible( <grp>, <cpol> ) . . . . . . . . . . . .  test irreducibility
//
//  Compute the degrees of the irreducible factors of the  polynomial  <cpol> 
//  and  update s <grp>'recognize`dimsReducible.
//  This function is one of Celler's functions see [5].
//
procedure IsReducible(grp,cpol)

     // reducible groups still possible
     if not grp`recognize`isReducible then return; end if;
     
     // compute the degrees of the irreducible factors
     facs := [x[1]:i in [1..x[2]],x in Factorisation(cpol)];
     deg := [Degree(x):x in facs];

     // compute all possible dims (one could restrict this to 2s <= d)
     dims := {0};
     for g in deg do
         dims join:= {i+g:i in dims};
     end for;

     // and intersect it with <grp>`recognize`dimsReducible
     if 0 eq #grp`recognize`dimsReducible then
         grp`recognize`dimsReducible := dims;
     else
         grp`recognize`dimsReducible meet:= dims;
     end if;

     // G acts irreducibly if only 0 and d are possible
     if #grp`recognize`dimsReducible eq 2 then
         grp`recognize`isReducible := false;
         InfoRecog(2,"The group acts irreducibly.");
     end if;

end procedure;
          


//////////////////////////////////////////////////////////////////////
//
//  RuleOutForms (grp, c) . . . . . . . . . . . .  rule out forms on V
//
//  This  function implements a  few cheap test to  rule out or narrow 
//  down the forms left invariant by the group.  It uses Celler's code
//  for finding invariant forms.
//
RuleOutForms := function(grp, c)

    field := BaseRing(grp);
    grp`forms`n +:= 1;


    // we first apply a cheap test to check whether we can rule
    // out bilinear forms
    //    if grp`forms`bilinFlag eq true then
    //  a := ClassicalForms_ScalarMultipleDual(grp,c);
    //end if;

    // then we apply a cheap test to check whether we can rule
    // out sesquilinear forms
    //    if grp`forms`sesquiFlag  eq true then
    //  a := ClassicalForms_ScalarMultipleFrobenius(grp, c);
    //end if;

    if grp`forms`bilinFlag eq false and
       grp`forms`sesquiFlag eq false then
         grp`forms`formType := "linear";
         return false;
    else return true;
    end if;

end function;


differmodtwo := function( E )

    for e in E do
        if E[1] mod 2 ne e mod 2 then return true; end if;
    end for;
    return false;
end function;

           

//////////////////////////////////////////////////////////////////////
//
//  TestNoForms (grp) . . . . . . check whether grp preserves no forms
//
procedure TestNoForms(grp)

    if differmodtwo(grp`recognize`E) then
        // now we know that grp preserves no forms
	grp`forms`formType := "linear";
        grp`forms`bilinFlag := false;
        grp`forms`sesquiFlag := false;
        InfoRecog(2, "The group preserves no forms.");
     end if;

end procedure;


procedure TestSesquiFlag(grp)

    for e in grp`recognize`E do 
        if e mod 2 eq 0 then
	    grp`forms`sesquiFlag := false;
            InfoRecog(2,"The group does not preserve a sesquilinear form.");
	    return;
        end if;
    end for;

end procedure;

//////////////////////////////////////////////////////////////////////
//
//  CheckForms(grp,case) . . . . . we ran forms - is it consistent ?
//
CheckForms := function(grp, Case)

    return true;
    if grp`forms`formType ne "unknown" then
        return true;
    end if;
    if Case ne "unknown" and grp`forms`formType ne Case then
        InfoRecog(2," group preserves form of type " cat Case );
	return false;
    end if;

    return true;

end function;

//////////////////////////////////////////////////////////////////////
//
//  TestRandomElement( <grp>, <g> ) . . . . . . .  test random element
//   
//  The  function  TestRandomElement() takes  a  group  <grp>  and  an
//  element <g> as  input.  It is assumed that  grp contains a  record
//  component 'recognize' storing  information  for  the   recognition
//  algorithm.  TestRandomElement() calls the  function IsPpdElement()
//  to determine whether <g> is a ppd(d, q;e)-element for some d/2 < e
//  <= d, and whether it is large.  If <g> is a ppd(d,q;e)-element the
//  value e is  added to  the set  grp`recognize`E, which records  all
//  values e  for  which  ppd-elements  have  been  selected.  If,  in
//  addition,  <g>   is   large,  e   is   also  stored   in  the  set
//  grp`recognize`LE,  which records all  values e  for which a  large
//  ppd-element has been selected.  The component grp`recognize`basic,
//  is  used to record  one value e for which a basic  ppd-element has
//  been  found,  as we  only require  one basic  ppd-element  in  our
//  algorithm.  Until such an element has been  found it is set to the
//  value 'false'.   Therefore the  function TestRandomElement()  only
//  calls the  function IsPpdElement() with input  parameters <g>, d*a
//  and p  if grp`recognize`basic  is  'false'.   If <g>  is  a  basic
//  ppd(d,q;e)-element then e is stored as grp`recognize`basic.
//  
procedure TestRandomElement(grp,g,~res)

    d := Degree(grp);
    //print "Testing Random Element";

    // compute the characteristic polynomial
    cpol := CharacteristicPolynomial(g);
    IsReducible(grp,cpol);
    ppd := IsPpdElement(BaseRing(grp),cpol,d,grp`q,1);
    // first we test whether this element restricts forms
    //    if grp`forms`formType eq "unknown" then
    //forms := RuleOutForms(grp,cpol);
    //end if;

    if Type(ppd) eq BoolElt then
       res := d;
       return;
    end if;

    str1 := "Found a ";
    Include(~grp`recognize`E, ppd[1]);
    if ppd[2] eq true then
        Include(~grp`recognize`LE, ppd[1]);
        str1 := str1 cat "large ";
    end if;
       
    if #grp`recognize`basic lt 1 then
        // We only need one basic ppd-element.
        // Also each basic ppd-element is a ppd-element.
        bppd := IsPpdElement(BaseRing(grp),cpol,d,grp`p,grp`k);
        if Type(bppd) ne BoolElt then
            str1 := str1 cat "and  basic ";
            Include(~grp`recognize`basic,bppd[1]);
        end if;
    end if;
    str := str1 cat "ppd(" cat IntegerToString(d) cat ", " cat 
          IntegerToString(grp`q) cat "; "
                cat IntegerToString(ppd[1]) cat ")-element"; 
    InfoRecog(2, str);
  
    if grp`forms`formType eq "unknown" then
        TestNoForms(grp);
    end if;
     
    if grp`forms`formType eq "unknown" and 
       grp`forms`sesquiFlag then
        TestSesquiFlag(grp);
    end if;
    res := ppd[1];


end procedure;

ApplicableParameters := function( grp, Case )

    d := Degree(grp);
    if d le 2 then
        InfoRecog( 1, "The degree has to be at least 3");
	return false;
    end if;

    if d mod 2 eq 0 and Case eq "orthogonalcircle" then
        InfoRecog( 1, "In the case " cat Case cat " d has to be odd" );
        return false;
    end if;

    if d mod 2 ne 0 and Case in [ "orthogonalplus", "orthogonalminus", 
       "symplectic" ] then
        InfoRecog( 1, "In the case " cat Case cat " d has to be even" );
        return false;
    end if;

    if Case eq "unitary" then 
        if Degree(BaseRing(grp)) mod 2 ne 0 then
            InfoRecog(1,"In the case " cat Case cat " q has to be a square");
            return false;
        end if;
    end if;

    return true;

end function;

//////////////////////////////////////////////////////////////////////
// 
//  GenericParameters( grp, Case ) . . . . . .  are (Case,d,q) generic 
//
//   In  our  algorithm we attempt to find two different ppd-elements,
//  that is  a ppd(d, q; e_1)-element and a ppd(d, q; e_2)-element for
//  d/2 < e_1 < e_2 <= d.  We also require that  at least one  of them
//  is a large ppd-element and one  is a  basic ppd-element.  For some
//  values of (Case, $d$, $q$) however, such ppd-elements do not exist
//  in a classical group. This function tests whether they do.
//
GenericParameters := function( grp, Case )


    if not assigned grp`recognize then InitRecog(grp,Case); end if;
    d := Degree(grp);
    q := grp`q;

    if Case eq "linear" and d le 2 then
        InfoRecog(2, "The group does not have generic parameters.");
        return false;
    elif Case eq "linear" and d eq 3 then
        fact := Factorisation(q+1);
        if #fact eq 1 and fact[1,1] eq 2 then
            InfoRecog(2, "The group does not have generic parameters.");
            return false;
        end if;
        return true;
    elif Case eq "symplectic" and (d lt 6 or (d mod 2 ne 0) or
        [d,q] in [[6,2],[6,3],[8,2]]) then
        InfoRecog(2, "The group does not have generic parameters.");
        return false;
    elif Case eq "unitary" and (d lt 5 or d eq 6 or [d,q] eq [5,4]) then
        InfoRecog( 2, "The group does not have generic parameters.");
        return false;
    elif Case eq "orthogonalplus" and ( d mod 2 ne 0 or d lt 10 or
     (d eq 10 and q eq 2)) then
        InfoRecog( 2, "The group does not have generic parameters.");
       return false;
    elif Case eq "orthogonalminus" and (d mod 2 ne 0 or d lt 6 or
     [d,q] in [[6,2],[6,3],[8,2]]) then
        InfoRecog(2, "The group does not have generic parameters.");
       return false;
    elif Case eq "orthogonalcircle" then
        if d lt 7 or [d,q] eq [7,3] then
            InfoRecog( 2, "The group does not have generic parameters.");
            return false;
        end if;
        if d mod 2 eq 0 then
            InfoRecog( 2, "The group does not have generic parameters.");
            return false;
        end if;
        if q mod 2 eq 0 then
           InfoRecog(1,"The group is not irreducible, because in the ");
       InfoRecog(1,"orthogonalcircle case, if d is odd, then q has to be odd");
            return false;
        end if;
    end if;

    return true;

end function;   
       
//////////////////////////////////////////////////////////////////////
// 
//  IsGeneric( grp, N_gen ) . . . . . . .  is <grp> a generic subgroup
//
//   In  our  algorithm we attempt to find two different ppd-elements,
//  that is  a ppd(d, q; e_1)-element and a ppd(d, q; e_2)-element for
//  d/2 < e_1 < e_2 <= d.  We also require that  at least one  of them
//  is a large ppd-element and one  is a  basic ppd-element.   In that
//  case  <grp> is  a  generic  subgroup  of  GL(d,q).   The  function
//  IsGeneric()  takes  as  input  the  parameters <grp> and  <N_gen>.
//  It chooses up to <N_gen> random elements in <grp>.  If among these
//  it  finds  the  two  required  different  ppd-elements,  which  is
//  established   by    examining    the    sets    <grp>`recognize`E,
//  <grp>`recognize`LE,  and  <grp>`recognize`basic,  then it  returns  
//  true. If after <N_gen> independent  random selections  it fails to
//  find two  different  ppd-elements,  the  function returns 'false';
//  
IsGeneric := function(grp,N_gen)


    if not assigned grp`recognize then
        InitRecog(grp,"unknown");
    end if;
    if grp`recognize`isGeneric then
        InfoRecog(2,"The group is generic.");
        return true;
    end if;
    b := grp`d;
    process := RandomProcess (grp);
    for N in [1..N_gen] do
        g := Random(process);
        // g := Random(grp);
        grp`recognize`n +:= 1;
        TestRandomElement(grp,g,~null);
        if #grp`recognize`E ge 2 and
           #grp`recognize`LE ge 1 and
           #grp`recognize`basic ge 1 then
               grp`recognize`isGeneric := true;
               str := "The group is generic in " cat 
                       IntegerToString(grp`recognize`n) cat
                      " random element selections";
               InfoRecog(2, str );
               return true;
        end if;
    end for;


    return false;

end function;

//////////////////////////////////////////////////////////////////////
//
//  RuledOutExtFieldParameters(grp,Case, N) . . . . .  test parameters
// 
//  The function RuledOutExtFieldParameters() tests whether b, the gcd
//  of all values e for which a ppd( d, q; e )-element has been found,
//  is either 1 (in the linear,  unitary and  orthogonal-circle cases) 
//  or 2 in all other cases. It decides  whether  we  have  sufficient
//  information to rule out  extension field groups. Its justification
//  comes from the discussion in Section 3.3 in [2].
//  
differmodfour := function(E)
    for e in E do
        if E[1] mod 4 ne e mod 4 then return true; end if;
    end for;
    return false;
end function;

FindCounterExample := function(grp,prop,N)

    g := Id(grp);
    if prop(g) then return true; end if;

    process := RandomProcess (grp);
    for i in [1..N] do
        // g := Random(grp);
        g := Random(process);
        grp`recognize`n +:= 1;
        TestRandomElement(grp,g,~null);
        if prop(g) or #grp`recognize`E gt 2 then
           return true;
        end if;
    end for;

    return false;
end function;



RuledOutExtFieldParameters := function(grp,Case, N)

    d := Degree(grp);
    q := grp`q;
    E := grp`recognize`E;


    if Case eq "linear" then
        if not IsPrime(d) 
           or Seqset(E) ne {d-1,d}
           or d-1 in grp`recognize`LE then
            return true;
        end if;
        if d eq 3 and q eq 5 then
            // in this case q = 2*3-1 and there is no large ppd(3,5;2)-element
            fn := function(g) return (Order(g) mod 5 eq 0 or 
                                      Order(g) mod 8 eq 0 or
                                      Order(g) mod 24 eq 0); end function;
            if FindCounterExample ( grp, fn, N ) then
                    return true;
            end if;
        elif d eq 3 and q eq 2 then
            fn := function(g) return Order(g) mod 2 eq 0; end function;
                        if FindCounterExample ( grp, fn, N ) then
                    return true;
            end if;
        elif d eq 3 and Seqset(E) eq Seqset([2,3]) then
            i:= Factorization(q+1);
            if #i eq 2 and i[2][1] eq 3 and i[2][2] eq 1 and i[1][1] eq 2 then
                // q = 3*2^s-1
                InfoRecog(2,"Searching for element of order divisible by 12");
                fn := function(g) return Order(g) mod 12 eq 0; end function;
                if FindCounterExample ( grp, fn, N ) then
                    return true;
                end if;
            end if;
        end if;
    elif Case eq "unitary" then
       return true;
    elif Case eq "symplectic" then
       if d mod 4 eq 2 and q mod 2 eq 1 then
          for i in [1..#E] do
              if E[i] mod 4 eq 0 then return true; end if;
          end for;
          return false;
       elif d mod 4 eq 0 and q mod 2 eq 0 then
          for i in [1..#E] do
              if E[i] mod 4 eq 2 then return true; end if;
          end for;
          return false;
       elif d mod 4 eq 0 and q mod 2 eq 1 then
          return differmodfour(E);
       elif d mod 4 eq 2 and q mod 2 eq 0 then
          return #E gt 0;
       else
          error "ERROR : d cannot be odd in Case Sp";
       end if;
    elif Case eq "orthogonalplus" then
       if d mod 4 eq 2 then
          for i in [1..#E] do
              if E[i] mod 4 eq 0 then return true; end if;
          end for;
          return false;
       elif d mod 4 eq 0 then
          return differmodfour(E);
       else error "ERROR : d cannot be odd in Case O+";
       end if;
    elif Case eq "orthogonalminus" then
       if d mod 4 eq 0 then
          for i in [1..#E] do
              if E[i] mod 4 eq 2 then return true; end if;
          end for;
          return false;
       elif d mod 4 eq 2 then
          return differmodfour(E);
       else error "ERROR : d cannot be odd in Case O-";
       end if;
    elif Case eq "orthogonalcircle" then
       return true;
    end if;

    return false;
end function;     

//////////////////////////////////////////////////////////////////////
//
//  IsExtensionField( grp, case, N_ext) . . . rule out extension field 
//
//  Once we have proved that  the  group <grp>  is generic  we need to
//  rule  out  the  extension  field case, that is we need to  find  a
//  b-witness for each of the pi(d) distinct prime divisors b of d, or
//  in some cases a pair of witnesses, as discussed in Section 3.3  of
//  [2].   The function IsExtensionField() is  designed  to show  that
//  <grp> does not preserve an extension field structure.  It takes as
//  input  the  (generic)  group  <grp>  and  the  number  <N_ext>  of
//  allowable random selections for this function.
//  
IsExtensionField := function(grp, Case, N_ext)

    if not assigned grp`recognize then InitRecog(grp, Case); end if;
    if grp`recognize`isGeneric and
       grp`recognize`possibleOverLargerField eq false then
        InfoRecog(2,"The group is not an extension field group.");
        return 0;
    end if;

    b := grp`d;
    if #grp`recognize`E gt 0 then
        b := Gcd(Setseq(Seqset(grp`recognize`E) join {grp`d}));
    end if;
    if Case in ["linear", "unitary", "orthogonalcircle"] then
        bx := 1;
    else
        bx := 2;
    end if;


    if b eq bx and Case ne "unknown" then
        if RuledOutExtFieldParameters(grp,Case, N_ext) then
            InfoRecog(2,"The group is not an extension field group.");
            grp`recognize`possibleOverLargerField := false;
            InfoRecog(2,"Determining invariant forms.");
            if not assigned grp`forms`formType or 
               grp`forms`formType eq "unknown" then
               form := StoreClassicalForms(grp, Case);
               if form cmpeq false then return "no form"; end if;
            end if;
            return 0;
        end if;
    end if;

    N := 1;
    process := RandomProcess (grp);
    while N le N_ext do
        // g := Random(grp);
        g := Random(process);
        grp`recognize`n +:= 1;
        TestRandomElement(grp,g,~ppd);
        N +:= 1;
        if b gt bx then
            b := Gcd(b,ppd);
        end if;
        if b eq bx or b eq 1 then
            // if we don't know the form yet then we need to test it here.
            if grp`forms`formType eq "unknown" then
                InfoRecog(2,"Determining invariant forms.-");
	        form := StoreClassicalForms(grp, Case);
                if form cmpeq false then return "no form"; end if;
            end if;
            // reset bx
            if Case in [ "linear",  "unitary", "orthogonalcircle" ] then 
                 bx := 1;
            end if;
        end if;

        if b eq bx and grp`forms`formType ne "unknown" then
            testext := RuledOutExtFieldParameters(grp,Case, N_ext);
            if testext then
                 InfoRecog(2,"The group is not an extension field group");
                 grp`recognize`possibleOverLargerField := false;
                 return N;
            end if;
        end if;
    end while;

    InfoRecog(1,"The group could preserve an extension field structure.");
    return true;

end function;
  
//////////////////////////////////////////////////////////////////////
// 
//  
//   Functions  for  ruling   out  the   nearly  simple groups
//  
//  Now  assume  that <grp>  is irreducible on the  underlying  vector
//  space and has a ppd(d,q;e_1)-element  and  a  ppd(d,q;e_2)-element
//  for d/2 < e_1 < e_2 <= d of which at least one is large and one is
//  basic.  Then Tables  6 and  7 in [2] list the nearly simple groups
//  which are possibilities for the commutator  subgroup  of <grp> and
//  the   elements   to  be  sought  in  order   to   rule  out  these
//  possibilities. The function IsGenericNearlySimple() tries  to find
//  these elements for  the various possibilities for d and q.  As all
//  groups in the table satisfy e_2 = e_1+1 the value of <case> has to
//  be the "linear".  If  <grp> contains a classical group  then  such
//  elements can  be found with high probability.   The output  of the
//  function is either  'false', if  <grp>  is  not nearly simple,  or
//  'true' and <grp> might be nearly simple.  If the output is 'false'
//  then we will know with certainty that <grp> is not a nearly simple
//  group.   If  the  output is  'true'  then  in  each  case  we know
//  precisely what the  possibilities are for the nearly simple group;
//  in most  cases there  is  a  unique  choice for  the simple  group
//  involved. Either <grp> is nearly simple or there is a small chance
//  that the output 'true'  is incorrect and  <grp> contains Omega. If
//  in  fact <grp>  contains Omega then the probability with which the
//  algorithm will return the statement 'true' can be made arbitrarily
//  small  depending  on  the  number  <N_sim>  of  random  selections
//  performed.
//  

IsAlternating := function(grp,N)

    q := grp`q;
    
    if grp`d ne 4 or q ne grp`p or (3 le q and q lt 23) then
        InfoRecog(2,"G' is not an alternating group.");
        return false;
    end if;

    if q eq 2 then
        gmod := GModule(grp);
        P := OrbitImage(grp,{x:x in gmod|x ne Zero(gmod)});
        RandomSchreier (P);
        if Order(P) ne 3*4*5*6*7 then
            InfoRecog(2,"G' is not an alternating group.");
            return false;
        else
            InfoRecog(2,"G' might be A_7.");
            Include(~grp`recognize`possibleNearlySimple,"A7");
            return true;
        end if;
    end if;

    if q ge 23 then
        InfoRecog( 3, "Searching for ppd(d,q;e)-element with e even.");
        fn := function(g) return (4 in grp`recognize`LE); end function;
        if FindCounterExample(grp,fn,N) ne false then
            InfoRecog(2,"G' is not an alternating group.");
            return false;
        end if;
        Include(~grp`recognize`possibleNearlySimple,"2.A7");
        InfoRecog(2,"G' might be 2.A_7.");
        return true;
    end if;

end function;

IsMathieu := function(grp,N)

     d := Degree(grp);
     q := grp`q;
     E := grp`recognize`E;

     if not [d,q] in [[5,3],[6,3],[11,2]] then
         InfoRecog(2,"G' is not a Mathieu group.");
         return false;
     end if;

     if d in [5,6] then
         fn := function(g)
             ord := Order(g);
             return (ord mod 121 eq 0 or (d eq 5 and ord eq 13) or 
                 (d eq 6 and ord eq 7));
         end function;
     else
         fn := function(g)
             return 6 in E or 7 in E or 8 in E or 9 in E;
         end function;
     end if;

     if FindCounterExample(grp,fn,N) ne false then
         InfoRecog(2,"G' is not a Mathieu group.");
         return false;
     end if;

     if d eq 5 then
         Include(~grp`recognize`possibleNearlySimple,"M_11");
         InfoRecog(2,"G' might be M_11.");
     elif d eq 6 then
         Include(~grp`recognize`possibleNearlySimple,"2M_12");
         InfoRecog(2,"G' might be 2M_12.");
     else
         Include(~grp`recognize`possibleNearlySimple,"M_23");
         Include(~grp`recognize`possibleNearlySimple,"M_24");
         InfoRecog(2,"G' might be M_23 or M_24.");
     end if;

     return true;

end function;

function IsPSL(grp,N)

    E := grp`recognize`E;
    LE := grp`recognize`LE;
    d := Degree(grp);
    q := grp`q;
    k := grp`k;
    p := grp`p;

    if d eq 3 and q eq 5 or q eq 2 then
        InfoRecog(2,  "G' is not PSL(2,7)");
        return false;
    end if;

    if d eq 6 and q eq 2 then
        InfoRecog(2,  "G' is not PSL(2,11)");
        return false;
    end if;

    if d eq 3 then
        str := "PSL(2,7)";
        i := [x[1]:j in [1..x[2]],x in Factorisation(q+1)];
        if q ne 5 and  i[#i] eq 3 and (#i eq 1 or i[#i-1] eq 2)
          and ((q^2-1) mod 9 ne 0 
          or Maximum([x[1]:j in [1..x[2]],x in Factorisation(q^2-1)]) gt 3) 
        then
            // q = 3*2^s-1 and q^2-1 has no large ppd
            fn := function(g) 
                ord := Order(g);
                return ((12 mod ord ne 0) and (p^(2*k)-1) mod ord eq 0);
            end function;
        elif q eq 5 then
            fn := function(g) return true; end function;
        else
            if p eq 3 or p eq 7 then 
                fn := function(g) return true;  end function;
            else fn := function(g) return 2 in LE; end function;
            end if;
        end if;
    elif [d,q] eq [5,3] then
        str := "PSL(2,11)";
        fn := function(g)
            ord := Order(g);
            return (ord mod 11^2 eq 0 or ord mod 20 eq 0);
        end function;
    elif d eq 5 and p ne 5 and p ne 11 then
        str := "PSL(2,11)";
        fn := function(g) return (3 in LE or 4 in LE); end function;
    elif [d,q] eq [6,3] then
        str := "PSL(2,11)";
        fn := function(g)
            return (Order(g) mod 11^2 eq 0 or 6 in E);
        end function;
    elif d eq 6 and p ne 5 and p ne 11 then
        str := "PSL(2,11)";
        fn := function(g) return (6 in E or 4 in LE); end function;
    else
        str := "PSL(2,r)"; fn := function(g) return true; end function;
    end if;

    i := FindCounterExample(grp,fn,N);
    if not i or IsEmpty(E) then
       InfoRecog(2, "G' might be " cat str );
       return true;
    end if;

    // test whether e_2 = e_1 + 1 and
    // e_1 + 1 and 2* e_2 + 1 are primes
    if i ne false or E[2]-1 ne E[1] or
        not IsPrime(E[1]+1) or not IsPrime(2*E[2]+1) then
        InfoRecog(2,  "G' is not " cat str);
        return false;
    end if;

    str := "PSL(2" cat IntegerToString(2*E[2]+1) cat ")";
    InfoRecog(2,"G' might be " cat str);
    Include(~grp`recognize`possibleNearlySimple,str);
    return true;

end function;
     
IsGenericNearlySimple := function (grp,Case,N)

    if Case ne "linear" then return false; end if;
    if N lt 0 then return true; end if;
    
    if not assigned grp`recognize then InitRecog(grp,Case); end if;
    isal := IsAlternating(grp,N) or IsMathieu(grp,N) or IsPSL(grp,N);
    if not isal then
       grp`recognize`possibleNearlySimple := {};
    end if;
    return isal;

end function;


/////////////////////////////////////////////////////////////////////////////
//
//  The following functions deal with the Non-generic cases. See [3].
//

/////////////////////////////////////////////////////////////////////////////
//
//  NonGenericLinear (grp, N) . . . . . . . . . . . . non-generic linear case
//
//  Recognise non-generic linear matrix groups over finite fields:
//  In order to prove that a group G <= GL( 3, 2^s-1) contains SL, we need to
//  find an element of order a multiple of 4 and a large and basic ppd(3,q;3)-
//  element
//
NonGenericLinear := function( grp, N )
    
    if not assigned grp`recognize then InitRecog(grp,"linear"); end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;
    order4 := false;
    d := grp`d;
    process := RandomProcess (grp);
    while  N gt 0  do 
        N := N - 1;
        // g := Random(grp);
        g := Random(process);
        grp`recognize`n +:= 1;
        if order4 eq false then
            ord := Order(g);
            if ord mod 4 eq 0 then
                order4 := true;
            end if;
        end if;
        
        if #grp`recognize`LE eq 0 then
            TestRandomElement( grp, g, ~null );
        end if;
        
        if #grp`recognize`LE ge 1 and 3 in grp`recognize`LE and
           3 in grp`recognize`basic and order4 eq true  then
               return true;
        end if;
    end while;

    
    return false;
    
end function;


/////////////////////////////////////////////////////////////////////////////
//
//
//  Find one element of each order in the list <orders>.
//
PropElementsOrder := function( orders )
    
    str := "Searching for elements with orders divisible by ";
    for o in orders do
        str := str cat IntegerToString(o) cat " ";
    end for;
    InfoRecog( 2, str );
    prop := function(g )
        
        ord := Order(g);
        grp := Parent(g);
        Include(~grp`recognize`orders,ord);
        InfoRecog( 2, "  Found element of order  " cat IntegerToString(ord));

        for i in [ 1 .. #orders ] do
            fnd := false;
            for ord in grp`recognize`orders do
                if  ord mod orders[i] eq 0 then
                    fnd := true;
                end if;
            end for;
            if fnd eq false then return false; end if;
        end for;
        
        return true;
    end function;
    
    return prop;
    
end function; 



/////////////////////////////////////////////////////////////////////////////
//
//
//  Find one element whose order is the list <orders>.
//
PropOneElementOrders := function( orders )
    
    str := "Searching for elements with orders divisible by ";
    for o in orders do
        str := str cat IntegerToString(o) cat " ";
    end for;
    InfoRecog( 2, str );
    prop := function (g)

	    grp := Parent(g);
            ord := Order(g);
            InfoRecog( 2, "  Found element of order "cat IntegerToString(ord));
            Include(~grp`recognize`orders, ord );
            for o in orders do 
                if ord mod o eq 0 then
	            return true;
                end if;
            end for;
            return false;
    end function;

    return prop;
    
end function;

PropDivides := function( ord )
    
    str :=  "Searching for elements of order > 2 and  dividing " 
             cat IntegerToString(ord);
    InfoRecog( 2, str );
    
    prop := function( g )
        
	grp := Parent(g);
        o := Order(g);
        Include(~grp`recognize`orders,o);
        if o gt 2 and ord mod o eq 0 then
            InfoRecog(2, "  Found element of order " cat IntegerToString(o) );
            return true;
        end if;
	return false;
    end function;
    
    return prop;
    
end function;

// EOB & ACN fix for CRD problem Dec 2011 
PropDividesNC := function( ord )
    
    str :=  "Searching for elements of order > 2 and  dividing " 
             cat IntegerToString(ord);
    InfoRecog( 2, str );
    
    prop := function( g )
        
	grp := Parent(g);
        o := Order(g);
        Include(~grp`recognize`orders,o);
        if o gt 2 and ord mod o eq 0 and IsCentral (grp, g^2) eq false then 
            InfoRecog(2, "  Found element of order " cat IntegerToString(o) );
            return true;
        end if;
	return false;
    end function;
    
    return prop;
    
end function;


PropTwoPower := function(  s )

        str := "Searching for elements of order 2^" cat IntegerToString(s);
        InfoRecog( 2, str );
    
	prop := function(g)

	    grp := Parent(g);
	    o := Order(g);
            Include(~grp`recognize`orders,o);
	    
            cf := Factorization(o);
	    ret := ( #cf eq 1 and cf[1][1] eq 2 and cf[1][2] eq s);
            if ret eq true then
                str := "  Found element of order " cat IntegerToString(o);
                InfoRecog( 2, str );
            end if;
            return ret;
	end function;
	return prop;
end function;

PropPPDD2 := function( e )
    
    
   InfoRecog( 2, "Searching for ppd( d, q; d/2)-elements" );
   prop := function (g)
       
        grp := Parent(g);
        if e in grp`recognize`E then return true; end if;

        d := grp`d;
        if not d mod 2 eq 0 then return false; end if;
        // compute the characteristic polynomial
        cpol := CharacteristicPolynomial( g );
        IsReducible(grp, cpol );
        ppd := IsPpdElementD2(BaseRing(grp),cpol,d,grp`q,1);
        if Type(ppd) eq BoolElt then return false; end if;
        Include(~grp`recognize`E,ppd[1]);
        if ppd[2] eq true then 
            Include(~grp`recognize`LE,ppd[1]);
        end if;

        if ppd[1] ne e then return false; end if;
        InfoRecog(2,"  Found ppd(d,q;d/2)-element");

        return true;
        
    end function;
    
    return prop;
    
end function;


PropLargePpd := function(  e )
    
   str := "Searching for large ppd( d, q; " cat IntegerToString(e)
          cat ")-elements";
   InfoRecog( 2, str );
   prop := function (g)
       
        grp := Parent(g);
        if e in grp`recognize`LE then
            return true;
        end if;                
        d := Degree(grp);
        // compute the characteristic polynomial
        cpol := CharacteristicPolynomial( g );
        IsReducible(grp, cpol );
        ppd := IsPpdElement(BaseRing(grp),cpol,d,grp`q,1);
        if Type(ppd) eq BoolElt then return false; end if;

        Include(~grp`recognize`E,ppd[1]);
        // ppd[2] is the boolean islarge
        if ppd[2] eq true then Include(~grp`recognize`LE,ppd[1]); end if;
        if ppd[1] ne e then return false; end if;
        if ppd[2] ne true then return false; end if;
        str := "  Found a large ppd(" cat IntegerToString(d) cat ", "
                cat IntegerToString(grp`q) cat "; " cat IntegerToString(ppd[1])
                cat  ")-element";
        InfoRecog(2,str);
        return true;
        
    end function;
    
    return prop;
    
end function;


PropBasic := function( e )
    
    str := "Searching for basic ppd( d, q; "  cat IntegerToString(e)
                cat  ")-elements";
    InfoRecog( 2, str );
    prop := function (g)
       
        grp := Parent(g);
        if e in grp`recognize`basic then
            return true;
        end if;                
        d := grp`d;
        // compute the characteristic polynomial
        cpol := CharacteristicPolynomial( g );
        IsReducible(grp, cpol );
        
        bppd := IsPpdElement(BaseRing(grp),cpol,d,grp`p,grp`k);
        if Type(bppd) ne BoolElt then
            Include(~grp`recognize`basic,bppd[1]);
            str := "  Found a basic ppd(" cat IntegerToString(d) cat ", "
                cat IntegerToString(grp`q) cat "; " cat 
                    IntegerToString(bppd[1]) cat  ")-element";
            InfoRecog( 2, str );
        end if;
        if e in grp`recognize`basic then
            return true;  
        end if;
        
        return false;
        
    end function;
    
    return prop;
    
end function;


PropLargeAndBasic := function( e )
    
   str :=  "Searching for large and basic ppd( d, q; " cat
              IntegerToString(e) cat ")-elements";
   InfoRecog( 2, str );

   prop := function (g)
       
        grp := Parent(g);
        if e in grp`recognize`LE and e in grp`recognize`basic then
            return true;
        end if;                
        d := grp`d;
        // compute the characteristic polynomial
        cpol := CharacteristicPolynomial( g );
        IsReducible( grp, cpol );
        ppd := IsPpdElement(BaseRing(grp),cpol,d,grp`q,1);
        if Type(ppd) eq BoolElt then return false; end if;

        Include(~grp`recognize`E,ppd[1]);
        if ppd[2] eq true then 
                Include(~grp`recognize`LE,ppd[1]);
        end if;
        if ppd[1] ne e then return false; end if;
        if ppd[2] ne true then return false; end if;

        bppd := IsPpdElement(BaseRing(grp),cpol,d,grp`p,grp`k);
        if Type(bppd) ne BoolElt then 
            Include(~grp`recognize`basic,ppd[1]);
            str := "  Found a large and basic ppd(" cat IntegerToString(d) 
                      cat ", " cat IntegerToString(grp`q) cat "; " 
                      cat IntegerToString(ppd[1])  cat  ")-element";
            InfoRecog( 2, str );
            return true;  
        end if;
        
        return false;
        
    end function;
    
    return prop;
    
end function;

/* EOB -- original function */

PropLargeAndSpecial := function( e )

    str :=  "Searching for large and special ppd( d, q; " cat
               IntegerToString(e) cat ")-elements";
    InfoRecog(2, str );
    prop := function (g)
       
        grp := Parent(g);
        d := grp`d;
        q := grp`q;
        
        // compute the characteristic polynomial of g
        cpol := CharacteristicPolynomial(  g );
        IsReducible(grp, cpol );

        ppd := IsPpdElementD2(BaseRing(grp),cpol,d,grp`q,1);
        if Type(ppd) eq BoolElt then return false; end if;

        Include(~grp`recognize`E,ppd[1]);
        if ppd[2] eq true then Include(~grp`recognize`LE, ppd[1]); end if;

        // test whether g is a large ppd-element
        if ppd[1] ne e then return false; end if;
        if ppd[2] ne true then return false; end if;
        
        
        // first we test whether the characteristic polynomial has
        // two factors of degree d/2. 
        facs := [x[1]:i in [1..x[2]],x in Factorisation(cpol)];
        deg := [Degree(x):x in facs];
        
        if #deg ne 2 or deg[1] ne deg[2] or deg[1] ne d/2 then
            return false;
        end if;
        
        str := "  Found a large and special ppd(" cat IntegerToString(d) 
               cat ", " cat IntegerToString(q) cat "; " 
               cat IntegerToString(ppd[1])  cat  ")-element";

        // Now we compute the r-part h of g
        r := ppd[3];
        s := Order(g);
        while s mod r eq 0 do s := Integers()! (s/r); end while;
	if s eq 1 and #facs eq 2 then 
            InfoRecog( 2, str );
	    return true;
        end if;
        h := g^s;
        gmod := GModule(sub< grp| h>);
	if #CompositionFactors( gmod )  eq 2 then
            InfoRecog( 2, str );
	    return true;
        end if;
	return false;
	
    end function;
    
    return prop;
    
end function;

/* EOB -- new function */

PropLargeAndSplitting := function( e )

    str :=  "Searching for large and splitting ppd( d, q; " cat
               IntegerToString(e) cat ")-elements";
    InfoRecog(2, str );
    prop := function (g)
       
        grp := Parent(g);
        d := grp`d;
        q := grp`q;
        
        // compute the characteristic polynomial of g
        cpol := CharacteristicPolynomial(  g );
        IsReducible(grp, cpol );

        ppd := IsPpdElementD2(BaseRing(grp),cpol,d,grp`q,1);
        if Type(ppd) eq BoolElt then return false; end if;

        Include(~grp`recognize`E,ppd[1]);
        if ppd[2] eq true then Include(~grp`recognize`LE, ppd[1]); end if;

        // test whether g is a large ppd-element for e
        if ppd[1] ne e then return false; end if;
        // ppd[2] is the boolean islarge
        if ppd[2] ne true then return false; end if;
        
        
        // first we test whether the characteristic polynomial has
        // two factors of degree d/2. 
        facs := [x[1]:i in [1..x[2]],x in Factorisation(cpol)];
        deg := [Degree(x):x in facs];
        
        if #deg ne 2 or deg[1] ne deg[2] or deg[1] ne d/2 then
            return false;
        end if;
        
        str := "  Found a large and splitting ppd(" cat IntegerToString(d) 
               cat ", " cat IntegerToString(q) cat "; " 
               cat IntegerToString(ppd[1])  cat  ")-element";

        // Now we compute the r-part h of g
        s := Order(g);
        s := Gcd( s, ppd[3] );
        h := g^s;
        // now order(h) is the product of all ppds dividing |g|, see
        // Section 6.1 page 250 of [3]
        if h eq One(grp) then return false; end if;
        gmod := GModule(sub< grp| h>);
        cf := CompositionFactors( gmod );
        // cf is a list of composition factors of the vector space
        // as an <h>-module
	if #cf eq 2 and IsIsomorphic(cf[1],cf[2]) ne true then
            InfoRecog( 2, str );
	    return true;
        end if;
	return false;
	
    end function;
    
    return prop;
    
end function;


FindElementsProp := function( properties )

    prop := function( g )
        
        grp := Parent(g);
        for f in properties do
            if f( grp, g ) eq false then
                return false;
            end if;
        end for;
        
        return true;
        
    end function;
    
    return prop;
    
end function;

FindVec := function(V,phi)

    v := Random(V); 
    while InnerProduct(v * phi, v) ne 0 or v eq 0*v do
        v := Random( V );
    end while;

    return v;
end function;



//////////////////////////////////////////////////////////////////////
//
//  FindBase (d, q, phi) . . . . . . . . . . . find appropriate basis
//
//  The following function returns a matrix B such that B qf B^T has
//  the form ( 0, 0, 0, -1), ( 0, 0, 1, 0 ) (0, 1, 0, 0), (-1, 0, 0, 0)
//
FindBase := function( d, q, phi)


     form2 := MatrixAlgebra(GF(q), 4)![0,0,0,-1,0,0,1,0,0,1,0,0,-1,0,0,0];
     mat1 :=TransformForm(phi,"orthogonalplus");
     mat2 :=TransformForm(form2,"orthogonalplus");
     mat := mat2 * mat1^-1;

     return mat;

end function;


/////////////////////////////////////////////////////////////////////////////
//
//  FindBaseC2 (d, q, qf) . . . . . . . . . find appropriate basis in char 2
//
//  The following function returns a matrix B such that Q(vB) = Q_0(v)
//  where Q_0 is the standard quadratic form given in Taylor p. 187
//
FindBaseC2 := function( d, q, qf)

     form2 := MatrixAlgebra(GF(q),4)![0,0,0,-1,0,0,1,0,0,0,0,0,0,0,0,0];
     mat  :=TransformForm(qf,"orthogonalplus");
     mat2 :=TransformForm(form2,"orthogonalplus");
     mat := mat2 * mat^-1;
     //print mat * phi * Transpose(mat) eq form2;

     return mat;
//
//    V := VectorSpace(GF(q), d);
//
//    v1 := FindVec(V,qf);
//    v3 := FindVec(V,qf);
//    while InnerProduct( (v1+v3) * qf, (v1+v3)) eq 0 do
//        v3 := FindVec(V,qf);
//    end while;
//    v3 := v3/InnerProduct((v1+v3)*qf,(v1+v3));
//    
//    v2 := FindVec(V,qf);
//    while InnerProduct((v1+v2) * qf, (v1+v2)) ne 0 or
//          InnerProduct((v2+v3) * qf, (v2+v3)) ne 0 do
//        v2 := FindVec(V,qf);
//    end while;
//    
//    v4 := FindVec(V,qf);
//    while InnerProduct( (v1+v4) * qf, (v1+v4)) ne 0  or
//          InnerProduct( (v2+v4) * qf, (v2+v4)) eq 0  or
//          InnerProduct( (v3+v4) * qf, (v3+v4)) ne 0  do
//        v4 := FindVec(V,qf);
//    end while;
//    v4 := v4/InnerProduct((v2+v4)*qf,(v2+v4));
//
//    v := [ v1[1], v1[2], v1[3], v1[4], v2[1], v2[2], v2[3], v2[4], 
//           v4[1], v4[2], v4[3], v4[4], v3[1], v3[2], v3[3], v3[4]];
//    
//    return GL( d, GF(q)) ! v;
//
end function;

KroneckerFactorsTwoDim := function(g, q)


    mats := MatrixAlgebra( GF(q), 4);
    smats := MatrixAlgebra( GF(q), 2);
    A := smats!ExtractBlock( mats!g, 1, 1, 2, 2 );
    B := smats!ExtractBlock( mats!g, 1, 3, 2, 2 );
    C := smats!ExtractBlock( mats!g, 3, 1, 2, 2 );
    D := smats!ExtractBlock( mats!g, 3, 3, 2, 2 );
    if Determinant(A) eq 0 then
        return [];
    end if;
    b := (B * A^-1)[1][1];
    c := (C * A^-1)[1][1];
    d := (D * A^-1)[1][1];
    I := ScalarMatrix( smats, 1);

    if B*A^-1 ne I*b or C*A^-1 ne I*c or D*A^-1 ne I*d then
        return [];
    end if;

    return [ smats![ 1, b, c, d], A];
end function;

Decompose := function(grp, N, sz)

        d := grp`d;
        q := grp`q;
        smats := MatrixAlgebra( GF(q), 2);
    
        phi := StoreClassicalForms( grp, "orthogonalplus" );
        if phi eq false or grp`forms`bilinFlag ne true then
            InfoRecog(2,"No invariant classical form found");
            return false;
        end if;

        if assigned grp`forms`bc then
            bc := grp`forms`bc;
        else
            if q mod 2 ne 0 then 
                InfoRecog(3,"Performing base change");
                if Type(grp`forms`bilinearForm) eq BoolElt then
                    InfoRecog(2,"Decompose: No bilinear form found");
                    return false;
                end if;
                bc := FindBase (d, q, grp`forms`bilinearForm);
                InfoRecog(3,"Computed base change matrix");
                bc := bc^-1;
                grp`forms`bc := bc;
            else 
                if Type(grp`forms`quadraticForm) eq BoolElt then
                    InfoRecog(2,"Decompose: No quadratic form found");
                    return false;
                end if;
                bc := FindBaseC2 (d, q, grp`forms`quadraticForm);
                InfoRecog(3,"Computed base change matrix for char 2\n");
                bc := bc^-1;
                grp`forms`bc := bc;
            end if;
        end if;
     

        sq1 := {smats|};
        sq2 := {smats|};
        m  := ScalarMatrix( MatrixAlgebra(BaseRing(grp), 2), 
                    BaseRing(grp)!PrimitiveElement(GF(q)));

        process := RandomProcess (grp);
        scalars := sub< GL(2,q) | m >;
        for i in [ 1..20*N] do
            // g := Random(grp);
            g := Random(process);
            grp`recognize`n +:= 1;
            kf := KroneckerFactorsTwoDim( g^bc, q );
            if #kf eq 0 then 
                kf := KroneckerFactorsTwoDim( (g^2)^bc, q );
            end if;
            if #kf ne 0 then
                sq1 := sq1 join {smats|kf[1]};
                sq2 := sq2 join {smats|kf[2]};
                gp1 := sub<GL(2, GF(q))|sq1>;
                gp2 := sub<GL(2, GF(q))|sq2>;
                if (Order(gp1/(gp1 meet scalars)) mod sz  eq 0)
                   and (Order(gp2/(gp2 meet scalars)) mod sz eq 0) then
                    return true;
                end if;
            end if;
        end for;      
        return false;

end function;    

PropPlusPlus := function(grp)
    
        InfoRecog(2, "Searching for (+,+)-elements" );
        form := StoreClassicalForms( grp, "orthogonalplus");
        if form cmpeq false or grp`forms`bilinFlag eq false then
            error "group does not preserve a bilinear form";
        end if;
        phi :=  grp`forms`bilinearForm;
        d := grp`d;
        q := grp`q;

        if assigned grp`forms`bc then
            bc := grp`forms`bc;
        else
            if IsOdd (q) then 
                InfoRecog(3,"Performing base change");
                bc := FindBase (d, q, phi);
                InfoRecog(3,"Computed base change matrix");
                bc := bc^-1;
                grp`forms`bc := bc;
            else 
                if Type(grp`forms`quadraticForm) eq BoolElt then
                    InfoRecog(2,"PropPlusPlus: No quadratic form found");
                    return false;
                end if;
                bc := FindBaseC2 (d, q, grp`forms`quadraticForm);
                InfoRecog(3,"Computed base change matrix for char 2\n");
                bc := bc^-1;
                grp`forms`bc := bc;
            end if;
        end if;
        

        prop := function( g )
            
            kf := KroneckerFactorsTwoDim( g^bc, q );
            if #kf eq 0 then 
                kf := KroneckerFactorsTwoDim( (g^2)^bc, q );
            end if;
            if #kf eq 0 then
                return false; 
            end if;
            o1 := ProjectiveOrder( kf[1] );
            o2 := ProjectiveOrder( kf[2] );
            ret := (q+1) mod o1 eq 0 and (q+1) mod o2 eq 0;
            ret := ret and ((q mod 2 eq 0 and o1 gt 2 and o2 gt 2)
                        or  (q mod 2 ne  0 and o1 gt 4 and o2 gt 4));
            // new code added July 2010
            F := BaseRing (Parent (g)); a := Degree (F);
            p := Characteristic (F);
            if not IsTwoPowerMinusOne(q) and q ne 8 then
               if not exists{ r: r in PrimeBasis (o1) |
                  IsPrimitivePrimeDivisor(p, (2*a), r)} then
                  ret :=  false;
               end if;
               if not exists{ r: r in PrimeBasis (o2) |
                  IsPrimitivePrimeDivisor( p, (2*a), r)} then
                  ret :=  false;
               end if;
            elif q eq 8 then
               if not o1 mod 9 eq 0 or not o2 mod 9 eq 0 then
                  ret :=  false;
               end if;
            else
               if o1 lt (q+1)/2 or o2 lt (q+1)/2 then ret := false; end if;
            end if;
            // end of new code
            if ret eq true then
                InfoRecog(2, "  Found a (+,+)-element" );
            end if;
	    return ret;
        end function;
        
        return prop;
end function;    


PropMinusMinus := function(grp)
    
    
        InfoRecog(2, "Searching for (-,-)-elements" );
        form := StoreClassicalForms( grp, "orthogonalplus" );
        if form cmpeq false or grp`forms`bilinFlag eq false then
            error "group does not preserve a bilinear form";
        end if;
        phi :=  grp`forms`bilinearForm;
        d := grp`d;
        q := grp`q;
        if assigned grp`forms`bc then
            bc := grp`forms`bc;
        else
            if IsOdd (q) then 
                InfoRecog(3,"Performing base change");
                bc := FindBase (d, q, phi);
                InfoRecog(3,"Computed base change matrix");
                bc := bc^-1;
                grp`forms`bc := bc;
            else 
                if Type(grp`forms`quadraticForm) eq BoolElt then
                    InfoRecog(2,"PropMinusMinus: No quadratic form found");
                    return false;
                end if;
                bc := FindBaseC2 (d, q, grp`forms`quadraticForm);
                InfoRecog(3,"Computed base change matrix for char 2\n");
                bc := bc^-1;
                grp`forms`bc := bc;
            end if;
        end if;

        
        prop := function( g )
            
            kf := KroneckerFactorsTwoDim( g^bc, q);
            if #kf eq 0 then 
                kf := KroneckerFactorsTwoDim( (g^2)^bc, q);
            end if;
            if #kf eq 0 then 
                return false; 
            end if;
            o1 := ProjectiveOrder( kf[1] );
            o2 := ProjectiveOrder( kf[2] );
            ret := (q-1) mod o1 eq 0 and (q-1) mod o2 eq 0;
            ret := ret and ((q mod 2 eq 0 and o1 gt 2 and o2 gt 2)
                        or  (q mod 2 ne  0 and o1 gt 4 and o2 gt 4));
            if ret eq true then
                InfoRecog(2, "  Found a (-,-)-element" );
            end if;
	    return ret;
        end function;
        
        return prop;
	
end function;


PropPlusMinus := function(grp)

        InfoRecog(2, "Searching for (+,-)-elements or (-,+)-elements" );
        form := StoreClassicalForms( grp, "orthogonalplus");
        if form cmpeq false or grp`forms`bilinFlag eq false then
            error "group does not preserve a bilinear form";
        end if;
        phi :=  grp`forms`bilinearForm;
        d := grp`d;
        q := grp`q;
        if assigned grp`forms`bc then
            bc := grp`forms`bc;
        else
            if IsOdd (q) then 
                InfoRecog(3,"Performing base change");
                bc := FindBase (d, q, phi);
                InfoRecog(3,"Computed base change matrix");
                bc := bc^-1;
                grp`forms`bc := bc;
            else 
                if Type(grp`forms`quadraticForm) eq BoolElt then
                    InfoRecog(2,"PropPlusMinus: No quadratic form found");
                    return false;
                end if;
                bc := FindBaseC2 (d, q, grp`forms`quadraticForm);
                InfoRecog(3,"Computed base change matrix for char 2\n");
                bc := bc^-1;
                grp`forms`bc := bc;
            end if;
        end if;

        
        prop := function( g )
            
            kf := KroneckerFactorsTwoDim( g^bc, q );
            if #kf eq 0 then 
                kf := KroneckerFactorsTwoDim( (g^2)^bc, q );
            end if;
            if #kf eq 0 then 
                return false; 
            end if;
            o1 := ProjectiveOrder( kf[1] );
            o2 := ProjectiveOrder( kf[2] );
            ret := ((q+1) mod o1 eq 0 and (q-1) mod o2 eq 0 ) or
            ((q-1) mod o1 eq 0 and (q+1) mod o2 eq 0 );
            ret := ret and ((q mod 2 eq 0 and o1 gt 2 and o2 gt 2)
                        or  (q mod 2 ne  0 and o1 gt 4 and o2 gt 4));
            if ret eq true then
                InfoRecog(2, "  Found a (+,-)-element or (-,+)-element" );
            end if;
	    return ret;
        end function;
        
        return prop;
end function; 


    
FindExample := function ( grp, prop, N )
        
        
        flag := [ 0 : i in [1 .. #prop] ];
        
        process := RandomProcess (grp);
        for i in [ 1 .. N ] do 
            // g := Random(grp);
            g := Random(process);
            grp`recognize`n := grp`recognize`n + 1;
            for j in [1 .. #prop] do 
                if flag[j] eq 0 and prop[j](g) then
                    flag[j] := 1;
                end if;
            end for;
            if not 0 in flag  then return true; end if;
        end for;
        
        return false;
end function;

//
//  Test whether q = 2^s - 1 for some s > 0
// 
IsTwoPowerMinusOne := function( q )
    
    r := Factorization(q+1);
    
    if #r gt 1 or r[1][1] ne 2 then 
        return false;
    end if;
    
    return true;
    
end function;


//
//  Test whether q = 3 * 2^s - 1 for some s >= 0
// 
IsThreeTwoPowerMinusOne := function( q )
    
    r := Factorization(q+1);
    
    if #r eq 1 and r[1][1] eq 3 and r[1][2] eq 1 then 
        return true;
    end if;
    
    if #r gt 2 or r[1][1] ne 2  or ( r[2][1] ne 3 or r[2][2] ne 1) then 
        return false;
    end if; 
   
    return true;
    
end function;

/////////////////////////////////////////////////////////////////////////////
//
//  Recognise non-generic symplectic matrix groups over finite fields
//
NonGenericSymplectic := function(grp,N)

    if not assigned grp`recognize then InitRecog(grp,"symplectic"); end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;
    
    d := grp`d;
    q := grp`q;

    if d eq 8 and q eq 2 then
        prop := [ PropElementsOrder(  [ 5, 9, 17 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 2 then
        prop := [ PropElementsOrder( [ 5, 7, 9 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 3 then
        prop := [ PropElementsOrder( [ 5, 7 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 3 then
        prop := [ PropElementsOrder( [ 5, 9 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 2 then
        V := VectorSpace(GF(2), 4);
        zero := Zero (V);
        V := { v: v in V | v ne zero}; 
        P := OrbitImage(grp, V);
        str :=  "Permutation representation on 15 non-zero vectors has order" 
                cat IntegerToString(Order(P));
        InfoRecog( 2, str );
        // fix by EOB November 2008: Sp(4, 2) has order 720  
        RandomSchreier (P);
        return Order(P) mod  720 eq 0;
    elif d eq 4 and q eq 5 then
        prop := [ PropElementsOrder( [ 13, 15 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and not IsTwoPowerMinusOne(q) and 
                   not IsThreeTwoPowerMinusOne(q) and q ne 2 then
        prop := [ PropLargeAndBasic( 4 ), PropLargeAndSplitting(  2 ) ];
        return FindExample( grp, prop, N );
    elif d eq 4  and q ge 7 and IsTwoPowerMinusOne(q) then
        prop := [ PropLargeAndBasic(4), PropOneElementOrders( [4]) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q ge 11 and IsThreeTwoPowerMinusOne(q) then
        prop := [ PropLargeAndBasic(  4), 
                  PropOneElementOrders( [3,4] )];
        return FindExample( grp, prop, N );
    else
        InfoRecog(2,"NonGenericSymplectic: d and q must have been be generic");
        return false;
    end if;
    
    
end function;

/////////////////////////////////////////////////////////////////////////////
//        
//  Recognise non-generic orthogonal plus matrix groups over finite fields
//
        
NonGenericOrthogonalPlus := function(grp,N)
    

    if not assigned grp`recognize then InitRecog(grp,"orthogonalplus"); end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;
    
    d := grp`d;
    q := grp`q;

    // EOB -- only way I can get 8 to work correctly is to set N high 
    if d eq 8 then N := Maximum (N, 200); end if;

    if d eq 10 and q eq 2 then
        prop := [ PropElementsOrder( [ 17,31 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 8 and q eq 2 then
        prop := [ PropElementsOrder( [ 7,9,10,15 ] ) ];
        if not FindExample( grp, prop, N ) then return false; end if;
        V := VectorSpace( BaseRing(grp), d);
        v := V.1;
        orb := Orbit( grp, v );
        if not #orb in [ 120, 135 ] then return false; end if;
	P := OrbitImage( grp, orb);
        RandomSchreier (P);
	return #P mod  174182400 eq 0;
    elif d eq 8 and q eq 3 then
        prop := [ PropElementsOrder( [ 7,13 ] ) ];
        if not FindExample( grp, prop, N ) then return false; end if;
        V := VectorSpace( BaseRing(grp), d);
        U := sub< V | V.1 >;
        orb := Orbit(grp, U);
	if not #orb in [ 1080, 1120] then return false; end if;
        P := OrbitImage(grp, U);
        RandomSchreier (P);
        if #P mod 4952179814400 ne 0 then return false; end if;
        return true;
    elif d eq 8 and  q eq 5 then 
        prop := [ PropElementsOrder( [ 3,7,13 ] ) ];
        good := FindExample( grp, prop, N ) and RandomElementOfOrder (grp, 312);
        if not good then return false; end if;
        V := VectorSpace (grp);
        U := sub<V | V.1>;
        P := OrbitImage(grp, U);
        RandomSchreier (P); 
        if #P mod 8911539000000000000 ne 0 then return false; end if;
        return true;
    elif d eq 8 and (q eq 4 or q gt 5) then 
        prop := [ PropLargeAndBasic( 6 ), PropLargeAndSplitting( 4) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 2 then
        prop := [ PropElementsOrder( [7, 15 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 3 then
        prop := [ PropElementsOrder( [5, 13 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q ge 4 then
        prop := [ PropLargeAndBasic( 4 ), PropPPDD2( 3 ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and (q eq 8 or q ge 11) then
        prop := [PropPlusPlus(grp), PropPlusMinus(grp), 
                 PropMinusMinus(grp)];
        return FindExample( grp, prop, N+10 );
    elif d eq 4 and q eq 2 then
        RandomSchreier (grp);
        if #grp mod 36 ne 0 then return false; end if;
        return Decompose( grp, N, 2 * 3  );
    elif d eq 4 and q eq 3 then
        RandomSchreier (grp);
        if Order(grp) mod 288 ne 0 then return false; end if;
        return Decompose( grp, N, 3 * 4  );
    elif d eq 4 and q eq 4 then
        V := VectorSpace( BaseRing(grp), d);
        v := V.1;
        o := Orbit( grp, v );
        if not #o in [ 75, 60 ] then return false; end if;
        P := OrbitImage( grp, o);
        RandomSchreier (P);
        if #P mod 3600 ne 0 then return false; end if;
        return Decompose(grp, N, 3);
    elif d eq 4 and q eq 5 then
        V := VectorSpace( BaseRing(grp), d);
        o := Orbit( grp, V.1 );
        if not #o in [ 144, 120 ] then return false; end if;
        P := OrbitImage( grp, o);
        RandomSchreier (P);
        return Order(P) mod 7200 eq 0;
    elif d eq 4 and q eq 7 then
        V := VectorSpace( BaseRing(grp), d);
        o := Orbit( grp, V.1 );
        str :=  "The group has an orbit of length " cat IntegerToString(#o);
        str := str cat " on the non-zero vectors";
        InfoRecog(2, str);
        if not #o in [ 384, 336 ] then return false; end if;
        P := OrbitImage( grp, o);
        RandomSchreier (P);
        str := "The permutation representation of the group on " cat
               "this orbit has order ";
        str := str cat IntegerToString(Order(P));
        InfoRecog(2, str);
        if  Order(P) mod 56448 ne 0 then return false; end if;
        return Decompose( grp, N, 168 );
    elif d eq 4 and q eq 9 then
        V := VectorSpace( BaseRing(grp), d);
        o := Orbit( grp, V.1 );
        str :=  "The group has an orbit of length " cat IntegerToString(#o);
        str := str cat " on the non-zero vectors";
        InfoRecog(2, str);
        if not #o in [ 800, 720 ] then return false; end if;
        P := OrbitImage( grp, o);
        RandomSchreier (P);
        str := "The permutation representation of the group on this orbit "
                cat "has order ";
        str := str cat IntegerToString(Order(P));
        InfoRecog(2, str);
        return Order(P) mod 259200 eq 0;
    else
        InfoRecog(2,"NonGenericO+: d and q must have been be generic"); 
        return false;
    end if;
     
end function;
 
/////////////////////////////////////////////////////////////////////////////
//
//  Recognise non-generic orthogonal minus matrix groups over finite fields
//  
NonGenericOrthogonalMinus := function(grp,N )

    if not assigned grp`recognize then InitRecog(grp,"orthogonalminus");end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;
    
    d := grp`d;
    q := grp`q;

    if d eq 8 and q eq 2 then
        prop := [ PropElementsOrder( [ 9, 17 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 3 then
        prop := [ PropElementsOrder( [ 5, 7, 9 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q eq 2 then 
        prop := [ PropElementsOrder( [ 5, 9 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 2 then 
        prop := [ PropElementsOrder( [ 3, 5 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 3 then
//        prop := [ PropElementsOrder( [ 5 ] ) ];
//        if not FindExample( grp, prop, N ) then return false; end if;
//        orbs := LineOrbits( grp );
//        str :=  "The group has " cat IntegerToString(#orbs);
//        str := str cat " orbits on 1-subspaces";
//        InfoRecog(2, str);
//        return #orbs eq 3;
        // fix EOB October 2008 
        prop := [ PropElementsOrder( [ 3, 5 ] ) ];
        if not FindExample( grp, prop, N ) then return false; end if;
        orbs := LineOrbits( grp );
        str :=  "The group has " cat IntegerToString(#orbs);
        str := str cat " orbits on 1-subspaces";
        InfoRecog(2, str);
        return #orbs le 3; 
    elif d eq 4 and q ge  4 then
        process := RandomProcess (grp);
        while N gt 0 do
            N := N-1;
            // g := Random(grp);
            g := Random(process);
            cpol := CharacteristicPolynomial(g);
            ppd := IsPpdElement(BaseRing(grp),cpol,d,grp`q,1);
            if Type(ppd) ne BoolElt and ppd[1] eq 4 and ppd[2] eq true then
                // found a basic lppd( 4, q; 4)-element
                InfoRecog( 2, "  Found a ppd( 4,q; 4)-element" );
                for x in Generators(grp) do
                    c := (x, g);
                    if not IsIdentity (c) and not IsIdentity ((c, g)) then
                        InfoRecog( 2, "The group is not O-(2,q^2)" );
                        // Bug fix 10.5.2007 ACN
	                return true;
                    end if;
                end for;
            end if;
        end while;
        return false;
    else
        InfoRecog(2, "NonGenericO-: d and q must have been generic");
        return false;
    end if;
end function;

// EOB & ACN fix for CRD problem Dec 2011 
PropLargeAndBasicGT5 := function(g)

    o := Order (g);
    if o le 5 then return false; end if;

    F := BaseRing (Parent (g));
    q := #F;
    r := Characteristic (F);
    a := Ilog (r, q);
    basis := PrimeBasis (o);
    Exclude(~basis, 2);
  
    S := {p : p in basis | (q + 1) mod p eq 0 and 
                 forall {i :i in [1..2 * a - 1] | r^i - 1 mod p ne 0}};
    if #S eq 0 then return false; end if;

    p := Maximum (S);

    if (p eq 3 and o mod 9 ne 0) then return false; end if;

    // we now know that p divides q^2 - 1, o is large and basic and o gt 5 
    if p eq 5 and IsCentral (Parent(g), g^5) eq true then
       return false;
    end if;
    
    return true;
end function;

// Note that PropLargeAndBasic(2) returns a function which
// takes as argument a group element.

/////////////////////////////////////////////////////////////////////////////
//
//  Recognise non-generic orthogonal circle matrix groups over finite fields
//
NonGenericOrthogonalCircle := function(grp,N)

    if not assigned grp`recognize then 
        InitRecog(grp,"orthogonalcircle");
    end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;

    d := grp`d;
    q := grp`q;

    if IsOdd (d) and IsEven (q) then
        InfoRecog(1,
        "The group is not irreducible and our algorithm does not apply");
        grp`recognize`applies := false;
        return "Does not apply";
    end if;
    if d eq 7 and q eq 3 then
        prop := [ PropElementsOrder( [ 5, 7, 13 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 5 and q eq 3 then
        prop := [ PropElementsOrder( [ 5, 9] ) ];
        return FindExample( grp, prop, N );
    elif d eq 5 and q ge 5 then 
        prop := [ PropLargePpd(  4 ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 3 then 
        prop := [ PropElementsOrder( [ 3 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 5 then 
        prop := [ PropElementsOrder( [ 3, 5 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 7 then 
        prop := [ PropElementsOrder( [ 4, 7 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 9 then 
        // fix from ACN June 7, 2012 replace two commented lines by next f 
        // f := function(x) return (PropOneElementOrders([4,8])(x) and 
        //                 not IsCentral(grp, sub<grp|x^2>)); end function;
        f := function(x) return Order(x) in [4,8] and
                    not IsCentral(grp, sub<grp|x^2>); end function;
        prop := [ PropElementsOrder( [ 3, 4, 5 ] ), f ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 11 then 
        prop := [ PropElementsOrder(  [ 3, 11 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 19 then 
        prop := [ PropElementsOrder( [ 5, 9, 19 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q ge 31 and IsTwoPowerMinusOne(q) then 
        s := Factorization(q+1)[1][2];
        prop := [ PropTwoPower(s-1), PropDivides(q-1) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and q gt 11 and IsThreeTwoPowerMinusOne(q) then 
        s := Factorization(q+1)[1][2];
        prop := [ PropTwoPower(s-1), PropDivides(q-1) ];
        return FindExample( grp, prop, N );
    elif d eq 3 and not IsThreeTwoPowerMinusOne(q) and not 
	IsTwoPowerMinusOne(q) then 
        prop := [ PropLargeAndBasicGT5, PropDividesNC(q-1) ];
        g := FindExample( grp, prop, N );
        return FindExample( grp, prop, N );
    else
        InfoRecog(2, "NonGenericOCircle: d and q must have been be generic");
        return false;
    end if;

return false;

end function;

/////////////////////////////////////////////////////////////////////////////
//
//  Recognise non-generic unitary matrix groups over finite fields
//
NonGenericUnitary := function(grp, N)


    if not assigned grp`recognize then 
        InitRecog(grp,"unitary");
    end if;
    if not assigned grp`recognize`orders then 
        grp`recognize`orders := {};
    end if;
    
    d := Degree(grp);
    q := grp`q;

    if d eq 6 and q eq 4 then
        prop := [ PropElementsOrder( [ 7, 10, 11 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 6 and q ge 9 then
        prop := [ PropLargeAndBasic( 5), PropPPDD2( 3 ) ];
        return FindExample( grp, prop, N );
    elif d eq 5 and q eq 4 then 
        prop := [ PropElementsOrder( [ 11, 12 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 4 then 
        prop := [ PropElementsOrder( [ 5, 9 ] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q eq 9 then 
        prop := [ PropElementsOrder( [ 5, 7, 9] ) ];
        return FindExample( grp, prop, N );
    elif d eq 4 and q gt 9 then 
        str :=  "As q^3-1 mod 7 = 0 we need an element of"
                cat "order > 7 and divisible by 7";
        InfoRecog( 2, str );
        IsOther := function( r, q )
	    for x in Factorization( q^2 - 1 ) do
                if x[1] eq r then return false; end if;
            end for;
	    for x in Factorization( q - 1 ) do
                if x[1] eq r then return false; end if;
            end for;
            return true;
        end function;
	fn := function(x) 
            grp := Parent(x);
            q := grp`q;
            f := Factorization( q^3 -1 );
            for  x in f do
                if IsOther( x[1], q ) then return true; end if;
            end for;
            if (q^3 -1) mod 7 eq 0 and (q^2 - 1) mod 7 ne 0 and
                (q - 1) mod 7 ne 0 then
                o := Order(x); 
                Include(~grp`recognize`orders,o);
                return o mod 7 eq 0 and o mod  (7*(q-1)) ne 0;
            end if;
            return true;
        end function;
        g := function(x) return PropBasic(3)(x) and fn(x); end function;
        prop := [ g, PropPPDD2(2)];
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 4 then
        V := VectorSpace( BaseRing(grp), d);
        U := { V | v: v in V | v ne 0 }; 
        P := OrbitImage(grp, U);
        RandomSchreier (P);
        str :=  "Permutation representation on  non-zero vectors"
         cat  "has order " cat IntegerToString(Order(P)) ;
        InfoRecog( 2, str );
        if Order(P) mod 216 eq 0 then return true; end if;
        return false;
    elif d eq 3 and q eq 9 then 
        f := function(x) return (PropOneElementOrders( [6])(x) and 
                   not IsCentral(grp, sub<grp|x^3>)); end function;
        prop := [ PropElementsOrder( [ 7 ] ), f ];
        InfoRecog( 2, "The cube of the  element of order 6 is not central" );
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 16 then 
        f := function(x) return (PropOneElementOrders( [5])(x) and
                   not IsCentral(grp, sub<grp|x>)); end function;
        prop := [ PropElementsOrder( [ 13 ] ), f ];
        InfoRecog( 2, "The element of order 5 is not central" );
        return FindExample( grp, prop, N );
    elif d eq 3 and q eq 25 then 
        f := function(x) return PropOneElementOrders([8])(x) and 
                   not IsCentral(grp, sub<grp|x^4>); end function;
        prop := [ PropElementsOrder( [ 5, 7 ] ),  f];
        InfoRecog( 2, "The element of order 8 is not central" );
        return FindExample( grp, prop, N );
    elif d eq 3 and q ge 49  then 
        f := function(x)
            local o;
            grp := Parent(x);
	    o := ProjectiveOrder(x);
            if o ge 3 and (q-1) mod o eq 0 then
               str :=  "  Found element of projective order ";
               str := str cat IntegerToString(o);
               InfoRecog(2, str );
               return true;
            end if;
	    return false;
        end function;
        str := "Searching for elements of order > 3 mod scalars"
              cat " and dividing " cat IntegerToString(q-1);
        InfoRecog(2, str );
        prop := [ function(x) 
                  return (PropLargeAndBasic(3)(x) and 
                         (ProjectiveOrder(x) gt 7 ) ); end function, f];
        return FindExample( grp, prop, N );
    else
        InfoRecog(2, "NonGenericUnitary: d and q must have been be generic");
        return false;
    end if;

    return false;

end function;

        
/////////////////////////////////////////////////////////////////////////////
// 
// NonGeneric( grp, Case, N ) . . . . . . . .  handles the non-generic cases
//
//  Recognise non-generic matrix groups over finite fields
//

NonGeneric := function ( grp, Case, N )

    if Case eq "linear" then
        return NonGenericLinear( grp, N );
    elif Case eq "symplectic" then
        return NonGenericSymplectic( grp, N );
    elif Case eq "unitary" then 
        return NonGenericUnitary( grp, N );
    elif Case eq "orthogonalplus" then 
        return NonGenericOrthogonalPlus( grp, N );
    elif Case eq "orthogonalminus" then 
        return NonGenericOrthogonalMinus( grp, N );
    elif Case eq "orthogonalcircle" then 
        return NonGenericOrthogonalCircle( grp, N );
    else
        InfoRecog(2, "NonGeneric: unknown Case");
        return false;
    end if;

    
end function;

    
//////////////////////////////////////////////////////////////////////
//
//  RecogniseClassicalNP(grp[,case[,N]]) . . . . . . .
//                    . . . .  Does <grp>  contain a classical group?
// 
//  Input:
//
//  - a group <grp>, which is a subgroup of  GL(d,q) 
//  - an optional string <case>, one of "unknown", "linear", "symplectic",
//           "orthogonalplus", "orthogonalminus", or "orthogonalcircle"
//  - an optional integer <NumberOfElements>
//
//  Output:
//
//  Either a boolean, i.e. either 'true' or 'false' 
//  or the string "Does not apply"
//
//  The  algorithm  is designed  to  test  whether <grp>  contains the
//  corresponding classical group Omega (see [1]).
//       
intrinsic 
RecognizeClassical( grp :: GrpMat : Case := "unknown", 
NumberOfElements := ClassicalRecognitionElements (Degree (grp), BaseRing (grp)) ) -> BoolElt 
{Use the  Niemeyer-Praeger algorithm  to  test  whether <grp>  
 contains the corresponding classical group.}

    d := Degree (grp);
    if d ge 3 then 
    require Case in ["unknown", "linear", "symplectic",
                     "orthogonalcircle", "orthogonalplus",
                     "orthogonalminus", "unitary"]: "Case not valid";
    elif d eq 2 then 
       require Case in ["unknown", "linear", "symplectic",
                        "orthogonalplus",
                        "orthogonalminus", "unitary"]: "Case not valid";
    elif Degree (grp) eq 1 then 
       // degree 1 included to avoid crashes 
       if not assigned grp`recognize then
          InitRecog(grp,Case);
          grp`recognize`isLinearGroup := true;
       end if;
       return true; 
    end if;

    // degree 2 case handled separately 
    if Degree (grp) eq 2 then 
       if not assigned grp`recognize then
          InitRecog(grp,Case);
       end if;
       return RecogniseDegree2 (grp, Case: NumberOfElements := NumberOfElements); 
    end if;

    if IsTrivial (grp) then return false; end if;

    /* avoid calling Forms code for group whose derived group 
       does not act absolutely irreducibly */

    if IsAbsolutelyIrreducible (grp) eq false then
       return false; 
    end if;

    q := #BaseRing (grp);
    if (d eq 3 and q eq 3) or (d eq 4 and q eq 2) then
       flag := IsSemiLinear (grp);
       if flag cmpeq true or flag cmpeq "unknown" then
          flag := SymmetricBilinearForm (grp);
          if flag then
             InitRecog(grp,Case);
             if d eq 4 then grp`recognize`isOrthogonalPlusGroup := true;
             else grp`recognize`isOrthogonalCircleGroup := true; end if;
             return true;
          else
             return false;
          end if;
       end if;
    end if;

    if Case eq "unknown" and assigned grp`recognize and
        assigned grp`forms`formType  then
	Case := grp`forms`formType;
    end if;
  
    if Case eq "linear" then
        N := 25;
    else
        N := 30;
    end if;

    if Degree(grp) lt 50 then
        N := N + 20;
    end if;

     N := Maximum( N, NumberOfElements);

    // if we already know the answer, return it
    if assigned grp`recognize then
        if Case eq "linear" and assigned grp`recognize`isLinearGroup then
            return grp`recognize`isLinearGroup;
        elif Case eq "symplectic" and 
             assigned grp`recognize`isSymplecticGroup then
            return grp`recognize`isSymplecticGroup;
        elif Case eq "unitary" and assigned grp`recognize`isUnitaryGroup then
            return grp`recognize`isUnitaryGroup;
        elif Case eq "orthogonalminus" 
            and assigned grp`recognize`isOrthogonalMinusGroup then
            return grp`recognize`isOrthogonalMinusGroup;
        elif Case eq "orthogonalplus" 
            and assigned grp`recognize`isOrthogonalPlusGroup then
            return grp`recognize`isOrthogonalPlusGroup;
        elif Case eq "orthogonalcircle" 
            and assigned grp`recognize`isOrthogonalCircleGroup then
            return grp`recognize`isOrthogonalCircleGroup;
        end if;
    end if;

    // if necessary initialise the record recognize
    // and compare the given case with information 
    // already known about invariant forms     
    if not assigned grp`recognize then
        InitRecog(grp,Case);
    else
        if not assigned grp`forms`formType then
	    grp`forms`formType := "unknown";
        end if;
        if grp`forms`formType ne "unknown" then 
            if  Case ne "unknown" then
                if grp`forms`formType ne Case  then
    	            InfoRecog(1,"The group is already known to preserve ");
                    InfoRecog(1,"a form of type " cat grp`forms`formType );
	            InfoRecog(1,"Thus Case is wrong" );
	            return false;
                else
	            str := "The group is known to preserve ";
                    if Case eq "linear" then 
                        str := str cat "no forms";
                    else str := str cat "a form of type " cat Case;
                    end if;
	            InfoRecog( 1, str);
	        end if;
            else
	        Case := grp`forms`formType;
	        InfoRecog( 1, "The group is already known to preserve ");
	        InfoRecog( 1, "a form of type " cat Case );
	        InfoRecog( 1, "Thus Case is " cat Case );
            end if;
        else  
            // the form is not yet known, set some flags according to Case
            grp`recognize`n := 0;
            grp`forms`bilinFlag := true; 
            grp`forms`sesquiFlag := Degree(BaseRing(grp)) mod 2 eq 0;
            if Case eq "unknown"  then
                grp`forms`bilinFlag := true;
                grp`forms`sesquiFlag := 
                    Degree(BaseRing(grp)) mod 2 eq 0;
            end if;
            grp`recognize`possibleOverLargerField := true;
            grp`recognize`possibleNearlySimple    := {};
        end if;
    end if;
 
    if not ApplicableParameters( grp, Case ) then return false; end if;

    // test whether the theory applies for this group and case
    if GenericParameters(grp,Case) eq false then
        nongen := NonGeneric( grp, Case, N+30 );
        if Type( nongen ) eq MonStgElt and nongen eq "Does not apply" then
            return false;
        end if;
        if CaseCheck(grp, Case) eq false then
            InfoRecog(1,"The group is not of type " cat Case );
            return false;
        end if;
        if nongen cmpeq false then 
            InfoRecog(1,"Either the group does not contain Omega");
            InfoRecog(1,"or the group is not of type " cat Case );
            return false;
        end if;

        if not SetReturnNP(grp,Case) then 
            InfoRecog(1,"The case was wrong." );
            return false; 
        end if;
        str := "Proved that the group contains a classical group of type ";
        str := str cat Case cat " in " cat 
        IntegerToString(grp`recognize`n) cat " random selections.";
        InfoRecog( 1, str );
        return true;
    end if;

    n := grp`recognize`n;
    // try to establish whether the group is generic
    if not IsGeneric(grp,N) then
        InfoRecog(1,"The group does not seem to be generic");
        // before we exit, we just check for forms
        if grp`forms`formType eq "unknown" then 
            form := StoreClassicalForms(grp, Case);
            if form cmpeq false then return false; end if;
        end if;

    end if;

    if not CaseCheck( grp, Case) then
         return false;
    end if;


    if Case eq "unknown" then
        if assigned grp`forms`formType and 
        grp`forms`formType ne "unknown" then
            Case := grp`forms`formType;
            if GenericParameters( grp, Case ) eq false then
                nongen := NonGeneric( grp, Case, N );
                if CaseCheck(grp,Case) eq false then
                    InfoRecog(1, "The group is not of type " cat Case );
                    return false;
                end if;
                if nongen cmpeq false then 
                   InfoRecog(1,"The group probably does not contain Omega.");
                   return false;
                end if;
                if not SetReturnNP(grp,Case) then 
                    InfoRecog(1,"The case was wrong" );
                    return false; 
                end if;
                str := "Proved that the group contains a classical" cat
                          " group of type \n";
                str := str cat Case cat " in " cat 
                       IntegerToString(grp`recognize`n) cat 
                       " random selections.";
                InfoRecog( 1, str );
                return true;
            end if; 
        else
            form := StoreClassicalForms(grp, Case);
            if form cmpeq false then return false; end if;
            if grp`forms`formType eq "unknown" then
                if grp`recognize`isReducible eq true then
                    if IsIrreducible( grp ) then
                        grp`recognize`isReducible := false;
                    else
                        InfoRecog(1, "The group acts reducibly and");
                        InfoRecog(1, "the algorithm does not apply.");
                        grp`recognize`applies := false;
                        return "Does not apply";
                    end if;
                    InfoRecog(1, "Could not determine classical forms.");
                end if;
                return false;
	    else
                Case := grp`forms`formType;
            end if;
        end if;
    end if;

    // By now we know that the group must have generic parameters.
    // Hence, if the group turned out to be non-generic we return false
    if grp`recognize`isGeneric eq false then
        InfoRecog(1,"The group is not generic" );
	return false;
    end if;

    if Case ne "unknown" and assigned grp`forms`formType and
       grp`forms`formType ne "unknown" and
           Case ne grp`forms`formType then
	    InfoRecog( 1, Case cat " is not the right case");
	    InfoRecog( 1, "The case is " cat grp`forms`formType);
           return false;
    end if;

    isext := IsExtensionField(grp, Case, N-grp`recognize`n+n); 
    if Type(isext) eq MonStgElt and isext eq "no form" or 
        CheckForms(grp,Case) eq false then
        return false;
    end if;
    if Case eq "unknown" then
        if GenericParameters( grp, grp`forms`formType ) eq false then
            InfoRecog(1,"Either algorithm does not apply in this case\n");
            InfoRecog(1,"or the group is not of type " cat Case);
            grp`recognize`applies := false;
            return "Does not apply";
	end if;
    end if;

    Case := grp`forms`formType;

    if isext cmpeq true then
        return false;
    elif isext cmpeq false then
        str := "The group does not preserve a";
        if Case eq "symplectic" then
            str := str cat " symplectic form";
        else
            str := str cat " quadratic form";
        end if;
        InfoRecog(1, str );
        return false;
    end if;
    
    // Now we know that the group preserves no extension field structure on V
    if IsGenericNearlySimple(grp,Case,N-grp`recognize`n+n) then
        InfoRecog(1,"The group could be a nearly simple group.");
        return false;
    end if;
    n := grp`recognize`n - n;
    InfoRecog(2,"The group is not nearly simple.");

    // maybe the number of random elements selected was not sufficient
    // to prove that the group acts irreducibly. In this case we call
    // the meataxe
    if grp`recognize`isReducible eq true then
        if IsIrreducible(grp) then
            grp`recognize`isReducible := false;
        else
            grp`recognize`isReducible := true;
        end if;
    end if;
    // if the group acts reducibly then our algorithm does not apply
    if grp`recognize`isReducible then
        SetNotAbsIrred(grp);
        str := "The group acts reducibly";
        InfoRecog(1, str cat " and the algorithm does not apply.");
        grp`recognize`applies := false;
        return "Does not apply";
    end if;
    InfoRecog(2,"The group acts irreducibly.");

    if CaseCheck(grp,Case) eq false then
        InfoRecog(1, "The group is not of type " cat Case );
        return false;
    end if;

    if not SetReturnNP(grp,Case) then
        InfoRecog(1,"The case was wrong." );
        return false; 
    end if;
    str := "Proved that the group contains a classical group of type ";
    str := str cat Case cat " in " cat IntegerToString(grp`recognize`n);
    str := str cat " random selections.";
    InfoRecog( 1, str );
    return true;

end intrinsic;

intrinsic 
RecogniseClassical( grp :: GrpMat :
                           Case := "unknown", 
                           NumberOfElements := 25 ) -> BoolElt 
{Use the  Niemeyer-Praeger algorithm  to  test  whether <grp>  
 contains the corresponding classical group.}

    return RecognizeClassical (grp: Case := Case, 
                    NumberOfElements := NumberOfElements); 
end intrinsic;

intrinsic ClassicalType (grp::GrpMat) -> MonStgElt
{Return the type if <grp> is known to be a classical matrix group 
 in its natural representation and false otherwise}
 
   if not assigned grp`recognize then
       tmp := RecognizeClassical( grp );
       if tmp cmpeq false then return false; end if;
   end if;

  if assigned grp`recognize`isLinearGroup 
     and grp`recognize`isLinearGroup eq true  then 
         return "linear";
  end if;

  if assigned grp`recognize`isUnitaryGroup 
     and grp`recognize`isUnitaryGroup eq true  then 
         return "unitary";
  end if;

  if assigned grp`recognize`isSymplecticGroup 
     and grp`recognize`isSymplecticGroup eq true  then 
         return "symplectic";
  end if;

  if assigned grp`recognize`isOrthogonalPlusGroup 
     and grp`recognize`isOrthogonalPlusGroup eq true  then 
         return "orthogonalplus";
  end if;

  if assigned grp`recognize`isOrthogonalMinusGroup 
     and grp`recognize`isOrthogonalMinusGroup eq true  then 
         return "orthogonalminus";
  end if;

  if assigned grp`recognize`isOrthogonalCircleGroup 
     and grp`recognize`isOrthogonalCircleGroup eq true  then 
         return "orthogonalcircle";
  end if;

  if grp`recognize`applies eq false then
         return "Does not apply";
  end if;

  return false;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//
//  IsLinearGroup ( <grp> ) .. . . . . . .  does <grp> contain SL(d,q)
//
//  This function tests whether the subgroup <grp> of GL(d,q) contains
//  SL(d,q). If the function could establish this fact, it returns true
//  and otherwise false. Hence, if the function returns false, there is
//  a small chance that <grp> contains SL(d,q). See RecognizeClassical
//  for more details.
//

intrinsic IsLinearGroup (grp::GrpMat) ->  MonStgElt
{Return true if grp is known to be contained in GL(d,q) and contains SL(d,q)} 

    if not assigned grp`recognize or (assigned grp`recognize and 
       not assigned grp`recognize`isLinearGroup) then
        tmp := RecognizeClassical( grp : Case := "linear" );
        if tmp cmpeq false then return false; end if;
    end if;

    if assigned grp`recognize`isLinearGroup then 
         return grp`recognize`isLinearGroup; 
    elif grp`recognize`applies eq false then
         return "Does not apply";
    else 
         return false;
    end if;

end intrinsic;

intrinsic IsSymplecticGroup (grp::GrpMat) ->  MonStgElt
{Return true if grp is known to be contained in GSp(d,q) and contains Sp(d,q)}

    if not assigned grp`recognize or (assigned grp`recognize and 
        not assigned grp`recognize`isSymplecticGroup) then
         tmp := RecognizeClassical( grp : Case := "symplectic" );
         if tmp cmpeq false then return false; end if;
    end if;

    if assigned grp`recognize`isSymplecticGroup then 
         return grp`recognize`isSymplecticGroup;
    elif grp`recognize`applies eq false then
         return "Does not apply";
    else 
         return false;
    end if;

end intrinsic;

/* 
intrinsic IsSpecialOrthogonalGroup (grp::GrpMat) ->  BoolElt 
{Returns true if grp is contained in GO^e(d,q) and contains SO^e(d,q)}

   if IsTrivial (grp) then return false; end if;
   if Degree (grp) eq 2 then 
      flag, type, special, quad, bil := RecognizeOmega2 (grp);
      if flag then return special; else return false; end if;
  else
     flag := IsOrthogonalGroup (grp);
     if not flag then return false; end if;
     cf := ClassicalForms (grp);
     bil := cf`bilinearForm;
     return exists {i : i in [1..Ngens (grp)] | SpinorNorm (grp.i, bil) eq 1};
  end if;
end intrinsic;
*/

intrinsic IsOrthogonalGroup (grp::GrpMat) ->  MonStgElt
{Returns true if grp is known to be contained 
 in GO^e(d,q) and contains the corresponding subgroup Omega of SO^e(d,q)}

   if not assigned grp`recognize or (assigned grp`recognize and  not
      (assigned grp`recognize`isOrthogonalPlusGroup or
       assigned grp`recognize`isOrthogonalMinusGroup or
       assigned grp`recognize`isOrthogonalCircleGroup )) then
       if IsOdd (Degree (grp)) then
           tmp := RecognizeClassical( grp : Case := "orthogonalcircle" );
           if tmp cmpeq false then return false; end if;
       else
           tmp := RecognizeClassical( grp ); 
           if tmp cmpeq false then return false; end if;
       end if;
   end if;

   plus := assigned grp`recognize`isOrthogonalPlusGroup 
           and grp`recognize`isOrthogonalPlusGroup;
   minus := assigned grp`recognize`isOrthogonalMinusGroup 
            and grp`recognize`isOrthogonalMinusGroup;
   if (plus or minus) then 
      return (plus or minus);
   elif assigned grp`recognize`isOrthogonalCircleGroup then 
      return grp`recognize`isOrthogonalCircleGroup;
   elif grp`recognize`applies eq false then
      return "Does not apply";
   else 
      return false;
   end if;

end intrinsic;

intrinsic IsUnitaryGroup (grp::GrpMat) ->  MonStgElt
{Return true if grp is known to be contained GU(d,q) and contains SU(d,q)}

    if not assigned grp`recognize or (assigned grp`recognize and 
       not assigned grp`recognize`isUnitaryGroup) then
        tmp := RecognizeClassical( grp : Case := "unitary" );
        if tmp cmpeq false then return false; end if;
    end if;

    if assigned grp`recognize`isUnitaryGroup then 
         return grp`recognize`isUnitaryGroup;
    elif grp`recognize`applies eq false then
         return "Does not apply";
    else
         return false;
    end if;

end intrinsic;


//////////////////////////////////////////////////////////////////////
RecogniseClassical := RecognizeClassical;
