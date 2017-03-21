freeze;

// written by Florian Hess, version 20060111

CHECK := false;



/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/*
    Please notify me (hess@math.tu-berlin.de) if or prior you make any
    changes in this file to avoid me possibly undoing your changes when
    updating this file.

    mch- 25/05/06 - just added the simple intrinsics
    MakeMap/HomWithPreimageHnadler to export the nicer
    preimage error handling here. Also added Reduce parameter
    in MakeAutomorphismGroup function.
    02/06/06 - added FldQuad to "list" of allowable base fields
    15/06/06 - and FldCyc!
    17/06/06 - bug fix in MakeIsomorphisms (line 6717)- see note there.
    18/07/06 - added clause in MakeAutomorphismGroup to use specialised,
     much faster version of GenericGroup: CrvGenericGroup. This returns
     a permutation group rather than an FP group.
    13/02/08 - minor change - added a=0 special case to RepresentInGenerators
     (function line 5846)
*/


/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/*

   Automorphisms of function fields.
   
   The file consists roughly of three sections.
     1. Almost unique local uniformisers and parametrisations.
     2. General support for maps, field and function field homomorphisms.
     3. Automorphisms of algebraic function fields of
        transcendence degree one.

*/

  
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/*

  1. Almost unique local parameters at a place P of degree one.

        Some code to associate to a place of degree one        
        a local uniformizer which depends on at most two 
        parameters in the constant field. The resulting
        local parametrisations are fairly unique.

  These are obtained by taking n-th roots of inverses of elements of smallest
  D-pole order n at P, where D is usually the zero divisor. 

  The following provides essentially the map F -> k((pi)) where
  pi is such an almost unique local parameter, plus supporting
  functionality. 
                      
*/

   
ulp_fmt := recformat< 
           P,        // place of degree one
           D,        // divisor of dimension ge 2
           a,        // b element in D - r*P with r maximal and r ne 0
                     // Then a = b or a = 1/b such that v_P(a) = |r|.
           n,        // n = |r| = v_P(a)
           x,        // the local parameter at P             
           x_in_t,   // x expressed as a series in t where t^n = a
           m,        // The relative precision of x_in_t
           pos       // the position in F`ulp                
>;   
                     
declare attributes  FldFunG:  ulp;    // list of ulp records.
declare verbose     ULP,  2;
     

CheckArguments := function(D, P)
   if FunctionField(D) cmpne FunctionField(P) then
      return false, "Arguments must belong to the same function field";
   end if;
   if Valuation(D, P) ne 0 then 
      return false, "Arguments must be coprime";
   end if;
   if Degree(P) ne 1 then 
      return false, "Second argument must have degree one";
   end if;
   if not IsZero(D) and Dimension(D) ne 0 then
      return false, "First argument must have dimension zero";
   end if;
   return true, "ok";   
end function;   
   

intrinsic FirstPoleElement(D::DivFunElt, P::PlcFunElt) -> RngElt, RngIntElt
{Return the first pole element and its pole order wrt D at P}  
//   
//  Return element which realizes first pole order at P, and the
//   pole order.
//  
     ok, mess := CheckArguments(D, P);     
     require ok : mess;   

     F := FunctionField(P);
     if IsZero(D) then     
        while not Dimension(D) eq 2 do
           D := D + P;
        end while;
        x := Representative( [ z : z in Basis(D) | not IsConstant(z) ] );
        return x, Valuation(D, P);
     else   
        while not Dimension(D) eq 1 do
           D := D + P;
        end while;
        x := Representative( Basis(D) );
        return x, Valuation(D, P);
     end if;
end intrinsic;


intrinsic FirstPoleElement(P::PlcFunElt) -> RngElt, RngIntElt
{Return the first pole element and its pole order at P}  
        
    D := DivisorGroup(FunctionField(P))!0;     
    ok, mess := CheckArguments(D, P);     
    require ok : mess;   
        
    return FirstPoleElement(D, P);

end intrinsic;


intrinsic HasAlmostUniqueLocalUniformizer(D::DivFunElt, P::PlcFunElt) 
  -> Bool, FldFunElt, RngIntElt 
{Compute an almost unique local uniformizer wrt D at P, if it exists}

    ok, mess := CheckArguments(D, P);     
    require ok : mess;   
    
    F := FunctionField(P);
    if not assigned F`ulp then
       F`ulp := [];
    end if;
    L := [ z : z in F`ulp | z`P eq P and z`D eq D ];
    assert #L le 1;
    if #L eq 1 then
       ulp := Representative(L);
       pos := ulp`pos;
       return true, F`ulp[pos]`a, F`ulp[pos]`n;
    end if;
    a, n := FirstPoleElement(D, P);        
    p := Characteristic(F);
    if not IsZero(p) and IsDivisibleBy(n, p) then
       return false, _, _;   
    end if;
    a := 1/a;
    a := a + 1 - 1; // work around bug in prod rep
    x := LocalUniformizer(P);
    c := Evaluate(a/x^n, P);   
    a := a / c;
    ulp := rec< ulp_fmt | P := P, D := D, a := a, n := n, x := x >;
    ulp`pos := #F`ulp + 1;
    pos := ulp`pos;
    Append(~F`ulp, ulp);
    return true, F`ulp[pos]`a, F`ulp[pos]`n;
    
end intrinsic;    


intrinsic HasAlmostUniqueLocalUniformizer(P::PlcFunElt) 
  -> Bool, FldFunElt, RngIntElt 
{Compute an almost unique local uniformizer at P, if it exists}

    D := DivisorGroup(FunctionField(P))!0;     
    ok, mess := CheckArguments(D, P);     
    require ok : mess;   
    
    return HasAlmostUniqueLocalUniformizer(D, P);
    
end intrinsic;


/////////////////////////////////////////////////////////////////////////////

  
ExpandRel := function(a, P, x, m)  
//
// Expand a to a series in x with m meaningful coeffs  
//  
   res, xx := Expand(a, P: RelPrec := m);
   assert x eq xx;
vprint ULP :"m: ", m;
vprint ULP :"res: ", res;
vprint ULP :"m+1: ", m+1;
vprint ULP :"res: ", Expand(a, P: RelPrec := m);
//assert ChangePrecision(Expand(a, P:RelPrec := m+1), m) eq res;
   /*
   if x ne xx then
      x_in_xx := Expand(x, P: RelPrec := m);
      xx_in_x := Reverse(x_in_xx);
      res := Evaluate(res, xx_in_x);
   end if;
   */
   /*  
   print "ExpandRel: m is ", m;
   print "ExpandRel: Val a is ", Valuation(a, P);   
   print "ExpandRel: Val res is ",  Valuation(Evaluate(res, x)-a, P);
   */
   res := res + O(Parent(res).1^(Valuation(res) + m));  
   //assert Valuation(Evaluate(res, x)-a, P) - Valuation(a, P) ge m;
   return res;
end function;	


UpdatePrecision := procedure(F, pos, m)
    if not assigned F`ulp[pos]`x_in_t or F`ulp[pos]`m lt m then
  //  vprint ULP : "Update prec: old m is ", F`ulp[pos]`m, ", new m is ", m;
      // do everything with +1 as Reverse appears to loose precision
      a_in_x := ExpandRel(F`ulp[pos]`a, F`ulp[pos]`P, F`ulp[pos]`x, m+1);
      //  vprint ULP : "a_in_x", a_in_x;
      //  vprint ULP : "a: ", F`ulp[pos]`a;
      //  vprint ULP : "v_P(a): ", Valuation(F`ulp[pos]`a,F`ulp[pos]`P);
      //  vprint ULP : "a_in_pi: ", Expand(F`ulp[pos]`a, F`ulp[pos]`P);
      //  vprint ULP : "a_in_x: ", ExpandRel(F`ulp[pos]`a, F`ulp[pos]`P, F`ulp[pos]`x, m+1);
      R := PolynomialRing(Parent(a_in_x));
      f := (R.1)^F`ulp[pos]`n - a_in_x;
      vprint ULP : "Update prec: f is ", f;
      t_in_x := Representative(Roots(f, m+1))[1];
      vprint ULP : "Update prec: t_in_x is ", t_in_x;
      assert (RelativePrecision(t_in_x) eq Infinity()
              or RelativePrecision(t_in_x) ge m+1);
      x_in_t := Reverse(t_in_x);
      S := Parent(t_in_x);
      AssignNames(~S, ["t"]);
      vprint ULP : "x_in_t is ", x_in_t;
      assert (RelativePrecision(x_in_t) eq Infinity()
              or RelativePrecision(x_in_t) ge m);
      F`ulp[pos]`m := m;   
      F`ulp[pos]`x_in_t := x_in_t;   
   end if;
end procedure;

    
   
intrinsic HasAlmostUniqueLocalParametrization(D::DivFunElt, P::PlcFunElt) ->
Bool, UserProgram
{Returns the parametrization function wrt D at P, if it exists. The function takes the desired relative precision as second argument}
                                                     
    ok, mess := CheckArguments(D, P);     
    require ok : mess;   
                                                     
    F := FunctionField(P);
    ok := HasAlmostUniqueLocalUniformizer(D, P);
    if not ok then
       return false, _;
    end if;
    L := [ z : z in F`ulp | z`P eq P and z`D eq D ];
    assert #L eq 1;
    if #L eq 1 then
       ulp := Representative(L);
       pos := ulp`pos;
    end if;
    UpdatePrecision(F, pos, 1);
    f := function(z, m)
       res := ExpandRel(z, P, F`ulp[pos]`x, m);
       UpdatePrecision(F, pos, m);
       res := Evaluate(res, F`ulp[pos]`x_in_t);
       assert (RelativePrecision(res) eq Infinity()
            or RelativePrecision(res) ge m);
       return res + O((Parent(res).1)^(Valuation(res) + m));
    end function;
    return true, f;
       
end intrinsic;


intrinsic HasAlmostUniqueLocalParametrization(P::PlcFunElt) ->
Bool, UserProgram
{Returns the parametrization function at P, if it exists. The function takes the desired relative precision as second argument}
                                                     
    D := DivisorGroup(FunctionField(P))!0;     
    ok, mess := CheckArguments(D, P);     
    require ok : mess;   
                                                     
    return HasAlmostUniqueLocalParametrization(D, P);
    
end intrinsic;


/////////////////////////////////////////////////////////////////////////////
/*

    2. Morphisms of fields, of morphisms of fields, of field extensions,
       and of function fields.

    For the rough idea:    
      A field object represents a field.  
      A field morphism represents a monomorphism F -> F' of fields.
      A morphism of field morphisms K -> F and K' -> F' represents  
          two compatible field morphisms F -> F' and K -> K'.
      A field extension F/K represents among other things a 
          monomorphism K -> F.   
      A field extension morphism represents among other things a morphism
          of the corresponding field morphisms.
      A function field morphism is a field extension morphism of the 
          function field over its constant field of definition.  
      From these morphism one can extract Magma maps performing the mapping.  

*/
  
  
/////////////////////////////////////////////////////////////////////////////
//
//  Error Handling
//

ErrStat := true;
ErrorHandler := function(ErrStat, mess)
   if ErrStat then
       Traceback();
   end if;
   error mess;
end function;


/////////////////////////////////////////////////////////////////////////////
//  
//  Technical map support
//  

forward IsSameRationalFunctionField;
  
declare attributes Map : static, 
  
                         do_magma_image, // whether images are computed using
                                         // the map of the image function
                         image,          // image function 
                         imageconstr,    // constructor of image function
                         imagedone,      // unassigned: imageconstr has not
                                         // been executed.
                                         // assigned: first result of 
                                         // imageconstr                   

                         do_magma_preimage,  
                         maybe_has_preimage, // whether preimage exists, maybe 
                         preimage,             
                         preimageconstr,  
                         preimagedone, 
                           
                         components;     // for composites

/*
  
   A map imported to the map concept below has f`static defined
   and indicates whether Magma uses f`static`image and f`static`preimage  
   for image and preimage computation via f`static`do_magma_image
   and f`static`do_magma_preimage. 
                                        
   It is possible that f`static`do_magma_preimage is true but
   f`static`preimage is set. This is then used in our HasPreimage(f, x)
   as opposed to HasPreimage(x, f) which uses the internal preimage rule. 
  
   A generic map f uses f`static`image and f`static`preimage.
   Generic maps allow to lazy evaluate and/or add image and preimage functions
   after (!) the map has been defined (imageconstr, preimageconstr).
  
*/
     

// preimages in Magma do not report errors well
//  hence the following substitutes  

// map<>, hom<> take only result return value from preimage function
                                        
DoErrorPreimage := function(preimage)  
   return function(y)
      ok, x := preimage(y);
      if not ok then
         return ErrorHandler(ErrStat, "Preimage does not exist");
      end if;
      return x;
   end function;
end function;
   
   
intrinsic Preimage(f::Map, z::Any) -> FldElt
{Return preimage of z under f};
   require Codomain(f) cmpeq Parent(z) or
           IsSameRationalFunctionField(Domain(f), Parent(z)) or
           ( Type(Codomain(f)) cmpeq SetEnum and z in Codomain(f) ) 
    : "Element is not in the codomain";  
   ok, g := HasPreimageFunction(f);
   require ok : "No preimage function defined";
   ok, res := g(z);
   require ok : "Preimage does not exist";   
   return res;
end intrinsic;


intrinsic HasPreimage(f::Map, z::Any) -> Bool, FldElt
{Return boolean and preimage of z under f if it exists};
    if not assigned f`static then
	ok, g := HasPreimage(z, f);
	if ok then
	    return ok, g;
	else
	    return ok, _;
	end if;
    end if;
   if not ( Codomain(f) cmpeq Parent(z) or
            IsSameRationalFunctionField(Domain(f), Parent(z)) or
           ( Type(Codomain(f)) cmpeq SetEnum and z in Codomain(f) ) ) then
      return false, _; 
   end if;      
   ok, g := HasPreimageFunction(f);
   require ok : "No preimage function defined";
   return g(z);
end intrinsic;


MakePreimageFunction := function(static)
  if assigned static`preimage then
     return true, static`preimage; 
  end if;
  if assigned static`preimageconstr and 
     not assigned static`preimagedone then
     ok, preimage := static`preimageconstr(static);
     delete static`preimageconstr;
     static`preimagedone := ok;
     if ok then
        static`preimage := preimage;
        return true, preimage;
     end if;   
  end if;
  if assigned static`preimagedone then
      assert static`preimagedone eq false;
      return false, _;
  end if;
  // could be moved to Composition() as preimage method to install.
  if assigned static`components then
      L := static`components;
      I := [];
      for g in L do
         ok, preim := HasPreimageFunction(g);     
         if ok then
            Append(~I, preim);
         else
            break;
         end if;   
      end for;
      if #I ne #L then
         return false, false;
      end if;
      h := function(y) 
         for g in Reverse(I) do
            ok, y := g(y);
            if not ok then 
               return false, _;
            end if;
         end for;
         return true, y;
       end function;
       static`preimage := h;
       return true, h;
  end if;   
  static`preimagedone := false;
  return false, _;
end function;


MakeLazyPreimageFunction := function(static)
   if assigned static`preimage then
       return static`preimage;
   end if;
   preimage := function(x)
      if assigned static`preimage then
         return static`preimage(x);
      end if;
      ok, preimage := MakePreimageFunction(static);
      if ok then
         // static`preimage := preimage; is done in MakePreimageFunction.
         return preimage(x);
      end if;
      return ErrorHandler(ErrStat, 
                  "No algorithm for computing preimages given");
   end function;
   return preimage;
end function;


intrinsic HasPreimageFunction(f::Map : Lazy := false) -> Bool, UserProgram
{True and the preimage function of f if it cen be determined, false otherwise}
    if not assigned f`static or not f`static`maybe_has_preimage then
        return false, _;
    end if;    
    if assigned f`static`preimage then
       return true, f`static`preimage;
    end if;
    if f`static`do_magma_preimage then       
       return true, function(y)  
                       ok, y := IsCoercible(Codomain(f), y);
                       if not ok then
                          return ErrorHandler(ErrStat, 
                            "Argument is not coercible into codomain of map");
                       end if;
                       return HasPreimage(y, f); 
                    end function; 
    end if;
    if Lazy then
        preimage := MakeLazyPreimageFunction(f`static);
        return true, preimage;
    end if;
    return MakePreimageFunction(f`static); 
end intrinsic;      


// the following yields mem loops if preimageconstr or preimage   
//  contains a reference to f or to static                                    

/*
  Example: 

     preim := function(x) 
                 ok, x := IsCoercible(G, x);
                 if not ok then
                     return ErrorHandler(ErrStat,
                             "Argument is not coercible into codomain of map");
                 end if;
                 return true, x+1; 
              end function;
*/

                                     
InstallPreimage := function(f, preimage)
    assert assigned f`static;
    if not assigned f`static`preimage then
       f`static`preimage := preimage;   
       f`static`maybe_has_preimage := true;
       f`static`do_magma_preimage := false;
    end if;
    return f;
end function;
 

/* 
   preimageconstr gets no argument returns Bool and UserProgram.
   To avoid mem loop no use of f or static in imageconstr.
*/
  
InstallPreimageConstructor := function(f, preimageconstr)
    assert assigned f`static;
    if assigned f`static`preimage or assigned f`static`preimageconstr then
        return f;
    end if;
    f`static`preimageconstr := preimageconstr;   
    delete f`static`preimagedone;
    f`static`maybe_has_preimage := true;
    f`static`do_magma_preimage := false;
    return f;
end function;
   
     
////////////////////////////////////////////////////////////////////////////   
   
// similar symmetric (!) things for images   
// except that image function might be implicit in map  
// and that there is always an image function (which may not be total).
  
  
DoErrorImage := function(Image)  
   if CHECK then
       return function(y)
	  ok, x := Image(y);
	  if not ok then
	     return ErrorHandler(ErrStat, "Image does not exist");
	  end if;
	  return x;
       end function;
   else
       return function(y)
	  ok, x := Image(y);
	  return x;
       end function;
   end if;
end function;
   
   
intrinsic Image(f::Map, z::Any) -> FldElt
{Return image of z under f};
   require Domain(f) cmpeq Parent(z) or 
           IsSameRationalFunctionField(Domain(f), Parent(z)) or
           ( Type(Domain(f)) cmpeq SetEnum and z in Domain(f) )  
       : "Element is not in the domain";  
   return f(z);
end intrinsic;


intrinsic HasImage(f::Map, z::Any) -> Bool, FldElt
{Return boolean and image of z under f if it exists};
   if not ( Codomain(f) cmpeq Parent(z) or
            IsSameRationalFunctionField(Domain(f), Parent(z)) or
           ( Type(Codomain(f)) cmpeq SetEnum and z in Codomain(f) ) ) then
      return false, _; 
   end if;      
   return ImageFunction(f)(z);
end intrinsic;


MakeImageFunction := function(static)
  if assigned static`image then
     return true, static`image; 
  end if;
  if assigned static`imageconstr and 
     not assigned static`imagedone then
       ok, image := static`imageconstr(static);
       delete static`imageconstr;
       assert ok;
       static`imagedone := ok;
       static`image := image;
       return true, image;
  end if;
  // could be moved to Composition() as image method to install.
  if assigned static`components then
      L := static`components;
      I := [ ImageFunction(g) : g in L ];
      h := function(x) 
         for im in I do
            ok, x := im(x);
            if not ok then 
               return false, _;
            end if;
         end for;
         return true, x;
       end function;
       static`image := h;
       return true, h;
  end if;   
  assert false;
  return false, _;
end function;


MakeLazyImageFunction := function(static)
   if assigned static`image then
       return static`image;
   end if;
   image := function(x)
      if assigned static`image then
         return static`image(x);
      end if;
      ok, image := MakeImageFunction(static);
      if ok then
         // static`image := image; is done in MakeImageFunction.
         return image(x);
      end if;
      return ErrorHandler(ErrStat, 
                  "No algorithm for computing images given");
   end function;
   return image;
end function;


intrinsic ImageFunction(f::Map : Lazy := false) -> UserProgram
{The image function of f}
    if not assigned f`static or f`static`do_magma_image then
        return function(x)                    
                    ok, x := IsCoercible(Domain(f), x);
                    if not ok then
                      return ErrorHandler(ErrStat, 
                           "Argument is not coercible into domain of map");
                    end if;
                  return true, f(x); 
               end function;
    end if;
    // f is generic map
    if Lazy then
        image := MakeLazyImageFunction(f`static);
    else
        ok, image := MakeImageFunction(f`static);
        assert ok;
    end if;
    return image; 
end intrinsic;      


// the following yield mem loops if imageconstr or image   
//  contains a reference (use) to f or to static

/*
  Example: 

     image := function(x) 
                 ok, x := IsCoercible(F, x);
                 if not ok then
                     return ErrorHandler(ErrStat,
                             "Argument is not coercible into domain of map");
                 end if;
                 return x eq 1, x+1;
              end function;
*/

InstallImage := function(f, image)
    assert assigned f`static;
    assert f`static`do_magma_image eq false;
    assert not assigned f`static`image;  
    f`static`image := image;
    return f;
end function;

   
/* 
   imageconstr gets no argument returns Bool and UserProgram.
   To avoid mem loop no use of f or static in imageconstr.
*/
   
InstallImageConstructor := function(f, imageconstr)
    assert assigned f`static;
    assert not assigned f`static`image;    
    assert not assigned f`static`imageconstr;    
    assert f`static`do_magma_image eq false;
    f`static`imageconstr := imageconstr;   
    delete f`static`imagedone;
    return f;
end function;
   
   
////////////////////////////////////////////////////////////////////////////   

   
CoercionMap := function(F, G)   
   f := Coercion(F, G);
   f`static := Coercion(Integers(), Integers());
   f`static`image := function(x)
      ok, x := IsCoercible(F, x);
      if not ok then
         return ErrorHandler(ErrStat, 
                  "Argument is not coercible into domain of map");
      end if;
      return true, G!x;
   end function;
   f`static`do_magma_image := false;   
   f`static`preimage := function(y)
      ok, y := IsCoercible(G, y);
      if not ok then
         return ErrorHandler(ErrStat, 
                  "Argument is not coercible into codomain of map");
      end if;
      return IsCoercible(F, y);
   end function;
   f`static`maybe_has_preimage := true;
   f`static`do_magma_preimage := false;      
   return f;         
end function;
   
   
// could think of flatten components ...
   
CompositionMap := function(f, g)   
   h := f * g;
   h`static := Coercion(Integers(), Integers());
   h`static`components := [ f, g ];
   h`static`do_magma_image := true;
   h`static`do_magma_preimage := false;
   h`static`maybe_has_preimage := true;  
   return h;
end function;
   
CompositionMapSequence := function(L)   
   h := &* L;
   h`static := Coercion(Integers(), Integers());
   h`static`components := L;
   h`static`do_magma_image := true;
   h`static`do_magma_preimage := false;
   h`static`maybe_has_preimage := true;  
   return h;
end function;
   
   
ImportMap := function(f, has_preimage)
    if assigned f`static then
       return f;
    end if;
    assert has_preimage in { true, false };
    static := Coercion(Integers(), Integers());
    static`do_magma_image := true;
    static`do_magma_preimage := true;
    static`maybe_has_preimage := has_preimage;
    f`static := static;
    return f;
end function;
   
   
GenericMap := function(F, G)   
   static := Coercion(Integers(), Integers());   
   image := MakeLazyImageFunction(static);
   preimage := MakeLazyPreimageFunction(static);
   static`do_magma_image := false;   
   static`do_magma_preimage := false;   
   static`maybe_has_preimage := false;
   f := map< F -> G | x :-> DoErrorImage(image)(x), 
                      y :-> DoErrorPreimage(preimage)(y) >;
   f`static := static;
   return f;   
end function;   
   
   
/* Btw, the following does not work since f`data`image := .. does not   
   change f_data and hence f_data`image is not set.
                                                 
GenericMap := function(F, G)   
   f_data := rec< generic_map_fmt | >;
   f := map< F -> G | x :-> f_data`image(x), 
                      y :-> DoErrorPreimage(f_data`preimage)(y) >;      
   f`data := f_data;
   return f;   
end function;   
*/   
  
  
GenericMapFromMap := function(f)  
   assert assigned f`static;
   g := GenericMap(Domain(f), Codomain(f));
   // need to copy one by one so g`static remains the same object
   g`static`do_magma_image := false;  
   if f`static`do_magma_image or assigned f`static`image then
        g`static`image := ImageFunction(f);
   else
        // keep lazy evaluation
        if assigned f`static`imagedone then
            g`static`imagedone := f`static`imagedone;         
        end if;
        g`static`imageconstr := f`static`imageconstr;         
   end if;
   g`static`do_magma_preimage := false;
   if f`static`do_magma_preimage or assigned f`static`preimage then
        ok, preimage := HasPreimageFunction(f);
        if ok then
           g`static`preimage := preimage;
        end if;
        g`static`maybe_has_preimage := ok;
   else
        // keep lazy evaluation
        if assigned f`static`preimagedone then
           g`static`preimagedone := f`static`preimagedone;         
        end if;
        if assigned f`static`preimageconstr then
            g`static`preimageconstr := f`static`preimageconstr;         
        end if;
        if assigned f`static`preimageconstr then
            g`static`maybe_has_preimage := f`static`maybe_has_preimage;
        end if;
   end if;
   if assigned f`static`data then
      g`static`data := f`static`data;
   end if;
   return g;
end function;


// handling of inverse is proper job of categories
//  the following is for technical convenience
//  It behaves quite like Inverse()

HasInverseMap := function(f)
    assert assigned f`static;
    ok, preim := HasPreimageFunction(f : Lazy := true);
    if not ok then
        return false, _;
    end if;
    image := ImageFunction(f : Lazy := true);
    g := GenericMap(Codomain(f), Domain(f));
    g := InstallImage(g, preim);
    g := InstallPreimage(g, image);
    return true, g;
end function;
   

// 2 intrinsics below added 25/05/06 (mch) as convenience function for export
intrinsic MakeHomWithPreimageHandler(dom::Any,cod::Any,f::Any,g::Any) -> Map
{}
    h := hom< dom -> cod | x :-> f(x),
                                y :-> DoErrorPreimage(g)(y) >;
    h := ImportMap(h, false);
    h := InstallPreimage(h, g);       
    return h;
end intrinsic;

intrinsic MakeMapWithPreimageHandler(dom::Any,cod::Any,f::Any,g::Any) -> Map
{}
    h := map< dom -> cod | x :-> f(x),
                                y :-> DoErrorPreimage(g)(y) >;
    h := ImportMap(h, false);
    h := InstallPreimage(h, g);       
    return h;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
//  
//  Category
//  
  
declare attributes SetFormal: data;  
declare attributes Map: data;
declare attributes RngInt: FieldCategory, FunctionFieldCategory;
declare attributes Fld: FunctionFieldCategory;

// it would be better to split this into
// separate record for the single categories   

category_fmt := recformat< 
                type,
                SPrintCategory,
                IsObject, IsMorphism, AreEqualObjects,
                AreEqualMorphisms, 
                HasMorphism,
                Morphism, 
                MorphismFromImages,
                HasMorphismFromImages,
                MorphismFromImagesAndBaseMorphism,
                HasMorphismFromImagesAndBaseMorphism,
                HasCoercion, Coercion, HasIdentity,
                Identity, IsIdentity, HasComposition, Composition,
                ImportExternalMorphism,
                HasCompositionSequence, CompositionSequence,
                Extension, HasExtension, 
                HasRightCancellation, 
                RightCancellation,
                HasRestriction, Restriction,
                HasBaseExtension, BaseExtension,
                HasBaseExtensionMorphisms, BaseExtensionMorphisms,
                SupportsExtension,
                SpecifyInverseMorphisms, HasInverse, Inverse,
                InstallInverseConstructor, PreimageConstructorViaInverse,
                HasIsomorphismExtension, HasIsomorphismExtensions,
                IsomorphismExtension, IsomorphismExtensions,
                HasMorphismAutomorphism, HasMorphismAutomorphisms,
                MorphismAutomorphism, MorphismAutomorphisms,
                HasIsomorphismsOverBase, HasAutomorphismsOverBase,
                IsIsomorphism, IsEndomorphism, IsAutomorphism,
                IsIsomorphic, 
                HasIsomorphisms, Isomorphisms,
                HasAutomorphisms, Automorphisms,
                IsIsomorphicOverBase, IsomorphismsOverBase,
                Degree,
                BaseObject, ExtensionMorphism,
                basecategory, baseobject, morphismcategory, 
                morphismcategoryoverbase,
                extcategory, CextToCmor, extcategoryoverbase,    
                HasFrobeniusEndomorphism, FrobeniusEndomorphism
                >;


intrinsic IsCategory(C::Any) -> Bool
{}
    return Type(C) eq SetFormal and assigned C`data;
end intrinsic;  


intrinsic IsFieldCategory(C::Any) -> SetFormal
{}
   if not IsCategory(C) then
    return false;
   end if;
   return C`data`type eq "FieldCategory";
end intrinsic;


intrinsic IsMorphismCategory(C::Any) -> SetFormal
{}
   if not IsCategory(C) then
    return false;
   end if;
   return C`data`type eq "MorphismCategory";
end intrinsic;


intrinsic IsMorphismCategory(C::Any, D::Any) -> SetFormal
{Whether C is a morphism category of D}
  
  if not IsCategory(C) or not IsCategory(D) then
    return false;
   end if;
   if not IsMorphismCategory(C) then
      return false;
   end if;
   // handle comparison
   return BaseCategory(C) cmpeq D;
   
end intrinsic;


intrinsic IsExtensionCategory(C::Any) -> SetFormal
{}
   if not IsCategory(C) then
    return false;
   end if;
   return C`data`type eq "ExtensionCategory" or
          C`data`type eq "FunctionFieldCategory";
end intrinsic;


intrinsic IsExtensionCategory(C::Any, D::Any) -> SetFormal
{}  
  if not IsCategory(C) or not IsCategory(D) then
    return false;
   end if;
   if not IsExtensionCategory(C) then
      return false;
   end if;
   // handle comparison
   return BaseCategory(C) cmpeq D;
end intrinsic;


intrinsic IsFunctionFieldCategory(C::Any) -> SetFormal
{}
   if not IsCategory(C) then
    return false;
   end if;
   return C`data`type eq "FunctionFieldCategory";
end intrinsic;


intrinsic IsFunctionFieldCategory(C::Any, D::Any) -> SetFormal
{}  
  if not IsCategory(C) or not IsCategory(D) then
    return false;
   end if;
   if not IsFunctionFieldCategory(C) then
      return false;
   end if;
   // handle comparison
   return BaseCategory(C) cmpeq D;
end intrinsic;


intrinsic HasFixedBaseObject(C::Any) -> Any
{}
   if not IsCategory(C) then
    return false;
   end if;
   if assigned C`data`baseobject then
       return true, C`data`baseobject;
    else
       return false, _;
    end if;
end intrinsic;


intrinsic BaseCategory(C::SetFormal) -> SetFormal, Any
{}
   require IsCategory(C) :
      "Argument must be a category";
   require IsMorphismCategory(C) or IsExtensionCategory(C) :
     "Argument must be a morphism or extension category";
   if HasFixedBaseObject(C) then
      return C`data`basecategory, C`data`baseobject;
   else
      return C`data`basecategory, _;
   end if;
end intrinsic;


// ( cannot install print function otherwise )
  
intrinsic SPrintCategory(C::SetFormal) -> MonStgElt
{}    
   require IsCategory(C) :
     "Argument is not a category";
   return C`data`SPrintCategory();
end intrinsic;

   
intrinsic PrintCategory(C::SetFormal)
{}    
   require IsCategory(C) :
     "Argument is not a category";
   print SPrintCategory(C);
end intrinsic;


//  Objects do not have a category because for one    
//  Magma doesn't support this and because they might
//  belong to different categories (which would btw also be 
//  possible with morphisms but is not yet available)
  
  
// need to choose silly name in order not to rename Type() aka
// Category()
  
intrinsic ParentCategory(f::Map) -> SetFormal
{}    
  require assigned f`static and assigned f`static`data :
    "Argument is not a morphism of a category";
  return f`static`data`category;
end intrinsic;

intrinsic IsObject(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  return C`data`IsObject;  
end intrinsic;

intrinsic IsMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsMorphism;  
end intrinsic;

intrinsic AreEqualObjects(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`AreEqualObjects;  
end intrinsic;

intrinsic AreEqualMorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`AreEqualMorphisms;  
end intrinsic;

intrinsic HasMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasMorphism :
     "Method not defined for category";
  return C`data`HasMorphism;  
end intrinsic;

intrinsic Morphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`Morphism :
     "Method not defined for category";
   return C`data`Morphism;  
end intrinsic;


intrinsic HasMorphismFromImages(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasMorphismFromImages :
     "Method not defined for category";
  return C`data`HasMorphismFromImages;  
end intrinsic;

intrinsic MorphismFromImages(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`MorphismFromImages :
     "Method not defined for category";
   return C`data`MorphismFromImages;  
end intrinsic;
     

intrinsic HasMorphismFromImagesAndBaseMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasMorphismFromImagesAndBaseMorphism :
     "Method not defined for category";
  return C`data`HasMorphismFromImagesAndBaseMorphism;  
end intrinsic;

intrinsic MorphismFromImagesAndBaseMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`MorphismFromImagesAndBaseMorphism :
     "Method not defined for category";
   return C`data`MorphismFromImagesAndBaseMorphism;  
end intrinsic;


intrinsic SupportsExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`SupportsExtension :
     "Method not defined for category";
  return C`data`SupportsExtension;  
end intrinsic;

intrinsic HasExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasExtension :
     "Method not defined for category";
  return C`data`HasExtension;  
end intrinsic;

intrinsic Extension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`Extension :
     "Method not defined for category";
   return C`data`Extension;  
end intrinsic;

intrinsic HasRightCancellation(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasRightCancellation :
     "Method not defined for category";
  return C`data`HasRightCancellation;  
end intrinsic;


intrinsic RightCancellation(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`RightCancellation :
     "Method not defined for category";
  return C`data`RightCancellation;  
end intrinsic;


intrinsic HasRestriction(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasRestriction :
     "Method not defined for category";
  return C`data`HasRestriction ;  
end intrinsic;


intrinsic Restriction(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`Restriction :
     "Method not defined for category";
  return C`data`Restriction ;  
end intrinsic;


intrinsic HasBaseExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasBaseExtension :
     "Method not defined for category";
  return C`data`HasBaseExtension;  
end intrinsic;


intrinsic BaseExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`BaseExtension :
     "Method not defined for category";
  return C`data`BaseExtension;  
end intrinsic;


intrinsic HasBaseExtensionMorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasBaseExtensionMorphisms :
     "Method not defined for category";
  return C`data`HasBaseExtensionMorphisms;  
end intrinsic;


intrinsic BaseExtensionMorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`BaseExtensionMorphisms :
     "Method not defined for category";
  return C`data`BaseExtensionMorphisms;  
end intrinsic;


intrinsic HasCoercion(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasCoercion :
     "Method not defined for category";
   return C`data`HasCoercion;  
end intrinsic;

intrinsic Coercion(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`Coercion;  
end intrinsic;

intrinsic HasIdentity(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasIdentity;  
end intrinsic;

intrinsic Identity(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`Identity;  
end intrinsic;

intrinsic IsIdentity(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsIdentity;  
end intrinsic;


intrinsic ImportExternalMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`ImportExternalMorphism :
     "Method not defined for category";
   return C`data`ImportExternalMorphism;  
end intrinsic;

intrinsic HasComposition(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasComposition;  
end intrinsic;

intrinsic Composition(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`Composition;  
end intrinsic;

intrinsic HasCompositionSequence(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasCompositionSequence;  
end intrinsic;

intrinsic CompositionSequence(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`CompositionSequence;  
end intrinsic;

intrinsic Degree(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`Degree :
     "Method not defined for category";
  return C`data`Degree;  
end intrinsic;

intrinsic SpecifyInverseMorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`SpecifyInverseMorphisms;  
end intrinsic;

intrinsic HasInverse(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasInverse;  
end intrinsic;
  
intrinsic InstallInverseConstructor(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`InstallInverseConstructor;  
end intrinsic;

intrinsic PreimageConstructorViaInverse(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`PreimageConstructorViaInverse;  
end intrinsic;

intrinsic IsIsomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsIsomorphism;  
end intrinsic;


intrinsic IsEndomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsEndomorphism;  
end intrinsic;


intrinsic IsAutomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsAutomorphism;  
end intrinsic;


intrinsic IsIsomorphic(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsIsomorphic;  
end intrinsic;


intrinsic HasIsomorphismExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasIsomorphismExtension;  
end intrinsic;


intrinsic HasIsomorphismExtensions(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasIsomorphismExtensions;  
end intrinsic;


intrinsic IsomorphismExtension(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsomorphismExtension;  
end intrinsic;


intrinsic IsomorphismExtensions(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsomorphismExtensions;  
end intrinsic;

intrinsic HasMorphismAutomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasMorphismAutomorphism;
end intrinsic;

intrinsic HasMorphismAutomorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasMorphismAutomorphisms;
end intrinsic;

intrinsic MorphismAutomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`MorphismAutomorphism;
end intrinsic;

intrinsic MorphismAutomorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`MorphismAutomorphisms;
end intrinsic;


intrinsic HasIsomorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasIsomorphisms;  
end intrinsic;


intrinsic Isomorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`Isomorphisms;  
end intrinsic;


intrinsic HasAutomorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`HasAutomorphisms;  
end intrinsic;


intrinsic Automorphisms(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`Automorphisms;  
end intrinsic;


intrinsic IsIsomorphicOverBase(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsIsomorphicOverBase;  
end intrinsic;


intrinsic IsomorphismsOverBase(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
   return C`data`IsomorphismsOverBase;  
end intrinsic;


intrinsic BaseObject(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`BaseObject :
     "Method not defined for category";
  return C`data`BaseObject;  
end intrinsic;


intrinsic ExtensionMorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`ExtensionMorphism :
     "Method not defined for category";
  return C`data`ExtensionMorphism;  
end intrinsic;


intrinsic HasFrobeniusEndomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`HasFrobeniusEndomorphism :
     "Method not defined for category";
  return C`data`HasFrobeniusEndomorphism;  
end intrinsic;


intrinsic FrobeniusEndomorphism(C::SetFormal) -> UserProgram  
{} 
  require assigned C`data :
     "Argument must be a category";
  require assigned C`data`FrobeniusEndomorphism :
     "Method not defined for category";
  return C`data`FrobeniusEndomorphism;  
end intrinsic;



//////////////////////////////////////////////////////////////////////////////
//
//  Record formats for various morphisms.
//

// Convention: field unset -> unknown                                   
//             otherwise known                                   
                                   

//  Field morphisms.
//
//   could have more attributes here like separable, finite type or so.  
//   do morphism of fields and field extension morphism in one rec currently   
  
field_map_fmt := recformat<

           // morphisms      
                 
           category,     // category to which map belongs      
           type,         // "coercion", "composition", "rule", "import"      
           is_identity,  // whether map is id in cat      
                 
           inverseexists,  // unassigned, "true", "false", "unknown"
           inverse,        // inverse morphism
           inverseconstr,  // constructor of inverse morphism
           tmp1, tmp2,     // temporary storage
                                  
           // field morphisms
           // additional type possible: "extension"                
                                                                
           // extension info                              
           ext_i, ext_j,       // i and j used in extension
           coeffmap,          // base map connects domains of i and j
           images,            // images of the gens of domain
                                                                
           // whether map supports extension                            
           supportsextension, // whether maps supports extension of maps
           affineequations,   // affine equations of corr. field extension
           polys,             // representation functions as polys for fldelts 
           gens,              // the corr. generators                 
                                                                
           // Invariants                                                     
           degree,            // degree of the corresponding field extension
                                                                
           //////////////////////////////////////////////////////////////
                                                                
           // ext field  maps
                                                              
           basemap,      // map of the base rings (*map_fmt or empty)
           invbasemap,   // inverse direction into F or BaseField(F)
           i, j         // vertical maps
                                                              
/* currently unused, code not yet included.                 
           basis,        // function to compute basis (finite dimension only)
           eltseq,       // function to represent in basis
           seqelt,       // converse to eltseq
           norm,         // function to compute norm map (which computes norms)
           is_extfldmap, // whether map is extension field map, then codomain
                         // is representing field extension
           extfldmap,    // corresponding trigonal extension field map
           maptoextfldmap, // map from map to extfldmap
           repmap,       // representing map for forget functor
           is_base_ext,  // whether geometric base fldfun extension
                         //  by base map
           different     // different of the funfld extension 
*/
           >;
   

//  Morphism morphisms.
//     type is only "morphism"

morphismcat_map_fmt := recformat< 
                           category, type, is_identity, top, bottom,
                           inverseexists, inverse, inverseconstr, tmp1, tmp2
                       >;  


//  Extension morphisms.
//     type is only "morphism".
//     The maps are exactly the same like for morphisms cats  
//     except that the carrier map is F -> G not i -> j  


extcat_map_fmt := recformat< 
                      category, type, is_identity, top, bottom,
                      inverseexists, inverse, inverseconstr, tmp1, tmp2
                  >;  

// Function field morphisms.
//     exactly the same like extension morphisms.

fldfun_map_fmt := recformat< 
                     category, type, is_identity, top, bottom,
                     inverseexists, inverse, inverseconstr, tmp1, tmp2
                  >;  

/////////////////////////////////////////////////////////////////////////////


ImportMorphism := function(f, C, type)
   if CHECK then
       assert assigned f`static;
       assert not assigned f`static`data;
       assert IsCategory(C);
       assert type in { "coercion", "import", "composition", "extension", 
			"rule", "morphism" };
       assert IsObject(C)(Domain(f));  
       assert IsObject(C)(Codomain(f));  
   end if;
   case C`data`type :
   when "FieldCategory" :  
       f_data := rec< field_map_fmt | >;
   when "MorphismCategory" :  
       f_data := rec< morphismcat_map_fmt | >;
   when "ExtensionCategory" :  
       f_data := rec< extcat_map_fmt | >;
   when "FunctionFieldCategory" :  
       f_data := rec< fldfun_map_fmt | >;
   else
       return ErrorHandler(ErrStat, 
                  "Invalid category type for morphism creation");
   end case;
   f_data`category := C;
   f_data`type := type;
   f`static`data := f_data;
   return f;
end function;
   
   
SpecifyInverseMorphismsPlain := function(f, g)  
   f`static`data`inverseexists := "true";
   g`static`data`inverseexists := "true";
   // mem loops
   f`static`data`inverse := g;
   g`static`data`inverse := f;
   return f, g;
end function;   
   
   
MakeIdentityPlain := function(f)   
   // (!:) called for its side effects in IsIdentity()
   f`static`data`is_identity := true;
   delete f`static`preimageconstr;
   f`static`data`inverseexists := "true";
   f`static`data`inverse := true;
   delete f`static`data`inverseconstr;
   return f;
end function;
   
   
/*   
   
GenericMorphism := function(F, G, C, type)
   f := GenericMap(F, G);
   f := ImportMorphism(f, C, type);
   return f;
end function;
   
*/ 
  
  
MakeGenericCategory := function()
   
   // this make something handle unique.
   // cmpeq -> handle comparison  
   // functors can the be maps on C  
     
   C := {! x in PowerStructure(Map) !};
   C`data := rec< category_fmt | >;
   
   // Generic stuff
   // These mehods are required to work for every category  
   // The Has* versions have to be defined in the respective categories  
     
   C`data`IsMorphism := function(f)
      return ISA(Type(f), Map) and assigned f`static and 
             assigned f`static`data and f`static`data`category cmpeq C;
   end function;   
      
   // ok is bool   
   C`data`Identity := function(F)
      ok, map, mess := HasIdentity(C)(F);
      if not ok then
         return ErrorHandler(ErrStat, mess);
      end if;
      return map;
   end function;
     
   // return bool   
   C`data`IsIdentity := function(f)
      if not IsMorphism(C)(f) then
         return ErrorHandler(ErrStat, 
            SPrintCategory(C) cat ": Argument is not morphism the category");
      end if;
      res := AreEqualMorphisms(C)(f, Identity(C)(Domain(f)));
      if res then
         f := MakeIdentityPlain(f);
      end if;
      return res;
   end function;
      
   // ok is "true", "false", "unknown"
   C`data`Inverse := function(f)
      ok, map, mess := HasInverse(C)(f);
      if ok cmpne "true" then
         ErrorHandler(ErrStat, mess);
      end if;
      return map;
   end function;
      
   // returns "true", "false", "unknown"
   C`data`IsIsomorphism := function(f)
      if not IsMorphism(C)(f) then
         return ErrorHandler(ErrStat, 
       SPrintCategory(C) cat ": Argument is not morphism in category");
      end if;
      res, g, mess := HasInverse(C)(f);
      return res, mess;
   end function;
      
   // returns "true", "false"
   C`data`IsEndomorphism := function(f)
      if not IsMorphism(C)(f) then
         return ErrorHandler(ErrStat, 
          SPrintCategory(C) cat ": Argument is not morphism in category");
      end if;
      if not AreEqualObjects(C)(Domain(f), Codomain(f)) then
         return "false";
      end if;
      return "true";   
   end function;
      
   // returns "true", "false", "unknown"
   C`data`IsAutomorphism := function(f)
      if not IsMorphism(C)(f) then
         return ErrorHandler(ErrStat, 
           SPrintCategory(C) cat ": Argument is not morphism in category");
      end if;
      if not AreEqualObjects(C)(Domain(f), Codomain(f)) then
         return "false", SPrintCategory(C) cat 
             ": Domain and codomain of argument are not equal";
      end if;
      return IsIsomorphism(C)(f);   
   end function;
      
   // ok is bool
   C`data`Composition := function(f, g)
      ok, map, mess := HasComposition(C)(f, g);
      if not ok then
         return ErrorHandler(ErrStat, mess);
      end if;
      return map;
   end function;
     
   // returns bool
   C`data`HasCompositionSequence := function(L)   
   //
   // Composition of morphisms in a sequence
   //
      if #L lt 1 then 
     return false, false, SPrintCategory(C) cat 
            ": Sequence length must be greater than 0";
      end if;   
      h := L[1];
      HasComposition := HasComposition(C);
      for i in [2..#L] do
        ok, h, mess := HasComposition(h, L[i]);
        if not ok then break; end if;   
      end for;
      if not ok then
         return false, false, mess; 
      end if;                      
      return true, h, "ok";
   end function;   
      
   C`data`CompositionSequence := function(L)   
     ok, map, mess := HasCompositionSequence(C)(L);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
   end function;      
      
   C`data`HasRestriction := function(f, i, j)   
      IsMorphism := IsMorphism(C);
      if not IsMorphism(f) then
         return false, false, SPrintCategory(C) cat 
                ": First argument is not morphism of category";
      end if;
      if not IsMorphism(i) then
         return false, false, SPrintCategory(C) cat 
                ": Second argument is not morphism of category";
      end if;
      if not IsMorphism(j) then
         return false, false, SPrintCategory(C) cat 
                ": Third argument is not morphism of category";
      end if;
      if not AreEqualObjects(C)(Domain(f), Codomain(i)) then
         return false, false, SPrintCategory(C) cat 
    ": Domain of first argument is not equal to Codomain of second argument";
      end if;
      if not AreEqualObjects(C)(Codomain(f), Codomain(j)) then
         return false, false, SPrintCategory(C) cat 
   ": Codomain of first argument is not equal to Codomain of third argument";
      end if;
      h := Composition(C)(i, f);
      // use more map info to better support compositions?
      ok, c, mess := HasRightCancellation(C)(h, j);
      if not ok then
         return false, false, mess;
      end if;
      cc := GenericMapFromMap(c);  
      // here we could check whether possibly given constrs yield
      //  good result etc ...  
      preimageconstr := function(static)
         ok, finv, mess := HasInverse(C)(f);
         if ok cmpne "true" then
            static`data`tmp1 := ok;
            static`data`tmp2 := finv;
            return false, false;
         end if;
         hinv := Composition(C)(j, finv);
         ok, cinv, mess := HasRightCancellation(C)(hinv, i);
         if not ok then
            static`data`tmp1 := "false";
            static`data`tmp2 := false;
            return false, false;
         end if;
         static`data`tmp1 := "true";
         static`data`tmp2 := cinv;
         image := ImageFunction(cinv);
         return true, image;         
      end function;
      inverseconstr := function(cc)
         if not assigned cc`static`data`tmp1 then
            ok, preim := HasPreimageFunction(cc);
         end if;
         ok := cc`static`data`tmp1;
         ccinv := cc`static`data`tmp2;
         delete cc`static`data`tmp1;
         delete cc`static`data`tmp2;
         return ok, ccinv;
      end function;
      delete cc`static`preimageconstr;
      cc := InstallPreimageConstructor(cc, preimageconstr);
      delete cc`static`data`inverseconstr;
      cc := InstallInverseConstructor(C)(cc, inverseconstr);   
      return true, cc, "ok";
   end function;

   ///////////////////////////////////////////////////////////////////////
   // Support for inverses
          
   C`data`SpecifyInverseMorphisms := function(f, g)   
      // maybe not so good that existing inverse info
      // could be overwritten?                                     
      IsMorphism := IsMorphism(C);
      if not IsMorphism(f) or not IsMorphism(g) then
         return ErrorHandler(ErrStat, SPrintCategory(C) cat 
           ": Arguments are not morphisms of category");   
      end if;
      ok, h := HasComposition(C)(f, g);
      if not ok or not IsIdentity(C)(h) then
         return ErrorHandler(ErrStat, SPrintCategory(C) cat 
           ": First argument followed by second is not identity");
      end if;
      ok, h := HasComposition(C)(g, f);
      if not ok or not IsIdentity(C)(h) then
         return ErrorHandler(ErrStat, SPrintCategory(C) cat 
           ": Second argument followed by first is not identity");
      end if;
      return SpecifyInverseMorphismsPlain(f, g);  
   end function;   

   /* 
      inverseconstr gets f as argument and returns "true", "false", "unknown" 
      as first argument and Map or false as second.
      To avoid mem loop no use of f or static in imageconstr other than
      through parameter f.
   */

   C`data`InstallInverseConstructor := function(f, inverseconstr)
       if not IsMorphism(C)(f) then
          return ErrorHandler(ErrStat, SPrintCategory(C) cat 
            ": First argument is not morphism of category");   
       end if;
       if Type(inverseconstr) cmpne UserProgram then
          return ErrorHandler(ErrStat, SPrintCategory(C) cat 
            ": Second argument is not a user program");   
       end if;           
       if assigned f`static`data`inverse and 
                   f`static`data`inverse cmpne false then
          return f;
          /*
          return ErrorHandler(ErrStat, SPrintCategory(C) cat 
            ": Morphism already has an inverse");   
          */   
       end if;         
       if assigned f`static`data`inverseconstr then
          return f;
          /*
          return ErrorHandler(ErrStat, SPrintCategory(C) cat 
            ": Morphism already has an inverse constructor");   
          */   
       end if;         
       if not assigned f`static`data`is_identity or
          not f`static`data`is_identity then
          // inverseconstr would never be called and deleted for f = id
          f`static`data`inverseconstr := inverseconstr;   
          delete f`static`data`inverseexists;
       end if;
       return f;
   end function;   
      
   /* not used.   
   C`data`PreimageConstructorViaInverse := function(f)   
       if not IsMorphism(C)(f) then
          return ErrorHandler(ErrStat, SPrintCategory(C) cat 
            ": First argument is not morphism of category");   
       end if;
       // when stored in f this causes a mem loop
       //    ( the problem is that f is not accessible
       //      when x@@f is called. )
       return function(static)
          ok, g := HasInverse(C)(f);
          if g cmpeq false then
             return ok, false, "No preimage function via inverse available";   
          end if;
          image := ImageFunction(g : Lazy := true);
          return true, image;
       end function;
   end function;
   */   
     
   EvalInverseResults := function(C, f, res, g)                
      if res eq "false" then
         return "false", false, SPrintCategory(C) cat 
           ": Inverse does not exist";
      end if;
      if res eq "unknown" then
         return "unknown", false, SPrintCategory(C) cat 
           ": No algorithm to decide existence of inverse";
      end if;
      // true
      if g cmpeq false then
         return "true", false, SPrintCategory(C) cat
   ": Inverse exists but morphism does not have algorithm to compute inverse";
      end if;                 
      if g cmpeq true then  // identity
          return "true", f, "ok"; 
      end if;
      return "true", g, "ok";
   end function;   
     
   MakeInverseMorphism := function(f)
      // information has been computed?  
      if assigned f`static`data`inverseexists then
         assert assigned f`static`data`inverse;
         return EvalInverseResults(C, f, f`static`data`inverseexists, 
                                         f`static`data`inverse);   
      end if;   
      // nothing found out yet
      // so do some work
      if assigned f`static`data`inverseconstr then
         res, g := f`static`data`inverseconstr(f);
         delete f`static`data`inverseconstr;
         f`static`data`inverseexists := res;   
         f`static`data`inverse := g;
         if g cmpne false then   
            assert res eq "true";
            f, g := SpecifyInverseMorphismsPlain(f, g);
         end if;   
         return EvalInverseResults(C, f, res, g);
      end if;  
      // no algorithm for inverse ...
      // a sufficient test
      //   could be inverseconstr for maps of type "composition".   
      if f`static`data`type eq "composition" then
         L := Components(f);
         assert #L gt 1;
         M := [ PowerStructure(Map) | ];
         HasInverse := HasInverse(C);
         for f1 in L do
            res, g1, mess := HasInverse(f1);
            if res cmpne "true" then
               f`static`data`inverseexists := "unknown";
               f`static`data`inverse := false;
               return EvalInverseResults(C, f, "unknown", false);
            end if;
            if g1 cmpne false then
               Append(~M, g1);   
            end if;   
         end for;
         if #M ne #L then
            f`static`data`inverseexists := "true";
            f`static`data`inverse := false;
            return EvalInverseResults(C, f, "true", false);
         else 
            M := Reverse(M);
            ok, g, mess := HasCompositionSequence(C)(M);
            assert ok;
            f, g := SpecifyInverseMorphismsPlain(f, g);
            return EvalInverseResults(C, f, "true", g);
         end if;
      end if;
      // nothing found out
      f`static`data`inverseexists := "unknown";
      f`static`data`inverse := false;
      return EvalInverseResults(C, f, "unknown", false); 
   end function;

   // First return value: "true", "unknown", "false"
   // Second return value: inverse morphism
   //    If first "true" and second false then inverse exists but
   //    cannot be computed
   // Third return value: error/message string

   C`data`HasInverse := function(f)   
      if not IsMorphism(C)(f) then
         return "false", false, SPrintCategory(C) cat
           ": Argument is not morphism of category";
      end if;
      if assigned f`static`data`is_identity and f`static`data`is_identity then
          return "true", f, "ok";
      end if;
      return MakeInverseMorphism(f);
   end function;
      
   return C;
   
end function;
   
   
IsSameRationalFunctionField := function(F, G)
   if { Type(F), Type(G) } subset { FldFun, FldFunRat } then
      return F eq G;
   end if;
   return false;
end function;
   
   

/////////////////////////////////////////////////////////////////////////////
//  
//  Functors
//  
  
//  
// should fit this better into framework  
// and make much better support  
//  
  
functor_map_fmt := recformat<
                   is_functor, 
                   ObjectMap, MorphismMap,
                   ObjectMapHasPreimage, MorphismMapHasPreimage
                      >;

// Domain and Codomain are the categories!

intrinsic IsFunctor(f::Map) -> Bool
  {}
  if not assigned f`static and 
     not assigned f`static`data and 
     not assigned f`data`is_functor then
     return false;  
   end if;
   return f`static`data`is_functor;
end intrinsic;


intrinsic Functor(C::SetFormal, D::SetFormal, 
                  f::UserProgram, g::UserProgram) -> Map
 {}
  require IsCategory(C) and IsCategory(D) :
    "First two arguments must be categories";
  // no further testing done
  F := map< C -> D | x :-> x >;
  F`static`data := rec< functor_map_fmt | >;
  F`static`data`is_functor := true;
  F`static`data`ObjectMap := f;
  F`static`data`MorphismMap := g;
  return F;
  
end intrinsic;


intrinsic Functor(C::SetFormal, D::SetFormal, 
                  f::UserProgram, g::UserProgram,
                  f_preimage::UserProgram, g_preimage::UserProgram) -> Map
 {}
  require IsCategory(C) and IsCategory(D) :
    "First two arguments must be categories";
  // no further testing done
  F := map< C -> D | x :-> x >;
  F := ImportMap(F, false);
  F`static`data := rec< functor_map_fmt | >;
  F`static`data`is_functor := true;
  F`static`data`ObjectMap := f;
  F`static`data`MorphismMap := g;
  F`static`data`ObjectMapHasPreimage := f_preimage;
  F`static`data`MorphismMapHasPreimage := g_preimage;
  return F;
  
end intrinsic;


intrinsic ObjectMap(f::Map) -> UserProgram
  {}
  require IsFunctor(f) :
    "Map must be a functor";
  return f`static`data`ObjectMap;
end intrinsic;


intrinsic MorphismMap(f::Map) -> UserProgram
  {}
  require IsFunctor(f) :
    "Map must be a functor";
  return f`static`data`MorphismMap;
end intrinsic;


intrinsic ObjectMapHasPreimage(f::Map) -> UserProgram
  {}
  require IsFunctor(f) :
    "Map must be a functor";
  return f`static`data`ObjectMapHasPreimage;
end intrinsic;


intrinsic MorphismMapHasPreimage(f::Map) -> UserProgram
  {}
  require IsFunctor(f) :
    "Map must be a functor";
  return f`static`data`MorphismMapHasPreimage;
end intrinsic;

   
/////////////////////////////////////////////////////////////////////////////
//  
//  Utilities.
//


//  Some fix inconsistencies in Magma.

  
intrinsic IsPerfect(F::Fld) -> Bool
{Return whether field is perfect}  
    return Characteristic(F) eq 0 or    
           IsFinite(F); 
end intrinsic;        


intrinsic IsPerfect(F::RngUPolRes) -> Bool
{Return whether field is perfect}  
    require IsField(F) :
      "Argument must be a field";
    return IsPerfect(BaseRing(F));
end intrinsic;        
        
  
intrinsic Degree(F::FldFunRat) -> .
{The degree of F over its base, always infinity}  
  return Infinity();
end intrinsic;  
  
  
intrinsic BaseField(F::FldFin) -> FldFin
{The ground field of F}  
  return GroundField(F);
end intrinsic;  


intrinsic BaseField(F::FldFunRat) -> Fld
{The base field of F}  
   R := BaseRing(F);
   require IsField(R) :
       "Rational function field is not defined over a field";
   return R;       
end intrinsic;  


intrinsic BaseField(F::RngUPolRes) -> Fld
{The base field of F}  
  R := BaseRing(F);
  require IsField(R) : "Base ring must be a field";
  return R;  
end intrinsic;  


intrinsic ISABaseField(F::Fld, G::Fld) -> Bool
{Whether G is among the (recursively defined) base fields of F}  
   if G cmpeq F then
      return true;
   end if; 
   if BaseField(F) cmpeq F then
      return false;
   end if;
   return ISABaseField(BaseField(F), G);
end intrinsic;  


intrinsic Degree(F::Fld, K::Fld) -> .
{The degree of F over K}  
  require ISABaseField(F, K) : 
     "Second argument is not a base field of first argument";
  if F cmpeq K then
     return 1; 
  end if;
  return Degree(F) * Degree(BaseField(F), K);
end intrinsic;  


intrinsic IsPrimeField(F::Fld) -> BoolElt
{Whether F is a prime field}  
  return PrimeField(F) cmpeq F;
end intrinsic;  

// version in Magma does not work for higher ranks
intrinsic ConstantField(F::FldFunRat) -> Fld
{The constant field of F}  
  R := BaseRing(F);
  require IsField(R) : "Base ring is not a field";
  return R;
end intrinsic;  


intrinsic IsSimple(F::FldFun) -> BoolElt
{}  
  require Degree(F) cmpne Infinity(): "Function must not be of infinite degree";
  return Ngens(F) eq 1 and IsSimple(EquationOrderFinite(F));
end intrinsic;  


/*
   
// The following is generically wrt RngMPol.
//  This may eliminate too much info, if we want to recreate
//  fields from their equations. Hence alternative versions below ...
//
//  For the maps we only need to give generator images 
//  so we do not need the unified RngMPol situation.
//

PolynomialsFieldExtension := function(a)  
   F := Parent(a);
   case Type(F):
      when FldFin:
         R := PolynomialRing(GroundField(F), 1 : Global);
         a := PolynomialRing(GroundField(F))!Eltseq(a);
         return Evaluate(a, R.1), R!1;
      when FldNum,FldQuad,FldCyc:
         if Ngens(F) gt 1 then
            return ErrorHandler(ErrStat, "Unsupported number field case");
         end if;
         R := PolynomialRing(BaseField(F), 1 : Global);
         a := PolynomialRing(BaseField(F))!Eltseq(a);
         return Evaluate(a, R.1), R!1;
      when FldFunRat: 
         if Rank(F) eq 1 then
           R := PolynomialRing(BaseRing(F), 1 : Global);
           return Evaluate(Numerator(a), R.1), Evaluate(Denominator(a), R.1);
         else     
           return Numerator(a), Denominator(a);
         end if;           
      when FldFun:
         a := RationalFunction(a);
         return Numerator(a), Denominator(a);
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
    end case;
end function;

   
AffineEquationsFieldExtension := function(F)
   case Type(F):
      when FldFin:
         R := PolynomialRing(GroundField(F), 1 : Global);
         a := DefiningPolynomial(F);
         return [ Evaluate(a, R.1) ];
      when FldNum,FldQuad,FldCyc:
         if Ngens(F) gt 1 then
            R := PolynomialRing(BaseField(F), Ngens(F) : Global);
            L := DefiningPolynomial(F);
            L := [ R | Evaluate(L[i], R.i) : i in [1..Ngens(F)] ];
            return L;
         end if;
         R := PolynomialRing(BaseField(F), 1 : Global);
         a := DefiningPolynomial(F);
         return [ Evaluate(a, R.1) ];
      when FldFunRat:
         return [ PolynomialRing(BaseField(F), Rank(F) : Global) | ];
      when FldFun:
         if IsFinite(Degree(F)) then 
            R := PolynomialRing(BaseField(F), Ngens(F) : Global);
            L := DefiningPolynomials(F);
            L := [ R | Evaluate(L[i], R.i) : i in [1..Ngens(F)] ];
            return L;   
         else 
            return [ DefiningPolynomial(F) ];            
         end if;
      when RngUPolRes:
         return [ Modulus(F) ];           
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
    end case;
end function;

*/


PolynomialsFieldExtension := function(a)  
//
// Lift to free ring 
//
   F := Parent(a);
   case Type(F):
      when FldFin:
         R := PolynomialRing(GroundField(F) : Global);
         a := R!Eltseq(a);
         return a, R!1;
      when FldNum,FldQuad,FldCyc:
         if Ngens(F) gt 1 or not IsSimple(F) then
            return ErrorHandler(ErrStat, "Unsupported number field case");
         end if;
         R := PolynomialRing(BaseField(F) : Global);
         a := R!Eltseq(a);
         return a, R!1;
      when FldFunRat: 
         return Numerator(a), Denominator(a);
      when FldFun:
         a := RationalFunction(a);
         return Numerator(a), Denominator(a);
      when RngUPolRes:
         R := PreimageRing(F);
         assert Type(R) eq RngUPol;
         return R!a;           
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
    end case;
end function;


AffineEquationsFieldExtension := function(F)
   case Type(F):
      when FldFin:
         a := DefiningPolynomial(F);
         return [ a ];
      when FldNum,FldQuad,FldCyc:
         if Ngens(F) gt 1 or not IsSimple(F) then
            return ErrorHandler(ErrStat, "Unsupported number field case");
         end if;
         a := DefiningPolynomial(F);
         return [ a ];
      when FldFunRat:
         return [ Parent(Numerator(F.1)) | ];
      when FldFun:
         if IsFinite(Degree(F)) then
            if Ngens(F) gt 1 or not IsSimple(F) then
               return ErrorHandler(ErrStat, "Unsupported function field case");
            end if;
            // deal with silly k[x] case
            R := BaseField(F);
            return [ R!Eltseq(DefiningPolynomial(F)) ];
         end if;	 
         return [ DefiningPolynomial(F) ];            
      when RngUPolElt:
         return [ Modulus(F) ];           
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
    end case;
end function;


/////////////////////////////////////////////////////////////////////////////
//  
//  Field category 
//  
//                           
  
// Could think of transcendence stuff: basis, separating, differentials,
//  derivations ...   


intrinsic FieldCategory() -> SetFormal
{Create category of fields}                           
  
  Z := Integers();
  if assigned Z`FieldCategory then
     return Z`FieldCategory;
  end if;
  
  C := MakeGenericCategory();
  C`data`type := "FieldCategory";
  Z`FieldCategory := C;
  
  // fairly generic stuff 

  C`data`HasIdentity := function(F)
      if not IsObject(C)(F) then
         return false, false, SPrintCategory(C) cat
                ": Argument is not object of category";
      end if;
      ok, map, mess := HasCoercion(C)(F, F);
      assert ok;
      map := MakeIdentityPlain(map);
      return true, map, "ok";
  end function;
      
  C`data`Coercion := function(F, G)
     ok, map, mess := HasCoercion(C)(F, G);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
        
  C`data`Extension := function(c, i, j, I)
     ok, map, mess := HasExtension(C)(c, i, j, I);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
               
  C`data`RightCancellation := function(f, g)
     ok, map, mess := HasRightCancellation(C)(f, g);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
   
  C`data`Restriction := function(f, i, j)
     ok, map, mess := HasRestriction(C)(f, i, j);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  // special stuff   
    
  C`data`SPrintCategory := function()
    return "Field category";     
  end function;
    
  C`data`IsObject := function(F)
     return ISA(Type(F), Fld) or 
            ( Type(F) eq RngUPolRes and IsField(F) );
            // this is for general residue class fields of places
  end function;   

  C`data`AreEqualObjects := function(F, G)
     return F cmpeq G;        
  end function;     
     
  GeneratorsOverBaseField := function(F)  
   if BaseField(F) cmpeq F then
      return [ F | ];
   end if;
   case Type(F):
      when FldFin:
         return [ F.1 ];
      when FldNum,FldQuad,FldCyc:
         return [ F.i : i in [1..Ngens(F)] ]; 
      when FldFunRat: 
         return [ F.i : i in [1..Rank(F) ] ];
      when FldFun:
        if IsFinite(Degree(F)) then
            return [ F.i : i in [1..Ngens(F)] ];
        end if;
        if Ngens(F) eq 1 then
         // standard rational alff 
         // it works like a general alff only F.2 does not work       
           gens := [ F.1, 4711 ];  
           assert IsZero(Evaluate(DefiningPolynomial(F), gens));
           return gens;   
        end if;
        assert Ngens(F) eq 2;
        return [ F.1, F.2 ];         
      when RngUPolRes:
        return [ F.1 ];
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
   end case;
  end function;
     
  C`data`AreEqualMorphisms := function(f, g)   
     if CHECK then
	 IsMorphism := IsMorphism(C);
	 if not IsMorphism(f) then
	    return ErrorHandler(ErrStat, SPrintCategory(C) cat 
	      ": First argument is not morphisms of category");
	 end if;   
	 if not IsMorphism(g) then
	    return ErrorHandler(ErrStat, SPrintCategory(C) cat 
	      ": Second argument is not morphisms of category");
	 end if;   
     end if;
     if f cmpeq g then
        return true;
     end if;
     if Domain(f) cmpne Domain(g) then
        return false;
     end if;
     if Codomain(f) cmpne Codomain(g) then
        return false;
     end if;
     /* for speedup?
     if assigned f`static`data`is_coercion and f`static`data`is_coercion and 
        assigned g`static`data`is_coercion and g`static`data`is_coercion then
        return true;
     end if;
     */
     if assigned f`static`data`is_identity and f`static`data`is_identity and 
        assigned g`static`data`is_identity and g`static`data`is_identity then
        return true;
     end if;
     F := Domain(f);
     /* 
     // This should apply and make it faster quite often  
     if assigned f`static`data`ext_i and 
        assigned g`static`data`ext_i and 
        f`static`data`ext_i cmpeq g`static`data`ext_i and 
        f`static`data`ext_j cmpeq g`static`data`ext_j then  
        return 
          f`static`data`images eq g`static`data`images and
          AreEqualMaps( f`static`data`coeffmap, g`static`data`coeffmap );
     end if;
     */
     // general case
     if BaseField(F) cmpeq F then
        // no further testing possible, would need representation details of F
        // have to conclude
        assert IsPrimeField(F);  
        return true;
     end if;
     L := GeneratorsOverBaseField(F);
     fL := [ f(x) : x in L ];
     gL := [ g(x) : x in L ];
     if fL ne gL then
        return false;
     end if;
     // restrict maps to base field
     f := Composition(C)(Coercion(C)(BaseField(F), F), f);
     g := Composition(C)(Coercion(C)(BaseField(F), F), g);
     return AreEqualMorphisms(C)(f, g);
  end function;   
     
  C`data`HasCoercion := function(F, G)
    // workaround for finite fields because CoveringStructure
    // yields left instead of right field when isomorphic       
    // and left field is standard field  
    if Type(F) cmpeq FldFin and Type(F) eq Type(G) then
       if Characteristic(F) ne Characteristic(G) then
          return false, false, "F must be subfield of G";
       end if;
       k := PrimeField(F);
       if IsDivisibleBy(Degree(G, k), Degree(F, k)) then
          Embed(F, G);
       else   
          return false, false, "F must be subfield of G";
       end if;
    else   
       if not CoveringStructure(F, G) cmpeq G then 
          return false, false, "F must be subfield of G";
       end if;   
    end if;   
    /* yyy 1 */
    f := ImportMorphism(CoercionMap(F, G), C, "coercion");    
    if F cmpeq G then
       f := MakeIdentityPlain(f); // not normally required in Coercion
       f`static`data`degree := 1;
    else
       f`static`data`is_identity := false;                         
       f`static`data`inverseconstr := function(f)
          // check a couple of cases   
          if ISABaseField(G, F) then 
             return "false", false;
          end if;   
          if Degree(C)(f) eq 1 then
             g := ImportMorphism(CoercionMap(G, F), C, "coercion");    
             g`static`data`is_identity := false;                         
             g`static`data`degree := 1;
             return "true", g;
          else
             return "false", false;
          end if;
       end function;     
    end if;
    return true, f, "ok";
  end function;     
     
  MyLCM := function(L)
     if IsField(Universe(L)) then
        return One(Universe(L));
     end if;
     return LCM(L);          
  end function;
     
  MyEvaluate := function(f, L)
     if Type(Parent(f)) eq RngUPol then
        assert #L eq 1;
        f := PolynomialRing(BaseRing(Universe(L)))!f;
        return Evaluate(f, L[1]);
     end if;
     return Evaluate(f, L);
  end function;
     
  CombineExtensionInfo := function(F1, affeq1, polys1, gens1, 
                                   F2, affeq2, polys2, gens2)
    //
    //  combine data for map1 followed by map2
    //
    P1 := Universe(affeq1);
    P2 := Universe(affeq2);     
    r1 := Rank(P1);
    r2 := Rank(P2);
    P := PolynomialRing(BaseRing(P1), r2 + r1);
    h1 := hom< P1 -> P | [ P.(i + r2) : i in [1..r1] ] >;
    PG := [ P | P.i : i in [1..r2] ];
    split := function(a)
      num := [ Universe(affeq1) | ];
      den := [ Universe(affeq1) | ];
      for c in Coefficients(a) do
         n, d := polys1(c);
         Append(~num, n);
         Append(~den, d);
      end for;
      d := MyLCM( den );
      c := [ h1( (d * num[i]) div den[i] ) : i in [1..#num] ];
      m := [ MyEvaluate(m, PG) : m in Monomials(a) ];
      return &+ [ P | c[i] * m[i] : i in [1..#num] ], h1(d);
    end function;
    affeq := [ P | ];  
    for a in affeq2 do
      Append(~affeq, split(a));
    end for;
    affeq := affeq cat [ h1(a) : a in affeq1 ];
    gens := gens2 cat gens1;
    polys := function(a)  
        if Parent(a) cmpne F2 then
           return ErrorHandler(ErrStat, 
                          "Element is not in required field");         
        end if;
        num2, den2 := polys2(a);
        num2n, num2d := split(num2);
        den2n, den2d := split(den2);
        return num2n * den2d, num2d * den2n;
    end function;   
    return affeq, polys, gens;     
  end function;
     
  SupportsExtensionDegreeOne := function(i)   
    // this should not be applied for degree one 
    // extension where the domain is the base field  
    assert Degree(C)(i) cmpeq 1;
    ok, preim := HasPreimageFunction(i);
    if not ok then
       return false, false, false, false, "No preimage function given";
    end if;
    R := PolynomialRing(Domain(i));
    affineequations := [ R | ];
    polys := function(a) 
       return R!z where _, z := preim(a), One(R); 
    end function;
    gens := [ Codomain(i) | ];   
    i`static`data`supportsextension := true;
    i`static`data`affineequations := affineequations;
    i`static`data`polys := polys;
    i`static`data`gens := gens;
    return true, affineequations, polys, gens, "ok";
  end function;
     
  C`data`SupportsExtension := function(i)   
  //   
  //  Whether map can be used to extend other maps along it   
  //  Returns bool, eqn list, poly function, gens
  //           
  //  eqn_list fits with GeneratorsOverBase() if i is coercion  
  //  from base field.                                               
  //                                                 
    if not IsMorphism(C)(i) then
     return false, false, false, SPrintCategory(C) cat
            ": Argument is not a morphism of category";
    end if;   
    if not assigned i`static`data`supportsextension then
      if IsIdentity(C)(i) then
         R := PolynomialRing(Domain(i));
         affineequations := [ R | ];
         polys := function(a) return a, One(R); end function;
         gens := [ Codomain(i) | ];   
         i`static`data`supportsextension := true;
         i`static`data`affineequations := affineequations;
         i`static`data`polys := polys;
         i`static`data`gens := gens;
         return true, affineequations, polys, gens, "ok";
      end if;
      // do it for the components
      L := Components(i);
      if #L gt 1 then
         ok, affineequations, polys, gens, mess := 
           SupportsExtension(C)(L[1]);
         if not ok then
            return false, false, false, false, mess;
         end if;
         for r in [2..#L] do
            f := L[r];
            ok, a, p, g, mess := SupportsExtension(C)(f);
            if not ok then
               return false, false, false, false, mess;
            end if;
            affineequations, polys, gens := 
              CombineExtensionInfo(Domain(f), affineequations, polys, gens, 
                                   Codomain(f), a, p, g);
         end for;
         i`static`data`supportsextension := true;
         i`static`data`affineequations := affineequations;
         i`static`data`polys := polys;
         i`static`data`gens := gens;
         return true, affineequations, polys, gens, "ok";
      end if;
      // case to be dealt with, but not so easy, hence for now false
      if not i`static`data`type eq "coercion" then
         if Degree(C)(i) eq 1 then
            return SupportsExtensionDegreeOne(i);
         end if;
         i`static`data`supportsextension := false;
         return false, false, false, false, SPrintCategory(C) cat 
                ": Can only handle coercion at the moment";
      end if;
      F := Codomain(i);
      K := Domain(i);
      if K cmpne BaseField(F) then
         // try substructures ...
         ok, j, mess := HasCoercion(C)(K, BaseField(F));
         if ok then
            ok, a, p, g, mess := SupportsExtension(C)(j);
            if not ok then
               return false, false, false, false, mess;
            end if;
            jn := Composition(C)(j, Coercion(C)(BaseField(F), F));
            assert not CHECK or AreEqualMorphisms(C)(i, jn);
            ok, affineequations, polys, gens := SupportsExtension(C)(jn);
            assert ok;
            i`static`data`supportsextension := true;
            i`static`data`affineequations := affineequations;
            i`static`data`polys := polys;
            i`static`data`gens := gens;
            return true, affineequations, polys, gens, "ok";
         end if;
         // try relative field
         case Type(F):
         when FldFin:
           Embed(K, F);
           f := MinimalPolynomial(F.1, K);
           G := ext< K | f >;
           Embed(F, G);
           f := Coercion(C)(F, G);
           finv := Coercion(C)(G, F);  
           j := Coercion(C)(K, G);
         when FldNum,FldQuad,FldCyc:
           if AbsoluteDegree(K) eq AbsoluteDegree(F) then
              // bug in RelativeField: not the case for deg one exts!
              // hence do this  
              return SupportsExtensionDegreeOne(i);          
           end if;
           G := RelativeField(K, F);
           assert BaseField(G) cmpeq K;
           f := Coercion(C)(F, G);
           finv := Coercion(C)(G, F);  
           j := Coercion(C)(K, G);
         else    
           return false, false, false, false, SPrintCategory(C) cat
  ": Domain of argument cannot be realized as (recursive) base field of codomain of argument";
         end case;
         ok, a, p, g, mess := SupportsExtension(C)(j);
         if not ok then
            return false, false, false, false, mess;
         end if;
         i`static`data`supportsextension := true;
         i`static`data`affineequations := a;
         i`static`data`polys := function(x)
            return p(Image(f, x));
         end function;
         i`static`data`gens := [ F | Image(finv, x) : x in g ];
         return true, i`static`data`affineequations, i`static`data`polys, i`static`data`gens, "ok";
      end if;   
      // first the affine equations
      case Type(F):
      when FldFin:
        a := DefiningPolynomial(F);
        affineequations := [ a ];
      when FldNum,FldQuad,FldCyc:
         if Ngens(F) gt 1 then
            return ErrorHandler(ErrStat, "Unsupported number field case");
         end if;
         a := DefiningPolynomial(F);
         // silly case: Z instead of Q
         R := BaseRing(Parent(a));
         if not IsField(R) then
             a := PolynomialRing(FieldOfFractions(R))!a;
         end if;
         affineequations := [ a ];
      when FldFunRat:
         affineequations := [ Parent(Numerator(F.1)) | ];
      when FldFun:
         if IsFinite(Degree(F)) then
            R := Parent(RationalFunction(F.1));        
            assert Type(R) in { RngUPol, RngMPol };
            if Type(R) cmpeq RngUPol then
               // don't forget silly k[x] case
               R := PolynomialRing(BaseField(F) : Global);
               affineequations := [ R!Eltseq(DefiningPolynomial(F))];
            else
               // don't forget silly k[x] case
               // and one var for every gen!  
               R := PolynomialRing(BaseField(F) : Global);
               L := [ R!Eltseq(f) : f in DefiningPolynomials(F) ];
               assert #L eq Ngens(F);
               // the following global is essential  
               // otherwise there is false coercion in HasExtension().  
               R := PolynomialRing(BaseField(F), #L : Global);
               affineequations := [ R | Evaluate(L[i], R.i) : i in [1..#L] ];
            end if;
         else
            affineequations := [ DefiningPolynomial(F) ];            
         end if;   
      when RngUPolRes:
         affineequations := [ Modulus(F) ];           
      else 
         return ErrorHandler(ErrStat, "Unsupported case in maps.m");
      end case;
     // now the polys 
     case Type(F):
     when FldFin:
        R := PolynomialRing(GroundField(F) : Global);
        polys := function(a) return R!Eltseq(a), R!1; end function;
     when FldNum,FldQuad,FldCyc:
        if Ngens(F) gt 1 then
          return ErrorHandler(ErrStat, "Unsupported number field case");
        end if;
        R := PolynomialRing(BaseField(F) : Global);
        polys := function(a) return R!Eltseq(a), R!1; end function;
     when FldFunRat: 
        polys := function(a) return Numerator(a), Denominator(a); end function;
     when FldFun:
        // distributive alffs return coeffs
        //  not in base field but fof(maxord(basefield))         
        //  This is a bug!                             
        SR := Parent(RationalFunction(F.1));                            
        R := BaseRing(SR);
        assert Type(SR) in { FldFunRat, RngUPol, RngMPol };
        assert Type(R) in { FldFun, FldFunRat, FldFin, FldRat, FldNum, FldQuad,
                            FldCyc, FldFunOrd, RngUPolRes };
        if Type(R) cmpeq FldFunOrd then
           // extract alff from fof
           F1 := FunctionField(Order(R)); 
           assert ISA(Type(F1), FldFunG);
           assert Type(SR) eq RngMPol;
           SF1 := PolynomialRing(F1, Rank(SR) : Global);
           c := Coercion(R, SF1);
           h := hom< SR -> SF1 | c, [ SF1.i : i in [1..Rank(SF1)] ] >; 
           polys := function(a)
              a := h(RationalFunction(a));
              return a, One(SF1);
           end function;
        else   
           if Type(SR) cmpeq RngUPol or Type(SR) cmpeq RngMPol then
              polys := function(a)
                 return RationalFunction(a), One(SR);
              end function;
           else   
              polys := function(a)
                 a := RationalFunction(a);
                 return Numerator(a), Denominator(a); 
              end function;
           end if;
        end if;         
     when RngUPolRes:
        R := PreimageRing(F);
        assert Type(R) eq RngUPol;
        polys := function(a)
           return R!a, One(R);
        end function;   
     else 
        return ErrorHandler(ErrStat, "Unsupported case in maps.m");
     end case;
     // now the gens
     gens := GeneratorsOverBaseField(F);  
     i`static`data`supportsextension := true;
     i`static`data`affineequations := affineequations;
     i`static`data`polys := polys;
     i`static`data`gens := gens;
   end if;
   if not i`static`data`supportsextension then
      return false, false, false, false, SPrintCategory(C) cat
             ": Cannot handle this field case for extension";
   end if;  
   return true, i`static`data`affineequations, i`static`data`polys, i`static`data`gens, "ok";
  end function;
    
  FieldCategoryExtension := function(c, i, j, I, L, polys)   
    F := Codomain(i);
    G := Codomain(j);
    cc := Composition(C)(c, j);
    map := hom< Universe(L) -> G | cc, I >;
    if not &and [ IsZero(map(x)) : x in L ] then
       return false, SPrintCategory(C) cat 
              ": Image generators are invalid", _, _;
    end if;
    // now c is a field map, hence it is injective, hence
    // map must be injective, and is a field map.
    // yyy 2       
    image := function(x)
       return true, map(num) / map(den) where num, den := polys(x);
    end function;
    f := GenericMap(F, G);
    f := InstallImage(f, image);
    f := ImportMorphism(f, i`static`data`category, "extension");      
    f`static`data`coeffmap := c;
    f`static`data`ext_i := i;
    f`static`data`ext_j := j;
    f`static`data`images := I;
    return true, "ok", f, map;
  end function;
   
  C`data`HasExtension := function(c, i, j, I)
     IsMorphism := IsMorphism(C);
     if not IsMorphism(c) then
        return false, false, SPrintCategory(C) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(i) then
        return false, false, SPrintCategory(C) cat 
               ": Second argument is not morphism of category";
     end if;
     if not IsMorphism(j) then
        return false, false, SPrintCategory(C) cat 
               ": Third argument is not morphism of category";
     end if;
     AreEqualObjects := AreEqualObjects(C);
     if not AreEqualObjects(Domain(c), Domain(i)) or
        not AreEqualObjects(Codomain(c), Domain(j)) then
        return false, false, SPrintCategory(C) cat 
               ": Morphisms do not fit together for extension";
     end if;
     /*
     //  lazy maps need more work, e.g. in Cmor when check that 
     //  top and bottom commute. If true is returned here or there
     //  does it mean that operation will be usccessul etc. 
     if Type(I) cmpeq UserProgram then
        // lazy case           
        f := ImportMorphism(GenericMap(F, G), C, "morphism");
        delete f`static`preimage;
        imageconstr := function(static)
           print "in iamgeconstr";
           ok, g := HasMorphismFromImagesAndBaseMorphism(C)(F, G, I(), c); 
           if not ok then
              return ErrorHandler(ErrStat, 
                             "Lazy image function construction failed");
           end if;
           image := ImageFunction(g : Lazy := false);                  
           return true, image;   
        end function;
        f := InstallImageConstructor(f, imageconstr);
        return true, f, "lazy ok";           
     end if;
     */
     if not AreEqualObjects(Universe(I), Codomain(j)) then
        return false, false, SPrintCategory(C) cat 
               ": Images must be defined over codomain of c";
     end if;
     ok, L, polys := SupportsExtension(C)(i);
     if not ok then
        return false, false, SPrintCategory(C) cat 
               ": Morphism does not support extension";
     end if;
     if #I ne Rank(Universe(L)) then
       return false, false, SPrintCategory(C) cat 
              ": I must have correct length";
     end if;   
     ok, mess, f, map := FieldCategoryExtension(c, i, j, I, L, polys);
     // consider also intelligent degree, preimage and inverse functions?
     // maybe only on demand  
     if not ok then
        return false, false, mess;
     end if;
     return ok, f, mess;
  end function;
     
  C`data`HasComposition := function(f, g)   
     IsMorphism := IsMorphism(C);
     if not IsMorphism(f) then
        return false, false, SPrintCategory(C) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(g) then
        return false, false, SPrintCategory(C) cat 
               ": Second argument is not morphism of category";
     end if;
     if not AreEqualObjects(C)(Codomain(f), Domain(g)) then
        return false, false, SPrintCategory(C) cat 
   ": Codomain of first argument is not equal to domain of second argument";
     end if;
     // yyy 3
     h := ImportMorphism(CompositionMap(f, g), C, "composition");
     if assigned f`static`data`degree and assigned g`static`data`degree then
        h`static`data`degree := f`static`data`degree * g`static`data`degree;
     end if;   
     // further information is preserved in the data fields of the components
     // of h, so we need not store or process it here.
    return true, h, "ok";  
  end function; 
     
  // in other cats this might not be unique 
  // hence signature sufficient here?      
  C`data`HasRightCancellation := function(f, g)   
     IsMorphism := IsMorphism(C);
     if not IsMorphism(f) then
        return false, false, SPrintCategory(C) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(g) then
        return false, false, SPrintCategory(C) cat 
               ": Second argument is not morphism of category";
     end if;
     if not AreEqualObjects(C)(Codomain(f), Codomain(g)) then
        return false, false, SPrintCategory(C) cat 
   ": Codomain of first argument is not equal to codomain of second argument";
     end if;
     F := Domain(f);     
     if BaseField(F) cmpeq F then
        // no further testing possible, would need representation details of F
        // have to conclude
        assert IsPrimeField(F);  
        c := Coercion(C)(F, Domain(g));
        return true, c, "ok";
     end if;
     ok, gpre := HasPreimageFunction(g);
     if not ok then
        return false, false, SPrintCategory(C) cat 
            ": Second argument does not have preimage function";
     end if;
     L1 := GeneratorsOverBaseField(F);
     L2 := [ Domain(g) | ];
     for a in L1 do
        ok, b := gpre(f(a));
        if not ok then
           return false, false, SPrintCategory(C) cat 
                  ": Right cancellation is not possible";
        end if;
        Append(~L2, b);   
     end for;
     i := Coercion(C)(BaseField(F), F);
     f := Composition(C)(i, f);
     ok, c, mess := HasRightCancellation(C)(f, g);
     if not ok then
        return false, false, mess;
     end if;
     j := Identity(C)(Domain(g));
     ok, h, mess := HasExtension(C)(c, i, j, L2);
     assert ok;
     return true, h, "ok";     
  end function;
          
  // redefine generic method
  SpecifyInverseMorphismsC := SpecifyInverseMorphisms(C);  
  C`data`SpecifyInverseMorphisms := function(f, g)
      // yyy 11
      f := GenericMapFromMap(f);
      g := GenericMapFromMap(g);      
      delete f`static`preimage;
      delete g`static`preimage;
      f := InstallPreimage(f, g`static`image);
      g := InstallPreimage(g, f`static`image);
      // this does also check that f and g are inverse
      f, g := SpecifyInverseMorphismsC(f, g);
      f`static`data`degree := 1;
      g`static`data`degree := 1;
      return f, g;      
  end function;
     
  // redefine generic method   
  HasInverseC := HasInverse(C);   
  C`data`HasInverse := function(f)   
     if Degree(C)(f) cmpne 1 then
        f`static`data`inverseexists := "false";
        f`static`data`inverse := false;
        return "false", false, SPrintCategory(C) cat ": Degree is not one";   
     end if;
     res, g, mess := HasInverseC(f);
     if res eq "unknown" and f`static`data`type eq "composition" then
        // since category is fields we can conclude more precisely here
        // over the generic case  
        for f1 in Components(f) do
           res1, g1, mess1 := HasInverseC(f1);
           if res1 eq "false" then
              f`static`data`inverseexists := "false";
              f`static`data`inverse := false;
              return "false", false, mess1;   
           end if;
        end for;
     end if;
     return res, g, mess;
  end function;
     
  // redefine (stupid) generic method   
  C`data`IsIsomorphism := function(f)
     if Degree(C)(f) ne 1 then
        return "false", SPrintCategory(C) cat 
          ": Degree is not equal to one";
     end if;
     assert Degree(C)(f) eq 1;
     return "true", "ok";
  end function;
     
  C`data`Degree := function(f)
     if not IsMorphism(C)(f) then
        return false, false, SPrintCategory(C) cat 
               ": Argument is not morphism of category";
     end if;
     if assigned f`static`data`degree then
        return f`static`data`degree;
     end if;
     L := Components(f);
     for ii in [1..#L] do
        g := L[ii];      
        if not assigned g`static`data`degree then
           case Type(Codomain(g)) :
             when FldFin :
             g`static`data`degree := Degree(Codomain(g), Domain(g));
           when FldNum, FldQuad, FldCyc :
             d := AbsoluteDegree(Codomain(g));
             e := AbsoluteDegree(Domain(g));
             assert d mod e eq 0;
             g`static`data`degree := d div e;
           when FldFunRat, FldFun:
             if Type(Domain(g)) in { FldFin, FldRat, FldNum, FldQuad, FldCyc } then
                g`static`data`degree := Infinity();
             elif AreEqualObjects(C)(ConstantField(Codomain(g)), 
                                        Domain(g)) then
                g`static`data`degree := Infinity();
             else
               if Type(Codomain(g)) eq FldFunRat then
                  if Rank(Codomain(g)) ne 1 then
                     return ErrorHandler(ErrStat, 
                                    "Unsupported case in degree (1)");
                  end if;   
               end if;  
               // need to do some analysing
               F := Domain(g);
               G := Codomain(g);
//  this is wrong ...               
//               if ISABaseField(G, F) then  
//                  g`static`data`degree := Degree(G, F);
//               else
                  // need to do some further analysing
                  E := FunctionFieldCategory();
                  i := Coercion(C)(BaseObject(E)(F), F);
                  j := Coercion(C)(BaseObject(E)(G), G);
                  ok, c := HasRestriction(C)(g, i, j);
                  if not ok then
                     return ErrorHandler(ErrStat, 
                                    "Unsupported case in degree (2)");
                  end if;
                  x := SeparatingElement(Domain(g));
                  e := Degree(x);
                  d := Degree(g(x));
                  if d eq 0 then
                     g`static`data`degree := Infinity();
                  end if;
                  assert d mod e eq 0;
                  g`static`data`degree := (d div e) * Degree(C)(c);
           //  end if; 
             end if; 
          when RngUPolRes :
            // handle one simple case
            ok, c := HasCoercion(C)(Domain(g), Codomain(g));
            assert ok;
            if AreEqualObjects(C)(Domain(g), BaseField(Codomain(g))) and 
               AreEqualMorphisms(C)(g, c) then
               g`static`data`degree := Degree(Modulus(Codomain(g)));
            else
         return ErrorHandler(ErrStat, "Unsupported RngUPolRes case in degree");
            end if;   
          else : 
             return ErrorHandler(ErrStat, "Unsupported case in degree");
           end case;
        end if;   
     end for;
     f`static`data`degree := &* [ g`static`data`degree : g in L ];
     return f`static`data`degree;
  end function;
     
  // technical (ugly) thing to turn maps into morphisms   
  C`data`ImportExternalMorphism := function(f, is_iso)
     // yyy 4
     f := ImportMap(f, true);  
     f := ImportMorphism(f, C, "import");
     if is_iso then
        f`static`data`degree := 1;
        inverseconstr := function(f)
            g := ImportMap(Inverse(f), true);
            g := ImportMorphism(g, C, "import");
            g`static`data`degree := 1;
            return "true", g;      
        end function;         
        f := InstallInverseConstructor(C)(f, inverseconstr);      
     end if;
     return f;        
  end function;
     
  MakeAutomorphisms := function(F, s)
     // identity must come first!
     if s eq 0 then
        return "true", [], "ok";
     end if;
     if s eq 1 then
        return "true", [ Identity(C)(F) ], "ok";
     end if;
     if IsPrimeField(F) then
        return "true", [ Identity(C)(F) ], "ok";
     end if;
     case Type(F) :
       when FldFin :
         p := Characteristic(F);
         L := [];
         // identity will be first
         for i in [0..Minimum(s, Degree(F, PrimeField(F)))-1] do
            ok, f := HasFrobeniusEndomorphism(C)(F, p^i);
            assert ok;
            Append(~L, f);
         end for;
         return "true", L, "ok";   
       when FldNum,FldQuad,FldCyc :
         if BaseField(F) cmpne Rationals() then
            Fabs := AbsoluteField(F);
            f := Coercion(C)(Fabs, F);
            ok, g := HasInverse(C)(f);
            assert ok cmpeq "true";
            ok, L, mess := HasAutomorphisms(C)(Fabs, s);
            assert ok cmpeq "true";
            // better define in direct terms?
            L := [ CompositionSequence(C)( [g, h, f ] ) : h in L ];
         else   
            M := Automorphisms(F);
            L := [];
            // turn into morphisms
            for i in [1..#M] do         
               f := ImportExternalMorphism(C)(M[i], true); 
               Append(~L, f);   
            end for;     
         end if;
         assert IsIdentity(C)(L[1]);
         return "true", L, "ok";
       when FldFunRat, FldFun :
          // s is gt 1
          if not Type(ConstantField(F)) in { FldFin, FldNum, FldRat, FldQuad, FldCyc } 
             or ( Type(F) eq FldFunRat and Rank(F) gt 1) then
             return "unknown", false, SPrintCategory(C) cat 
                 ": No algorithm for computing automorphisms available for "
                 cat Sprint(F);
          end if;
          
          // this is ok since here fields aut are equal to function field auts
          E := FunctionFieldCategory();
          ok, L := HasAutomorphisms(E)(F, s);
          assert ok cmpeq "true";   
          L := [ Top(f) : f in L ]; // cat is now C
          return "true", L, "ok";   
       else :
          return "unknown", false, SPrintCategory(C) cat
                 ": Field type currently unsupported";     
     end case;
  end function;

  MakeIsomorphismsRationalFunctionFields := function(F, G, c, s)
    assert { Type(F), Type(G) } eq { FldFunRat }; 
    assert s in { 0, 1 };
    if Rank(F) ne Rank(G) then
        return "false", false, SPrintCategory(C) cat ": Different ranks";
    end if;
    if c cmpeq false then
       ok, c, mess := IsIsomorphic(C)(BaseRing(F), BaseRing(G));   
       if ok cmpeq "unknown" then
           return "unknown", false, SPrintCategory(C) cat 
   	          ": No isomorphy test for these base fields" cat
                  Sprint(F) cat " and " cat Sprint(G);
       end if;
       if ok cmpeq "false" then
           return "false", false, SPrintCategory(C) cat 
	          ": Base fields not isomorphic";
       end if;
       assert ok cmpeq "true";
    end if;
    i := Coercion(C)(BaseRing(F), F);
    j := Coercion(C)(BaseRing(G), G);
    ok, _, _, L := SupportsExtension(C)(j);
    assert ok;
    ok, f, mess := HasExtension(C)(c, i, j, L);
    assert ok;
    if s gt 0 then
       ok, _, _, M := SupportsExtension(C)(i);
       assert ok;
       ok, d := HasInverse(C)(c);
       assert ok cmpeq "true";
       ok, g, mess := HasExtension(C)(d, j, i, M);
       assert ok;
       f, g := SpecifyInverseMorphisms(C)(f, g);
       return "true", [ f ], "ok";
    end if;
    return "true", [], "ok";
  end function;

  MakeIsomorphisms := function(F, G, s)
     if F cmpeq G then
        // assertion here is that prime fields are cmp-equal
        if s eq 0 then
           return "true", [], "ok";
        end if;
        if s eq 1 then
           return "true", [ Identity(C)(F) ], "ok";
        end if;
        if IsPrimeField(F) then
           return "true", [ Identity(C)(F) ], "ok";
        end if;
     end if;
     if Characteristic(F) ne Characteristic(G) then
        return "false", [], "ok";
     end if;
     case Type(F) :
       when FldFin :
          if #F ne #G then
             return "false", false, SPrintCategory(C) cat
                    ": Different field sizes";
          end if;
          Embed(F, G);
          if s gt 0 then
             ok, f := HasCoercion(C)(F, G);
          else
             ok, _ := HasCoercion(C)(F, G);          
          end if;
          assert ok;                 
       when FldNum, FldQuad, FldCyc :
          if s gt 0 then
            ok, f := IsIsomorphic(F, G);
          else
            ok, _ := IsIsomorphic(F, G);
          end if;          
          if not ok then
             return "false", false, SPrintCategory(C) cat ": Not isomorphic";
          end if;
          if s gt 0 then
             f := ImportExternalMorphism(C)(f, true);             
          end if;   
       when FldFunRat, FldFun :
          if { Type(F), Type(G) } eq { FldFunRat } and s le 1 then
          // this aims at more general semi trivial cases which cannot 
          // be handled by the general alff iso algo
             ok, L, mess := MakeIsomorphismsRationalFunctionFields(F, G, 
                             false, s);
             if ok cmpne "true" then
                 return ok, false, mess;
             end if; 
             if s gt 0 then 
                f := L[1];
             end if;
          else
             if not Type(ConstantField(F)) in { FldFin, FldNum, FldRat, FldQuad, FldCyc } then 
                 return "unknown", false, SPrintCategory(C) cat 
   	          ": No isomorphy test for these base fields: " cat
                  Sprint(F) cat " and " cat Sprint(G);
             end if;
             E := FunctionFieldCategory();
             ok, f := IsIsomorphic(E)(F, G);
             if ok cmpne "true" then
                return "false", false, SPrintCategory(C) cat
                  ": Not isomorphic";
             end if;
             f := Top(f); // cat is now C   
          end if;
       else :
         return "unknown", false, SPrintCategory(C) cat
                 ": Field type currently unsupported";     
     end case;
     // have one isomorphism, make the rest   
     if s eq 0 then
        L := [];   
     elif s eq 1 then   
        L := [ f ];
     else
        ok, L, mess := MakeAutomorphisms(F, s);
        if ok cmpne "true" then
           return ok, false, mess;
        end if;
        // maybe some simplification would be good here
        L := [ Composition(C)(g, f) : g in L ];   
     end if;
     if F cmpeq G then
        assert IsIdentity(C)(L[1]);
     end if;
     return "true", L, "ok";
  end function;
     
  C`data`HasAutomorphisms := function(F, s)   
     if not IsObject(C)(F) then
        return "unknown", false, SPrintCategory(C) cat
               ": First argument is not object of category";     
     end if;
     if s eq 0 then
        return "true", [], "ok";
     end if;
     if s eq 1 then
        return "true", [ Identity(C)(F) ], "ok";
     end if;
     ok, L, mess := MakeAutomorphisms(F, s);
     return ok, L, mess;
  end function;         
     
  C`data`HasIsomorphisms := function(F, G, s)
     // s is integer ge 0   
     if not IsObject(C)(F) then
        return "unknown", false, SPrintCategory(C) cat
               ": First argument is not object of category";     
     end if;
     if not IsObject(C)(G) then
        return "unknown", false, SPrintCategory(C) cat
               ": Second argument is not object of category";     
     end if;
     if Type(F) cmpne Type(G) then
        return "unknown", false, SPrintCategory(C) cat
               ": Fields are of different type, currently not supported";     
     end if;
     if AreEqualObjects(C)(F, G) then
        return HasAutomorphisms(C)(F, s);
     end if;
     ok, L, mess := MakeIsomorphisms(F, G, s);
     return ok, L, mess;
  end function;
     
  C`data`IsIsomorphic := function(F, G)
     if not IsObject(C)(F) then
        return "unknown", false, SPrintCategory(C) cat
               ": First argument is not object of category";     
     end if;
     if not IsObject(C)(G) then
        return "unknown", false, SPrintCategory(C) cat
               ": Second argument is not object of category";     
     end if;
     ok, L, mess := HasIsomorphisms(C)(F, G, 1);
     if ok cmpne "true" then
        return ok, false, mess;
     end if;
     return "true", L[1], mess;
  end function;
          
  C`data`Isomorphisms := function(F, G, s)
     ok, map, mess := HasIsomorphisms(C)(F, G, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  C`data`Automorphisms := function(F, s)
     ok, map, mess := HasAutomorphisms(C)(F, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
/*

  Not used at the moment. 

  MakeMorphismAutomorphisms := function(i, s)
     // ie. commuting automorphisms of domain and codomain
     if IsPrimeField(Domain(i)) then
        return MakeAutomorphisms(Codomain(i), s);
     end if;
     if IsIdentity(C)(i) then
        return MakeAutomorphisms(Codomain(i), s);
     end if;
     // this is wasteful and should be improved
     // ( especially when i has trans deg one )
     ok, L, mess := MakeAutomorphisms(Codomain(i), s);
     if ok cmpne "true" then
        return "unknown", false, 
          "Cannot make morphism automorphisms from automorphisms";
     end if;
     S := [ f : f in L | HasRestriction(C)(f, i, i) ];
     return "true", S, "ok";
  end function;
     
  SupplementWithAuts := function(f, i, s)   
     // have one isomorphism f, make the rest by composing with auts
     if s eq 0 then
        L := [];   
     elif s eq 1 then   
        L := [ f ];
     else
        ok, L, mess := MakeMorphismAutomorphisms(i, s);
        if ok cmpne "true" then
           return ok, false, mess;
        end if;
        // maybe some simplification would be good here
        L := [ Composition(C)(g, f) : g in L ];   
     end if;
     return "true", L, "ok";   
  end function;

  C`data`HasMorphismAutomorphisms := function(i, s)   
     // s is integer ge 0   
     IsMorphism := IsMorphism(C);
     if not IsMorphism(i) then
        return false, false, SPrintCategory(C) cat 
               ": First argument is not morphism of category";
     end if;
     ok, L, mess := MakeMorphismAutomorphisms(i, s);
     return ok, L, mess;     
  end function;

  C`data`HasMorphismAutomorphism := function(c, i, j)   
     return HasMorphismAutomorphisms(C)(c, i, j, 1);
  end function;

  C`data`MorphismAutomorphism := function(c, i, j)
     ok, map, mess := HasMorphismAutomorphism(C)(c, i, j);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  C`data`MorphismAutomorphisms := function(c, i, j, s)
     ok, map, mess := HasMorphismAutomorphisms(C)(c, i, j, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;

*/
     
  MakeIsomorphismExtensions := function(c, i, j, s)   
     // Compute field morphisms f such that i * f = c * j.
     if Degree(C)(i) cmpne Degree(C)(j) then
        return "false", false, "Degrees are different";
     end if;
     ok1, g := HasInverse(C)(i);
     ok2 := IsIsomorphism(C)(j);
     if ok1 eq "true" and ok2 eq "true" then
        f := CompositionSequence(C)( [g, c, j] );
        return "true", [ f ], "ok";
     end if;
     if IsPrimeField(Domain(c)) then
        return MakeIsomorphisms(Codomain(i), Codomain(j), s);
     end if;
     // semi trivial case
     if { Type(Codomain(i)), Type(Codomain(j)) } eq { FldFunRat } 
        and s le 1 then
        ok, L, mess := MakeIsomorphismsRationalFunctionFields(Codomain(i),
                          Codomain(j), c, s);
        assert ok cmpeq "true";
        return "true", L, "ok";
     end if;
     // this is wasteful and should be improved
     // ( especially when i has trans deg one )
     ok, L, mess := MakeIsomorphisms(Codomain(i), Codomain(j), s);
     if ok cmpeq "unknown" then
        return "unknown", false, SPrintCategory(C) cat 
          ": Cannot make isomorphism extensions from isomorphisms";
     end if;
     if ok cmpeq "false" then
        return "false", false, SPrintCategory(C) cat
          "Codomains are not isomorphic";
     end if;
     assert ok cmpeq "true";
     S := [];
     for f in L do
        if AreEqualMorphisms(C)(Composition(C)(i, f), 
                                Composition(C)(c, j)) then
           Append(~S, f);
        end if;
     end for;
     return "true", S, "ok";
  end function;
     
  C`data`HasIsomorphismExtensions := function(c, i, j, s)   
     // s is integer ge 0   
     IsMorphism := IsMorphism(C);
     if not IsMorphism(c) then
        return "unknown", false, SPrintCategory(C) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(i) then
        return "unknown", false, SPrintCategory(C) cat 
               ": Second argument is not morphism of category";
     end if;
     if not IsMorphism(j) then
        return "unknown", false, SPrintCategory(C) cat 
               ": Third argument is not morphism of category";
     end if;
     AreEqualObjects := AreEqualObjects(C);
     if not AreEqualObjects(Domain(c), Domain(i)) or
        not AreEqualObjects(Codomain(c), Domain(j)) then
        return "false", false, SPrintCategory(C) cat 
               ": Morphisms do not fit together for extension";
     end if;
     if IsIsomorphism(C)(c) cmpne "true" then
        return "unknown", false, SPrintCategory(C) cat 
               ": First argument is not known to be ismorphism of category";
     end if;
     // can do only a couple of cases yet
     // ( could compute all isomorphisms and then see which extend c )
     ok, L, mess := MakeIsomorphismExtensions(c, i, j, s);
     return ok, L, mess;     
  end function;
          
  C`data`HasIsomorphismExtension := function(c, i, j)   
     return HasIsomorphismExtensions(c, i, j, 1);
  end function;

  C`data`IsomorphismExtension := function(c, i, j)
     ok, map, mess := HasIsomorphismExtension(C)(c, i, j);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  C`data`IsomorphismExtensions := function(c, i, j, s)
     ok, map, mess := HasIsomorphismExtensions(C)(c, i, j, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  C`data`HasFrobeniusEndomorphism := function(F, q)
     if not IsObject(C)(F) then
        return false, false, SPrintCategory(C) cat 
               ": First argument is not object in category";
     end if;
     if q eq 1 then
        return true, Identity(C)(F), "ok";
     end if;
     ok, p, r := IsPrimePower(q);
     if not ok then
        return false, false, SPrintCategory(C) cat 
               ": Second argument must be a prime power";
     end if;   
     if p ne Characteristic(F) then
        return false, false, SPrintCategory(C) cat ": The characteristic must be prime and q must be a power of the characteristic";
     end if;
     if IsFinite(F) then
     // reduction
       r := r mod Degree(F, PrimeField(F));
       q := p^r;
     end if;  
     // yyy 5
     f := hom< F -> F | x :-> x^q, y :-> Root(y, q) >;
     // perfect etc and degree setting missing  
     f := ImportMap(f, false);
     f := InstallPreimage(f, function(y) 
                                return true, Root(y, q); end function);
     f := ImportMorphism(f, C, "rule");
     if IsFinite(F) then  
        g := hom< F -> F | y :-> Root(y, q), x :-> x^q >;
        g := ImportMap(g, false);
        g := InstallPreimage(g, function(x) 
                                   return true, x^q; end function);
        g := ImportMorphism(g, C, "rule");        
        f, g := SpecifyInverseMorphismsPlain(f, g);
        f`static`data`degree := 1;
        g`static`data`degree := 1;
     end if; 
     return true, f, "ok";
  end function;

  C`data`FrobeniusEndomorphism := function(F, q)
     ok, map, mess := HasFrobeniusEndomorphism(C)(F, q);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  return C;   
     
end intrinsic;                           


// quite special hence outside general definitions

intrinsic CoefficientMorphism(f::Map) -> Map
{The coefficient morphism of the field morphism f}
  
  require IsMorphism(f) and IsFieldCategory(ParentCategory(f)) :
     "Argument must be morphism of field category";

  if assigned f`static`data`coeffmap then
     return f`static`data`coeffmap;
  end if;
  
  F := Domain(f);
  map := Composition(Coercion(ParentCategory(f))(BaseField(F), F), f);
  
  f`static`data`coeffmap := map;
  return map;
  
end intrinsic;  

  
/////////////////////////////////////////////////////////////////////////////
//  
//  Morphism category
//  
  

intrinsic Top(f::Map) -> Map
{}
  require assigned f`static and 
          assigned f`static`data and assigned f`static`data`top :
     "Morphism does not have top morphism";
  return f`static`data`top;
end intrinsic;
  

intrinsic Bottom(f::Map) -> Map
{}
  require assigned f`static and 
          assigned f`static`data and assigned f`static`data`bottom :
     "Morphism does not have bottom morphism";
  return f`static`data`bottom;
end intrinsic;



MakeMorphismCategory := function(C, S)
  
  has_fixed_base := S cmpne false;
  Cmor := MakeGenericCategory();
  
  // fairly generic stuff

  Cmor`data`Coercion := function(i, j)   
     ok, map, mess := HasCoercion(Cmor)(i, j);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cmor`data`HasIdentity := function(i)   
     if not IsObject(Cmor)(i) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Argument is not object of category";
     end if;
     ok, map, mess := HasCoercion(Cmor)(i, i);     
     assert ok;
     map := MakeIdentityPlain(map);
     return true, map, "ok";
  end function;
     
  // special stuff  
    
  if has_fixed_base then
     Cmor`data`SPrintCategory := function()
        return "Morphism category of " cat
          SPrintCategory(BaseCategory(Cmor)) cat
          " over base object " cat Sprint(S);
     end function;
  else
     Cmor`data`SPrintCategory := function()
        return "Morphism category of " cat 
          SPrintCategory(BaseCategory(Cmor));     
     end function;
  end if;        
        
  if has_fixed_base then
     Cmor`data`IsObject := function(f)
        return IsMorphism(C)(f) and
               AreEqualObjects(C)(Domain(f), S);
     end function;   
  else
     Cmor`data`IsObject := function(f)
        return IsMorphism(C)(f);
     end function; 
  end if;      
        
  Cmor`data`AreEqualObjects := function(f, g)
     return IsObject(Cmor)(f) and IsObject(Cmor)(g) and
            AreEqualMorphisms(C)(f, g);
  end function;
     
  Cmor`data`AreEqualMorphisms := function(f, g)   
     ok := IsMorphism(Cmor)(f) and IsMorphism(Cmor)(g) and 
           AreEqualObjects(Cmor)(Domain(f), Domain(g)) and
           AreEqualObjects(Cmor)(Codomain(f), Codomain(g)) and         
           AreEqualMorphisms(C)(Top(f), Top(g)) and
           AreEqualMorphisms(C)(Bottom(f), Bottom(g));
     return ok;           
  end function;   
     
  Cmor`data`HasMorphism := function(i, j, f, g)   
     IsObject := IsObject(Cmor);
     if not IsObject(i) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;   
     if not IsObject(j) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not object of category";
     end if;   
     IsMorphism := IsMorphism(C);
     if not IsMorphism(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Third argument is not morphisms of base category";
     end if;
     if not IsMorphism(g) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Fourth argument is not morphisms of base category";
     end if;
     if has_fixed_base then
        if not IsIdentity(C)(g) then
           return false, false, SPrintCategory(Cmor) cat 
         ": Fourth argument is not an identity morphism of base category";
        end if;
     end if;
     AreEqualObjects := AreEqualObjects(C);
     if not AreEqualObjects(Codomain(i), Domain(f)) or 
        not AreEqualObjects(Codomain(f), Codomain(j)) or
        not AreEqualObjects(Domain(j), Codomain(g)) or
        not AreEqualObjects(Domain(g), Domain(i)) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Morphisms do not form square";
     end if;   
     ok, u, mess := HasComposition(C)(i, f);   
     if not ok then
        return false, false, mess;
     end if;
     ok, v, mess := HasComposition(C)(g, j);   
     if not ok then
        return false, false, mess;
     end if;
     if not AreEqualMorphisms(C)(u, v) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Morphisms do not form commutative square";
     end if;
     // yyy 6
     map := hom< i -> j | x :-> x >;   
     map := ImportMap(map, false);
     map := ImportMorphism(map, Cmor, "morphism");
     map`static`data`top := f;
     map`static`data`bottom := g;
     // No need to deal with inverses and isomorphisms since
     // morphisms are not maps and inverses are dealt with via top and bottom
     return true, map, "ok";   
  end function;   
     
  Cmor`data`Morphism := function(i, j, f, g)   
     ok, map, mess := HasMorphism(Cmor)(i, j, f, g);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cmor`data`HasCoercion := function(i, j)   
  //   
  //  Idea is that f and g as above are "naturally" given   
  //  
     IsObject := IsObject(Cmor);
     if not IsObject(i) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(j) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not object of category";
     end if;
     ok, f := HasCoercion(C)(Codomain(i), Codomain(j));
     if not ok then
        return false, false, SPrintCategory(Cmor) cat 
               ": No coercion of the top objects known";
     end if;   
     // if has_fixed_base then this will be the identity
     ok, g := HasCoercion(C)(Domain(i), Domain(j));
     if not ok then
        return false, false, SPrintCategory(Cmor) cat 
               ": No coercion of the bottom objects known";
     end if;   
     ok, u, mess := HasComposition(C)(i, f);   
     if not ok then
        return false, false, mess;   
     end if;
     ok, v, mess := HasComposition(C)(g, j);   
     if not ok then
        return false, false, mess;   
     end if;
     if not AreEqualMorphisms(C)(u, v) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Coercion does not form commutative square";
     end if;
     // yyy 7 
     map := hom< i -> j | x :-> x >;   
     map := ImportMap(map, false);
     map := ImportMorphism(map, Cmor, "morphism");     
     map`static`data`top := f;
     map`static`data`bottom := g;
     return true, map, "ok";   
  end function;   
     
  Cmor`data`HasComposition := function(f, g)   
     IsMorphism := IsMorphism(Cmor);
     if not IsMorphism(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(g) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not morphism of category";
     end if;
     if not AreEqualObjects(Cmor)(Codomain(f), Domain(g)) then
        return false, false, SPrintCategory(Cmor) cat 
   ": Codomain of first argument is not equal to domain of second argument";
     end if;
     ok, h_top, mess := HasComposition(C)(Top(f), Top(g));
     if not ok then
        return false, false, mess;
     end if;
     ok, h_bottom, mess := HasComposition(C)(Bottom(f), Bottom(g));
     if not ok then
        return false, false, mess;
     end if;
     ok, h, mess := HasMorphism(Cmor)(Domain(f), Codomain(g), h_top, h_bottom);
     if not ok then
        return false, false, mess;
     end if;
     return true, h, "ok";  
  end function;   
     
  // redefine generic inverse  
  // we have been lazy and need now to define f`static`data`inverse() 
  HasInverseCmor := HasInverse(Cmor);  
  Cmor`data`HasInverse := function(f)
     if not IsMorphism(Cmor)(f) then
        return "false", false, SPrintCategory(Cmor) cat 
          ": Argument is not morphism of category";
     end if;
     if assigned f`static`data`inverseexists then
         return HasInverseCmor(f);
     end if;
     if not assigned f`static`data`inverseconstr then
        inverseconstr := function(f)
           res, invf_top, mess1 := HasInverse(C)(Top(f));           
           // check various cases
           if res ne "true" then
              if res eq "false" then
                 return "false", false, mess1;
              end if;
              res, invf_bottom, mess2 := HasInverse(C)(Bottom(f));
              if res eq "false" then
                 return "false", false, mess2;
              end if;
              return "unknown", false, mess1;
           end if; 
           res, invf_bottom, mess2 := HasInverse(C)(Bottom(f));           
           if res ne "true" then
              return res, false, mess2;
           end if;
           // all ok
           ok, invf, mess := HasMorphism(Cmor)(Codomain(f), Domain(f), 
                                               invf_top, invf_bottom);
           assert ok;
           return "true", invf, "ok";
        end function;
        f := InstallInverseConstructor(Cmor)(f, inverseconstr);      
     end if;
     // now proceed with generic method
     return HasInverseCmor(f);  
  end function;
     
  Cmor`data`SpecifyInverseMorphisms := function(f, g)   
      IsMorphism := IsMorphism(Cmor);
      if not IsMorphism(f) or not IsMorphism(g) then
         return ErrorHandler(ErrStat, SPrintCategory(Cmor) cat 
           ": Arguments are not morphisms of category");   
      end if;
      ok, h := HasComposition(Cmor)(f, g);
      if not ok or not IsIdentity(Cmor)(h) then
         return ErrorHandler(ErrStat, SPrintCategory(Cmor) cat 
           ": First argument followed by second is not identity");
      end if;
      ok, h := HasComposition(Cmor)(g, f);
      if not ok or not IsIdentity(Cmor)(h) then
         return ErrorHandler(ErrStat, SPrintCategory(Cmor) cat 
           ": Second argument followed by first is not identity");
      end if;
      // yyy 12
      f_top, g_top := SpecifyInverseMorphisms(C)(Top(f), Top(g));
      f_bottom, g_bottom := SpecifyInverseMorphisms(C)(Bottom(f), Bottom(g));
      ff := GenericMapFromMap(f);
      ff`static`data`top := f_top;
      ff`static`data`bottom := f_bottom;
      gg := GenericMapFromMap(g);
      gg`static`data`top := g_top;
      gg`static`data`bottom := g_bottom;
      ff, gg := SpecifyInverseMorphismsPlain(ff, gg);
      return ff, gg;      
  end function;   
     
     
  Cmor`data`IsIsomorphism := function(f)
     if not IsMorphism(Cmor)(f) then
        return "false", false, SPrintCategory(Cmor) cat 
          ": Argument is not morphism of category";
     end if;
     ok1, mess1 := IsIsomorphism(C)(Top(f));
     if ok1 cmpeq "false" then
        return "false", mess1;
     end if;
     ok2, mess2 := IsIsomorphism(C)(Bottom(f));
     if ok2 cmpeq "false" then
        return "false", mess2;
     end if;
     if ok1 cmpeq "unknown" then
        return "unknown", mess1;
     end if;
     if ok2 cmpeq "unknown" then
        return "unknown", mess2;
     end if;
     return "true", "ok";
  end function;
     
  Cmor`data`SupportsExtension := function(i)
     if not IsMorphism(Cmor)(i) then
        return false, false, false, SPrintCategory(Cmor) cat 
               ": Argument is not a morphism of category";
     end if;
     ok, L_top, polys_top, gens_top, mess := SupportsExtension(C)(Top(i));
     if not ok then
        return false, false, false, false, false, false, false, mess;
     end if;
     ok, L_bottom, polys_bottom, gens_bottom, mess := 
       SupportsExtension(C)(Bottom(i));
     if not ok then
        return false, false, false, false, false, false, false, mess;
     end if;
     return true, L_top, polys_top, gens_top, 
                  L_bottom, polys_bottom, gens_bottom, "ok";     
  end function;
     
  Cmor`data`HasExtension := function(c, i, j, I_top, I_bottom)
  //
  //  This is actually a (commutative) cube.   
  //  
     IsMorphism := IsMorphism(Cmor);
     if not IsMorphism(c) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(i) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not morphism of category";
     end if;
     if not IsMorphism(j) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Third argument is not morphism of category";
     end if;
     if has_fixed_base then
        if #I_bottom ne 0 then
          return false, false, SPrintCategory(Cmor) cat 
               ": Fifth argument is not empty";
        end if;
        // exercise a little help
        I_bottom := [ Codomain(Bottom(j)) | ];
     end if;
     AreEqualObjects := AreEqualObjects(Cmor);
     if not AreEqualObjects(Domain(c), Domain(i)) or
        not AreEqualObjects(Codomain(c), Domain(j)) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Morphisms do not fit together for extension";
     end if;
     ok, f_top, mess := HasExtension(C)(Top(c), Top(i), Top(j), I_top);     
     if not ok then
        return false, false, mess;
     end if;          
     ok, f_bottom, mess := HasExtension(C)(Bottom(c), Bottom(i), Bottom(j), 
                                           I_bottom);     
     if not ok then
        return false, false, mess;
     end if;          
     ok, f, mess := HasMorphism(Cmor)(Codomain(i), Codomain(j), 
                                      f_top, f_bottom);
     if not ok then
        return false, false, mess;
     end if;          
     return ok, f, "ok";     
  end function;
     
  Cmor`data`HasRightCancellation := function(f, g)
     if not IsMorphism(Cmor)(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(Cmor)(g) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not morphism of category";
     end if;
     if not AreEqualObjects(Cmor)(Codomain(f), Codomain(g)) then
        return false, false, SPrintCategory(C) cat 
   ": Codomain of first argument is not equal to codomain of second argument";
     end if;
     ok, h_top, mess := HasRightCancellation(C)(Top(f), Top(g));
     if not ok then
        return false, false, mess;
     end if;
     ok, h_bottom, mess := HasRightCancellation(C)(Bottom(f), Bottom(g));
     if not ok then
        return false, false, mess;
     end if;
     ok, h, mess := HasMorphism(Cmor)(Domain(f), Domain(g), h_top, h_bottom);
     if not ok then
        return false, false, mess;
     end if;
     return true, h, "ok";     
  end function;
     
  Cmor`data`HasIsomorphisms := function(f, g, s)   
     if not IsObject(Cmor)(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cmor)(g) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not object of category";
     end if;
     // again wasteful
     ok, L, mess := HasIsomorphisms(C)(Codomain(f), Codomain(g), s);
     if ok cmpne "true" then
        return "unknown", false, SPrintCategory(Cmor) cat 
          ": Cannot compute isomorphisms of codomains of arguments";
     end if;
     S := [];
     for d in L do
        ok, c, mess := HasRestriction(C)(d, f, g);
        if ok then
           ok, h, mess := HasMorphism(Cmor)(f, g, d, c);
           if ok then
              Append(~S, h);
           end if;
        end if;
     end for;
     return "true", S, "ok";
  end function;
     
  Cmor`data`IsIsomorphic := function(F, G)
     if not IsObject(Cmor)(F) then
        return "unknown", false, SPrintCategory(Cmor) cat
               ": First argument is not object of category";     
     end if;
     if not IsObject(Cmor)(G) then
        return "unknown", false, SPrintCategory(Cmor) cat
               ": Second argument is not object of category";     
     end if;
     ok, L, mess := HasIsomorphisms(Cmor)(F, G, 1);
     if ok cmpne "true" then
        return ok, false, mess;
     end if;
     return "true", L[1], mess;
  end function;
     
  Cmor`data`HasAutomorphisms := function(f, s)   
      if not IsObject(Cmor)(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;
     // side effect: identity is first!
     return HasIsomorphisms(Cmor)(f, f, s);
  end function;
     
  Cmor`data`Isomorphisms := function(F, G, s)
     ok, map, mess := HasIsomorphisms(Cmor)(F, G, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  Cmor`data`Automorphisms := function(F, s)
     ok, map, mess := HasAutomorphisms(Cmor)(F, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  Cmor`data`HasBaseExtension := function(F, c)
     if not IsObject(Cmor)(F) then
        return false, false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;
     if not IsExtensionCategory(C) then
        return false, false, false, SPrintCategory(Cmor) cat 
               ": Base category must be extension category";
     end if;
     D := MorphismCategory( BaseCategory(C) ); 
     if not IsMorphism(D)(c) then
        return false, false, false, SPrintCategory(Cmor) cat 
               ": Second argument is not morphism of base morphism category";
     end if;
     if not AreEqualObjects(D)(Bottom(F), Domain(c)) then
        return false, false, false, SPrintCategory(Cmor) cat 
   ": Bottom morphism of first argument must be equal to domain of second argument";
     end if;
     f := F;
     i := Bottom(c);
     j := Top(c);
     c := Codomain(c);
     ok, fb, ib, jb, mess := HasBaseExtensionMorphisms(C)(f, i, j, c);
     if not ok then
        return false, false, false, mess;
     end if;
     ok, ext, mess := HasMorphism(Cmor)(f, fb, jb, ib);
     assert ok;
     return true, fb, ext, "ok";
  end function;
     
  Cmor`data`BaseExtension := function(F, c)
     ok, F1, map, mess := HasBaseExtension(Cmor)(F, c);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return F1, map;
  end function;
     
  return Cmor;
     
end function;
   
   
intrinsic MorphismCategory( C::SetFormal : Global := true ) -> SetFormal
{Create morphism category of given category C} 
  
  require IsCategory(C) :
    "Argument must be a category";
  
  if Global and assigned C`data`morphismcategory then
     return C`data`morphismcategory;
  end if;
  
  Cmor := MakeMorphismCategory(C, false);
  Cmor`data`type := "MorphismCategory";
  
  Cmor`data`basecategory := C;
  
  if Global then
     // mem loop
     C`data`morphismcategory := Cmor;  
  end if;  
  
  return Cmor; 
  
end intrinsic;


intrinsic MorphismCategory( C::SetFormal, S::Any : Global := true ) 
                                                             -> SetFormal
{Create morphism category of given category C over base S} 
  
  require IsCategory(C) :
    "First argument must be a category";
  require IsObject(C)(S) :
    "Second argument must be object of category";

  if Global then
     if assigned C`data`morphismcategoryoverbase then
        AreEqualObjectsC := AreEqualObjects(C);
        for Cmor in C`data`morphismcategoryoverbase do
           _, T := BaseCategory(Cmor);
           if AreEqualObjectsC(T, S) then
              return Cmor;
           end if;
        end for;
     else 
        C`data`morphismcategoryoverbase := [ PowerStructure(SetFormal) | ];
     end if;
  end if;
     
  Cmor := MakeMorphismCategory(C, S);
  Cmor`data`type := "MorphismCategory";
  
  Cmor`data`basecategory := C;
  Cmor`data`baseobject := S;
  
  if Global then
     // mem loop
     Append(~C`data`morphismcategoryoverbase, Cmor);  
  end if;
  
  return Cmor;
  
end intrinsic;  


/////////////////////////////////////////////////////////////////////////////
//  
//  Extension category
//  
//  
//  Problems: Cannot make "trivial" extension objects in Magma
//  
//  Can view objects as extensions only by coercion at the moment.
//  Hence 1. in general, base field not uniquely determined
//           but interpretion in an ext category over a fixed base fairly 
//           clear.    
//        2. Special type like FldFun "naturally" determines base field.  
//           Hence interpretation in ext category without fixed base clear.
  
  
  
  
  
FieldExtensionFromAffineEquations := function(L, F)
//
//  Cannot handle too many cases yet.
//    L is list of zero/one equation either zero dim or one dim.
//    Universe(L) can be quite general.
//    Have the usual problem: Create affine alg or isomorphic FldFun?
//       Again easy type change would be good.
//
//  Basically: Create FOF(Universe(L) / ideal< Universe(L) | L >)
//             and make the type close to the original type and
//             to the type of BaseRing(Universe(L)).
//
   R := BaseRing(Universe(L));
   assert IsField(R);
   type := Type(F);
   if not IsFinite(Degree(F)) then
      if Type(F) eq FldFunRat then
         assert #L eq 0;
         if Type(Parent(Numerator(F.1))) eq RngUPol then
             return true, FunctionField(R), "ok";
         else
             return true, FunctionField(R, Rank(Parent(Numerator(F.1)))), "ok";
         end if;  
      end if;
      if not Type(F) cmpeq FldFun or #L gt 1 then
          return false, false, "Unsupported case";
      end if;
      if not IsIrreducible(L[1]) then
          return false, false, "Not irreducible";
      end if;
      return true, FunctionField(L[1]), "ok";
   end if; 
   // make finite extension
   // print "Type R ", Type(R), " type F ", Type(F);
   case Type(R):
      when FldFin:
         assert #L eq 1;
         if not IsIrreducible(L[1]) then
            return false, false, "Not irreducible";
         end if;
         return true, ext< R | L[1] >, "ok";
      when FldNum, FldQuad, FldCyc:
         if #L gt 1 then
            return false, false, "Unsupported number field case";
         end if;
         if not IsIrreducible(L[1]) then
            return false, false, "Not irreducible";
         end if;
         return true, NumberField(L[1]), "ok";
      when FldFunRat, FldFun: 
         if Type(R.1) eq FldFunRatMElt then
            return false, false, "Unsupported function field case";
         end if;
         if Type(Universe(L)) cmpeq RngMPol then
            // make vars into one var
            S := PolynomialRing(R : Global);
            z := [ S.1 : i in [1..Rank(Universe(L))] ];
            L := [ Evaluate(f, z) : f in L ];
            // better check for irreducibility here. Not done yet.
            // otherwise failure in FunctionField()  
            F := FunctionField(L);
            return true, F, "ok";
         end if;
         assert Type(Universe(L)) cmpeq RngUPol;
         if not IsIrreducible(L[1]) then
            return false, false, "Not irreducible";
         end if;
         return true, FunctionField(L[1]), "ok";
      else 
         return false, false, "Unsupported case";
    end case;

end function;
   
   
   
BaseExtensionSpecial := function(R, f)
  assert Type(R) in { RngUPol, RngMPol };
  assert Domain(f) cmpeq BaseRing(R);
  if Type(R) eq RngUPol then
    S := PolynomialRing(Codomain(f) : Global);
    c := Coercion(BaseRing(S), S);
    // yyy 8
    g := hom< R -> S | f * c, S.1 >;
    g := ImportMap(g, false);
    g := InstallPreimage(g, 
            function(y)
               L1 := Eltseq(y);
               L := [ BaseRing(R) | ];
               for a in L1 do
                  ok, b := HasPreimage(f, a);
                  if not ok then
                     return false, _;
                  end if;
                  Append(~L, b);
               end for;
               return true, R!L;
            end function);
  else
    S := PolynomialRing(Codomain(f), Rank(R) : Global);
    c := Coercion(BaseRing(S), S);
    // yyy 9
    g := hom< R -> S | f * c, [ S.i : i in [1..Rank(R)] ] >;
    g := ImportMap(g, false);
    g := InstallPreimage(g, 
            function(y)
               L1 := Coefficients(y);
               L := [ BaseRing(R) | ];
               for a in L1 do
                  ok, b := HasPreimage(f, a);
                  if not ok then
                     return false, _;
                  end if;
                  Append(~L, b);
               end for;
               M := ChangeUniverse(Monomials(y), R);
               return true, &+ [ L[i] * M[i] : i in [1..#L] ];
            end function);
  end if;	
  return S, g;
end function;
   
   
////////////////////////////////////////////////////////////////////////////   
  
  
MakeExtensionCategory := function(C, S)
   
  has_fixed_base := S cmpne false;
  Cext := MakeGenericCategory();
   
  // fairly generic stuff

  Cext`data`Coercion := function(F, G)   
     ok, map, mess := HasCoercion(Cext)(F, G);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cext`data`HasIdentity := function(F)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": Argument is not object in category";
     end if;
     ok, map, mess := HasCoercion(Cext)(F, F);     
     assert ok;
     map := MakeIdentityPlain(map);
     return true, map, "ok";
  end function;
     
  // special stuff  
    
  if has_fixed_base then  
     Cext`data`SPrintCategory := function()
        return "Extension category of " cat
          SPrintCategory(BaseCategory(Cext)) cat
          " over base object " cat Sprint(S);
     end function;
  else   
     Cext`data`SPrintCategory := function()
        return "Extension category of " cat 
          SPrintCategory(BaseCategory(Cext));     
     end function;
  end if;   
     
  if has_fixed_base then  
     Cext`data`IsObject := function(F)
        // cannot make new objects hence take old
        return IsObject(C)(F) and HasCoercion(C)(S, F);
     end function; 
  else
     Cext`data`IsObject := function(F)
        // cannot make new objects hence take old
        return IsObject(C)(F);
     end function; 
  end if;
  
  Cext`data`AreEqualObjects := function(F, G)
      return AreEqualObjects(C)(F, G);        
  end function;     
     
  Cext`data`AreEqualMorphisms := function(f, g)   
     ok := IsMorphism(Cext)(f) and IsMorphism(Cext)(g) and 
           AreEqualObjects(Cext)(Domain(f), Domain(g)) and
           AreEqualObjects(Cext)(Codomain(f), Codomain(g)) and         
           AreEqualMorphisms(C)(Top(f), Top(g)) and
           AreEqualMorphisms(C)(Bottom(f), Bottom(g));
     return ok;           
  end function;   
     
  if has_fixed_base then   
     Cext`data`BaseObject := function(F)
        if not IsObject(Cext)(F) then
           return ErrorHandler(ErrStat, SPrintCategory(Cext) cat 
             ": Argument is not object in category");
        end if;
        assert IsField(F);
        return S;
     end function;
  else
     Cext`data`BaseObject := function(F)
        if not IsObject(Cext)(F) then
           return ErrorHandler(ErrStat, SPrintCategory(Cext) cat 
             ": Argument is not object in category");
        end if;
        assert IsField(F);
        return BaseField(F);
     end function;
  end if;   
     
  Cext`data`ExtensionMorphism := function(F)
     // this is not a morphism of Cext but of C 
     if not IsObject(Cext)(F) then
        return ErrorHandler(ErrStat, SPrintCategory(Cext) cat 
              ": Argument is not object of category");
     end if;
     assert IsField(F);
     ok, f, mess := HasCoercion(C)(BaseObject(Cext)(F), F);
     assert ok;
     return f;
  end function;
     
  if has_fixed_base then   
     Cmor := MorphismCategory(C, S);   
  else
     Cmor := MorphismCategory(C);
  end if;
     
  // make functor from Cext to Cmor   
     
  CextToCmorObjectMap := function(F)
     if not IsObject(Cext)(F) then
        return ErrorHandler(ErrStat, SPrintCategory(Cext) cat 
              ": Argument is not object of category");
     end if;
     return ExtensionMorphism(Cext)(F);      
  end function;
     
  CextToCmorMorphismMap := function(f)
     if not IsMorphism(Cext)(f) then
        return ErrorHandler(ErrStat, SPrintCategory(Cext) cat 
              ": Argument is not morphism of category");
     end if;
     i := ExtensionMorphism(Cext)(Domain(f));
     j := ExtensionMorphism(Cext)(Codomain(f));
     f_top := Top(f);
     f_bottom := Bottom(f);
     ok, h, mess := HasMorphism(Cmor)(i, j, f_top, f_bottom);
     assert ok;
     return h;
  end function;
     
  CextToCmorObjectMapHasPreimage := function(i)
     if not IsObject(Cmor)(i) then
        return false, false, SPrintCategory(Cmor) cat 
               ": First argument is not object of category";
     end if;
     F := Codomain(i);
     if not AreEqualObjects(C)(Domain(i), BaseObject(Cext)(F)) then
        return false, false, SPrintCategory(C) cat 
 ": Domain of morphism and base object of codomain of morphism are not equal";
     end if;
     ok, ii, mess := HasCoercion(C)(Domain(i), F);
     if not ok then
        return false, false, 
           ": No coercion from domain of morphism to codomain of morphism";
     end if;
     if not AreEqualMorphisms(C)(i, ii) then
        return false, false, ": Coercion and morphism are not equal";
     end if;
     return true, F, "ok";
  end function;
     
  CextToCmorMorphismMapHasPreimage := function(f)
     if not IsMorphism(Cmor)(f) then
        return false, false, SPrintCategory(Cmor) cat 
               ": Argument is not morphism of category";
     end if;
     i := Domain(f);
     j := Codomain(f);
     ok, F, mess := CextToCmorObjectMapHasPreimage(i);
     if not ok then
        return false, false, mess;
     end if;
     ok, G, mess := CextToCmorObjectMapHasPreimage(j);
     if not ok then
        return false, false, mess;
     end if;
     // basically copy Top(f) and change data field ...
     // yyy 10  
     h := GenericMapFromMap(f`static`data`top);      
     delete h`static`data;
     h := ImportMorphism(h, Cext, "morphism");
     h`static`data`top := f`static`data`top;
     h`static`data`bottom := f`static`data`bottom;
     if assigned f`static`data`is_identity then
        if f`static`data`is_identity then
           h := MakeIdentityPlain(h);
           return true, h, "ok";
        end if;
        h`static`data`is_identity := false;
     end if;
     /* this is needed since fmor might have inverseconstr.
        Can't leave it to HasInverse(Cext) since this     
        constructs an new fmor from f without inverseconstr */ 
     inverseconstr := function(h)
        ok, finv, mess := HasInverse(Cmor)(f);
        if ok cmpne "true" then
           return ok, false;
        end if;
        g := GenericMapFromMap(finv`static`data`top);        
        delete g`static`data;
        g := ImportMorphism(g, Cext, "morphism");
        if assigned finv`static`data`is_identity then
           g`static`data`is_identity := finv`static`data`is_identity;
        end if;
        g`static`data`top := finv`static`data`top;
        g`static`data`bottom := finv`static`data`bottom;
        return "true", g, "ok";   
     end function;
     h := InstallInverseConstructor(Cext)(h, inverseconstr);   
     return true, h, "ok";
  end function;
     
  CextToCmor := Functor(Cext, Cmor, 
                        CextToCmorObjectMap, CextToCmorMorphismMap,
                        CextToCmorObjectMapHasPreimage, 
                        CextToCmorMorphismMapHasPreimage );   
  
  Cext`data`HasMorphism := function(F, G, f, g)   
     ObjectMap := ObjectMap(CextToCmor);
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cext)(G) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not object of category";
     end if;
     i := ObjectMap(F);
     j := ObjectMap(G);
     ok, h, mess := HasMorphism(Cmor)(i, j, f, g);
     if not ok then
        return false, false, mess;
     end if;
     ok, hh, mess := MorphismMapHasPreimage(CextToCmor)(h);
     assert ok;
     return true, hh, "ok";
  end function;   
     
  Cext`data`Morphism := function(F, G, f, g)   
     ok, map, mess := HasMorphism(Cext)(F, G, f, g);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cext`data`HasMorphismFromImagesAndBaseMorphism := function(F, G, I, c)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cext)(G) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not object of category";
     end if;
     if not IsFieldCategory(C) then
        return false, false, SPrintCategory(Cext) cat 
               ": Base category must be field category";
     end if;
     if not IsMorphism(C)(c) then
        return false, false, SPrintCategory(Cext) cat 
               ": Fourth argument is not morphism of base category";
     end if;
     if not AreEqualObjects(C)(BaseObject(Cext)(F), Domain(c)) then
        return false, false, SPrintCategory(Cext) cat 
 ": Domain of fourth argument is not equal to base object of first argument";
     end if;
     if not AreEqualObjects(C)(BaseObject(Cext)(G), Codomain(c)) then
        return false, false, SPrintCategory(Cext) cat 
": Codomain of fourth argument is not equal to base object of second argument";
     end if;
     if not AreEqualObjects(C)(G, Universe(I)) then 
        return false, false, SPrintCategory(Cext) cat 
               ": Universe of third argument is not equal to second argument";
     end if;
     i := ExtensionMorphism(Cext)(F);        
     j := ExtensionMorphism(Cext)(G);        
     ok, f, mess := HasExtension(C)(c, i, j, I);   
     if not ok then
        return false, false, mess;
     end if;
     ok, ff, mess := HasMorphism(Cext)(F, G, f, c);
     assert ok;
     return true, ff, "ok";
  end function;   
     
  Cext`data`MorphismFromImagesAndBaseMorphism := function(F, G, I, c)   
     ok, map, mess := HasMorphismFromImagesAndBaseMorphism(Cext)(F, G, I, c);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cext`data`HasMorphismFromImages := function(F, G, I)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cext)(G) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not object of category";
     end if;
     if not IsFieldCategory(C) then
        return false, false, SPrintCategory(Cext) cat 
               ": Base category must be field category";
     end if;
     ok, c, mess := HasCoercion(C)(BaseObject(Cext)(F), BaseObject(Cext)(G));
     if not ok then
        return false, false, mess;
     end if;
     return HasMorphismFromImagesAndBaseMorphism(Cext)(F, G, I, c);
  end function;   
     
  Cext`data`MorphismFromImages := function(F, G, I)   
     ok, map, mess := HasMorphismFromImages(Cext)(F, G, I);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;   
     return map;   
  end function;   
     
  Cext`data`HasCoercion := function(F, G)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cext)(G) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not object of category";
     end if;
     i := ObjectMap(CextToCmor)(F);
     j := ObjectMap(CextToCmor)(G);
     ok, f, mess := HasCoercion(Cmor)(i, j);
     if not ok then
        return false, false, mess;
     end if;
     ok, ff, mess := MorphismMapHasPreimage(CextToCmor)(f);
     assert ok;
     return true, ff, "ok";
  end function;   
     
  Cext`data`HasComposition := function(f, g)   
     if not IsMorphism(Cext)(f) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(Cext)(g) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not morphism of category";
     end if;
     ff := MorphismMap(CextToCmor)(f);
     gg := MorphismMap(CextToCmor)(g);
     ok, hh, mess := HasComposition(Cmor)(ff, gg);
     if not ok then
        return false, false, mess;
     end if;
     ok, h, mess := MorphismMapHasPreimage(CextToCmor)(hh);
     assert ok;
     return true, h, "ok";
  end function;   
     
  Cext`data`Degree := function(f)
     if not IsMorphism(Cext)(f) then
        return "false", false, SPrintCategory(Cext) cat 
          ": Argument is not morphism of category";
     end if;
     return Degree(C)(Top(f));
  end function;
     
  // redefine generic inverse  
  // we have been lazy and need now to define f`static`data`inverse() 
  HasInverseCext := HasInverse(Cext);  
  Cext`data`HasInverse := function(f)
     if not IsMorphism(Cext)(f) then
        return "false", false, SPrintCategory(Cext) cat 
          ": Argument is not morphism of category";
     end if;
     if assigned f`static`data`inverseexists then
         return HasInverseCext(f);
     end if;
     if not assigned f`static`data`inverseconstr then
        inverseconstr := function(f)
           ff := MorphismMap(CextToCmor)(f);
           ok, gg, mess := HasInverse(Cmor)(ff);
           if ok cmpne "true" then
              return ok, false, mess;
           end if;
           ok, g, mess := MorphismMapHasPreimage(CextToCmor)(gg);
           assert ok;
           return "true", g, "ok";
        end function;   
        f := InstallInverseConstructor(Cext)(f, inverseconstr);      
     end if;
     // now proceed with generic method
     return HasInverseCext(f);  
  end function;
     
  // redefine generic version
  Cext`data`SpecifyInverseMorphisms := function(f, g)   
     if not IsMorphism(Cext)(f) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(Cext)(g) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not morphism of category";
     end if;
     ff := MorphismMap(CextToCmor)(f);
     gg := MorphismMap(CextToCmor)(g);
     ff, gg := SpecifyInverseMorphisms(Cmor)(ff, gg);
     ok, f, mess := MorphismMapHasPreimage(CextToCmor)(ff);
     assert ok;
     ok, g, mess := HasInverse(Cext)(f);
     assert ok cmpeq "true";
     return f, g;
  end function;
      
  Cext`data`IsIsomorphism := function(f)
     if not IsMorphism(Cext)(f) then
        return "false", false, SPrintCategory(Cext) cat 
          ": Argument is not morphism of category";
     end if;
     h := MorphismMap(CextToCmor)(f);
     return IsIsomorphism(Cmor)(h);
  end function;
     
  Cext`data`SupportsExtension := function(i)
     if not IsMorphism(Cext)(i) then
        return false, false, false, false, false, false, false,
               SPrintCategory(Cext) cat 
               ": Argument is not morphism of category";
     end if;
     ok, ii, mess := MorphismMap(CextToCmor)(i);
     if not ok then
        return false, false, false, false, false, false, false, mess;
     end if;
     ok, L_top, polys_top, gens_top, 
       L_bottom, polys_bottom, gens_bottom, mess := 
       SupportsExtension(Cmor)(ii);
     return ok, L_top, polys_top, gens_top, 
                L_bottom, polys_bottom, gens_bottom, mess;
  end function;
     
  Cext`data`HasExtension := function(c, i, j, I_top, I_bottom)
  //
  //  This is actually a (commutative) cube.   
  //  
    if not IsMorphism(Cext)(c) then
     return false, false, false, SPrintCategory(Cext) cat 
            ": First argument is not a morphism of category";
    end if;
    if not IsMorphism(Cext)(i) then
     return false, false, false, SPrintCategory(Cext) cat 
            ": Second argument is not a morphism of category";
    end if;
    if not IsMorphism(Cext)(j) then
     return false, false, false, SPrintCategory(Cext) cat 
            ": Third argument is not a morphism of category";
    end if;
    cc := MorphismMap(CextToCmor)(c);
    ii := MorphismMap(CextToCmor)(i);
    jj := MorphismMap(CextToCmor)(j);
    ok, ff, mess := HasExtension(Cmor)(cc, ii, jj, I_top, I_bottom);
    if not ok then
       return false, false, mess;
    end if;
    ok, f, mess := MorphismMapHasPreimage(CextToCmor)(ff);
    assert ok;
    return true, f, "ok";
  end function;
     
  Cext`data`HasRightCancellation := function(f, g)   
     if not IsMorphism(Cext)(f) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(Cext)(g) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not morphism of category";
     end if;
     if not AreEqualObjects(Cext)(Codomain(f), Codomain(g)) then
        return false, false, SPrintCategory(Cext) cat 
   ": Codomain of first argument is not equal to codomain of second argument";
     end if;
     ff := MorphismMap(CextToCmor)(f);
     gg := MorphismMap(CextToCmor)(g);
     ok, hh, mess := HasRightCancellation(Cmor)(ff, gg);
     if not ok then
        return false, false, mess;
     end if;
     ok, h, mess := MorphismMapHasPreimage(CextToCmor)(hh);
     assert ok;
     return true, h, "ok";     
  end function;
     
  // some special functions when base category is field category   
  MakeBaseExtension := function(F, c)
  // we need to "recreate" F ... so we do this recursively. 
  // ( Otherwise we could use SupportsExtension just in one step. )
    if AreEqualObjects(C)(F, Domain(c)) then
       return true, Codomain(c), c, "ok";
    end if;
    if IsIdentity(C)(c) then
       return true, F, Identity(C)(F), "ok";
    end if;
    ok, G, d, mess := $$(BaseField(F), c);
    if not ok then
       return false, false, false, mess;
    end if;
    i := Coercion(C)(BaseField(F), F);
    ok, A, _, L := SupportsExtension(C)(i); 
    assert ok;
    R := Universe(A);      
    S, cc := BaseExtensionSpecial(R, d);  
    AA := [ S | cc(x) : x in A ];
    ok, F1, mess := FieldExtensionFromAffineEquations(AA, F);
    if not ok then
       return false, false, false, ": Base extension does not exist";
    end if;
    j := Coercion(C)(BaseField(F1), F1);
    ok, _, polys1, L1 := SupportsExtension(C)(j);
    assert ok;
    ok, f := HasExtension(C)(d, i, j, L1);
    assert ok;
    // install some data in f
    if assigned d`static`data`degree then
       f`static`data`degree := d`static`data`degree;
    end if;
    R := Universe(A);
    map := hom< R -> F | L >;
    f := InstallPreimage(f, 
            function(y)
               ynum, yden := polys1(y);
               ok, xnum := HasPreimage(cc, ynum);
               if not ok then
                  return false, _;
               end if;
               ok, xden := HasPreimage(cc, yden);
               if not ok then
                  return false, _;
               end if;
               return true, map(xnum) / map(xden);
            end function);
     return true, F1, f, "ok";
  end function;
       
  Cext`data`HasBaseExtension := function(F, c)   
     if not IsObject(Cext)(F) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsMorphism(C)(c) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Second argument is not morphism of base category";
     end if;
     if not IsFieldCategory(C) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Base category must be field category";
     end if;
     if not AreEqualObjects(C)(BaseObject(Cext)(F), Domain(c)) then
        return false, false, false, SPrintCategory(Cext) cat 
  ": Base object of first argument must be equal to domain of second argument";
     end if;
     ok, F1, f, mess := MakeBaseExtension(F, c);
     if not ok then
        return false, false, false, SPrintCategory(Cext) cat mess;
     end if;
     ff := Morphism(Cext)(F, F1, f, c);
     return true, F1, ff, "ok";
  end function;   
     
  Cext`data`BaseExtension := function(F, c)
     ok, F1, map, mess := HasBaseExtension(Cext)(F, c);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return F1, map;
  end function;
     
  MakeBaseExtensionMorphisms := function(F, G, f, i, j, c)
     ok, Fb, ib, mess := HasBaseExtension(Cext)(F, i);
     if not ok then
        return false, false, false, mess;
     end if;
     ok, Gb, jb, mess := HasBaseExtension(Cext)(G, j);
     if not ok then
        return false, false, false, mess;
     end if;
     // find image of gens upstairs via downstairs
     ok, _, _, L := SupportsExtension(C)(ExtensionMorphism(Cext)(F));
     assert ok;
     M := [ G | Image(f, z) : z in L ];
     Mb := [ Gb | Image(jb, z) : z in M ];
     // check
     Lb := [ Fb | Image(ib, z) : z in L ];
     ok, _, _, Lbp := SupportsExtension(C)(ExtensionMorphism(Cext)(Fb));
     assert ok;
     assert Lbp eq Lb;
     // ok go on
     ok, fb, mess := HasMorphismFromImagesAndBaseMorphism(Cext)(Fb, Gb, Mb, c);
     assert ok;  
     // fill in info
     if assigned f`static`data`top`static`data`degree then
        fb`static`data`top`static`data`degree := 
               f`static`data`top`static`data`degree;
     end if;
     if assigned f`static`data`is_identity and f`static`data`is_identity and
        assigned c`static`data`is_identity and c`static`data`is_identity then
        fb := MakeIdentityPlain(fb);
     end if;
     return true, fb, ib, jb, "ok";
  end function;
     
  Cext`data`HasBaseExtensionMorphisms := function(f, i, j, c)   
  //   
  //  Base ext of domain(f) via i and codomain(f) via j  
  //  then base ext f correspondingly using c which
  //  connects codomain(i) and codomain(j).
  //  returns base ext fb of f and morphism morphism f -> fb
  //  
    if not IsMorphism(Cext)(f) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": First argument is not morphism of category";
     end if;
     if not IsMorphism(C)(i) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Second argument is not morphism of base category";
     end if;
     if not IsMorphism(C)(j) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Third argument is not morphism of base category";
     end if;
     if not IsMorphism(C)(c) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Fourth argument is not morphism of base category";
     end if;
     if not IsFieldCategory(C) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Base category must be field category";
     end if;
     F := Domain(f);
     G := Codomain(f);
     if not AreEqualObjects(C)(BaseObject(Cext)(F), Domain(i)) then
        return false, false, false, SPrintCategory(Cext) cat 
  ": Base object of domain of first argument must be equal to domain of second argument";
     end if;
     if not AreEqualObjects(C)(BaseObject(Cext)(G), Domain(j)) then
        return false, false, false, SPrintCategory(Cext) cat 
  ": Base object of codomain of first argument must be equal to domain of third argument";
     end if;
     if not AreEqualObjects(C)(Domain(c), Codomain(i)) then
        return false, false, false, SPrintCategory(Cext) cat 
  ": Domain of fourth argument must be equal to codomain of second argument";
     end if;
     if not AreEqualObjects(C)(Codomain(c), Codomain(j)) then
        return false, false, false, SPrintCategory(Cext) cat 
  ": Codomain of fourth argument must be equal to codomain of third argument";
     end if;
     if not AreEqualMorphisms(C)(Composition(C)(i, c), 
                                 Composition(C)(Bottom(f), j)) then
        return false, false, false, SPrintCategory(Cext) cat 
               ": Base morphisms do not commute";
     end if;
     ok, fb, ib, jb, mess := MakeBaseExtensionMorphisms(F, G, f, i, j, c);
     if not ok then
        return false, false, false, SPrintCategory(Cext) cat mess;
     end if;
     f_invble := ( assigned f`static`data`inverseexists and 
                            f`static`data`inverseexists eq "true" ) or
                   assigned f`static`data`inverseconstr;
     c_invble := ( assigned c`static`data`inverseexists and 
                            c`static`data`inverseexists eq "true" ) or
                   assigned c`static`data`inverseconstr;
     if f_invble and c_invble then
        preimageconstr := function(static)
           ok, g := HasInverse(Cext)(f);
           if ok cmpne "true" then
              static`data`tmp1 := ok;
              static`data`tmp2 := false;
              return false, false;
           end if;
           ok, d := HasInverse(C)(c);
           if ok cmpne "true" then
              static`data`tmp1 := ok;
              static`data`tmp2 := false;
              return false, false;
           end if;
           ok, gb, _, _, mess := MakeBaseExtensionMorphisms(G, F, g, j, i, d);
           assert ok;
           // side store inverse info
           static`data`tmp1 := "true";
           static`data`tmp2 := gb;
           image := ImageFunction(gb);           
           return true, image;           
        end function;
        inverseconstr := function(fb)       
           if not assigned fb`static`data`tmp1 then   
               ok, preim := HasPreimageFunction(fb);   
           end if;
           ok := fb`static`data`tmp1;
           gb := fb`static`data`tmp2;
           delete fb`static`data`tmp1;
           delete fb`static`data`tmp2;
           return ok, gb;
        end function;             
        // this replaces the generic preimageconstr
        delete fb`static`preimage;   
        delete fb`static`preimageconstr;   
        fb := InstallPreimageConstructor(fb, preimageconstr);
        // this replaces the generic inverseconstr
        delete fb`static`data`inverseconstr;
        fb := InstallInverseConstructor(Cext)(fb, inverseconstr);
     end if;
     return true, fb, ib, jb, "ok";
  end function;   
    
  Cext`data`BaseExtensionMorphisms := function(f, i, j, c)
     ok, fb, ext, mess := HasBaseExtensionMorphisms(Cext)(f, i, j, c);
     if not ok then
        return ErrorHandler(ErrStat, mess);
     end if;
     return fb, ext;
  end function;
     
  Cext`data`HasIsomorphisms := function(F, G, s)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": Second argument is not object of category";
     end if;
     i := ObjectMap(CextToCmor)(F);
     j := ObjectMap(CextToCmor)(G);
     ok, L, mess := HasIsomorphisms(Cmor)(i, j, s);
     if ok cmpne "true" then
        return ok, false, mess;
     end if;
     S := [];
     for f in L do
        ok, ff, mess := MorphismMapHasPreimage(CextToCmor)(f);
        assert ok;
        Append(~S, ff);
     end for;
     return "true", S, "ok";
  end function;
     
  Cext`data`IsIsomorphic := function(F, G)
     if not IsObject(Cext)(F) then
        return "unknown", false, SPrintCategory(Cext) cat
               ": First argument is not object of category";     
     end if;
     if not IsObject(Cext)(G) then
        return "unknown", false, SPrintCategory(Cext) cat
               ": Second argument is not object of category";     
     end if;
     ok, L, mess := HasIsomorphisms(Cext)(F, G, 1);
     if ok cmpne "true" then
        return ok, false, mess;
     end if;
     return "true", L[1], mess;
  end function;
     
  Cext`data`HasAutomorphisms := function(F, s)   
     if not IsObject(Cext)(F) then
        return false, false, SPrintCategory(Cext) cat 
               ": First argument is not object of category";
     end if;
     return HasIsomorphisms(Cext)(F, F, s);
  end function;
     
  Cext`data`Isomorphisms := function(F, G, s)
     ok, map, mess := HasIsomorphisms(Cext)(F, G, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  Cext`data`Automorphisms := function(F, s)
     ok, map, mess := HasAutomorphisms(Cext)(F, s);
     if ok cmpne "true" then
        return ErrorHandler(ErrStat, mess);
     end if;
     return map;
  end function;
     
  return Cext, CextToCmor;   
     
end function;
  
   
intrinsic ExtensionCategory( C::SetFormal : Global := true) -> SetFormal
{Create extension category of given category C} 
  
  require IsFieldCategory(C) :
    "Argument must be field category";
  /*
  require IsCategory(C) :
    "Argument must be a category";
  */
  
  if Global and assigned C`data`extcategory then
     return C`data`extcategory;
  end if;
  
  Cext, CextToCmor := MakeExtensionCategory(C, false);
  Cext`data`type := "ExtensionCategory";
  Cext`data`CextToCmor := CextToCmor;
  
  Cext`data`basecategory := C;
  
  if Global then
     // mem loop
     C`data`extcategory := Cext;  
  end if;     
  
  return Cext;   
  
end intrinsic;  

  
intrinsic ExtensionCategory( C::SetFormal, S::Any : Global := true) 
                             -> SetFormal
{Create extension category of given category C ove base object S} 
  
  require IsFieldCategory(C) :
    "First argument must be field category";
  /*
  require IsCategory(C) :
    "First argument must be a category";
  */
  require IsObject(C)(S) :
    "Second argument must be object of category";
  
  if Global then
     if assigned C`data`extcategoryoverbase then
        AreEqualObjectsC := AreEqualObjects(C);
        for Cext in C`data`extcategoryoverbase do
           _, T := BaseCategory(Cext);
           if AreEqualObjectsC(T, S) then
              return Cext;
           end if;
        end for;
     else
        C`data`extcategoryoverbase := [ PowerStructure(SetFormal) | ];
     end if;
  end if;
  
  Cext, CextToCmor := MakeExtensionCategory(C, S);
  Cext`data`type := "ExtensionCategory";
  Cext`data`CextToCmor := CextToCmor;
  
  Cext`data`basecategory := C;
  Cext`data`baseobject := S;
  if Global then
     // mem loop
     Append(~C`data`extcategoryoverbase, Cext);
  end if;
     
  return Cext;  
  
end intrinsic;  



/////////////////////////////////////////////////////////////////////////////
//  
//  Sub category
//  
  
//  Problem: No way of storing an embedding morphisms with an object
//  (different embeddings for the same object),
//  Hence not done yet.
//  Implementation via morphism category like extension category  
  
  

  
/////////////////////////////////////////////////////////////////////////////
//  
//  Function field category (of FldFun)
//  
  

forward CheckIsoInputOverBase;
forward CheckAutoInputOverBase;
forward MakeIsomorphismsOverBase;
forward MakeIsomorphisms;
forward MakeAutomorphismsOverBase;
forward MakeAutomorphisms;

  
MakeFunctionFieldCategory := function(Cext, S)
   
   has_fixed_base := S cmpne false;
   C := FieldCategory();
   Cext, CextToCmor := MakeExtensionCategory(C, S);
   
   Cext`data`basecategory := C;
   if has_fixed_base then
      Cext`data`baseobject := S;
   end if;
   
   Cext`data`SPrintCategory := function()
      return "Function field category";
   end function;
     
   if has_fixed_base then
      Cext`data`IsObject := function(F)
         if Type(F) eq FldFunRat then
            return Rank(F) eq 1 and BaseRing(F) eq S;
         end if;
         return Type(F) eq FldFun and ConstantField(F) eq S;
      end function;
   else
      Cext`data`IsObject := function(F)
         if Type(F) eq FldFunRat then
            return Rank(F) eq 1;
         end if;
         return Type(F) eq FldFun;
      end function;
   end if;
         
   Cext`data`BaseObject := function(F)
      if not IsObject(Cext)(F) then
         return ErrorHandler(ErrStat, SPrintCategory(Cext) cat
           ": Argument is not object in category");
      end if;
      return ConstantField(F);
   end function;
      
   Cext`data`HasIsomorphismsOverBase := function(F, G, c, s)   
      ok, mess := CheckIsoInputOverBase(F, G, c, C, Cext);
      if not ok then
         return ErrorHandler(ErrStat, mess);
      end if;
      return MakeIsomorphismsOverBase(F, G, c, s, "None");   
   end function;   
      
   Cext`data`HasAutomorphismsOverBase := function(F, c, s)   
      ok, mess := CheckAutoInputOverBase(F, c, C, Cext);
      if not ok then
         return ErrorHandler(ErrStat, mess);
      end if;
      return MakeAutomorphismsOverBase(F, c, s, "None");   
   end function;   
      
   // redefinition of generic methods
   // based on field iso (breaks infinite recursion)
      
   Cext`data`HasIsomorphisms := function(F, G, s)   
      if not IsObject(Cext)(F) then
         return ErrorHandler(ErrStat, SPrintCategory(Cext) cat
           ": First argument is not object in category");
      end if;
      if not IsObject(Cext)(G) then
         return ErrorHandler(ErrStat, SPrintCategory(Cext) cat
           ": Second argument is not object in category");
      end if;
      return MakeIsomorphisms(F, G, s, "None");   
   end function;   
      
   Cext`data`HasAutomorphisms := function(F, s)   
      if not IsObject(Cext)(F) then
         return ErrorHandler(ErrStat, SPrintCategory(Cext) cat
           ": First argument is not object in category");
      end if;
      return MakeAutomorphisms(F, s, "None");   
   end function;   
      
   return Cext, CextToCmor; 
   
end function;
   
   
intrinsic FunctionFieldCategory() -> SetFormal  
  {}
  
  Z := Integers();
  if assigned Z`FunctionFieldCategory then
     return Z`FunctionFieldCategory;
  end if;
  
  C := FieldCategory();
  Cext, CextToCmor := MakeFunctionFieldCategory(C, false);
  Cext`data`type := "FunctionFieldCategory";
  Cext`data`CextToCmor := CextToCmor;
     
  Z`FunctionFieldCategory := Cext;
  return Cext;
  
end intrinsic;


intrinsic FunctionFieldCategory(k::Fld) -> SetFormal  
  {}
  
  if assigned k`FunctionFieldCategory then
     return k`FunctionFieldCategory;
  end if;
  
  Cext, CextToCmor := MakeFunctionFieldCategory(FieldCategory(), k);
  Cext`data`type := "FunctionFieldCategory";
  Cext`data`CextToCmor := CextToCmor;
     
  k`FunctionFieldCategory := Cext;
  return Cext;
  
end intrinsic;


/////////////////////////////////////////////////////////////////////////////
// 
//  Function field category. 
//    Some induced operations on other structures  
//    Various others are still missing, like Norm().
//  
  
intrinsic Conorm(f::Map, P::PlcFunElt) -> DivFunElt
{Return conorm of P under f};
   C := FunctionFieldCategory();
   require IsMorphism(C)(f) : "Map must be function field morphism";
   require Domain(f) cmpeq FunctionField(P) or 
     IsSameRationalFunctionField(Domain(f), FunctionField(P))
     : "Place is not in the domain";  
   require IsFinite(Degree(C)(f)) : "Map must have finite degree";
   a, b := TwoGenerators(P);
   c := Image(f, a);
   d := Image(f, b);
   // this can be very inefficient ...
   return GCD( Numerator(Divisor(c)), Numerator(Divisor(d)) );
end intrinsic;


intrinsic Conorm(f::Map, D::DivFunElt) -> DivFunElt
{Return conorm of D under f};
   C := FunctionFieldCategory();
   require IsMorphism(C)(f) : "Map must be function field morphism";
   require Domain(f) cmpeq FunctionField(D) or
     IsSameRationalFunctionField(Domain(f), FunctionField(D))
    : "Divisor is not in the domain";  
   require IsFinite(Degree(C)(f)) : "Map must have finite degree";
   S, e := Support(D);
   S := [ Conorm(f, P) : P in S ];
   return &+ [ e[i]*S[i] : i in [1..#S] ];
end intrinsic;


intrinsic Cotrace(f::Map, D::DiffFunElt) -> DiffFunElt
{Return cotrace of D under f};
   C := FunctionFieldCategory();
   require IsMorphism(C)(f) : "Map must be function field morphism";
   require Domain(f) cmpeq FunctionField(D) or 
     IsSameRationalFunctionField(Domain(f), FunctionField(D))
     : "Differential is not in the domain";  
   require IsFinite(Degree(C)(f)) : "Map must have finite degree";
   x := SeparatingElement(Domain(f));
   a := D/Differential(x);
   return f(a) * Differential(f(x));
end intrinsic;


intrinsic Operation(f::Map, x::Any) -> Any
{Return result of operation of automorphism f on object x};
   C := FunctionFieldCategory();
   require IsMorphism(C)(f) : "Map must be function field morphism";
   require IsAutomorphism(C)(f) eq "true" 
     : "Function field morphism must be automorphism";
   if ISA(Type(x), FldFunGElt) then
      return Image(f, x);
   end if;
   if Type(x) cmpeq PlcFunElt then
      // this is not factorisation free and hence very slow.
      //   should be improved when used for perm rep of auts ... 
      y := Conorm(f, x);
      L := Support(y);
      assert #L eq 1;
      return L[1];  
   end if;
   if Type(x) cmpeq DivFunElt then
      return Conorm(f, x);
   end if;
   if Type(x) cmpeq DiffFunElt then
      return Cotrace(f, x);
   end if;
   require false : "No operation on given type of elements";   
end intrinsic;

     
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/*
    3. Automorphisms and isomorphisms functions.

      Mar 2004: Rewrite and extension of earlier versions.  
      Jun 2004: Incorporate orig stuff (coprime situation) 
      Oct 2004: And again
      Mar 2005: And again

    Algorithm is based on ANTS VI paper.

*/  
     

declare verbose Aut1, 3;  // internals                                   
declare verbose Aut2, 1;  // place selection etc.              


/////////////////////////////////////////////////////////////////////////////
//
//

  
//intrinsic EchelonBasis(V::SeqEnum, P::PlcFunElt, f::UserProgram) -> SeqEnum
//{}  
EchelonBasis := function(V, P, f)
  val := [ Valuation(v, P) : v in V ];
   j0 := Minimum(val);
   r := 0;
   Sort(~val, ~s);
   V := [ V[i^s] : i in [1..#V] ];
   repeat                
     r := r + #V; 
     // compute series expansions             
     B := [ f(V[i], r - j0 - val[i]) : i in [1..#V] ];
     vprint Aut1 : "Basis input: ";
     vprint Aut1 : B;
     M := Matrix([ [ Coefficient(b, j) : j in [j0..j0+r-1] ] : b in B ]); 
     //print "Matrix input";
     //print M;
     M, T := EchelonForm(M);
     //print "Matrix output";
     //print M;
     vprint Aut1 : "Basis output:";
     vprint Aut1 : [ &+ [ T[i][j]*B[j] : j in [1..#B] ] : i in [1..#B] ];
   until Rank(M) eq #V; 
   W := Reverse( [ &+ [ T[i][j]*V[j] : j in [1..#V] ] : i in [1..#V] ] );
   return W;
end function;     
//end intrinsic;
  

EchelonBasisWithPrecision := function(V, P, f, prec)
//   
//  Uses absolute precision O(t^prec) for echelon basis 
//   
   val := [ Valuation(v, P) : v in V ];
   j0 := Minimum(val);
   r := -j0 + prec;
   Sort(~val, ~s);
   V := [ V[i^s] : i in [1..#V] ];
   // compute series expansions             
   B := [ f(V[i], r + j0 - val[i]) : i in [1..#V] ];
   vprint Aut1 : "Basis input: ";
   vprint Aut1 : B;
   M := Matrix([ [ Coefficient(b, j) : j in [j0..j0+r-1] ] : b in B ]); 
   //print "Matrix input";
   //print M;
   M, T := EchelonForm(M);
   //print "Matrix output";
   //print M;
   vprint Aut1 : "Basis output:";
   vprint Aut1 : [ &+ [ T[i][j]*B[j] : j in [1..#B] ] : i in [1..#B] ];
   if Rank(M) ne #V then
      // wrong prec has been chosen or V not linearly independent        
      return ErrorHandler(ErrStat, "Rank of matrix is too low");        
   end if;
   W := Reverse( [ &+ [ T[i][j]*V[j] : j in [1..#V] ] : i in [1..#V] ] );
   return W;
end function;     


/////////////////////////////////////////////////////////////////////////////
//  
//  Fairly unique special models. 
//


special_model_fmt := recformat<
            P,      // place of degree one         
            n,      // special model degrees,
            x,      // corresponding function field elements
            b,      // basis = [ 1 ] cat [ x[2], ..., x[n1] ] 
            m,      // degrees of b = [ 0 ] cat [ n[2], ..., n[n1] ]  
            maxdeg, // maxdeg = n[n1]         
            R,      // polynomial ring in the x.                
//            Rrev,   // polynomial ring in the reversed x.                
//            rev,    // R -> Rrev reversing the coeffs        
    relations,      // the quadratic relations (mult table) in R
          ind,       // corresponding indices for t_i * t_j + ...           
//            I,      // ideal in Rrev of relations, 
//                    // variables in relations reversed         
//            A,      // Rrev / I         
//            f       // R -> A  
            nums,   // generator numerators represented in the model      
            dens    // generator denominators represented in the model
>;
   
   
MakeEmptyModel := function(P)   
   assert Degree(P) eq 1;
   assert IsGlobal(FunctionField(P)) or Genus(FunctionField(P)) ge 1;
   assert DimensionOfExactConstantField(FunctionField(P)) eq 1;
   M := rec<special_model_fmt | P := P >; 
   return M;
end function;
   
   
/*   
ReversingHom := function(R, Rrev)
  rev := hom< R -> Rrev | 
              x :-> Evaluate(x, Reverse([R.i : i in [1..Rank(R)]])), 
              y :-> Evaluate(y, Reverse([Rrev.i : i in [1..Rank(Rrev)]])) >;
  return rev;
end function;
*/   
   

ReverseVariables := function(I)
// 
//  Reverse the order of the variables in I 
//
  R := Parent(I.1);
  f := hom< R -> R | Reverse([R.i : i in [1..Rank(R)]]) >;
  J := ideal< R | f(Generators(I))>;
  return J;
end function;
     
   
   
ComputeGenerators := procedure(~M, only_orders)
//   
//  Compute n, m and some x, b in M.   
//   
//                       
   P := M`P;                    
   n1 := 0;
   repeat
      n1 := n1 + 1;
      E := n1 * P; 
   until Dimension(E) eq 2;
   n := [ n1 ];
   if not only_orders then
     x1 := Representative( [ z : z in Basis(E) | Valuation(z, P) eq -n1 ] );
     x := [ x1 ];
   end if;
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
      if not only_orders then
         x[i] := Representative( [ z : z in Basis(E) | 
                                   Valuation(z, P) eq -nn ] );
      end if;        
   end while;
   M`n := n;
   M`m := [ 0 ] cat [ n[i] : i in [2..n1] ];   
   if not only_orders then   
      M`x := x;
      M`b := [ 1 ] cat [ x[i] : i in [2..n1] ]; 
   end if;
   M`maxdeg := n[n1];
   M`R := PolynomialRing(ConstantField(FunctionField(P)), n1 : Global := true);
//   M`Rrev := PolynomialRing(ConstantField(FunctionField(P)), n1, "elim", n1-1);
//   // for Magma better reversed, for me forward.
//   M`rev := ReversingHom(M`R, M`Rrev);  
     
end procedure;
   


ComputeUniqueGenerators := procedure(~M, Q, expansion)
//                       
   ComputeGenerators(~M, true);
   B := Basis(M`maxdeg * M`P);  
   B := EchelonBasisWithPrecision(B, Q, expansion, 1);
   x := [ z : z in B | -Valuation(z, M`P) in M`n ];
   b := [ 1 ] cat [ x[i] : i in [ 2..M`n[1] ] ]; 
   M`x := x;
   M`b := b;
end procedure;
   


DegreeSpecial := function(x, M)
//   
//  The degree of x (multivariate polynomial) wrt M (also M`x und infty)
//
  assert assigned M`x;
  assert assigned M`n;
  assert assigned M`R;
//  assert assigned M`Rrev;
//  assert Parent(x) cmpeq M`R or Parent(x) cmpeq M`Rrev;
  assert Parent(x) cmpeq M`R;

  d := Parent(x) cmpeq M`R select M`n else Reverse(M`n);
  r := #d; 
  L := Monomials(x);
  deg := Maximum( [ &+ [ d[i] * Degree(z, i) : i in [1..r] ] : z in L ] );
  return deg;

end function;



BasisInDegree := function (M, d)
//   
//  Return a k-basis in degree d wrt to P in terms of x.
//   (order matters!)
//
  assert assigned M`x;
  assert assigned M`n;
  assert assigned M`R;
  
  n := M`n;
  n1 := n[1];         
  R := M`R;
  B := [ (R.1)^j : j in [0..d] | j * n1 le d ] cat
       [  (R.1)^j * R.i : j in [0..d], i in [2..n1] | j * n1 + n[i] le d ];
  cmp := function(a, b)
     return DegreeSpecial(a, M) - DegreeSpecial(b, M);
  end function;
  Sort(~B, cmp);   
  return B;
  
end function;


// Degree estimation for f,g is linear in genus and degree of a!
//   (see little note).


RepresentInGenerators := function(a, M)
//
//  Represent a in M: a = f(x) / g(x) multivariate polynomials. 
//
  assert assigned M`x;
  assert assigned M`n;
  assert assigned M`R;
  
  P := M`P;
  x := M`x;
  n := M`n;
  k := ConstantField(FunctionField(P));
 
  /* special case for a = 0 added mch 02/08 - actually called with
     a=0 when F is the AlFF of a line in the projective plane     */
  if a eq Parent(a)!0 then
    return (M`R)!0, (M`R)!1;
  end if;
  d := -Valuation(a, P);
  e := Maximum( 0, -d) - 1;
  repeat
     e := e + 1;
     Bnum := BasisInDegree(M, d+e);  
     Bden := BasisInDegree(M, e);  
     L := [ Evaluate(b, x) * a : b in Bden ] cat 
          [ -Evaluate(b, x) : b in Bnum ];
     V := Relations(L, k);
  until Rank(V) gt 0;
  v := V.1;
  i0 := #Bden;
  den := &+ [ v[i] * Bden[i] : i in [1..i0] ];
  num := &+ [ v[i + i0] * Bnum[i] : i in [1..#Bnum] ];
  const, c := IsCoercible(k, den);
  if const then 
     num := num / c;
     den := Parent(den)!1;
  end if;
  assert a eq Evaluate(num, x) / Evaluate(den, x);               
  return num, den;
  
end function;

   
   
ComputeGeneratorRelations := procedure(~M)
//
// Compute model of M in x.
//   This is a list of generators of the affine ideal.
//   The order of the generators matters!
//     (slightly different more special original variant -- faster?)        
//                       
  assert assigned M`x;
  assert assigned M`n;
  assert assigned M`R;
                       
  x := M`x;
  n := M`n;
  n1 := n[1];
  R := M`R;
  
  L := [ R | ];                     
  ind := [ Parent( [ Integers() | ] ) | ];
  for i,j in [2..n1] do
     num, den := RepresentInGenerators( x[i] * x[j], M );
     assert IsOne(den);
     Append(~L, R.i * R.j - num);
     Append(~ind, [i, j]);   
  end for;
  M`relations := L;
  M`ind := ind;
  
  /*
  Rrev := M`Rrev;
  rev := M`rev;
  I := ideal< Rrev | rev(L) >;
  A, f := quo< Rrev | I >;
  M`I := I;
  M`A := A;
  M`f := f;
  */
  
end procedure;


ComputeSpecialModel := function(P, f)
   F := FunctionField(P);
   M := MakeEmptyModel(P);
   ComputeUniqueGenerators(~M, P, f);
   ComputeGeneratorRelations(~M);
   return M;
end function;



////////////////////////////////////////////////////////////////////////////
//
//  Model comparison
//  
  
  
/*
  
special_model_pair_fmt := recformat<
          F1,  F2,    // function fields                 
          M1,  M2,    // special models
          T,          // transformation matrix                
          maps        // the possible maps                          
>;
   
MakeEmptyModelPair := function(M1, M2)   
   F1 := FunctionField(M1`P);
   F2 := FunctionField(M2`P);
   assert Genus(F1) eq Genus(F2);
   assert assigned M1`n and assigned M2`n;
   assert M1`n eq M2`n;
   MP := rec<special_model_pair_fmt | 
         F1 := F1, F2 := F2, M1 := M1, M2 := M2>;
   return MP;
end function;
   
*/
   
HasLinearShape := function(x)   
//
// Check whether polynomial has linear shape (linear in x_1, ..., x_(n-1),
//  and x_n doesn't matter)
//  
  n := Rank(Parent(x));
  ok := &and [ &+ [ Degree(y, i) : i in [1..n-1] ] le 1 : y in Monomials(x) ];
  return ok;
end function;
   
   
// to permanently and accessibly store M   
declare attributes Map : M;   
   

TwoParameterAffineTransformation := function(M1, M2, s)   
//
//  Compute (generic) transformations between special models 
//    at most s
//                         
  assert assigned M1`x;
  assert assigned M1`relations;
  assert assigned M2`x;
  assert assigned M2`relations;
  assert Universe(M1`relations) cmpeq Universe(M2`relations);
  assert M1`n eq M2`n;
  
  // find two param trafo
  n := M1`n;
  R := M1`R;
  S<c,b> := PolynomialRing(BaseRing(R), 2);
  SR := PolynomialRing(S, Rank(R));
  emb := hom< R -> SR | [ SR.i : i in [ 1..Rank(R) ] ] >;
  L1 := [ emb(z) : z in M1`relations ];
  L2 := [ emb(z) : z in M2`relations ];
  map := hom< SR -> SR | [ c^n[1] * SR.1 + b ] cat 
                         [ c^n[i] * SR.i : i in [2..Rank(SR)] ] >;
  L2prime := [ map(z) : z in L1 ];
  // scale L2 accordingly
  ind := M1`ind;  
  L2scaled := [ c^(n[i] + n[j]) * z    
                where z := L2[nu]
                where i := ind[nu][1]
                where j := ind[nu][2]
              : nu in [1..#L2] ];  
  // compare elements of L2 and L2prime coefficientswise
  L := [ L2scaled[nu] - L2prime[nu] : nu in [1..#L2] ]; 
  coeffs := &cat [ Coefficients(x) : x in L ];
  // find solutions
  J := ideal< S | coeffs >;
  vprint Aut1, 3 : "J is ", J;
  // this should always be fast
  B := GroebnerBasis(J);
  vprint Aut1, 3 : "Groebner Basis of J is ", B;
  V := Variety(J);  
  V := [ v : v in V | &and [ not IsZero(v[1]) ] ];
  // this is so that identity will be first created.
  t := Position(V, <1,0>);
  if t gt 0 then
     v := V[1];
     V[1] := V[t];
     V[t] := v;
  end if;
  // maximally s maps desired
  if #V gt s then
    V := [ V[i] : i in [1..s] ];
  end if;
  vprint Aut1, 3 : "V is ", V;
  vprint Aut1 : #V, "points computed";
  if #V eq 0 then
     return [];
  end if;
  // make maps of function fields
  C := FieldCategory();
  E := FunctionFieldCategory();
  F1 := FunctionField(M1`P);
  F2 := FunctionField(M2`P);
  assert IsObject(E)(F1);
  assert IsObject(E)(F2);
  k := BaseObject(E)(F1);
  assert k cmpeq BaseObject(E)(F2);
  MakeNumsDens := function(F, static)  
      assert FunctionField(static`M`P) cmpeq F;
      if assigned static`M`nums then
         return static`M`nums, static`M`dens;       
      end if;
      i := Coercion(C)(k, F);
      ok, affeq, polys, gens, mess := SupportsExtension(C)(i);
      assert ok;  
      // one way
      // this is a bit on foot, should/could use maps
      // to new field of fractions of affine algebras of dim gt 0.
      nums := [];
      dens := [];  
      for z in gens do
         nn, dd := RepresentInGenerators(z, static`M);
         Append(~nums, nn);   
         Append(~dens, dd);   
      end for;
      static`M`nums := nums;
      static`M`dens := dens;
      return nums, dens;
  end function;    
  // now make maps
  maps := [ Maps(F1, F2) | ];
  static1 := Coercion(Integers(), Integers());
  static2 := Coercion(Integers(), Integers());
  static1`M := M1;
  static2`M := M2;
  x1 := M1`x;
  x2 := M2`x;
  // 
  // The following only lazy creates the inverses.
  // Once one inverse has been computed, nums and dens are known
  // for the next inverse computation through static2.  
  //  
  for v in V do
     // make all maps R/I1 -> R/I2, lifted to R.
     c := v[1];
     b := v[2];
     nums1, dens1 := MakeNumsDens(F1, static1);
     map1 := hom< R -> R | [ c^n[1] * R.1 + b ] cat 
                          [ c^n[i] * R.i : i in [2..Rank(R)] ] >;
     I1 := [ Evaluate(map1(nums1[i]), x2) / Evaluate(map1(dens1[i]), x2) :
            i in [1..#nums1] ];
     ok, g1, mess := HasMorphismFromImages(E)(F1, F2, I1);             
     assert ok;            
     preimageconstr := function(static)
        nums, dens := MakeNumsDens(F2, static2);
        map := hom< R -> R | [ c^(-n[1]) * ( R.1 - b) ] cat 
                             [ c^(-n[i]) * R.i : i in [2..Rank(R)] ] >;
        I2 := [ Evaluate(map(nums[i]), x1) / Evaluate(map(dens[i]), x1) :
                i in [1..#nums] ];
        ok, g2, mess := HasMorphismFromImages(E)(F2, F1, I2);             
        assert ok;                  
        // some checks, might be a bit expensive.
        ok, h := HasComposition(E)(g1, g2);
        assert ok and IsIdentity(E)(h);
        ok, h := HasComposition(E)(g2, g1);
        assert ok and IsIdentity(E)(h);
        // temporarily store info for inverseconstr() below.
        static`data`tmp1 := "true";  
        static`data`tmp2 := g2;  
        image := ImageFunction(g2);
        return true, image;
     end function;  
     inverseconstr := function(g1)
        if not assigned g1`static`data`tmp1 then
           ok, preim := HasPreimageFunction(g1);
        end if;
        ok := g1`static`data`tmp1;
        g2 := g1`static`data`tmp2;
        delete g1`static`data`tmp1;
        delete g1`static`data`tmp2;
        assert ok cmpeq "true";
        return ok, g2;
     end function;   
     g1 := InstallPreimageConstructor(g1, preimageconstr);   
     delete g1`static`data`inverseconstr;   
     g1 := InstallInverseConstructor(E)(g1, inverseconstr);   
     Append(~maps, g1);
  end for;
  return maps;
end function;



////////////////////////////////////////////////////////////////////////////
//  
//  Tests.
//  
//  We make some restrictions to generality:  
//   The constant fields must be exact and perfect. 
//  
  
  
IsomorphismTestOverBase := function(F1, F2)
//   
//  Some quick tests. Returns false for not, and true for possibly
//  
   assert DimensionOfExactConstantField(F1) eq 1;
   assert DimensionOfExactConstantField(F2) eq 1;
   if Characteristic(F1) ne Characteristic(F2) then
      return "false", false, "Characteristics not equal";
   end if;   
   if Genus(F1) ne Genus(F2) then
      return "false", false, "Genera are not equal";
   end if;
   return "true", "Possibly isomorphic";
end function;
  
  
IsomorphismTest := function(F1, F2)
//   
//  Some quick tests. Returns false for not, and true for possibly
//    (and then also an constant field isomorphism).
//  
   assert DimensionOfExactConstantField(F1) eq 1;
   assert DimensionOfExactConstantField(F2) eq 1;
   C := FieldCategory();
   ok, c, mess := IsIsomorphic(C)(ConstantField(F1), ConstantField(F2));
   if ok ne "true" then
      return ok, false, mess;
   end if;
   if Genus(F1) ne Genus(F2) then
      return "false", false, "Genera are not equal";
   end if;
   return "true", c, "Possibly isomorphic";
end function;
   
   
////////////////////////////////////////////////////////////////////////////   
//   
//  Find possibly corresponding, suitable places   
//  
  
Search := function(W, S)
   p := Characteristic(FunctionField(Universe(W)));
   T := &cat [ [ < E, P, d > : P in L | (p eq 0 or (d mod p ne 0)) 
                 where _, d := FirstPoleElement(-E, P) ] 
               where L := [ P : P in S | Valuation(E, P) eq 0 ]
             : E in W ]; 
   if #T eq 0 then
     return false, false, [];
   end if;
   n := Minimum( [ Abs(x[3]) : x in T ] );
   T := [ < x[1], x[2] > : x in T | Abs(x[3]) eq n ];   
   return true, n, T;   
end function;


FindSpecialPlacesDegOne := function(S1, S2)   
//   
//  Global case, deg one.   
//    S1 some candidate places on the left. 
//    S2 all corresponding candidates on the right.
//    Requirement: S1 will be mapped into S2 if isomorphic.
//
    assert #S1 le #S2;
    vprint Aut2 : "Analysing given places of degree one";  
    F1 := FunctionField(Universe(S1));
    F2 := FunctionField(Universe(S2));
    vprint Aut2 : "  Number of places is ", #S1;
    if #S1 eq 0 then
        vprint Aut2 : "Done.";
        return "no info", false, false, false, "No places of degree one given";
    end if;
    // find suitable auxiliary divisor and places for F1
    vprint Aut2 : "  Search for suitable places with zero auxiliary divisor in F1";  
    ok1, n1, T1 := Search( [ DivisorGroup(F1)!0 ], S1 );   
    if not ok1 then
    vprint Aut2 : "  Search for suitable places with non-zero auxiliary divisor in F1";
       b := Maximum(Genus(F1), 5); // heuristic
       for j in [1..b] do
          vprint Aut2 : "    Exponent of auxiliary divisors is", j;
          expo := j;
          ok1, n1, T1 := Search( [ j*Q : Q in S1 ], S1 );   
          if ok1 then
             break;
          end if;
       end for;   
       if ok1 then
          auxdiv1 := true;
       else
         vprint Aut2 : "Done. Left pole numbers all divisible by p.";
       end if;
    else   
       auxdiv1 := false;
    end if;
    vprint Aut2 : "  Search for possible corresponding places in F2";
    if Set(S1) cmpeq Set(S2) then
       // computation already done for F2 
       if not ok1 then
         return "no info", false, false, false, 
                "Pole numbers all divisible by characteristic";   
       end if;
       n2 := n1;
       T2 := T1;
    elif #S1 eq #S2 then
       // find corresponding info for F2   
       if ok1 and not auxdiv1 then  
vprint Aut2 : "   with zero auxiliary divisor";
          ok2, n2, T2 := Search( [ DivisorGroup(F2)!0 ], S2 );   
       else 
   vprint Aut2 : "   with non-zero auxiliary divisor of exponent ", expo;
          ok2, n2, T2 := Search( [ expo*Q : Q in S2 ], S2 );   
       end if;
       if ok1 ne ok2 or n1 cmpne n2 or #T1 ne #T2 then   
          vprint Aut2 : "Done.";
          return "not iso", false, false, false, "Pole numbers are different";
       end if;          
       if not ok1 then   
          vprint Aut2 : "Done.";
          return "no info", false, false, false, 
                 "Pole numbers all divisible by characteristic";   
       end if;          
    else 
       // we only have possible embedding of S1 into S2
       // ( should be in the char zero weierstrass case
       //   and could be more general ).
       assert ok1 and not auxdiv1;
       D := DivisorGroup(F2)!0;
       T2 := [ < D, P >  : P in S2 |
               d eq n1 where _, d := FirstPoleElement(P) ];
       if #T2 lt #T1 then
          vprint Aut2 : "Done.";
          return "not iso", false, false, false, 
                 "Pole numbers are different";      
       end if;   
    end if;
    // (remark: this ensures that first map computed will be identity )
    t1 := T1[1];  
    // refine info further, find corresponding t2
    UF1 := UnderlyingRing(F1, BaseField(F1));
    G1 := GapNumbers(DivisorGroup(UF1)!t1[1], Places(UF1)!t1[2]);
    vprint Aut2 : "  Chosen place of F1 with gap numbers ", G1;
    // now compute T2 
    vprint Aut2 : "  Restrict to places of F2 with same gap numbers";
    UF2 := UnderlyingRing(F2, BaseField(F2));
    T2 := [ t2 : t2 in T2 | GapNumbers(DivisorGroup(UF2)!t2[1], Places(UF2)!t2[2]) eq G1 ];    
    if #T2 lt 1 then
      vprint Aut2 : "Done.";
      return "not iso", false, false, false, 
             "Pole numbers are different";      
    end if;   
    if F1 cmpeq F2 then
       // again to ensure that identity map comes first
       i := Position(T2, t1);
       assert i ge 1;
       t2 := T2[i]; T2[i] := T2[1]; T2[1] := t2;
    end if;
    vprint Aut2 : "  Number of possible auxiliary divisor/places pairs ", #T2; 
    vprint Aut2 : "Done.";
    return "maybe iso", t1[1], t1[2], T2, "ok";
end function;    
   
   
FindSpecialPlacesGlobalGeneric := function(F1, F2, places1, places2, md)   
//   
//  Global case, generic. places1 and places2 return places and
//   must be "symmetric". If isomorphic then there must be bijection
//   places1(d) -> places2(d).
//                                                     
    // find suitable auxiliary divisor and places for F1
    k := ConstantField(F1);  
    q := #k;
    C := FieldCategory();
    E := FunctionFieldCategory();    
    d := 1;
    found := false;
    repeat  
      vprint Aut2 : "Check places of degree ", d;
      S1 := places1(d);  
      S2 := places2(d);
      if #S1 ne #S2 then
         return "not iso", false, false, false, false, false, 
                "Number of places different";    
      end if;
      if #S1 ne 0 then
         // two disjoint strategies possible:
         // the first allows for smaller first pole order choice
         // but needs double split work if F1 cmpne F2.
         if true then
            c := Coercion(C)(k, GF(q^d));
            F1c, f1 := BaseExtension(E)(F1, c);
            T1 := &cat [ Parent( [ Places(F1c) | ] ) |
                         Support( Conorm(f1, P) )
                         : P in S1 ];
            if F1 cmpeq F2 then
               F2c := F1c;
               f2 := f1;
               T2 := T1;
            else
               F2c, f2 := BaseExtension(E)(F2, c);
               T2 := &cat [ Parent( [ Places(F2c) | ] )
                            | Support( Conorm(f2, P) )
                            : P in S2 ];
            end if;
            assert #T1 eq #T2;
         else
            P0 := Representative( S1 );
            c := Coercion(C)(k, GF(q^d));
            F1c, f1 := BaseExtension(E)(F1, c);
            T1 := [ Representative( [ P : P in Support( Conorm(f1, P0) ) ] ) ];
            F2c, f2 := BaseExtension(E)(F2, c);
            T2 := &cat [ Parent( [ Places(F2c) | ] ) 
                         | Support( Conorm(f2, P) ) 
                         : P in S2 ];
         end if;
         ok, D, P, T2, mess := FindSpecialPlacesDegOne(T1, T2);
         if ok eq "not iso" then
            return "not iso", false, false, false, false, false, mess;
         end if;
         if ok eq "maybe iso" then
            found := true;
            break;
         end if;
         assert ok cmpeq "no info";
      end if;
      d := d + 1;  
    until d gt md;
    if not found then
       return "no info", false, false, false, false, false, 
              "Cannot find suitable places";
    end if;
    return "maybe iso", f1, f2, D, P, T2, "ok"; 
end function;
   
   
FindSpecialPlacesGlobalDegreeOne := function(F1, F2)   
//   
//  Global case, degree one places
//   
    vprint Aut2 : "Analysing degree one places";
    places1 := function(d)
       return Places(F1, d);
    end function;
    places2 := function(d)
       return Places(F2, d);
    end function;
    md := 2 * Genus(F1) + 1;
    ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalGeneric(F1, F2, 
                                                  places1, places2, md);
    vprint Aut2 : "Done.";
    return ok, f1, f2, D, P, T2, mess;
end function;

  
FindSpecialPlacesGlobalWeierstrass := function(F1, F2)   
//   
//  Global case, Weierstrass places
//   
    vprint Aut2 : "Analysing Weierstrass places";
    S1 := WeierstrassPlaces(F1);
    S2 := WeierstrassPlaces(F2);
    if #S1 eq 0 then
       return "no info", false, false, false, false, false, 
              "There are no Weierstrass places";
    end if;
    if #S1 ne #S2 or 
      {* Degree(P) : P in S1 *} ne {* Degree(P) : P in S2 *} then
       vprint Aut2 : "Done.";
       return "not iso", false, false, false, false, false, 
              "Weierstrass places are different";
    end if;
    places1 := function(d)
       return [ Places(F1) | P : P in S1 | Degree(P) eq d ];
    end function;
    places2 := function(d)
       return [ Places(F2) | P : P in S2 | Degree(P) eq d ];
    end function;
    md := Maximum( [ Degree(P) : P in S1 ] );
    ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalGeneric(F1, F2, 
                                                  places1, places2, md);
    vprint Aut2 : "Done.";
    return ok, f1, f2, D, P, T2, mess;
end function;


FindSpecialPlacesCharZeroWeierstrass := function(F1, F2)   
//   
//  Char zero case, Weierstrass places
//   
    vprint Aut2 : "Analysing Weierstrass places";
    S1 := WeierstrassPlaces(F1);
    S2 := WeierstrassPlaces(F2);
    if #S1 eq 0 then
       return "no info", false, false, false, false, false, 
         "There are no Weierstrass places";
    end if;
    if #S1 ne #S2 or 
      {* Degree(P) : P in S1 *} ne {* Degree(P) : P in S2 *} then
       vprint Aut2 : "Done.";
       return "not iso", false, false, false, false, false, 
              "Weierstrass places are different";
    end if;
    // find suitable places for F1 and F2
    C := FieldCategory();
    E := FunctionFieldCategory();
    k := ConstantField(F1);  
    md := Minimum( [ Degree(P) : P in S1 ] );
    P0 := Representative( [ P : P in S1 | Degree(P) eq md ] );
            // here we could additionally choose one with small first 
            // pole order ... but how?
    K0 := ResidueClassField(P0);
    c := Coercion(C)(k, K0);
    F1c, f1 := BaseExtension(E)(F1, c);
    T1 := [ Representative( [ P : P in Support( Conorm(f1, P0) ) | 
                              Degree(P) eq 1 ] ) ];
    C := FieldCategory();
    D := ExtensionCategory(C, k);
    F2c, f2 := BaseExtension(E)(F2, c);
    T2 := [ P : P in S2 | Degree(P) eq md ];
    T2 := [ P : P in T2
            | IsIsomorphic(D)(ResidueClassField(P), K0) eq "true" ];
    T2 := &cat [ Parent( [ Places(F2c) | ] )
                 | Support( Conorm(f2, P) )
                 : P in T2 ];
    T2 := [ P : P in T2 | Degree(P) eq 1 ]; 
    ok, D, P, T2, mess := FindSpecialPlacesDegOne(T1, T2);
    assert ok eq "maybe iso";
    assert IsZero(D);
    vprint Aut2 : "Done.";
    return "maybe iso", f1, f2, D, P, T2, mess; 
end function;
   
   
   
FindSpecialPlaces := function(F1, F2, strat)    
//   
//  Constant fields must exact and equal.
//    and the genus must be the same.
//   "false" returned if failure.  
//  
  assert strat in { "None", "Weierstrass", "DegOne" };
  if Characteristic(F1) eq 0 then
    ok, f1, f2, D, P, T2, mess := FindSpecialPlacesCharZeroWeierstrass(F1, F2);
      assert ok in { "not iso", "maybe iso", "no info" };
      return ok, f1, f2, D, P, T2, mess;    
  end if;
  assert IsGlobal(F1);
  g := Genus(F1);
  q := #ConstantField(F1);
  if strat cmpeq "None" then  
     // a rough test what might be cheaper
     // compute Weierstrass places or places of degree one  
     if g ge 2 and g^2 lt q then
      ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalWeierstrass(F1, F2);
     else
      ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalDegreeOne(F1, F2);
     end if;    
  else
     if strat cmpeq "Weierstrass" and g ge 2 then     
    ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalWeierstrass(F1, F2);
     else        
    ok, f1, f2, D, P, T2, mess := FindSpecialPlacesGlobalDegreeOne(F1, F2);
     end if;
  end if;
  if not ok in { "maybe iso", "not iso" } then
     return "no info", false, false, false, false, false, mess;
  end if;
  assert ok in { "not iso", "maybe iso", "no info" };
  return ok, f1, f2, D, P, T2, mess;  
end function;   
   
   
////////////////////////////////////////////////////////////////////////////   
//   
//  Checks
//  
  
   
CheckFunctionFields := function(F1, F2)
   if not IsPerfect(ConstantField(F1)) or 
      not IsPerfect(ConstantField(F2)) then
      return false, "Constant fields must be perfect";
   end if;
   if DimensionOfExactConstantField(F1) ne 1 then
      return false, "Constant fields must be exact";
   end if;
   if DimensionOfExactConstantField(F2) ne 1 then
      return false, "Constant fields must be exact";
   end if;
   return true, "ok";
end function;
   
   
CheckIsoInputOverBase := function(F, G, c, C, Cext)
      if not IsObject(Cext)(F) then
         return false, SPrintCategory(Cext) cat
           ": First argument is not object in category";
      end if;
      if not IsObject(Cext)(G) then
         return false, SPrintCategory(Cext) cat
           ": Second argument is not object in category";
      end if;
      if c cmpne false then
         if not IsMorphism(C)(c) then
            return false, SPrintCategory(Cext) cat
              ": Third argument is not morphism in base category";
         end if;
         if not AreEqualObjects(C)(Domain(c), BaseObject(Cext)(F)) then
            return false, SPrintCategory(Cext) cat
   ": Domain of third argument is not equal to base object of first argument";
         end if;
         if not AreEqualObjects(C)(Codomain(c), BaseObject(Cext)(G)) then
            return false, SPrintCategory(Cext) cat
 ": Codomain of third argument is not equal to base object of second argument";
         end if;
         if IsIsomorphism(C)(c) cmpne "true" then
            return false, SPrintCategory(Cext) cat
              ": Third argument is not isomorphism in base category";
         end if;
      end if;
      return true, "ok";      
end function;   
   
   
CheckAutoInputOverBase := function(F, c, C, Cext)
      if not IsObject(Cext)(F) then
         return false, SPrintCategory(Cext) cat
           ": First argument is not object in category";
      end if;
      if c cmpne false then
         if not IsMorphism(C)(c) then
            return false, SPrintCategory(Cext) cat
                   ": Third argument is not morphism in category";
         end if;
         if not AreEqualObjects(C)(Domain(c), BaseObject(Cext)(F)) then
            return false, SPrintCategory(Cext) cat
  ": Domain of third argument is not equal to base object of first argument";
         end if;
         if IsAutomorphism(C)(c) cmpne "true" then
            return false, SPrintCategory(Cext) cat
                   ": Third argument is not automorphism in base category";
         end if;          
      end if;
      return true, "ok";      
end function;
   
   
////////////////////////////////////////////////////////////////////////////   
//   
//  Find isomorphisms
//  
  
  
IsomorphismsWithPlace := function(D1, P1, D2, P2, s)
//   
//  P1 and P2 are of degree one.
//  
  vprint Aut1 : "Relating D1 =", D1, ", P1 =", P1; 
  vprint Aut1 : "     and D2 =", D2, ", P2 =", P2;
  ok, expand1 := HasAlmostUniqueLocalParametrization(-D1, P1);
  assert ok;
  ok, expand2 := HasAlmostUniqueLocalParametrization(-D2, P2);
  assert ok;
  vprint Aut1 : "  Compute special model for F1";
  M1 := ComputeSpecialModel(P1, expand1); 
  vprint Aut1 : "  Compute special model for F2";
  M2 := ComputeSpecialModel(P2, expand2);
  vprint Aut1 : "  Relate special models";
  maps := TwoParameterAffineTransformation(M1, M2, s);
  vprint Aut1 : "Done for these D1, P1, D2, P2.";
  return maps;
end function;
   
      
LiftMorphismToStandardRationalAlff := function(f)   
   assert Domain(f) cmpeq Codomain(f) and Type(Domain(f)) eq FldFunRat;
   E := FunctionFieldCategory();
   kxf := Domain(f);
   F := FunctionField(Places(kxf));
   i := Coercion(E)(kxf, F);
   ok, j := HasInverse(E)(i);
   assert ok cmpeq "true";
   return CompositionSequence(E)([j, f, i]);
end function;
   
   
MakeIsomorphismsOverBase := function(F1, F2, c, s, strat)    
//   
//  F1 and F2 must be over the same base.
//  Compute at most s isomorphisms of F1 and F2 fixing the base.    
//   
    C := FieldCategory();
    is_id := IsIdentity(C)(c);
    // trivial cases
    if F1 cmpeq F2 and is_id then
       if s eq 0 then
          return "true", [], "Are isomorphic.";   
       end if;
       if s eq 1 then
          E := FunctionFieldCategory();
          id := Identity(E)(F1);
          return "true", [ id ], "Are isomorphic.";   
       end if;
    end if;
    // semi trivial cases
    if { Type(F1), Type(F2) } eq { FldFunRat } and s le 1 then
       // Q(x) case for example (univariate)
       E := FunctionFieldCategory();
       i := ExtensionMorphism(E)(F1);
       j := ExtensionMorphism(E)(F2);
       ok, L, mess := HasIsomorphismExtensions(C)(c, i, j, s);
       assert ok in { "true", "false", "unknown" };
       if ok cmpne "true" then
           return ok, false, mess;
       end if;
       if s eq 1 then
          ok, f := HasMorphism(E)(F1, F2, L[1], c);
          assert ok;
          L := [ f ];
       end if;
       // #L is le 1
       return "true", L, "Are isomorphic.";
    end if;
    // check the function fields 
    ok, mess := CheckFunctionFields(F1, F2);
    if not ok then 
       return "unknown", false, mess;
    end if;
    // isomorphism test
    ok, mess := IsomorphismTestOverBase(F1, F2);
    assert ok in { "true", "false" };
    if ok cmpeq "false" then
       return "false", [], mess;
    end if;
    E := FunctionFieldCategory();
    if not is_id then
       FF1, gg := BaseExtension(E)(F1, c);
       ok := IsomorphismTestOverBase(FF1, Domain(gg));
       assert ok eq "true";
    else
       FF1 := F1;
    end if;
    // start the real work
    ok, f1, f2, D, P, T2, mess := FindSpecialPlaces(FF1, F2, strat);
    if ok cmpeq "no info" then
       return "unknown", false, mess; 
    end if;
    if ok cmpeq "not iso" then
       return "false", [], mess;
    end if;
    assert ok cmpeq "maybe iso";
    // find maps upstairs
    if not IsFinite(s) then
       s := 10^50; // this is as good as infinity
    end if;
    maps := [];
    vprint Aut2 : "Looping over ", #T2, " pairs ...";
    for i in [1..#T2] do
       t := T2[i];
       vprint Aut2 : "  Considering pair ", i, " out of ", #T2, " ...";
       if s - #maps le 0 then
          break;   
       end if;
       maps := maps cat IsomorphismsWithPlace(D, P, t[1], t[2], s - #maps);
    end for;
    vprint Aut2 : "  Done.";
    // restrict
    E := FunctionFieldCategory();  
    vprint Aut2 : "Restrict maps to base field ...";
    if Degree(E)(f1) ne 1 then  
       res := HasRestriction(E);
       maps1 := [];
       for f in maps do
          ok, g := res(f, f1, f2); 
          if ok then
             Append(~maps1, g);
          end if;
       end for;
       maps := maps1;
    end if;
    vprint Aut2 : "  Done.";
    if not is_id then
       if Type(Codomain(gg)) eq FldFunRat then
       // deal with silly difference between "kxf" and "linear alff"
           gg := LiftMorphismToStandardRationalAlff(gg);
       end if;
       maps := [ Composition(E)(gg, f) : f in maps ];
    end if;
    if is_id and F1 cmpeq F2 and s ge 1 then
       assert IsIdentity(E)(maps[1]);
    end if;
    return "true", maps, "Are isomorphic.";
end function;
   
   
MakeIsomorphisms := function(F1, F2, s, strat)    
//
//  ( also includes base isomorphisms )
//
    // trivial cases
    if F1 cmpeq F2 then
       if s eq 0 then
          return "true", [], "Are isomorphic.";   
       end if;
       if s eq 1 then
          E := FunctionFieldCategory();
          id := Identity(E)(F1);
          return "true", [ id ], "Are isomorphic.";   
       end if;
    end if;
    // semi trivial cases
    if { Type(F1), Type(F2) } eq { FldFunRat } and s le 1 then
       // Q(x) case for example (univariate)
       C := FieldCategory();
       E := FunctionFieldCategory();
       i := ExtensionMorphism(E)(F1);
       j := ExtensionMorphism(E)(F2);
       ok, L, mess := HasIsomorphisms(C)(F1, F2, s);
       assert ok in { "true", "false", "unknown" };
       if ok cmpne "true" then
          return ok, false, mess;
       end if;
       if s eq 1 then
          ok, c := HasRestriction(C)(L[1], i, j);      
          assert ok;
          ok, f := HasMorphism(E)(F1, F2, L[1], c);
          assert ok;
          L := [ f ];
       else
          L := [];
       end if;
       return "true", L, "Are isomorphic.";
    end if;
    // check the function fields 
    ok, mess := CheckFunctionFields(F1, F2);
    if not ok then 
       return "unknown", false, mess;
    end if;
    k1 := ConstantField(F1);
    k2 := ConstantField(F2);
    C := FieldCategory();
    // mch - 06/06 - is say s=1 & k1 eq k2, then maybe isomorphisms
    //  exist but not over the identity isomorphism of k1. In that case
    //  calling HasIsomorphisms(C)(k1, k2, s) is inadequate: we may
    //  need all isomorphisms from k1 to k2 to find just 1 from F1 to F2.
    //  Quick fix: if k1,k2 are of "small" type, get all poss IMs k1->k2 here.
    typ := Type(k1);
    if (typ eq FldRat) or (typ eq FldFin) or ISA(typ, FldNum) then
	ok, L, mess := HasIsomorphisms(C)(k1, k2, Infinity());
    else
        ok, L, mess := HasIsomorphisms(C)(k1, k2, s);
    end if;
    if ok cmpeq "unknown" then
       return "unknown", false, 
         "Isomorphism test of constant fields yields: " cat mess;
    end if;
    assert ok in { "true", "false" };
    if ok cmpeq "false" then
       return "false", [], "Constant fields are not isomorphic: " cat mess;
    end if;
    maps := [];
    is_iso := false;
    for c in L do
       ok, maps1, mess := 
         MakeIsomorphismsOverBase(F1, F2, c, s - #maps, strat); 
       if ok cmpeq "unknown" then             
          return "unknown", false, mess;
       end if;
       is_iso := is_iso or ok cmpeq "true";
       maps := maps cat maps1;                 
    end for;
    if not is_iso then
       return "false", false, mess;
    end if;
    return "true", maps, "Are isomorphic.";   
end function;
   
   
   
declare attributes FldFunG : coeffauts, autsfull, auts;  


MakeAutomorphismsOverBase := function(F, c, s, strat)    
   if not assigned F`coeffauts then
       F`coeffauts := [];
       F`auts := [];
       F`autsfull := [];
    end if;
    i := Position(F`coeffauts, c);
    if i eq 0 then
       C := FieldCategory();
       for j in [1..#F`coeffauts] do
           if AreEqualMorphisms(C)(c, F`coeffauts[j]) then
              i := j;             
              break;
           end if;   
       end for;
    end if;
    if i gt 0 then 
       if #F`auts[i] ge s or F`autsfull[i] then
         S := Type(F) cmpeq FldFunRat 
              select Maps(G, G) where G := FunctionField(Places(F)) 
              else Maps(F, F);
         return "true",
                [ S | L[j] : j in [1..Round(Minimum([#L, s]))] ]
                where L := F`auts[i],
                "ok";                   
       end if;      
    end if;
    // simple solution for the moment
    ok, L, mess := MakeIsomorphismsOverBase(F, F, c, s, strat);     
    if ok cmpeq "true" then
       if i eq 0 then
          Append(~F`coeffauts, c);
          Append(~F`auts, L);
          Append(~F`autsfull, #L lt s);
       else
          F`auts[i] := L;
          F`autsfull[i] := #L lt s;   
       end if;
    end if;
    return ok, L, mess;
end function;  
   
   
MakeAutomorphisms := function(F, s, strat)    
    // check the function field 
    ok, mess := CheckFunctionFields(F, F);
    if not ok then 
       return "unknown", false, mess;
    end if;
    k := ConstantField(F);
    C := FieldCategory();
    // better do automorphisms here (storage reason)?
    ok, L, mess := HasIsomorphisms(C)(k, k, s);
    if ok cmpeq "unknown" then
       return "unknown", false, 
         "Automorphism computation of constant field yields: " cat mess;
    end if;
    assert ok cmpeq "true";
    maps := [];
    for c in L do
       ok, maps1, mess := 
         MakeAutomorphismsOverBase(F, c, s - #maps, strat); 
       if ok cmpeq "unknown" then             
          return "unknown", false, mess;
       end if;
       maps := maps cat maps1;                 
    end for;
    return "true", maps, "ok";   
end function;  
   
   
////////////////////////////////////////////////////////////////////////   
//  
// Some intrinsics for easy user use  
//  
  
  
intrinsic IsMorphism(f::Map) -> Bool
{True, if the map is a field or function field morphism, false otherwise}     
   if not assigned f`static or not assigned f`static`data then
       return false, _;
   end if;
   return IsFieldCategory(ParentCategory(f)) or 
          IsFunctionFieldCategory(ParentCategory(f));
end intrinsic;
  
  
intrinsic Equality(f::Map, g::Map) -> Bool  
{True, if the two maps are both field morphisms or function field morphisms and are equal, false otherwise}  
     require IsMorphism(f) and IsMorphism(g) :
         "Maps are required to be field or function field morphisms";
     if ParentCategory(f) cmpne ParentCategory(g) then
        return false;
     end if;
     C := ParentCategory(f);
     return AreEqualMorphisms(C)(f, g);
end intrinsic;          
          
  
// this is for use below   
  
intrinsic IdentityFieldMorphism(F::Fld) -> Map
{The identity automorphism of F}  
   C := FieldCategory();
   return Identity(C)(F);
end intrinsic;


intrinsic IsIdentity(f::Map) -> Map
{True if f is the identity morphism, false otherwise}  
    require IsMorphism(f) : 
         "Map is required to be field or function field morphism";
    C := ParentCategory(f);
    return IsIdentity(C)(f);
end intrinsic;


intrinsic HasInverse(f::Map) -> MonStgElt, Map   
{Either "true" and the inverse map, or "false" if inverse does not exist, or "unknown" if it cannot be computed}   
    require IsMorphism(f) : 
         "Map is required to be field or function field morphism";
    C := ParentCategory(f);
    return HasInverse(C)(f);
end intrinsic;                                              


intrinsic Composition(f::Map, g::Map) -> Map
{The composition of the morphisms f and g}  
    require IsMorphism(f) : 
         "First argument is required to be field or function field morphism";
    require IsMorphism(g) : 
         "First argument is required to be field or function field morphism";
    C := ParentCategory(f);
    require ParentCategory(g) cmpeq C :
         "Arguments must be morphisms of the same category";
    ok, h, mess := HasComposition(C)(f, g);
    require ok : mess;
    return h;
end intrinsic;


/////////////////////////


intrinsic Isomorphisms(F1::FldFunG, F2::FldFunG : 
            BaseMorphism := false,
            Bound := Infinity(), Strategy := "None") -> SeqEnum
{Returns a sequence of isomorphisms, extending BaseMorphism if given}   
      require Strategy in { "None", "Weierstrass", "DegOne" } :
"Optional argument Strategy must be \"None\", \"Weierstrass\" or \"DegOne\"";
      c := BaseMorphism;                 
      C := FieldCategory();
      Cext := FunctionFieldCategory();             

/*
       // FH temp
       if c cmpeq false and ConstantField(F1) cmpeq ConstantField(F2) then
         c := IdentityFieldMorphism(ConstantField(F1));
       end if;
       if c cmpeq true then
          c := false;
       end if;
*/

      if c cmpeq false then
         ok, mess := CheckIsoInputOverBase(F1, F2, c, C, Cext);
         require ok : mess;                   
         ok, L, mess := MakeIsomorphisms(F1, F2, Bound, Strategy);
      else
         if not IsMorphism(C)(c) then
            require not assigned c`static or 
              not assigned c`static`data : 
              "Coefficient map is already morphism of different category";
            c := ImportExternalMorphism(C)(c, true);
         end if;
         ok, mess := CheckIsoInputOverBase(F1, F2, c, C, Cext);
         require ok : mess;                   
         ok, L, mess := MakeIsomorphismsOverBase(F1, F2, c, Bound, Strategy);
      end if;
      require ok cmpne "unknown" :
        "No algorithm to compute isomorphisms for this special case (" 
          cat mess cat ")";
      if ok cmpeq "false" then
         return [ Maps(F1, F2) | ];
      end if;
      return L;
end intrinsic;


intrinsic Isomorphisms(F1::FldFunG, F2::FldFunG, 
                       P1::PlcFunElt, P2::PlcFunElt : 
            Bound := Infinity()) -> SeqEnum
{Returns a sequence of isomorphisms, extending the identity morphism of the base field, which map the place P1 to the place P2}   
      C := FieldCategory();
      Cext := FunctionFieldCategory();             
      require Degree(P1) eq 1 :
         "Third argument must have degree one";
      require Degree(P2) eq 1 :
         "Fourth argument must have degree one";
      require FunctionField(P1) cmpeq F1 :
        "Third argument must be place of first argument";
      require FunctionField(P2) cmpeq F2 :
        "Fourth argument must be place of second argument";
      s := Bound;
      ok, mess := CheckIsoInputOverBase(F1, F2, false, C, Cext);
      require ok : mess;                   
      ok, mess := CheckFunctionFields(F1, F2);
      require ok : mess;                   
      ok, mess := IsomorphismTestOverBase(F1, F2);
      if ok eq "false" then
         return [ Maps(F1, F2) | ];
      end if;
      require ConstantField(F1) cmpeq ConstantField(F2) :
         "Constant fields are required to be equal";
      if GapNumbers(P1) ne GapNumbers(P2) then
         return [ Maps(F1, F2) | ];
      end if;
      D1 := Zero(DivisorGroup(F1));
      D2 := Zero(DivisorGroup(F2));
      vprint Aut1 : "Relating D1 =", D1, ", P1 =", P1; 
      vprint Aut1 : "     and D2 =", D2, ", P2 =", P2;
      ok, expand1 := HasAlmostUniqueLocalParametrization(-D1, P1);
      require ok :
 "Case not yet implemented (first pole number not coprime to characeristic)";
      ok, expand2 := HasAlmostUniqueLocalParametrization(-D2, P2);
      assert ok;
      vprint Aut1 : "  Compute special model for F1";
      M1 := ComputeSpecialModel(P1, expand1); 
      vprint Aut1 : "  Compute special model for F2";
      M2 := ComputeSpecialModel(P2, expand2);
      vprint Aut1 : "  Relate special models";
      maps := TwoParameterAffineTransformation(M1, M2, s);
      vprint Aut1 : "Done for these D1, P1, D2, P2.";
      return maps;
end intrinsic;



intrinsic IsIsomorphic(F1::FldFunG, F2::FldFunG : 
             BaseMorphism := false,
             Strategy := "None") -> Bool, Map
{Returns whether isomorphic (wrt BaseMorphism), and an isomorphism}   
    c := BaseMorphism;
    L := Isomorphisms(F1, F2 : BaseMorphism := c, Bound := 1, 
                      Strategy := Strategy);
    if #L eq 0 then
      return false, _;
    end if;
    return true, L[1];
end intrinsic;



intrinsic Automorphisms(F::FldFunG : 
           BaseMorphism := false,
           Bound := Infinity(), Strategy := "None") -> SeqEnum
{Returns a sequence of automorphisms, extending BaseMorphism if given}   
       require Strategy in { "None", "Weierstrass", "DegOne" } :
"Optional argument Strategy must be \"None\", \"Weierstrass\" or \"DegOne\"";
       require IsPerfect(ConstantField(F)) :
          "Constant field must be perfect";
       C := FieldCategory();             
       Cext := FunctionFieldCategory();             
       require IsObject(Cext)(F) :
         SPrintCategory(Cext) cat
         ": First argument is not object in category";
       c := BaseMorphism;

/*
       // FH temp
       if c cmpeq false then
         c := IdentityFieldMorphism(ConstantField(F));
       end if;
       if c cmpeq true then
          c := false;
       end if;
*/

       if c cmpeq false then
          ok, mess := CheckAutoInputOverBase(F, c, C, Cext);             
          require ok : mess;            
          ok, L, mess := MakeAutomorphisms(F, Bound, Strategy);
          require ok cmpne "unknown" :
            "No algorithm to compute automorphisms for this special case ("
              cat mess cat ")";
          assert ok cmpeq "true";
          return L;
       end if;
       ok, mess := CheckAutoInputOverBase(F, c, C, Cext);             
       require ok : mess;            
       ok, L, mess := MakeAutomorphismsOverBase(F, c, Bound, Strategy);
       require ok cmpne "unknown" :
         "No algorithm to compute automorphisms for this special case ("
            cat mess cat ")";
       return L;
end intrinsic;



intrinsic Automorphisms(F::FldFunG, P1::PlcFunElt, P2::PlcFunElt :
                        Bound := Infinity() ) -> SeqEnum
{Returns a sequence of automorphisms, extending the identity morphisms on
   the base field, which map the place P1 to the place P2}   
      return Isomorphisms(F, F, P1, P2 : Bound := Bound);  
end intrinsic;



MakeAutomorphismGroup := function(F, L)
    E := FunctionFieldCategory();
    U := Domain(Universe(L));
    G, f := GenericGroup(
                  L : Eq := Equality, Mult := Composition, 
                  Id := Identity(E)(U), Reduce := true
           );
    /* mch 05/06 - above Reduce parameter added */
    // adapt f to better preimage use and for maps not in the 
    //  domain sequence but still valid 
    auts := Codomain(f);
    E := FunctionFieldCategory();
    preim := function(y)
       if not IsMorphism(E)(y) then
          return false, _;
       end if;
       // quick test
       i := Position(auts, y);
       if i eq 0 then
         // slow test
         for j in [1..#auts] do
            if AreEqualMorphisms(E)(y, auts[j]) then
                 i := j;
                 break;
            end if;
         end for;
       end if;
       if i eq 0 then
           return false, _;
       end if;
       return true, auts[i]@@f;
    end function;
    h := hom< G -> Maps(U, U) | x :-> f(x),
                                y :-> DoErrorPreimage(preim)(y) >;
    h := ImportMap(h, false);
    h := InstallPreimage(h, preim);       
    return G, h;
end function;
   
   
intrinsic AutomorphismGroup(F::FldFunG :
               BaseMorphism := false, 
               Bound := Infinity(), Strategy := "None") -> GrpFP, Map
{The automorphism group of the algebraic function field F, generated by automorphisms which extend BaseMorphism if given}
    c := BaseMorphism;
    if c cmpeq false then
       L := Automorphisms(F : Bound := Bound, Strategy := Strategy);
       G, f := MakeAutomorphismGroup(F, L);
       assert #G eq #L;
       U := Domain(Universe(L));
       return G, f, Aut(U);
    end if;
    require Type(c) cmpeq Map : "BaseMorphism must be a map";
    C := FieldCategory();               
    if not IsMorphism(C)(c) then
       require not assigned c`static or 
         not assigned c`static`data : 
         "Coefficient map is already morphism of different category";
       c := ImportExternalMorphism(C)(c, true);
    end if;
    ok, cinv := HasInverse(C)(c);
    require ok cmpeq "true" :
      "Coefficient map has no inverse";
    L1 := Automorphisms(F : BaseMorphism := c, Bound := Bound, 
                            Strategy := Strategy);
    if not AreEqualMorphisms(C)(c, cinv) then
       L2 := Automorphisms(F : BaseMorphism := cinv, Bound := Bound, 
                               Strategy := Strategy);
    else 
       L2 := [];
    end if;
    L := L1 cat L2;
    if IsIdentity(C)(c) then 
    /* clause added 07/06 - mch. Uses specialised, more efficient version
	of GenericGroup. Really should extend to non-identity-c case!     */
	G, f := CrvGenericGroup(L : Mult := Composition, Eq := Equality,
				Id := Identity(FunctionFieldCategory())(F));
    else
        G, f := MakeAutomorphismGroup(F, L);
    end if;
    assert not IsIdentity(C)(c) or #G eq #L;
    U := Domain(Universe(L));
    return G, f, Aut(U);
end intrinsic;

 
 
////////////////////////////////////////////////////////////////////////   
//  
//  Representations of automorphisms
//     Only for automorphisms which fix the constant field (,
//     because there is no (nice) way to represent the action
//     on the coefficients.)
//
  
  
CheckRepresentingMap := function(F, f)
   D := Domain(f);
   C := Codomain(f);
   if Type(C) cmpeq SetEnum then
      C := Universe(C);
   end if;
   if not ( C cmpeq F or
            ( Type(C) cmpeq PlcFun and FunctionField(C) cmpeq F) or
            ( Type(C) cmpeq DivFun and FunctionField(C) cmpeq F) or
            ( Type(C) cmpeq DiffFun and FunctionField(C) cmpeq F) ) then
      return false, "No operation of automorphisms of F on codomain of f";
   end if;
   if not ( Type(D) cmpeq SetEnum or
            ISA(Type(D), Mod) ) then
      return false, "No representing group for action on domain of f";   
   end if;
   return true, "ok";   
end function;
   
   
   
MakeRepresentation := function(F, f, s, strat)
   c := IdentityFieldMorphism(ConstantField(F));
   auts := Automorphisms(F : BaseMorphism := c, Bound := s, Strategy := strat);
   f := ImportMap(f, true);
   if Type(Domain(f)) cmpeq SetEnum then
       // permutation representation
       vprint Aut2 : "Computing permutation representation";  
       X := SetToSequence(Domain(f));
       if #X eq 0 then
           return false, false, false, false, "Set is empty";         
       end if;
       S := SymmetricGroup(Domain(f)); 
       assert IsIdentity(S!X);
       gens := [];
       kernel := [];
       A := [ f(i) : i in X ];
       for i in [1..#auts] do
          vprint Aut2 : "   Computing operation of automorphism ", i, " of ",
   #auts, " on set";     
          h := auts[i];
          B := [ Operation(h, x) : x in A ];
          Y := [];
          for x in B do
             // use of local HasPreimage here!
             ok, y := HasPreimage(f, x);
             if not ok then
                return false, false, false, false, 
                       "Set not invariant under automorphisms";
             end if;   
             Append(~Y, y);
          end for;
          Y := S!Y;
          Append(~gens, Y);   
          if IsIdentity(Y) then
             Append(~kernel, h);
          end if;
       end for;
       vprint Aut2 : "   Done.";
       G := sub< S | Set(gens) >;
       assert #G le #gens;
       assert #auts eq #G * #kernel;  
       vprint Aut2 : "Linking group and function field data ...";  
       E := FunctionFieldCategory();
       preim := function(y)
          if not IsMorphism(E)(y) then
             // this is a bit dirty but sooner or later somebody 
             //   would complain that there is no support for external maps
             F := Domain(y);  
             if F cmpne Codomain(y) then  
                return false, _;
             end if;
             if not ISA(Type(F), FldFunG) then
                return false, _;
             end if;
             C := FieldCategory();
             y := ImportExternalMorphism(C)(y, false);
             i := ExtensionMorphism(E)(F);
             ok, c, mess := HasRestriction(C)(y, i, i);
             if not ok then
                return false, _;
             end if;
             ok, y, mess := HasMorphism(E)(F, F, y, c);
             assert ok;   
          end if;
          // quick test
          i := Position(auts, y);
          if i eq 0 then
             // slow test
             for j in [1..#auts] do
                if AreEqualMorphisms(E)(y, auts[j]) then
                    i := j;
                    break;
                end if;
             end for;
          end if;
          if i eq 0 then
             return false, _;
          end if;
          return true, gens[i];
       end function;
       h := hom< G -> Maps(F, F) | x :-> auts[Position(gens, x)],
                 y :-> DoErrorPreimage(preim)(y) >;
       h := ImportMap(h, false);
       h := InstallPreimage(h, preim);       
       vprint Aut2 : "   Done.";
   else
       vprint Aut2 : "Computing linear representation";  
       // linear (matrix) representation 
       V := Domain(f);  
       assert ISA(Type(V), Mod);
       if Dimension(V) eq 0 then
           return false, false, false, "Dimension of domain is zero";         
       end if;
       S := GL(Dimension(V), BaseRing(V)); 
       gens := [];
       kernel := [];
       X := Basis(V);
       A := [ f(i) : i in X ];
       for i in [1..#auts] do
          vprint Aut2 : "   Computing operation of automorphism ", i, " of ",
   #auts, " on linear space";     
          h := auts[i];     
          B := [ Operation(h, x) : x in A ];
          Y := [];
          for x in B do
             // use of local (and then global) HasPreimage here!
             ok, y := HasPreimage(f, x);
             if not ok then
                return false, false, false, 
                       "Space not invariant under automorphisms";
             end if;   
             Append(~Y, y);
          end for;
          M := Matrix( [ Coordinates(V, y) : y in Y ] );
          assert [ x * M : x in X ] eq Y;
          M := S!M;
          Append(~gens, M);   
          if IsIdentity(M) then
             Append(~kernel, h);
          end if;
       end for;
       vprint Aut2 : "   Done.";
       G := sub< S | Set(gens) >;
       assert #G le #gens;
       assert #auts eq #G * #kernel;  
       vprint Aut2 : "Linking group and function field data ...";  
       E := FunctionFieldCategory();
       preim := function(y)
          if not IsMorphism(E)(y) then
             return false, _;
          end if;
          // quick test
          i := Position(auts, y);
          if i eq 0 then
             // slow test
             for j in [1..#auts] do
                if AreEqualMorphisms(E)(y, auts[j]) then
                    i := j;
                    break;
                end if;
             end for;
          end if;
          if i eq 0 then
             return false, _;
          end if;
          return true, gens[i];
       end function;
       h := hom< G -> Maps(F, F) | x :-> auts[Position(gens, x)],
                 y :-> DoErrorPreimage(preim)(y) >;
       h := ImportMap(h, false);
       h := InstallPreimage(h, preim);       
       vprint Aut2 : "   Done.";
   end if;
   return true, G, h, kernel, "ok";      
end function;
   
   
   
intrinsic Numeration(S::SetEnum) -> Map    
{Returns a numeration of the finite set S}   
   L := SetToSequence(S);
   n := #L;
   X := { 1..n };
   preim := function(y)
      if not y in S then
         return false, _;
      end if;
      return true, Position(L, y);
   end function;
   f := map< X -> S | x :-> L[x], y :-> DoErrorPreimage(preim)(y) >;   
   f := ImportMap(f, false);
   // set unknown inv
   f := InstallPreimage(f, preim);
   return f;  
end intrinsic;  


intrinsic AutomorphismGroup(F::FldFun, f::Map :
                       Strategy := "None") -> Grp, Map, SeqEnum
{Returns a representation of the automorphism group of F fixing the constant field through f}
   /* Test not yet possible in Magma:
   assert IsInjective(f); 
   */
   require Strategy in { "None", "Weierstrass", "DegOne" } :
"Optional argument Strategy must be \"None\", \"Weierstrass\" or \"DegOne\"";
   require IsPerfect(ConstantField(F)) :
      "Constant field must be perfect";
   Cext := FunctionFieldCategory();             
   require IsObject(Cext)(F) :
      SPrintCategory(Cext) cat
      ": First argument is not object in category";
   ok, mess := CheckRepresentingMap(F, f);                             
   require ok : mess;
   ok, G, h, K, mess := MakeRepresentation(F, f, Infinity(), Strategy); 
   require ok : mess;
   return G, h, K;    
end intrinsic;



///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

