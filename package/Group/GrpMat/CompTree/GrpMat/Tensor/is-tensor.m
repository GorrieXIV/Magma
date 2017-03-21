freeze;

import "../Smash/numbers.m": FactorList, ProperDivisors;
import "order.m": OrderTest;
import "is-projectivity.m": ProjectivityTest;
import "factorise-poly.m": FactorisePolynomials;
import "local.m": LocalTest;
import "../Smash/functions.m":
    SetTensorProductFlag, TensorProductFlag, SetGenerators, SetTensorBasis,
    SetTensorFactors;


/* tests for tensor product factorisation; if tensor decomposition 
   found, then Status is true and Result is the change of basis matrix */

procedure TensorTest (G, N, ~Status, ~Result, NonNegativeSolution:
                      Factors := [], Fast := false)

   factors := Factors;
   fast := Fast;
   
   Nmr := 20;
   NmrTries := 25;
   NmrSmash := 4;
   NmrProjective := 4;

   d, F := BasicParameters (G);
   q := #F;
   p := Characteristic (F);

   /* possible dimensions of tensor factors */
   if factors eq [] then 
      List := FactorList (d);
   else 
      List := factors;
      List := [x: x in List | &*x eq d];
   end if;
   Exclude (~List, [1, d]);

   vprintf Tensor: "List of dimensions of possible tensor factorisations is %o\n", List;

   if #List eq 0 then Status := false; Result := List; return; end if;

   /* check if the supplied matrices are already Kronecker products */
   for u in ProperDivisors (d) do 
      gens := Generators (G);
      if #gens eq 0 then gens := [Identity (G)]; end if;
      x, y := AreProportional (gens, u);
      if x then Status := true; Result := <Identity (G), u>; return; end if;
   end for;

   OrderTest (G, N, ~List, ~Record, ~Result);
   if Type (Result) ne BoolElt and not (Result cmpeq "unknown") then 
      Status := true; return;  
   end if;

   vprintf Tensor: "\nFinal list after order test is %o\n", List;

   if #List eq 0 then Status := false; Result := List; return; end if;

   /* if we have not called Smash already, then
      Smash some elements of prime order */

   Elts := []; L := Set (&cat (List));
   for i in [1..Minimum (#Record, NmrSmash)] do 
      g := Record[i][1]; o := Record[i][2];
      Status, Result, Elts := ProjectivityTest (G, g, o, Elts, 
                              NmrProjective, L : Exact := factors ne []);
      if Status eq true then return; end if;
      if #Elts ge NmrSmash then break; end if;
   end for;

   vprintf Tensor: "Outstanding is %o\n", List;

   /* examine tensor factorisation of characteristic polynomial */
   FactorisePolynomials (G, N, ~List, ~OutStanding, NonNegativeSolution);

   vprint Tensor: "\nFinal list after polynomial factorisation is ", List;
   vprint Tensor: "Outstanding is ", OutStanding;

   if #List eq 0 then Status := false; Result := List; return; end if;

   /* we may be interested only in a fast test and do not wish
      to invoke local test */
   if fast then Status := "unknown"; Result := List; return; end if; 

   /* outstanding dimensions */
   List := Set (&cat(List));
   vprint Tensor: "\nAt entry to Local, list is ", List;

   /* now carry out local subgroup test */
   LocalTest (G, ~List, ~Result, Nmr, NmrTries: Exact := factors ne []);

   if #List eq 0 then Status := false; Result := []; return; end if;

   if Type (Result) eq MonStgElt then 
      Status := "unknown"; Result := List; return;
   end if;

   if Type (Result) ne BoolElt then 
      Status := true; return;
   end if;
   
   Status := Result; Result := List; 

end procedure;

/* CB is a tuple containing change of basis matrix and the dimension 
   of the geometry found; return the two tensor factors of the group 
   G as matrix groups U and W */

ConstructTensorFactors := function (G, CBTup)

   CB := CBTup[1];
   DimU := CBTup[2];

   F := BaseRing (G);
   gens := [G.i^CB : i in [1..Ngens (G)]];
   if #gens eq 0 then gens := [Identity (G)]; end if;

   flag, Matrices := AreProportional (gens, DimU);

   u := Degree (Matrices[1][1][1]);
   w := Degree (Matrices[1][2][1]);

   matU := [Matrices[i][1] : i in [1..#Matrices]];
   matW := [Matrices[i][2] : i in [1..#Matrices]];
   U := sub <GL (u, F) | matU>;
   W := sub <GL (w, F) | matW>;

   return U, W;

end function;

TensorDimensions := function (G)
   fac := TensorFactors (G);
   u := Degree (Rep (fac[1]));
   w := Degree (Rep (fac[2]));
   return u, w;
end function;

procedure SetTypes (G)

   if TensorProductFlag (G) eq false then return; end if;

   T := TensorFactors (G);
   if Type (T[1]) eq GrpMat then return; end if;
   basis := TensorBasis (G);
   dim1 := Dimension (T[1]); dim2 := Dimension (T[2]);
   d := Degree (G); F := BaseRing (G);
   invbasis := (GL(d, F) ! basis)^-1;
   matrices := Generators (G);
   if AreProportional ([m^invbasis: m in matrices], dim1) then
     Result := <invbasis, dim1>;
   elif AreProportional ([m^invbasis: m in matrices], dim2) then
     Result := <invbasis, dim2>;
   else
     error "Error in Tensor";
   end if;
   SetTensorBasis (G, invbasis);
   U, W := ConstructTensorFactors (G, Result);
   SetTensorFactors (G, [U, W]);
end procedure;

IsTensorMain := function (G, NonNegativeSolution: 
                          Factors := [], Fast := false, RandomElements := 25)

   factors := Factors;
   fast := Fast;
   NmrTries := RandomElements;

   flag := TensorProductFlag (G);

   if Type (flag) cmpeq BoolElt then 
      SetTypes (G);
      return flag;
   end if;

   if Type (G) eq GrpMat then 
      SetGenerators (G, GroupGenerators (G));
   elif Type (G) eq ModGrp then 
      SetGenerators (G, GroupGenerators (Group (G)));
   else 
      error "IsTensor expects a group or a G-module";
   end if;

   d, F := BasicParameters (G);
   vprintf Tensor: "\nDimension = %o F is %o\n", d, F;

   TensorTest (G, NmrTries, ~Status, ~Result, NonNegativeSolution: 
                                      Factors := factors, Fast := fast);

   /* we may have only checked some of the possible factorisations */
   if #factors eq 0 and Status cmpeq false then 
      SetTensorProductFlag (G, false);
   end if;

   if Status cmpeq true then 
      CB := Result[1];
      SetTensorProductFlag (G, true);
      SetTensorBasis (G, CB);
      U, W := ConstructTensorFactors (G, Result);
      SetTensorFactors (G, [U, W]);
   end if;

   return Status;

end function; 

intrinsic IsTensor(G::GrpMat : Factors := [], Fast := false, 
                               RandomElements := 20) -> BoolElt
{Return true if we know G is a tensor product, 
 false if we know that G is not, otherwise "unknown"}
    
    if RecogniseClassical (G) eq true then
       flag := Degree (G) eq 4 and ClassicalType (G) eq "orthogonalplus";
       if flag then RandomElements := Maximum (RandomElements, 200); 
       else return false; end if;
    end if;

    try 
       return IsTensorMain (G, false: Factors := Factors, Fast := Fast, 
                                  RandomElements := RandomElements);
    catch err
       return "unknown";
    end try;
end intrinsic; 

/* 
intrinsic IsTensor(M::ModGrp : Factors := [], Fast := false, 
                               RandomElements := 20) -> BoolElt
{True iff M is a tensor product}
    factors := Factors; fast := Fast; NmrTries := RandomElements;
    return IsTensorMain (M, false: Factors := factors, Fast := fast, 
                                  RandomElements := NmrTries);
end intrinsic; 

*/
