freeze;

/*
  Thsi file contains basic intrinsics for homotopisms (Hmtp).
*/


import "Hom.m" : __GetHomotopism;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Domain( H::Hmtp ) -> TenSpcElt
{Returns the domain of H.}
  return H`Domain;
end intrinsic;

intrinsic Codomain( H::Hmtp ) -> TenSpcElt
{Returns the codomain of H.}
  return H`Codomain;
end intrinsic;

intrinsic Maps( H::Hmtp ) -> List
{Returns the list of maps for H.}
  return H`Maps;
end intrinsic;

intrinsic Kernel( H::Hmtp ) -> TenSpcElt 
{Returns the kernel as a subtensor of the domain of H.}
  dom := Frame(H`Domain);
  cod := Frame(H`Codomain);
  maps := H`Maps;
  v := H`Cat`Valence;
  K_frame := ChangeUniverse([],Parent(H`Domain`Domain[1])); //workaround
  for i in Reverse([0..v]) do
    if i @ H`Cat`Arrows eq 1 then
      try 
        S := Kernel(maps[v-i+1]);
      catch err
        error "Cannot compute the kernel in position",i;
      end try;
    elif i @ H`Cat`Arrows eq -1 then
      try 
        S := Image(maps[v-i+1]);
      catch err
        error "Cannot compute the image in position",i;
      end try;
    else
      S := dom[v-i+1];
    end if;
    Append(~K_frame, S);
  end for;
  F := func< x | x @ H`Domain >;
  return Tensor(K_frame,F,H`Domain`Cat);
end intrinsic;

intrinsic Image( H::Hmtp ) -> TenSpcElt
{Returns the image of H as a subtensor of the codomain of H.}
  dom := Frame(H`Domain);
  cod := Frame(H`Codomain);
  maps := H`Maps;
  v := H`Cat`Valence;
  I_frame := ChangeUniverse([],Parent(H`Domain`Domain[1]));
  for i in Reverse([0..v]) do
    if i @ H`Cat`Arrows eq 1 then
      try 
        S := Image(maps[v-i+1]);
      catch err
        error "Cannot compute the image in position",i;
      end try;
    elif i @ H`Cat`Arrows eq -1 then
      try 
        S := Kernel(maps[v-i+1]);
      catch err
        error "Cannot compute the kernel in position",i;
      end try;
    else
      S := dom[v-i+1];
    end if;
    Append(~I_frame, S);
  end for;
  F := func< x | x @ H`Codomain >;
  return Tensor(I_frame,F,H`Codomain`Cat);
end intrinsic;

intrinsic TensorCategory( H::Hmtp ) -> TenCat
{Returns the tensor category of H.}
  return H`Cat;
end intrinsic;

intrinsic ChangeTensorCategory( H::Hmtp, C::TenCat ) -> Hmtp
{Returns the homotopism with the given category.}
  return __GetHomotopism(H`Domain, H`Codomain, H`Maps : Cat := C );
end intrinsic;

intrinsic ChangeTensorCategory( ~H::Hmtp, C::TenCat )
{Returns the homotopism with the given category.}
  H`Cat := C;
end intrinsic;
