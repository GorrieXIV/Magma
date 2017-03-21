freeze;
///////////////////////////////////////////////////////////////////
//     Basic functions for Small Modular Curves                  //
//                                                               //
//             mch - 11/2011                                     //
///////////////////////////////////////////////////////////////////

//import "db_io.m": X0NData;

intrinsic SmallModularCurve(N::RngIntElt) -> Crv
{ Returns the model over Q for the X0N modular curve of level N from the small
  modular curve database }

    require N gt 0 : "Level N should be a positive integer";
    try
      X0Nd := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    return X0Nd`X0N;

end intrinsic;

intrinsic SmallModularCurve(N::RngIntElt, K::Rng) -> Crv
{ Returns the model over Q for the X0N modular curve of level N from the small
  modular curve database }

    require N gt 0 : "Level N should be a positive integer";
    require IsField(K) and (Characteristic(K) eq 0):
	"Currently, the second argument should be a characteristic 0 field";
    try
      X0Nd := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    return BaseChange(X0Nd`X0N,K);

end intrinsic;
