////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   QUADRATIC ORDERS AND INVARIANTS                  //
//                      OF BINARY QUADRATIC FORMS                     //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

freeze;

intrinsic QuadraticOrder(Q::QuadBin) -> RngQuad
    {The order in a quadratic number field of the same discriminant as Q.}
    return Order(Ideal(Q!1));
end intrinsic;

intrinsic Regulator(Q::QuadBin) -> FldReElt
    {The regulator of the quadratic order associated to Q, where
    Q is of positive discriminant.}
    require Discriminant(Q) gt 0 :
        "Argument must have positive discriminant.";
    return Regulator(QuadraticOrder(Q));
end intrinsic;


