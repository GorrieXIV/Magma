freeze;
////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                   LOCAL QUATERNION IDEAL ARITHMETIC                //
//                          FOR BRANDT MODULES                        //
//                            by David Kohel                          // 
//                                                                    // 
//////////////////////////////////////////////////////////////////////// 

forward HeckeAdjacencyMatrix;

////////////////////////////////////////////////////////////////////////
//                         Accessory Functions                        //
////////////////////////////////////////////////////////////////////////

function RandomElement(A,S)
    return A![ Random(S) : i in [1..4] ];
end function;

procedure ExtendAdjacencyHecke(M,prms)
    if not IsFull(M) then
	X := AmbientModule(M); 
	ExtendAdjacencyHecke(X,prms);
    end if;
    for p in prms do
	if IsFull(M) and p notin M`HeckePrimes then
	    h := Dimension(M);
	    M`HeckeOperators cat:= [ HeckeAdjacencyMatrix(M,p) ];
	    Append(~M`HeckePrimes,p);
	elif p notin M`HeckePrimes then
	    g := Dimension(M);
	    T := X`HeckeOperators[Index(X`HeckePrimes,p)];
	    U := M`Module; B := BasisMatrix(M);
	    Append(~M`HeckeOperators,
	            Matrix([ Coordinates(U,U!(B[i]*T)) : i in [1..g] ]));
	    Append(~M`HeckePrimes,p);
	end if;
    end for;
end procedure;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Isogeny Graphs                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function HeckeAdjacencyMatrix(M,p)
   Ideals := M`LeftIdeals;
   tyme := Cputime();
   Orders := [ RightOrder(I) : I in Ideals ];
   // We have to reduce the number isomorphism tests.
   // So either use Gram matrices or theta series.
   Grams := [ ReducedGramMatrix(O) : O in Orders ];
   h := #Ideals;
   MZ := RSpace(Integers(),2);
   Frontier := [ MZ!P : P in P1Classes(p) ]; 
   FF := FiniteField(p);
   PF := PolynomialRing(FF); X := PF.1;
   vprint Brandt : "Right order computation time:", Cputime(tyme);
   M := MatrixAlgebra(Integers(),h)!0;
   for i in [1..h] do
       I := Ideals[i];
       B := Orders[i];
       error if Level(B) mod p eq 0, "Not implemented when p divides the Eichler level";
       // (since all elements of B have min poly reducible mod p, so x1 cannot be found)
       repeat 
	   x1 := RandomElement(B,[-p div 2..p div 2]);
	   D1 := Trace(x1)^2 - 4*Norm(x1);
       until KroneckerSymbol(D1,p) eq -1;
       repeat
	   x2 := RandomElement(B,[-p div 2..p div 2]);
	   D2 := Trace(x2)^2 - 4*Norm(x2);
       until KroneckerSymbol(D2,p) eq 1;
       a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
       x2 := x2 - a2;
       for Q in Frontier do
	   J := I*LeftIdeal(B,[x2*(B!Q[1] + Q[2]*x1), B!p]);
	   G := ReducedGramMatrix(RightOrder(J));
           j:= 0;
           for k in [1..h] do
               if Grams[k] eq G and IsLeftIsomorphic(Ideals[k],J) then
                   j:= k; break;
               end if;
           end for;
	   error if j eq 0, "Brandt module ideal sequence incomplete.";
	   M[i,j] +:= 1;
       end for;
       vprint Brandt, 2 : "Adjacency ideals computed for i =", i;
   end for;
   return M;
end function;
