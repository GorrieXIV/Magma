174,1
V,DiffRng,1
A,RngDiff,4,Generators,URGenerators,IsDifferentialLSR,BaseRingDiffLSRExtension
S,DifferentialRing,The ring R with derivation D and constant ring C,0,3,0,0,0,0,0,0,0,-44,,0,0,175,,0,0,-44,,193,-38,-38,-38,-38,-38
S,RationalDifferentialField,"Creates the algebraic differential field in one variable over the constant field C, with differential (1) d ($.1)",0,1,0,0,0,0,0,0,0,-44,,193,-38,-38,-38,-38,-38
S,DifferentialLaurentSeriesRing,"Creates the differential ring of the form F=C((t)), with derivation t*d/dt",0,1,0,0,0,0,0,0,0,-24,,193,-38,-38,-38,-38,-38
S,AssignNames,,1,1,1,82,0,298,2,0,0,1,0,0,0,0,82,,1,1,193,,-38,-38,-38,-38,-38,-38
S,IsAlgebraicDifferentialField,,0,1,0,0,0,0,0,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsDifferentialField,,0,1,0,0,0,0,0,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsDifferentialRing,,0,1,0,0,0,0,0,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsDifferentialSeriesRing,,0,1,0,0,0,0,0,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsDifferentialLaurentSeriesRing,,0,1,0,0,0,0,0,0,0,-44,,36,-38,-38,-38,-38,-38
S,IsDifferentialRingElement,,0,1,0,0,0,0,0,0,0,-45,,36,-38,-38,-38,-38,-38
S,IsOrderTerm,True iff x is an order term in a differential series ring,0,1,0,0,0,0,0,0,0,194,,36,-38,-38,-38,-38,-38
S,HasProjectiveDerivation,True iff F is a differential ring with derivation weakly of the form t*d/dt,0,1,0,0,0,0,0,0,0,193,,36,-38,-38,-38,-38,-38
S,HasZeroDerivation,True iff the algebraic differential field or differential series ring F has (weak) zero derivation,0,1,0,0,0,0,0,0,0,193,,36,-38,-38,-38,-38,-38
S,Differential,The differential assigned to L,0,1,0,0,0,0,0,0,0,193,,56,-38,-38,-38,-38,-38
S,BaseRing,,0,1,0,0,0,0,0,0,0,193,,-44,-38,-38,-38,-38,-38
S,BaseField,,0,1,0,0,0,0,0,0,0,193,,-44,-38,-38,-38,-38,-38
S,ConstantRing,,0,1,0,0,0,0,0,0,0,193,,-44,-38,-38,-38,-38,-38
S,ConstantField,,0,1,0,0,0,0,0,0,0,193,,-24,-38,-38,-38,-38,-38
S,UnderlyingRing,The underlying ring of L,0,1,0,0,0,0,0,0,0,193,,-44,-38,-38,-38,-38,-38
S,UnderlyingField,The underlying field of L,0,1,0,0,0,0,0,0,0,193,,-24,-38,-38,-38,-38,-38
S,Derivation,The derivation of L,0,1,0,0,0,0,0,0,0,193,,175,-38,-38,-38,-38,-38
S,Derivative,"The derivation of the parent of x, applied to x",0,1,0,0,0,0,0,0,0,194,,194,-38,-38,-38,-38,-38
S,Generators,"The list of generators of F. If there is no list assigned to F, one is constructed by default from the UnderlyingRing(F)",0,1,0,0,0,0,0,0,0,193,,82,-38,-38,-38,-38,-38
S,Ngens,,0,1,0,0,0,0,0,0,0,193,,148,-38,-38,-38,-38,-38
S,.,,0,2,0,0,0,0,0,0,0,148,,0,0,193,,194,-38,-38,-38,-38,-38
S,Name,,0,2,0,0,0,0,0,0,0,148,,0,0,193,,194,-38,-38,-38,-38,-38
S,^,,0,2,0,0,0,0,0,0,0,148,,0,0,194,,194,-38,-38,-38,-38,-38
S,div,,0,2,0,0,0,0,0,0,0,194,,0,0,194,,194,-38,-38,-38,-38,-38
S,/,,0,2,0,0,0,0,0,0,0,194,,0,0,194,,194,-38,-38,-38,-38,-38
S,ChangeDerivation,"Returns a differential field field isomorphic to F, but whose derivation is f*Derivation(F), with f not (weakly equal to) 0. The map is the isomorphism of F to the new field",0,2,0,0,0,0,0,0,0,-45,,0,0,193,,193,175,-38,-38,-38,-38
S,ChangeDifferential,"Returns the algebraic differential field, whose underlying ring is the one of F, but with differential df. The map returned is the bijective map of F into the new algebraic differential field",0,2,0,0,0,0,0,0,0,56,,0,0,193,,193,175,-38,-38,-38,-38
S,ChangePrecision,Returns a differential series ring isomorphic to F with relative precision p. The map returned is the induced map of F to the new field,0,2,0,0,0,0,0,0,0,-45,,0,0,193,,193,175,-38,-38,-38,-38
S,ConstantFieldExtension,"Returns the field having the same structure as F, but whose constant field is the extension Cext of the constant field of F",0,2,0,0,0,0,0,0,0,-24,,0,0,193,,193,175,-38,-38,-38,-38
S,Differential,"Returns the differential of an element in the algebraic differential field F, as a differential in the differential space of the underlying ring of F",0,1,0,0,0,0,0,0,0,194,,5,-38,-38,-38,-38,-38
S,Eltseq,"Returns the coefficients over K, K must occur as a coefficient field",0,1,0,0,0,0,0,0,0,194,,82,-38,-38,-38,-38,-38
S,MinimalPolynomial,The minimal polynomial of the field element a over the coefficient field,0,1,0,0,0,0,0,0,0,194,,312,-38,-38,-38,-38,-38
S,O,Returns O(x),0,1,0,0,0,0,0,0,0,194,,194,-38,-38,-38,-38,-38
S,Truncate,The known part of the differential series x,0,1,0,0,0,0,0,0,0,194,,194,-38,-38,-38,-38,-38
S,Exponents,The interval from the valuation of x to (including) the degree of x,0,1,0,0,0,0,0,0,0,194,,82,-38,-38,-38,-38,-38
S,WronskianMatrix,"The Wronskian matrix of S=[y1,y2,...yn] over R",1,0,1,82,0,194,1,0,0,0,0,0,0,0,82,,177,-38,-38,-38,-38,-38
S,WronskianDeterminant,"The determinant of the Wronskian matrix of S=[y1,y2,...yn] over R and the Wronskian matrix itself",1,0,1,82,0,194,1,0,0,0,0,0,0,0,82,,194,177,-38,-38,-38,-38
S,ExactConstantField,"The field of constants of the algebraic differential field F, together with the inclusion map to F",0,1,0,0,0,0,0,0,0,193,,-24,175,-38,-38,-38,-38
S,SeparatingElement,Returns the separating element of the algebraic differential field F,0,1,0,0,0,0,0,0,0,193,,194,-38,-38,-38,-38,-38
S,DifferentialRingExtension,"The differential ring extension A = Universe(L) with deriv(A.i)=A!L[i], of the differential BaseRing of Universe(L)",1,0,1,82,0,63,1,0,0,0,0,0,0,0,82,,193,-38,-38,-38,-38,-38
S,DifferentialFieldExtension,"The differential field extension A=Q(Universe(L)) with deriv(A.i)=A!L[i], of the differential BaseRing of Universe(L)",1,0,1,82,0,63,1,0,0,0,0,0,0,0,82,,193,-38,-38,-38,-38,-38
S,ExponentialFieldExtension,"Creates a differential extension F(E) of the field F, where E satisfies Derivation(E)=f*E",0,2,0,0,0,0,0,0,0,194,,0,0,193,,193,-38,-38,-38,-38,-38
S,LogarithmicFieldExtension,"Creates a differential extension F(L) of the field F, where L satisfies Derivation(L)=f",0,2,0,0,0,0,0,0,0,194,,0,0,193,,193,-38,-38,-38,-38,-38
S,IsDifferentialIdeal,True iff I can be coerced as a differential ideal of R,0,2,0,0,0,0,0,0,0,64,,0,0,193,,36,-38,-38,-38,-38,-38
S,DifferentialIdeal,Returns the differential ideal I generated by L as an ideal of the underlying ring of Universe(L),1,0,1,82,0,194,1,0,0,0,0,0,0,0,82,,64,-38,-38,-38,-38,-38
S,QuotientRing,"The differential quotient ring QR=R/I with deriv(QR.i)=QR!(deriv(R[i])), together with the induced quotient map R -> QR",0,2,0,0,0,0,0,0,0,64,,0,0,193,,193,175,-38,-38,-38,-38
S,FieldOfFractions,"The differential field of fractions of R, together with the inclusion map of R in the field",0,1,0,0,0,0,0,0,0,193,,193,175,-38,-38,-38,-38
S,RingOfFractions,"The differential ring R[r^(-1): r in R is invertible] of fractions of R, together with the inclusion map",0,1,0,0,0,0,0,0,0,193,,193,175,-38,-38,-38,-38
