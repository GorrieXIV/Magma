174,1
A,RngDiffOp,3,BaseRing,ConstantRing,PolyRing
A,RngDiffOpElt,2,Parent,Element
S,DifferentialOperatorRing,Defines the ring of differential operators over the differential field F with induced derivation from F,0,1,0,0,0,0,0,0,0,193,,504,-38,-38,-38,-38,-38
S,AssignNames,,1,1,1,82,0,298,2,0,0,1,0,0,0,0,82,,1,1,504,,-38,-38,-38,-38,-38,-38
S,Name,,0,2,0,0,0,0,0,0,0,148,,0,0,504,,-1,-38,-38,-38,-38,-38
S,HackobjCoerceRngDiffOp,,0,2,0,0,0,0,0,0,0,-1,,0,0,504,,36,505,-38,-38,-38,-38
S,.,,0,2,0,0,0,0,0,0,0,148,,0,0,504,,505,-38,-38,-38,-38,-38
S,HackobjPrintRngDiffOp,,0,2,0,0,1,0,0,0,0,298,,0,0,504,,-38,-38,-38,-38,-38,-38
S,HackobjPrintRngDiffOpElt,,0,2,0,0,1,0,0,0,0,298,,0,0,505,,-38,-38,-38,-38,-38,-38
S,HackobjInRngDiffOp,Returns true if x is in R,0,2,0,0,0,0,0,0,0,504,,0,0,-1,,36,-38,-38,-38,-38,-38
S,HackobjParentRngDiffOpElt,,0,1,0,0,0,0,0,0,0,505,,504,-38,-38,-38,-38,-38
S,eq,,0,2,0,0,0,0,0,0,0,504,,0,0,504,,36,-38,-38,-38,-38,-38
S,eq,,0,2,0,0,0,0,0,0,0,505,,0,0,505,,36,-38,-38,-38,-38,-38
S,IsWeaklyEqual,True iff differential operator x is weakly equal to y,0,2,0,0,0,0,0,0,0,505,,0,0,505,,36,-38,-38,-38,-38,-38
S,IsWeaklyZero,True iff differential operator x is weakly equal to 0,0,1,0,0,0,0,0,0,0,505,,36,-38,-38,-38,-38,-38
S,HasProjectiveDerivation,True iff R is defined over a ring with derivation weakly of the form t*d/dt,0,1,0,0,0,0,0,0,0,504,,36,-38,-38,-38,-38,-38
S,HasZeroDerivation,True iff the derivation of R (weakly) acts as zero on the generator of the base ring,0,1,0,0,0,0,0,0,0,504,,36,-38,-38,-38,-38,-38
S,BaseRing,The base ring of R,0,1,0,0,0,0,0,0,0,504,,-44,-38,-38,-38,-38,-38
S,ConstantRing,The constant ring of R,0,1,0,0,0,0,0,0,0,504,,-44,-38,-38,-38,-38,-38
S,Derivation,The derivation of the base ring of R,0,1,0,0,0,0,0,0,0,504,,175,-38,-38,-38,-38,-38
S,Differential,The differential of the base ring to R,0,1,0,0,0,0,0,0,0,504,,56,-38,-38,-38,-38,-38
S,One,The identity element of R,0,1,0,0,0,0,0,0,0,504,,505,-38,-38,-38,-38,-38
S,Zero,The zero element of R,0,1,0,0,0,0,0,0,0,504,,505,-38,-38,-38,-38,-38
S,-,,0,1,0,0,0,0,0,0,0,505,,505,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,-45,,0,0,505,,505,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,505,,0,0,-45,,505,-38,-38,-38,-38,-38
S,-,,0,2,0,0,0,0,0,0,0,505,,0,0,505,,505,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,-45,,0,0,505,,505,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,505,,0,0,-45,,505,-38,-38,-38,-38,-38
S,+,,0,2,0,0,0,0,0,0,0,505,,0,0,505,,505,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,505,,0,0,-45,,505,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,-45,,0,0,505,,505,-38,-38,-38,-38,-38
S,*,,0,2,0,0,0,0,0,0,0,505,,0,0,505,,505,-38,-38,-38,-38,-38
S,^,,0,2,0,0,0,0,0,0,0,148,,0,0,505,,505,-38,-38,-38,-38,-38
S,IsZero,True iff L is the zero operator,0,1,0,0,0,0,0,0,0,505,,36,-38,-38,-38,-38,-38
S,IsOne,True iff L is the identity operator,0,1,0,0,0,0,0,0,0,505,,36,-38,-38,-38,-38,-38
S,IsMonic,True iff L is monic,0,1,0,0,0,0,0,0,0,505,,36,-38,-38,-38,-38,-38
S,IsDifferentialOperatorRing,Tests if the given object is a Ring of Differential Operators,0,1,0,0,0,0,0,0,0,-1,,36,-38,-38,-38,-38,-38
S,TranslationMap,Returns a map on R that replaces R.1 by (R.1+e),0,2,0,0,0,0,0,0,0,-45,,0,0,504,,175,-38,-38,-38,-38,-38
S,LiftMap,"Given the differential map mp : F -> FF on differential fields and a differential operator ring R over F, lift mp to a map on differential operator rings R -> RR. The basefield of RR is FF",0,2,0,0,0,0,0,0,0,504,,0,0,175,,175,-38,-38,-38,-38,-38
S,ChangeDerivation,"Returns a ring R' of differential operators with isomorphic base ring to the one of R, but whose derivation is f*Derivation(R), with f not (weakly equal to) 0. The map is the morphism R<D> -> R'<D'>, induced by D=(1/f)*D'",0,2,0,0,0,0,0,0,0,-45,,0,0,504,,504,175,-38,-38,-38,-38
S,ChangeDifferential,"Returns the differential operator ring with differential df, and whose underlying ring of its basefield coincides with the one of R. The map returned is the bijective map of R into the new operator ring",0,2,0,0,0,0,0,0,0,56,,0,0,504,,504,175,-38,-38,-38,-38
S,ConstantFieldExtension,"Returns the ring of differential operators with base ring isomorphic to the one of R, but whose constant field is Cext. The derivation is extended over the new constant field",0,2,0,0,0,0,0,0,0,-24,,0,0,504,,504,175,-38,-38,-38,-38
S,Localization,"Returns the operator ring whose differential has valuation -1 at pl, with derivation t *d/dt, where t is the uniformizing element at the place. Also the map between the operator rings, and the induced image of pl is returned",0,2,0,0,0,0,0,0,0,230,,0,0,504,,504,175,230,-38,-38,-38
S,Localization,"Given a differential operator ring over a the differential Laurent series ring C((t)), returns the operator ring whose derivation is of the form t*d/dt, and the and map between the operator rings",0,1,0,0,0,0,0,0,0,504,,504,175,-38,-38,-38,-38
S,Coefficients,"The coefficients of L, put in a sequence",0,1,0,0,0,0,0,0,0,505,,82,-38,-38,-38,-38,-38
S,Eltseq,"The coefficients of L, put in a sequence",0,1,0,0,0,0,0,0,0,505,,82,-38,-38,-38,-38,-38
S,Terms,The sequence of non-zero terms of L,0,1,0,0,0,0,0,0,0,505,,82,-38,-38,-38,-38,-38
S,Degree,The order of the differential operator L,0,1,0,0,0,0,0,0,0,505,,148,-38,-38,-38,-38,-38
S,Order,The order of the differential operator L,0,1,0,0,0,0,0,0,0,505,,148,-38,-38,-38,-38,-38
S,Coefficient,"The coefficient of D^i in L, where D is the derivation associated with L",0,2,0,0,0,0,0,0,0,148,,0,0,505,,-45,-38,-38,-38,-38,-38
S,LeadingCoefficient,The coefficient of the highest power of the derivation in L,0,1,0,0,0,0,0,0,0,505,,-45,-38,-38,-38,-38,-38
S,LeadingTerm,The leading term of L,0,1,0,0,0,0,0,0,0,505,,505,-38,-38,-38,-38,-38
S,IsWeaklyMonic,"If L is defined over a differential series ring, then returned is true iff the leading coefficient of the operator is weakly equal to 1",0,1,0,0,0,0,0,0,0,505,,36,-38,-38,-38,-38,-38
S,WeakOrder,"If L is defined over a differential series ring, then returned is the highest exponent in L, whose coefficient is not weakly equal to 0",0,1,0,0,0,0,0,0,0,505,,148,-38,-38,-38,-38,-38
S,WeakDegree,"If L is defined over a differential series ring, then returned is the highest exponent in L, whose coefficient is not weakly equal to 0",0,1,0,0,0,0,0,0,0,505,,148,-38,-38,-38,-38,-38
S,TruncateCoefficients,"If L is defined over a differential series ring, then returned is the operator whose coefficients are the truncations of the coefficients of L",0,1,0,0,0,0,0,0,0,505,,505,-38,-38,-38,-38,-38
S,MonicDifferentialOperator,"Returns the monic operator (1/LeadingCoefficient(L))*L for non-zero L. If L is 0, then it returns L",0,1,0,0,0,0,0,0,0,505,,505,-38,-38,-38,-38,-38
S,Adjoint,The formal adjoint differential operator of L,0,1,0,0,0,0,0,0,0,505,,505,-38,-38,-38,-38,-38
S,Apply,Apply the differential operator L to the function f,0,2,0,0,0,0,0,0,0,-45,,0,0,505,,-45,-38,-38,-38,-38,-38
S,@,Apply the differential operator L to the function f,0,2,0,0,0,0,0,0,0,505,,0,0,-45,,-45,-38,-38,-38,-38,-38
S,Translation,Replaces R.1 by (R.1+e) if L is an operator in R. The translation map on R is returned as a second argument,0,2,0,0,0,0,0,0,0,-45,,0,0,505,,505,175,-38,-38,-38,-38
S,Localization,"Returns the localized operator of L, and the embeddings map between the parents as well as the induced image of the place",0,2,0,0,0,0,0,0,0,230,,0,0,505,,505,175,230,-38,-38,-38
S,Localization,"Returns the localized operator of L, and the embeddings map between the parents",0,1,0,0,0,0,0,0,0,505,,505,175,-38,-38,-38,-38
S,CompanionMatrix,The companion matrix of the monic differential operator L,0,1,0,0,0,0,0,0,0,505,,177,-38,-38,-38,-38,-38
S,DifferentialRingExtension,"Constructs a differential ring extension of the differential ring F=BaseRing(L), by adding a formal solution of L and its derivatives",0,1,0,0,0,0,0,0,0,505,,193,-38,-38,-38,-38,-38
S,DifferentialFieldExtension,"Constructs a differential field extension of the differential field F=BaseRing(L), by adding a formal solution of L and its derivatives",0,1,0,0,0,0,0,0,0,505,,193,-38,-38,-38,-38,-38
S,SymmetricPower,The m-th symmetric power of L,0,2,0,0,0,0,0,0,0,148,,0,0,505,,505,-38,-38,-38,-38,-38
S,DifferentialOperator,The minimal differential operator to which roots of the irreducible polynomial f are solutions,0,1,0,0,0,0,0,0,0,312,,505,-38,-38,-38,-38,-38
