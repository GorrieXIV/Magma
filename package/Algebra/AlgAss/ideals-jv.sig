174,1
A,RngOrd,1,TotallyPositiveUnits
S,IsNarrowlyPrincipal,"Given an ideal I in a totally real number field, returns true iff I is principal with a totally positive generator (and also returns the generator in that case)",0,1,0,0,0,0,0,0,0,324,,36,323,-38,-38,-38,-38
S,IsTwoSidedIdeal,Returns true iff I is equipped with the structure of a two-sided ideal,0,1,0,0,0,0,0,0,0,437,,36,-38,-38,-38,-38,-38
S,Algebra,Returns the container algebra,0,1,0,0,0,0,0,0,0,437,,-60,-38,-38,-38,-38,-38
S,Conjugate,Returns the conjugate of I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,437,-38,-38,-38,-38,-38
S,LeftInverse,Returns the inverse (fractional) ideal to I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,437,-38,-38,-38,-38,-38
S,RightInverse,Returns the inverse (fractional) ideal to I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,437,-38,-38,-38,-38,-38
S,PseudoBasis,Returns a pseudobasis of I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,82,-38,-38,-38,-38,-38
S,PseudoBasis,Returns a pseudo basis for I over R,1,0,1,437,0,215,2,0,0,0,0,0,0,0,-54,,0,0,437,,82,-38,-38,-38,-38,-38
S,PseudoMatrix,Returns a pseudomatrix for I with respect to the basis of R,1,0,1,437,0,215,2,0,0,0,0,0,0,0,-54,,0,0,437,,438,-38,-38,-38,-38,-38
S,Norm,The norm of the ideal I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,324,-38,-38,-38,-38,-38
S,IsIntegral,Returns true iff x is integral,0,1,0,0,0,0,0,0,0,238,,36,-38,-38,-38,-38,-38
S,in,Return true iff a is in I. Here I must be an ideal (or fractional ideal) of an order in an associative algebra,0,2,0,0,0,0,0,0,0,437,,0,0,-45,,36,-38,-38,-38,-38,-38
S,subset,Return true if I is a subset of J,0,2,0,0,0,0,0,0,0,437,,0,0,437,,36,-38,-38,-38,-38,-38
S,RandomRightIdeal,Returns a random (small coefficient) right ideal of O,0,1,0,0,0,0,0,0,0,435,,437,-38,-38,-38,-38,-38
S,/,Returns the quotient I*(1/x),1,0,1,437,0,215,2,0,0,0,0,0,0,0,-45,,0,0,437,,437,-38,-38,-38,-38,-38
S,*,"Product of ideals I and J. Returns two objects by default: firstly I*J as a left ideal, and secondly I*J as a right ideal. When ""Sides"" is set to ""Left"" or ""Right"", only one of these is returned",2,0,1,437,0,215,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,437,,437,437,-38,-38,-38,-38
S,*,Product of (fractional) ideals of an order in an associative algebra,1,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,-45,,437,-38,-38,-38,-38,-38
S,*,Product of (fractional) ideals of an order in an associative algebra,1,0,1,437,0,215,2,0,0,0,0,0,0,0,-45,,0,0,437,,437,-38,-38,-38,-38,-38
S,IsCentral,True iff the element a of an associative algebra A belongs to the center of A,0,1,0,0,0,0,0,0,0,-61,,36,-38,-38,-38,-38,-38
S,IsCentral,True iff the element a of an associative order O belongs to the center of O,0,1,0,0,0,0,0,0,0,436,,36,-38,-38,-38,-38,-38
S,Colon,"Returns the colon (I:J), defined as the set of x in A such that x*J is contained in I, where I and J are both left (or right) ideals of the same order O. The output is a pseudomatrix with respect to the parent algebra A",2,0,1,437,0,215,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,437,,438,-38,-38,-38,-38,-38
S,LeftOrder,The left multiplicator order of I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,435,-38,-38,-38,-38,-38
S,RightOrder,The right multiplicator order of I,1,0,1,437,0,215,1,0,0,0,0,0,0,0,437,,435,-38,-38,-38,-38,-38
S,MultiplicatorRing,Returns the Side-multiplicator ring of I,0,1,0,0,0,0,0,0,0,437,,435,-38,-38,-38,-38,-38
S,IsLeftIsomorphic,"Returns true iff I,J are isomorphic left ideals",2,0,1,437,0,215,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,437,,36,18,-38,-38,-38,-38
S,IsRightIsomorphic,"Returns true iff I,J are isomorphic right ideals",2,0,1,437,0,215,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,437,,36,18,-38,-38,-38,-38
S,IsIsomorphic,"Returns true iff I,J are isomorphic (left or right) ideals (ie, whether I and J are in the same left or right ideal class), and if so, also returns an element x such that J = x*I (or I*x)",2,0,1,437,0,215,1,1,437,0,215,2,0,0,0,0,0,0,0,437,,0,0,437,,36,18,-38,-38,-38,-38
S,IsPrincipal,"Returns true iff I is a principal (left or right) ideal, and a generator",0,1,0,0,0,0,0,0,0,437,,36,18,-38,-38,-38,-38
S,ClassGroupPrimeRepresentatives,"Returns a map of sets from Cl(Z_F) to prime ideals of Z_F, prime to dd",0,2,0,0,0,0,0,0,0,217,,0,0,215,,175,-38,-38,-38,-38,-38
S,ClassGroupPrimeRepresentatives,"Returns a map of sets from Cl^S(Z_F) to prime ideals of Z_F, prime to dd, where S is a set of infinite places",1,2,1,82,0,332,3,0,0,0,0,0,0,0,82,,0,0,217,,0,0,215,,175,-38,-38,-38,-38,-38
S,LeftIdealClasses,Returns a sequence of representatives of the left ideal classes of O,1,0,1,435,1,215,0,319,1,0,0,0,0,0,0,0,435,,82,-38,-38,-38,-38,-38
S,RightIdealClasses,"Returns a sequence of representatives of the right ideal classes of O with support in the prime ideals in Support, if given",1,0,1,435,1,215,0,319,1,0,0,0,0,0,0,0,435,,82,82,-38,-38,-38,-38
S,Coordinates,"The coordinates of the sequence S of elements in an associative algebra A, relative to the given basis of A over the rationals",2,0,1,82,1,-61,0,27,1,1,82,1,-61,0,27,2,0,0,0,0,0,0,0,82,,0,0,82,,82,-38,-38,-38,-38,-38
