174,1
S,eq,Return true iff I equals J,0,2,0,0,0,0,0,0,0,65,,0,0,65,,36,-38,-38,-38,-38,-38
S,subset,Return true iff I is a subset of J,0,2,0,0,0,0,0,0,0,65,,0,0,65,,36,-38,-38,-38,-38,-38
S,+,Return the ideal I + J,0,2,0,0,0,0,0,0,0,65,,0,0,65,,65,-38,-38,-38,-38,-38
S,*,Return the ideal I * J,0,2,0,0,0,0,0,0,0,65,,0,0,65,,65,-38,-38,-38,-38,-38
S,ColonIdeal,"Return the colon ideal I:J (or ideal quotient of I by J), consisting of the polynomials f of P such that f * g is in I for all g in J",0,2,0,0,0,0,0,0,0,65,,0,0,65,,65,-38,-38,-38,-38,-38
S,IsProper,Return true iff I is not equal to the whole quotient ring,0,1,0,0,0,0,0,0,0,65,,36,-38,-38,-38,-38,-38
S,IsMaximal,Return true iff I is a maximal ideal,0,1,0,0,0,0,0,0,0,65,,36,-38,-38,-38,-38,-38
S,IsPrimary,Return true iff I is a primary ideal,0,1,0,0,0,0,0,0,0,65,,36,-38,-38,-38,-38,-38
S,IsRadical,True iff the ideal I is radical,0,1,0,0,0,0,0,0,0,65,,36,-38,-38,-38,-38,-38
S,IsZero,Return whether I is the zero ideal,0,1,0,0,0,0,0,0,0,65,,36,-38,-38,-38,-38,-38
S,ChangeRing,"Given an ideal I of a quotient ring P=R[x_1, ..., x_n] / J, where J is an ideal of R[x_1, ..., x_n], with coefficient ring R, together with a ring S, construct the ideal J of the polynomial ring Q=S[x_1, ..., x_n]/J obtained by coercing the coefficients of the elements of the basis of I into S. It is necessary that all elements of the old coefficient ring R can be automatically coerced into the new coefficient ring S",0,2,0,0,0,0,0,0,0,-44,,0,0,65,,65,-38,-38,-38,-38,-38
S,Radical,The radical of I,0,1,0,0,0,0,0,0,0,65,,65,-38,-38,-38,-38,-38
S,PrimaryDecomposition,The primary decomposition of ideal I,0,1,0,0,0,0,0,0,0,65,,82,82,-38,-38,-38,-38
S,RadicalDecomposition,The (prime) decomposition of the radical of I; note that this may be different to the associated primes of I,0,1,0,0,0,0,0,0,0,65,,82,-38,-38,-38,-38,-38
