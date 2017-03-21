174,1
S,Subcode,Returns a subcode of the (possibly additive) code C with k generators. k must be a non negative integer less than or equal to the number of generators of C,0,2,0,0,0,0,0,0,0,148,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,Subcode,"Returns the subcode of the (possibly additive) code C generated by the basis elements numbered in S, which must contain positive integers less than or equal to Ngens(C)",1,1,1,83,0,148,2,0,0,0,0,0,0,0,83,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,SubcodeWordsOfWeight,"Given a non negative integer S less than Length(C), return the subcode generated by those words of C with weight W. If NumWords is set to a non-zero positive integer then the number of words used will be limited to NumWords",0,2,0,0,0,0,0,0,0,148,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,SubcodeWordsOfWeight,"Given a set of non-negative integers S, each less than Length(C), return the subcode generated by those words of C whose weights lie in S If NumWords is set to a non-zero positive integer then the number of words used of each weight will be limited to NumWords",1,1,1,83,0,148,2,0,0,0,0,0,0,0,83,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,Juxtaposition,"Given codes C1=[n1,k,d1] and C2=[n2,k,d2], construct a [n1+n2,k,d>=d1+d2] code by pasting the generator matrix together",0,2,0,0,0,0,0,0,0,-39,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,ResidueCode,Take the residue of code C by puncturing at the support of a minimum word,0,1,0,0,0,0,0,0,0,-39,,-39,-38,-38,-38,-38,-38
S,ConstructionX,"Given a code C1=[n,k,d], a subcode C2=[n,k-l,d+e], and a code C3=[a,l,e], construct a code C=[n+a,k,d+e]",0,3,0,0,0,0,0,0,0,42,,0,0,42,,0,0,42,,42,-38,-38,-38,-38,-38
S,ConstructionX3,"Given a chain of codes C1=[n,k1,d1], C2=[n,k2,d2], and C3=[n,k3,d3] with k3 < k2 < k1, and suffix codes D1=[n1,k1-k2,e1] and D2=[n2,k2-k3,e2], construct a code C=[n+n1+n2,k1,d] with d >= min{d3,d1+e1,d2+e2.}",0,5,0,0,0,0,0,0,0,42,,0,0,42,,0,0,42,,0,0,42,,0,0,42,,42,-38,-38,-38,-38,-38
S,ConstructionXX,"C2 and C3 must be subcodes of C1, while the dimensions of D2 and D3 must add with the dimensions to C2 and C3 to give the dimension of C1. The returned code is constructed via the constructionXX algorithm of Alltop",0,5,0,0,0,0,0,0,0,42,,0,0,42,,0,0,42,,0,0,42,,0,0,42,,42,-38,-38,-38,-38,-38
S,ZinovievCode,Construct a generalized concatenated code from the given sequences of inner and outer codes,2,0,1,82,0,42,1,1,82,0,42,2,0,0,0,0,0,0,0,82,,0,0,82,,42,-38,-38,-38,-38,-38
S,ConstructionY1,"Given a binary linear [n,k,d] code C with dual distance d',return the [n-d',k-d'+1,>=d] code obtained by shortening in the positions of a word in Dual(C) of minimal weight",0,1,0,0,0,0,0,0,0,-39,,-39,-38,-38,-38,-38,-38
S,ConstructionY1,"Shorten the linear code C at the support of a word of weight w of the dual code, resulting in an [n-w,k-w+1,>=d] code",0,2,0,0,0,0,0,0,0,148,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,ExpurgateCode,The code obtained by deleting the code words contained in the sequence L from C,1,1,1,82,0,160,2,0,0,0,0,0,0,0,82,,0,0,42,,-39,-38,-38,-38,-38,-38
S,ExpurgateWeightCode,Delete a subspace generated by a word of weight w,0,2,0,0,0,0,0,0,0,148,,0,0,42,,-39,-38,-38,-38,-38,-38
S,ExtendCode,Extend C n times,0,2,0,0,0,0,0,0,0,148,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,PadCode,"Given a linear code, lengthen it by n positions (adding columns of zeros)",0,2,0,0,0,0,0,0,0,148,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,SubfieldCode,"If C is a code over F, then each element of F is mapped into a column vector over K. Returned is the code generated when each codeword of C is mapped into multiple codewords over K in this way",0,2,0,0,0,0,0,0,0,84,,0,0,42,,-39,-38,-38,-38,-38,-38
S,SubfieldRepresentationParityCode,"Given a linear code over GF(q^m), return a code whose codewords are obtained from those of C by expanding each coordinate in GF(q^m) as a vector of dimension m+1 over K := GF(q), including a parity check bit",0,2,0,0,0,0,0,0,0,84,,0,0,42,,42,-38,-38,-38,-38,-38
S,cat,Return the code concatenation of codes C1 and C2 (over the same field),0,2,0,0,0,0,0,0,0,-39,,0,0,-39,,-39,-38,-38,-38,-38,-38
S,SubfieldRepresentationCode,"Given a linear code over GF(q^m), return a code whose codewords are obtained from those of C by expanding each coordinate in GF(q^m) as a vector of dimension m over K := GF(q)",0,2,0,0,0,0,0,0,0,84,,0,0,42,,42,-38,-38,-38,-38,-38
S,ConcatenatedCode,"Create the [Nn,Kk,delta >= dD] concatenated code associated with the Outer [N,K,D]-code over GF(q^k) and the Inner [n,k,d]-code over GF(q) (where q is arbitrary)",0,2,0,0,0,0,0,0,0,42,,0,0,42,,42,-38,-38,-38,-38,-38
S,DirectSum,The direct sum of the codes in the sequence Q,1,0,1,82,0,-39,1,0,0,0,0,0,0,0,82,,-39,-38,-38,-38,-38,-38
S,AdditivePermutationCode,"The additive code corresponding to the K-span by the set of vectors obtained by applying the permutations of G to the vector u, which is a tuple over some extension field of K",0,3,0,0,0,0,0,0,0,224,,0,0,160,,0,0,84,,407,-38,-38,-38,-38,-38