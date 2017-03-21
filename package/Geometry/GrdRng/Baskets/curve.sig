174,1
A,GRCrvS,10,d,p,x1,e,N,t,magic,raw,rrb,rrc
S,RawCurve,,0,1,0,0,0,0,0,0,0,501,,502,-38,-38,-38,-38,-38
S,Curve,,0,3,0,0,0,0,0,0,0,267,,0,0,501,,0,0,267,,502,-38,-38,-38,-38,-38
S,Curve,,0,3,0,0,0,0,0,0,0,148,,0,0,501,,0,0,267,,502,-38,-38,-38,-38,-38
S,Curve,"The 3-fold curve singularity C of degree d with transverse type a point singularity p and invariants N_C = N, tau = t (magic = N/t; t = 1 if omitted)",0,4,0,0,0,0,0,0,0,148,,0,0,148,,0,0,501,,0,0,267,,502,-38,-38,-38,-38,-38
S,HackobjPrintGRCrvS,Print the curve singularity C,0,2,0,0,1,0,0,0,0,298,,0,0,502,,-38,-38,-38,-38,-38,-38
S,eq,"True iff the curve singularities C,D are equal (as far as RR is concerned)",0,2,0,0,0,0,0,0,0,502,,0,0,502,,36,-38,-38,-38,-38,-38
S,IsRawCurve,True iff C has essential data missing,0,1,0,0,0,0,0,0,0,502,,36,-38,-38,-38,-38,-38
S,Degree,Degree of the curve singularity C,0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,TransverseIndex,Index of the generic tranverse section of the curve singularity C,0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,TransverseType,Singularity that is the generic tranverse section of the curve singularity C,0,1,0,0,0,0,0,0,0,502,,501,-38,-38,-38,-38,-38
S,NormalNumber,Normal number N_C of the curve singularity C,0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,Index,"The index of the curve singularity C, that is, the invariant tau",0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,MagicNumber,"The rational number N/t of the curve singularity C, where N is the normal number and t is the index of C",0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,Dimension,Dimension of the variety on which the singularity C lies,0,1,0,0,0,0,0,0,0,502,,148,-38,-38,-38,-38,-38
S,IsIsolated,False for a curve singularity C,0,1,0,0,0,0,0,0,0,502,,36,-38,-38,-38,-38,-38
S,IsTerminalThreefold,False for a curve singularity C,0,1,0,0,0,0,0,0,0,502,,36,-38,-38,-38,-38,-38
S,IsCanonical,True iff the curve singularity C is canonical,0,1,0,0,0,0,0,0,0,502,,36,-38,-38,-38,-38,-38
S,FindIndexes,A sequence containing the possible values of the index tau for each curve of B,0,1,0,0,0,0,0,0,0,503,,82,-38,-38,-38,-38,-38
S,ChangeN,,0,2,0,0,0,0,0,0,0,148,,0,0,502,,502,-38,-38,-38,-38,-38
S,ChangeN,Return (or modify C to be) a curve singularity that has the same data as C except that its normal number is set to be N,0,2,0,0,1,0,0,0,0,148,,1,1,502,,-38,-38,-38,-38,-38,-38
S,ChangeN,,0,3,0,0,0,0,0,0,0,148,,0,0,148,,0,0,503,,503,-38,-38,-38,-38,-38
S,ChangeN,Return (or modify B to be) a basket in which the i-th curve singularity has its normal number set to be N,0,3,0,0,1,0,0,0,0,148,,0,0,148,,1,1,503,,-38,-38,-38,-38,-38,-38
