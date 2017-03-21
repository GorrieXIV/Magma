freeze;
 
intrinsic MonodromyWeights(M::ModBrdt) -> SeqEnum
    {}
    return [ e div 2 : e in M`AutoNums ];
end intrinsic;
