freeze;

/* 
 * Dan Roozemond, 2010. 
 */

ChevBasDataFormat := recformat<
	R : RootDtm,
	L : AlgLie,
	H : AlgLie,
	F,

	char : RngIntElt,
	NRoots : RngIntElt,
	
	EigenSpaces : SeqEnum,
	EigenVectors : SeqEnum,
	SCSAVectors : SeqEnum,
	
	PosNegPairs : SetEnum,
	CartInts : Mtrx,
	Degs: SeqEnum,
	
	IndFundSet : SetEnum, /* A set */

	IndFund : SeqEnum, /* Here we start identifying, so sequences */
	IndRts : SeqEnum,

	IndLong : SetEnum,	/* For characteristic 2 stuff */
	IndShort : SetEnum,
	PosNegPairsLong : SetEnum,
	PosNegPairsShort : SetEnum,

	ExtraspecialSigns : SeqEnum,
	RequiredNrs : Mtrx,

	BasisPos : SeqEnum,
	BasisNeg : SeqEnum,
	BasisCart : SeqEnum
>;

function NewChevBasData(R, L, H)
	return rec<ChevBasDataFormat | 
		R := R, 
		L := L, 
		H := H,
		F := BaseRing(L),
		char := Characteristic(BaseRing(L)),
		NRoots := 2*NumPosRoots(R),
		ExtraspecialSigns := [ <a[1],a[2],1> : a in ExtraspecialPairs(R) ]
	>;
end function;

function ChangeRingCBD(CBDin, F)
	local CBD,Lin,Hin,changeseqvec,changeseqL;

	CBD := CBDin;

	CBD`L := ChangeRing(CBD`L, F);
	CBD`H := sub<CBD`L | [ CBD`L!ChangeRing(Vector((CBDin`L)!x), F) 
		: x in Basis(CBDin`H) ]>;
	CBD`F := F;

	CBD`char := Characteristic(F);

	changeseqvec := procedure(~Q)
		Q := [ Vector(ChangeRing(q,F)) : q in Q ];
	end procedure;
	changeseqL := procedure(~Q)
		Q := [ CBD`L!(Vector(ChangeRing(q,F))) : q in Q ];
	end procedure;

	if assigned CBD`EigenSpaces then changeseqL(~(CBD`EigenSpaces)); end if;
	if assigned CBD`EigenVectors then changeseqvec(~(CBD`EigenVectors)); end if;
	if assigned CBD`SCSAVectors then changeseqL(~(CBD`SCSAVectors)); end if;

	if assigned CBD`BasisPos then changeseqL(~(CBD`BasisPos)); end if;
	if assigned CBD`BasisNeg then changeseqL(~(CBD`BasisNeg)); end if;
	if assigned CBD`BasisCart then changeseqL(~(CBD`BasisCart)); end if;

	return CBD;
end function;
