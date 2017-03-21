freeze;
 
///////////////////////////////////////////////////////////////////////
//			Fano database
// GB Oct 2003
///////////////////////////////////////////////////////////////////////

import "../HilbertSeries/misc.m": is_subseq;
import "../Fano/fanohilb.m": fano_degree, fano_hilbert_series;

forward
	compute_RR,
	sort_hilb_data,
	build_fanos;

intrinsic CreateFanoData(f::RngIntElt,r::RngIntElt:Bogomolov:=true) -> SeqEnum
{Construct a sequence of Fano 3-folds of Fano index f and Kawamata
index sum at most r}
    require f ge 3: "This creation intrinsic needs f ge 3";
	tt := Cputime();
	vprintf User1: "Time %o: computing baskets\n",Cputime(tt);
    r +:= 1;
    B := FanoBaskets(r,f);
    if #B eq 0 then
	return [];
    end if;
	vprintf User1: "Time %o: computing RR for %o baskets\n",Cputime(tt),#B;
    DD0 := compute_RR(f,B);
    DD := sort_hilb_data(DD0);
    bool := &and[ IsDefined(DD,i) : i in [1..#DD0] ];
    require bool: "insufficient precision in the Hilbert series";
	vprintf User1: "Time %o: building the Fanos\n",Cputime(tt);
    KK := build_fanos(DD,f);
	vprintf User1: "Time %o: building complete.\n",Cputime(tt);
    if Bogomolov then
	KK := [ X : X in KK | not IsBogomolovUnstable(X) ];
    end if;
    return KK;
end intrinsic;


/////////////////////////////////////////////////////////////////////

function compute_RR(f,BB)
    DD0 := [ ];
    S := PowerSeriesRing(Rationals(),21);
    for B in BB do
    	d := fano_degree(f,B);
	h := fano_hilbert_series(f,B);
	H := Coefficients(S!h);
	Append(~DD0,<f,B,Rationals()!d,h,H>);
    end for;
    return DD0;
end function;


function sort_hilb_data(DD0)
    HH := [ d[5] : d in DD0 ];
    Sort(~HH);
    DD := [ ];
    for n in [1..#DD0] do
	D := DD0[n];
	i := Index(HH,D[5]);
    	DD[i] := Append(D,i);
    end for;
    return DD;
end function;


function build_fanos(DD,f)
    Fanos := [];
    for i in [1..#DD] do
	D := DD[i];
	X := HackobjCreateRaw(GRFano);
	X`genus := D[1];
	X`basket := D[2];
	X`degree := D[3];
	X`hilbert := D[4];
	X`coeffs := D[5];
	X`fanoindex := f;
	X`dim := 3;

	W := FindFirstGenerators(X`hilbert : Precision:=100);
	X`firstw := W;
	_,W := CheckBasket(X`basket,W);
	Sort(~W);
	X`weights := W;

	Append(~Fanos,X);
    end for;
    return Fanos;
end function;

