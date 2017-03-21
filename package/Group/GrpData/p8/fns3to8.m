freeze;

intrinsic Internal_Single_3_8(i::RngIntElt) -> GrpPC
{ }
    require 1 le i and i le 1396077: "Index not in range";
    
    lengths := 
    [ 1, 58, 486, 1343, 330, 9, 4, 216747, 40521, 2163, 24, 23361, 494666,
     22343, 51, 578478, 14796, 566, 39, 10, 1 ];
    names := [ "rank1class8", "rank2class3", "rank2class4", "rank2class5",
    "rank2class6", "rank2class7", "rank3class2", "rank3class3", "rank3class4",
    "rank3class5", "rank3class6", "rank4class2", "rank4class3", "rank4class4",
    "rank4class5", "rank5class2", "rank5class3", "rank5class4", "rank6class2",
    "rank6class3", "rank7class2", "rank8class1" ];
    dir := GetLibraryRoot() cat "/data/data3to8/";

    base := 0;
    for j := 1 to #lengths do
	n := lengths[j];
	if i le base + n then
	    fn := dir cat names[j];
	    try
		list := eval Read(fn);
	    catch e
		s := Sprintf("\nDatabase file %o not present or not readable.  Please download and install the database from http://magma.maths.usyd.edu.au/magma/download/db/ (file data3to8.tar.gz) if you have not already done so and untar that while the current directory is %o",
		fn, GetLibraryRoot() cat "/data/");
		error s;
	    end try;

	    assert #list eq n;
	    G := SmallGroupDecoding(list[i - base], 6561);
	    return G;
	else
	    base +:= n;
	end if;
    end for;
    assert false;
end intrinsic;
