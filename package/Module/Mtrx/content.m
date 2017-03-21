freeze;

intrinsic RemoveRowContents(~X::Mtrx, ~G)
{Remove contents from rows of X; set G to the contents}
    V := RSpace(BaseRing(X), Ncols(X));
    G := [BaseRing(X) | ];
    for i := 1 to Nrows(X) do
        e := Eltseq(X[i]);
        g := GCD(e);
        Append(~G, g);
        if g gt 1 then
            e := [x div g: x in e];
            X[i] := V ! e;
        end if;
    end for;
end intrinsic;

intrinsic RemoveRowContents(~X::Mtrx)
{Remove contents from rows of X}
    RemoveRowContents(~X, ~G);
end intrinsic;

intrinsic RemoveRowContents(X::Mtrx) -> Mtrx
{Remove contents from rows of X}
    RemoveRowContents(~X);
    return X;
end intrinsic;
