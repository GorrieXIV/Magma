freeze;

// Mutation functions to do the obvious stuff.  Specific versions of
// these may exist where more efficient.

function check_args(name, x, y)
    return HasSignature(name, [Type(x), Type(y)]);
end function;

intrinsic 'join:='(~x::., y::.)
{Replace x with (x join y)}
    require check_args("join", x, y): "Bad argument types";
    x := x join y;
end intrinsic;

intrinsic 'meet:='(~x::., y::.)
{Replace x with (x meet y)}
    require check_args("meet", x, y): "Bad argument types";
    x := x meet y;
end intrinsic;

intrinsic 'diff:='(~x::., y::.)
{Replace x with (x diff y)}
    require check_args("diff", x, y): "Bad argument types";
    x := x diff y;
end intrinsic;

intrinsic 'sdiff:='(~x::., y::.)
{Replace x with (x sdiff y)}
    require check_args("sdiff", x, y): "Bad argument types";
    x := x sdiff y;
end intrinsic;

intrinsic 'cat:='(~x::., y::.)
{Replace x with (x cat y)}
    require check_args("cat", x, y): "Bad argument types";
    x := x cat y;
end intrinsic;

intrinsic '+:='(~x::., y::.)
{Replace x with x + y}
    require check_args("+", x, y): "Bad argument types";
    x := x + y;
end intrinsic;

intrinsic '-:='(~x::., y::.)
{Replace x with x - y}
    require check_args("-", x, y): "Bad argument types";
    x := x - y;
end intrinsic;

intrinsic '*:='(~x::., y::.)
{Replace x with x * y}
    require check_args("*", x, y): "Bad argument types";
    x := x * y;
end intrinsic;

intrinsic '/:='(~x::., y::.)
{Replace x with x / y}
    require check_args("/", x, y): "Bad argument types";
    x := x / y;
end intrinsic;

intrinsic '^:='(~x::., y::.)
{Replace x with x ^ y}
    require check_args("^", x, y): "Bad argument types";
    x := x ^ y;
end intrinsic;

intrinsic 'div:='(~x::., y::.)
{Replace x with x div y}
    require check_args("div", x, y): "Bad argument types";
    x := x div y;
end intrinsic;

intrinsic 'mod:='(~x::., y::.)
{Replace x with x mod y}
    require check_args("mod", x, y): "Bad argument types";
    x := x mod y;
end intrinsic;

intrinsic 'and:='(~x::., y::.)
{Replace x with x and y}
    require check_args("and", x, y): "Bad argument types";
    x := x and y;
end intrinsic;

intrinsic 'or:='(~x::., y::.)
{Replace x with x or y}
    require check_args("or", x, y): "Bad argument types";
    x := x or y;
end intrinsic;

intrinsic 'xor:='(~x::., y::.)
{Replace x with x xor y}
    require check_args("xor", x, y): "Bad argument types";
    x := x xor y;
end intrinsic;
