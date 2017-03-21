
freeze;

/*
intrinsic Sin(z::FldComElt) -> FldComElt
{The sine of z}
    i := Parent(z).1;
    u := Exp(i*z);
    return (u - 1/u)/(2*i);
end intrinsic;

intrinsic Cos(z::FldComElt) -> FldComElt
{The cosine of z}
    i := Parent(z).1;
    u := Exp(i*z);
    return (u + 1/u)/2;
end intrinsic;
*/

intrinsic Cosec(z::FldComElt) -> FldComElt
{The cosecant of z}
    s := Sin(z);
    error if IsZero(s), "Division by zero";
    return 1/s;
end intrinsic;

intrinsic Sec(z::FldComElt) -> FldComElt
{The secant of z}
    c := Cos(z);
    error if IsZero(c), "Division by zero";
    return 1/c;
end intrinsic;

/*
intrinsic Tan(z::FldComElt) -> FldComElt
{The tangent of z}
    i := Parent(z).1;
    u := Exp(2*i*z);
    den := u + 1;
    error if IsZero(den), "Division by zero";
    return (u - 1)/den;
end intrinsic;
*/

intrinsic Cot(z::FldComElt) -> FldComElt
{The cotangent of z}
    s := Sin(z);
    error if IsZero(s), "Division by zero";
    return Cos(z)/s;

    i := Parent(z).1;
    u := Exp(2*i*z);
    den := u - 1;
    error if IsZero(den), "Division by zero";
    return (u + 1)/den;
end intrinsic;

intrinsic Sincos(z::FldComElt) -> FldComElt, FldComElt
{The sine and cosine of z}
    i := Parent(z).1;
    u := Exp(i*z);
    return (u - 1/u)/(2*i), (u + 1/u)/2;
end intrinsic;

intrinsic Cosech(z::FldComElt) -> FldComElt
{The hyperbolic cosecant of z}
    s := Sinh(z);
    error if IsZero(s), "Division by zero";
    return s^-1;
end intrinsic;

intrinsic Sech(z::FldComElt) -> FldComElt
{The hyperbolic secant of z}
    c := Cosh(z);
    error if IsZero(c), "Division by zero";
    return c^-1;
end intrinsic;

intrinsic Coth(z::FldComElt) -> FldComElt
{The hyperbolic cotangent of z}
    t := Tanh(z);
    error if IsZero(t), "Division by zero";
    return t^-1;
end intrinsic;

intrinsic Argcosech(z::FldComElt) -> FldComElt
{Return y such that Cosech(y) = z}
    error if IsZero(z), "Division by zero";
    return Argsinh(z^-1);
end intrinsic;

intrinsic Argsech(z::FldComElt) -> FldComElt
{Return y such that Sech(y) = z}
    error if IsZero(z), "Division by zero";
    return Argcosh(z^-1);
end intrinsic;

intrinsic Argcoth(z::FldComElt) -> FldComElt
{Return y such that Coth(y) = z}
    error if IsZero(z), "Division by zero";
    return Argtanh(z^-1);
end intrinsic;

intrinsic Arccosec(z::FldComElt) -> FldComElt
{Return y such that Cosec(y) = z}
    error if IsZero(z), "Division by zero";
    return Arcsin(z^-1);
end intrinsic;

intrinsic Arcsec(z::FldComElt) -> FldComElt
{Return y such that Sec(y) = z}
    error if IsZero(z), "Division by zero";
    return Arccos(z^-1);
end intrinsic;

intrinsic Arccot(z::FldComElt) -> FldComElt
{Return y such that Cot(y) = z}
    error if IsZero(z), "Division by zero";
    return Arctan(z^-1);
end intrinsic;
