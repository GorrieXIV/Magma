
freeze;

intrinsic MaximalSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution to the constraints LHS <relations> RHS that maximises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L, true);
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;

intrinsic MinimalSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution to the constraints LHS <relations> RHS that minimises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L, false);
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;


intrinsic MaximalIntegerSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution in integers to the constraints LHS <relations> RHS that maximises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L, true);
    if CoefficientRing(objective) cmpne IntegerRing() then
      for i in [1..NumberOfColumns(objective)] do
        SetIntegerSolutionVariables(L, [i], true);
      end for;
    end if;
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;

intrinsic MinimalIntegerSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution in integers to the constraints LHS <relations> RHS that minimises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L, false);
    if CoefficientRing(objective) cmpne IntegerRing() then
      for i in [1..NumberOfColumns(objective)] do
        SetIntegerSolutionVariables(L, [i], true);
      end for;
    end if;
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;

intrinsic MaximalZeroOneSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution in zeroes and ones to the constraints LHS <relations> RHS that maximises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L, true);
    for i in [1..NumberOfColumns(objective)] do
      if CoefficientRing(objective) cmpne IntegerRing() then
        SetIntegerSolutionVariables(L, [i], true);
      end if;
        SetUpperBound(L, i, CoefficientRing(objective)!1);
    end for;    
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;


intrinsic MinimalZeroOneSolution(LHS::Mtrx, relations::Mtrx, RHS::Mtrx, objective::Mtrx)->Mtrx, RngIntElt
{Returns the solution in zeroes and ones to the constraints LHS <relations> RHS that minimises the objective function, and an integer code: 0 => optimal solution, 1 => failure, 2 => infeasible problem, 3 => unbounded problem, 4 => failure}
    require NumberOfRows(objective) eq 1 : 
         "Objective function must be a 1 x n matrix";
    require NumberOfColumns(objective) eq NumberOfColumns(LHS) : 
         "Objective function and LHS do not have the same number of variables";
    require NumberOfRows(LHS) eq NumberOfRows(relations)
            and NumberOfRows(relations) eq NumberOfRows(RHS) : 
         "Number of rows in LHS, RHS, and relations are not equal";
    require NumberOfColumns(RHS) eq 1 : 
         "RHS must be an n x 1 matrix";
    require NumberOfColumns(relations) eq 1 : 
         "relations must be an n x 1 matrix";
    require NumberOfRows(LHS) ge 1 : 
         "Must be at least one constraint";
    require NumberOfColumns(LHS) ge 1 : 
         "Must be at least one variable in LP";
    require CoefficientRing(LHS) eq CoefficientRing(RHS)
            and CoefficientRing(RHS) eq CoefficientRing(objective) :
         "LHS, RHS, and Objective Function must have the same coefficient ring";

    
    L := LPProcess(CoefficientRing(objective), NumberOfColumns(objective));
    SetObjectiveFunction(L, objective);
    SetMaximiseFunction(L,  false);
    for i in [1..NumberOfColumns(objective)] do
	if CoefficientRing(objective) cmpne IntegerRing() then
          SetIntegerSolutionVariables(L, [i], true);
	end if;
        SetUpperBound(L, i, CoefficientRing(objective)!1);
    end for;    
    for i in [1..NumberOfRows(LHS)] do
        lhs := RowSubmatrix(LHS, i, 1);
        rhs := RowSubmatrix(RHS, i, 1);
        case Sign(relations[i, 1]):
            when 1:
                AddConstraints(L, lhs, rhs : Rel := "ge");
            when 0:
                AddConstraints(L, lhs, rhs : Rel := "eq");
            when -1:    
                AddConstraints(L, lhs, rhs : Rel := "le");
        end case;     
    end for;
    return Solution(L);
end intrinsic;
