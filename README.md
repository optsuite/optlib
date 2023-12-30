# optlib
We are the team of Professor Wen Zaiwen from the Beijing International Center for Mathmatical Research (BICMR). 


We aim to formalize theorems from convex analysis and convex optimization in Lean4. Related topics include but are not limited to the definition and properties of convex functions, optimality conditions, convergence of various algorithms.

More topics related to computational mathematics will be included in the future.

# What we have done

## Analysis
- Basic.lean (This has been merged into mathlib)(https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean)
- Calculation.lean
- Gradient_div.lean
- Taylor.lean

## Function
- ClosedFunction.lean
- Convex_Function.lean
- Lsmooth.lean
- Minima_ClosedFunction.lean
- QuasiConvex_First_Order.lean
- StronglyConvex.lean
- Subgradient.lean

## Optimal
- Optimality_Condition_of_Unconstrained_Problem.lean

## Algorithm
- Gradient_Descent.lean
- Gradient_Descent_Strongly_Convex.lean
- Nestrov_Smooth.lean

## Example
- ConvexPerspectiveFraction.lean
- GeneralizedInequality.lean
- Normexamples.lean
- Polyhedron.lean
- SymPosde.lean

# What we plan to do

## Convex Analysis

- First Order Conditions for Convex Functions (Done)
- Second Order Conditions for Convex Functions
- Definition and Properties of Strongly Convex Functions (Done)
- Definition and Properties of L-smooth Functions (Done)
- Definition and Properties of Subgradients

## Optimality Conditions

- First Order Conditions for Constrained and Unconstrained Methods
- Second Order Conditions for Constrained and Unconstrained Methods
- KKT conditions

## Convergence of Optimization Algorithms

- Gradient Descent for Convex and Strongly Convex Functions (Done)
- Nesterov Accelerated Method for Smooth Functions (Done)
- Line Search Methods
- Subgradient Methods
- Proximal Gradient Methods 
- Nesterov Accelerated Method for Non-smooth Functions
- ADMM Methods