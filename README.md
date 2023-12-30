# optlib
We aim to formalize the broad area of *mathematical programming* including convex analysis, convex optimization, nonlinear programming, integer programming and etc in Lean4. Related topics include but are not limited to the definition and properties of convex and nonconvex functions, optimality conditions, convergence of various algorithms.

More topics related to computational mathematics such as numerical linear algebra and numerical analysis will be included in the future.

# What we have done

## Analysis
- Basic.lean (This has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean)
- Calculation.lean: the properties of the gradient of a function, including the chain rule, the product rule.
- Gradient_div.lean: the quotient rule of the gradient.
- Taylor.lean: the local expansion of a differentiable function.

## Function
- ClosedFunction.lean: the basic definitions and the properties of closed functions.
- Convex_Function.lean: the properties of convex functions.
- Lsmooth.lean: the properties of L-smooth functions.
- Minima_ClosedFunction.lean: Weierstrass theorem for closed functions.
- QuasiConvex_First_Order.lean: first order conditions for quasi-convex functions.
- StronglyConvex.lean: the properties of strongly convex functions. (Part of this has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Strong.lean)
- Subgradient.lean: the basic definitions and the properties of subgradient.

## Optimality
- Optimality_Condition_of_Unconstrained_Problem.lean: first order optimality conditions for unconstrained optimization problems.

## Algorithm
- Gradient_Descent.lean: convergence rate of gradient descent algorithm for smooth convex functions.
- Gradient_Descent_Strongly_Convex.lean: convergence rate of gradient descent algorithm for smooth strongly convex functions.
- Nestrov_Smooth.lean: convergence rate of Nesterov accelerated gradient descent algorithm for smooth convex functions.

## Example
- ConvexPerspectiveFraction.lean: convexity preservation of perspective transformations and linear fractional transformations.
- GeneralizedInequality.lean: partial order respected to proper cones.
- Normexamples.lean: examples of norm ball and norm cone and their convexity.
- Polyhedron.lean: the definition and convexity of polyhedrons.
- SymPosde.lean: convex conicity of symmetric matrices, semi-positive definite matrices and positive definite matrices.

# What we plan to do

## Convex Analysis

- First Order Conditions for Convex Functions (Done)
- Second Order Conditions for Convex Functions
- Definition and Properties of Strongly Convex Functions (Done)
- Definition and Properties of L-smooth Functions (Done)
- Definition and Properties of Subgradients
- ......

## Optimality Conditions

- First Order Conditions for Constrained and Unconstrained Methods
- Second Order Conditions for Constrained and Unconstrained Methods
- KKT conditions
- ......

## Convergence of Optimization Algorithms

- Gradient Descent for Convex and Strongly Convex Functions (Done)
- Nesterov Accelerated Method for Smooth Functions (Done)
- Line Search Methods
- Subgradient Methods
- Proximal Gradient Methods 
- Nesterov Accelerated Method for Non-smooth Functions
- ADMM Methods
- ......

## Many other things to be added ...

# References
- [H. Liu, J. Hu, Y. Li, Z. Wen, Optimization: Modeling, Algorithm and Theory (in Chinese)](http://faculty.bicmr.pku.edu.cn/~wenzw/optbook.html)
- [Rockafellar, R. Tyrrell, and Roger J-B. Wets. Variational analysis. Vol. 317. Springer Science & Business Media, 2009.](https://link.springer.com/book/10.1007/978-3-642-02431-3)
- [Nocedal, Jorge, and Stephen J. Wright, eds. Numerical optimization. New York, NY: Springer New York, 1999.](https://link.springer.com/chapter/10.1007/0-387-22742-3_18)
- [Nesterov, Yurii. Lectures on convex optimization. Vol. 137. Berlin: Springer, 2018.](https://link.springer.com/book/10.1007/978-3-319-91578-4)


# The Team
We are a team of undergraduate and graduate students at the Beijing International Center for Mathematical Research (BICMR) of Peking University, under the supervision of Professor Zaiwen Wen.

## Members

- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)
- Chenyi Li, School of Mathematical Sciences, Peking University, CHINA (lichenyi@stu.pku.edu.cn)
- Ziyu Wang, School of Mathematical Sciences, Peking University, CHINA (wangziyu-edu@stu.pku.edu.cn)

## Other Contributors
- Undergraduate students from Peking University:

   Hongjia Chen, Wanyi He, Yuxuan Wu, Shengyang Xu, Junda Ying, Penghao Yu, ...

- Undergraduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2023:

    Zhipeng Cao, Yiyuan Chen, Heying Wang, Zuokai Wen, Mingquan Zhang, Ruichong Zhang, ... 


# Installation

- A comprehensive installation guide in Chinese:
http://faculty.bicmr.pku.edu.cn/~wenzw/formal/docs/#/

# Copyright

Copyright (c) 2023 Chenyi Li, Ziyu Wang, Zaiwen Wen. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.

