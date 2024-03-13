# optlib

We aim to formalize the broad area of **mathematical optimization** including convex analysis, convex optimization, nonlinear programming, integer programming and etc in Lean4. Related topics include but are not limited to the definition and properties of convex and nonconvex functions, optimality conditions, convergence of various algorithms.

More topics related to computational mathematics such as numerical linear algebra and numerical analysis will be included in the future.

# Installation

- A comprehensive installation guide in Chinese:
  [http://faculty.bicmr.pku.edu.cn/~wenzw/formal/index.html](http://faculty.bicmr.pku.edu.cn/~wenzw/formal/index.html)

- Download guide provided by the official Lean team:
  https://leanprover-community.github.io/get_started.html

## How to use the code in this repository

- Before downloading your code, please check the lean-toolchain file to see the Lean 4 version for each branch.
  The Main Branch is for leanprover/lean4:v4.3.0 and the lean4v4.5.0-rc1 branch is for leanprover/lean4:v4.5.0-rc1.
  Please check your Lean4 version and see if they are matched.

- Take downloading the `Analysis` folder from the `mathematics_in_lean` directory as an example:

1. Identify the local directory where the Lean software can run, and open this directory with VScode (such as `mathematics_in_lean`).
2. Copy the provided `Analysis` folder entirely into this directory (`mathematics_in_lean`).
3. In this directory (`mathematics_in_lean`), locate a file named `lakefile.lean`.
4. If there is a `@[default_target]` section in this `lakefile.lean`, then add the following at the end of this section:
   ```
    lean_lib «Analysis» {
        -- add any library configuration options here
    }
   ```
   If there is no `@[default_target]` section, then add the following in `lakefile.lean`:
   ```
    @[default_target]
    lean_lib «Analysis» {
        -- add any library configuration options here
    }
   ```
   The complete code can be referred to in the corresponding section of the `lakefile.lean` file.
5. At this point, you can call the locally written Lean files across directories and also run the corresponding proof parts of the code in Lean.

- If anything goes wrong, please feel free to contact Chenyi Li through email (lichenyi@stu.pku.edu.cn).

# What we have done

## Analysis

- Basic.lean: the definition and basic properties of the gradient of a function. (This has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean)
- Calculation.lean: the properties of the gradient of a function, including the chain rule, the product rule.
- GradientDiv.lean: the quotient rule of the gradient.
- Lemmas.lean: useful lemmas such as the mean-value theorem and the taylor's expansion.

## Function

- ClosedFunction.lean: the basic definitions and the properties of closed functions. (This has been merged into mathlib)
- ConvexFunction.lean: the properties of convex functions.
- Lsmooth.lean: the properties of L-smooth functions.
- MinimaClosedFunction.lean: Weierstrass theorem for closed functions.
- QuasiConvex_First_Order.lean: first order conditions for quasi-convex functions.
- StronglyConvex.lean: the properties of strongly convex functions. (Part of this has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Strong.lean)
- BanachSubgradient.lean: the basic definitions of subgradient on a banach space.
- Subgradient.lean: the basic definitions and the properties of subgradient.
- Proximal.lean: the basic definitions and the properties of proximal operator

## Optimality

- OptimalityConditionOfUnconstrainedProblem.lean: first order optimality conditions for unconstrained optimization problems.

## Algorithm

- GradientDescent.lean: convergence rate of gradient descent algorithm for smooth convex functions.
- Gradient_Descent_Strongly_Convex.lean: convergence rate of gradient descent algorithm for smooth strongly convex functions.
- Nesterov_Smooth.lean: convergence rate of Nesterov accelerated gradient descent algorithm for smooth convex functions.
- Subgradient_method.lean: convergence rate of subgradient method with different choices of stepsize for nonsmooth convex functions.
- Proximal_Gradient.lean: convergence rate of the proximal gradient method for composite optimization problems.
- Nesterov_Acceleration_first.lean: convergence rate of the first version of Nesterov acceleration method for composite optimization problems.
- Nesterov_Acceleration_second.lean: convergence rate of the second version of Nesterov acceleration method for composite optimization problems.

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

We are a group of scholars and students with a keen interest in mathematical formalization.

## Members

- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)
- Chenyi Li, School of Mathematical Sciences, Peking University, CHINA (lichenyi@stu.pku.edu.cn)
- Ziyu Wang, School of Mathematical Sciences, Peking University, CHINA (wangziyu-edu@stu.pku.edu.cn)

## Other Contributors

- Undergraduate students from Peking University:

  Hongjia Chen, Wanyi He, Yuxuan Wu, Shengyang Xu, Junda Ying, Penghao Yu, ...

- Undergraduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2023:

  Zhipeng Cao, Yiyuan Chen, Heying Wang, Zuokai Wen, Mingquan Zhang, Ruichong Zhang, ...

# Copyright

Copyright (c) 2024 Chenyi Li, Ziyu Wang, Zaiwen Wen. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.
