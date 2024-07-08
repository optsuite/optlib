# optlib

We aim to formalize the broad area of **mathematical optimization** including convex analysis, convex optimization, nonlinear programming, integer programming and etc in Lean4. Related topics include but are not limited to the definition and properties of convex and nonconvex functions, optimality conditions, convergence of various algorithms.

More topics related to computational mathematics such as numerical linear algebra and numerical analysis will be included in the future.

Our GitHub web page corresponding to this work can be found at [here](https://optsuite.github.io/optlib/) .

## Lean4 Toolchain Installation

- A comprehensive installation guide in Chinese:
  [http://faculty.bicmr.pku.edu.cn/~wenzw/formal/index.html](http://faculty.bicmr.pku.edu.cn/~wenzw/formal/index.html)

- Download guide provided by the official Lean team:
  https://leanprover-community.github.io/get_started.html

- For Lean 4 users in China, the [glean](https://github.com/alissa-tung/glean) tool is recommended for using the [Shanghai Jiao Tong University mirror service](https://mirror.sjtu.edu.cn/).

## How to use the code in this repository

If anything goes wrong, please feel free to contact Chenyi Li through email (lichenyi@stu.pku.edu.cn).

The version of Lean4 that used by this repository can be checked [here](https://github.com/optsuite/optlib/blob/main/lean-toolchain).

### Use the `Convex` library as a Lean4 project dependency

In a Lean4 project, add these lines to your `lakefile.lean`:

```lean4
require convex from git
  "https://github.com/optsuite/optlib"
```

or in new `lakefile.lean` Lake DSL:

```lean4
require "optsuite" / "optlib" @ "git#master"
```

The convex library uses mathlib4 as a dependency, command `lake exe cache get` can be used to fetch mathlib4 cache.

### Contribute to the `Convex` library

The command

```sh
git clone https://github.com/optsuite/optlib.git && cd optlib && code .
```

will download the source of the convex library. After editing those files, you can fork this project on GitHub and file a pull request.

## What we have done

### Analysis

- [`Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean): (now `Mathlib/Analysis/Calculus/Gradient/Basic.lean`) the definition and basic properties of the gradient of a function. (**This file has been merged into mathlib4**, see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean)
- [`Calculation.lean`](Convex/Analysis/Calculation.lean): the properties of the gradient of a function, including the chain rule, the product rule.
- [`GradientDiv.lean`](Convex/Analysis/GradientDiv.lean): the quotient rule of the gradient.
- [`Lemmas.lean`](Convex/Analysis/Lemmas.lean): useful lemmas such as the mean-value theorem and the taylor's expansion.

### Function

- [`ClosedFunction.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Semicontinuous.lean): (now `Mathlib/Topology/Semicontinuous.lean`) the basic definitions and the properties of closed functions. (This file has been merged into mathlib4, see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Semicontinuous.lean)
- [`ConvexFunction.lean`](Convex/Function/ConvexFunction.lean): the properties of convex functions.
- [`Lsmooth.lean`](Convex/Function/Lsmooth.lean): the properties of L-smooth functions.
- [`MinimaClosedFunction.lean`](Convex/Function/MinimaClosedFunction.lean): Weierstrass theorem for closed functions.
- [`QuasiConvexFirstOrder.lean`](Convex/Function/QuasiConvexFirstOrder.lean): first order conditions for quasi-convex functions.
- [`StronglyConvex.lean`](Convex/Function/StronglyConvex.lean): the properties of strongly convex functions. (Part of this has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Strong.lean)
- [`BanachSubgradient.lean`](Convex/Function/BanachSubgradient.lean): the basic definitions of subgradient on a banach space.
- [`Subgradient.lean`](Convex/Function/Subgradient.lean): the basic definitions and the properties of subgradient.
- [`Proximal.lean`](Convex/Function/Proximal.lean): the basic definitions and the properties of proximal operator

### Optimality

- [`OptimalityConditionOfUnconstrainedProblem.lean`](Convex/Optimality/OptimalityConditionOfUnconstrainedProblem.lean): first order optimality conditions for unconstrained optimization problems.

### Algorithm

- [`GradientDescent.lean`](Convex/Algorithm/GradientDescent.lean): convergence rate of gradient descent algorithm for smooth convex functions.
- [`GradientDescentStronglyConvex.lean`](Convex/Algorithm/GradientDescentStronglyConvex.lean): convergence rate of gradient descent algorithm for smooth strongly convex functions.
- [`NesterovSmooth.lean`](Convex/Algorithm/NesterovSmooth.lean): convergence rate of Nesterov accelerated gradient descent algorithm for smooth convex functions.
- [`SubgradientMethod.lean`](Convex/Algorithm/SubgradientMethod.lean): convergence rate of subgradient method with different choices of stepsize for nonsmooth convex functions.
- [`ProximalGradient.lean`](Convex/Algorithm/ProximalGradient.lean): convergence rate of the proximal gradient method for composite optimization problems.
- [`NesterovAccelerationFirst.lean`](Convex/Algorithm/NesterovAccelerationFirst.lean): convergence rate of the first version of Nesterov acceleration method for composite optimization problems.
- [`NesterovAccelerationSecond.lean`](Convex/Algorithm/NesterovAccelerationSecond.lean): convergence rate of the second version of Nesterov acceleration method for composite optimization problems.

## What we plan to do

### Convex Analysis

- First Order Conditions for Convex Functions (Done)
- Second Order Conditions for Convex Functions
- Definition and Properties of Strongly Convex Functions (Done)
- Definition and Properties of L-smooth Functions (Done)
- Definition and Properties of Subgradients (Done)
- ......

### Optimality Conditions

- First Order Conditions for Constrained and Unconstrained Methods
- Second Order Conditions for Constrained and Unconstrained Methods
- KKT conditions
- ......

### Convergence of Optimization Algorithms

- Gradient Descent for Convex and Strongly Convex Functions (Done)
- Line Search Methods
- Subgradient Methods (Done)
- Proximal Gradient Methods (Done)
- Nesterov Acceleration Method (Done)
- ADMM Methods
- ......

### Many other things to be added ...

## References

- [Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. Formalization of Complexity Analysis of the First-order Optimization Algorithms](https://arxiv.org/abs/2403.11437)
- [H. Liu, J. Hu, Y. Li, Z. Wen, Optimization: Modeling, Algorithm and Theory (in Chinese)](http://faculty.bicmr.pku.edu.cn/~wenzw/optbook.html)
- [Rockafellar, R. Tyrrell, and Roger J-B. Wets. Variational analysis. Vol. 317. Springer Science & Business Media, 2009.](https://link.springer.com/book/10.1007/978-3-642-02431-3)
- [Nocedal, Jorge, and Stephen J. Wright, eds. Numerical optimization. New York, NY: Springer New York, 1999.](https://link.springer.com/chapter/10.1007/0-387-22742-3_18)
- [Nesterov, Yurii. Lectures on convex optimization. Vol. 137. Berlin: Springer, 2018.](https://link.springer.com/book/10.1007/978-3-319-91578-4)

## The Team

We are a group of scholars and students with a keen interest in mathematical formalization.

### Members

- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)
- Chenyi Li, School of Mathematical Sciences, Peking University, CHINA (lichenyi@stu.pku.edu.cn)
- Ziyu Wang, School of Mathematical Sciences, Peking University, CHINA (wangziyu-edu@stu.pku.edu.cn)

### Other Contributors

- Undergraduate students from Peking University:

  Hongjia Chen, Wanyi He, Yuxuan Wu, Shengyang Xu, Junda Ying, Penghao Yu, ...

- Undergraduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2023:

  Zhipeng Cao, Yiyuan Chen, Heying Wang, Zuokai Wen, Mingquan Zhang, Ruichong Zhang, ...

- Other collaborators:

  Anjie Dong, ...

## Copyright

Copyright (c) 2024 Chenyi Li, Ziyu Wang, Zaiwen Wen. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.
