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

## Main Contributions (What we have done)

### Differential

- [`Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean): (now `Mathlib/Analysis/Calculus/Gradient/Basic.lean`) the definition and basic properties of the gradient of a function. (**This file has been merged into mathlib4**, see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Calculus/Gradient/Basic.lean)
- [`Calculation.lean`](Optlib/Differential/Calculation.lean): the properties of the gradient of a function, including the chain rule, the product rule.
- [`GradientDiv.lean`](Optlib/Differential/GradientDiv.lean): the quotient rule of the gradient.
- [`Lemmas.lean`](Optlib/Differential/Lemmas.lean): useful lemmas such as the mean-value theorem and the taylor's expansion.
- [`Subdifferential.lean`](Optlib/Differential/Subdifferential.lean): the basic definitions and properties of subdifferentials for general nonsmooth functions.
- Subdifferentials for general proper functions (with the extended real numbers as its range) (Ongoing)

### Convex

- [`ConvexFunction.lean`](Optlib/Convex/ConvexFunction.lean): the properties of convex functions.
- [`QuasiConvexFirstOrder.lean`](Optlib/Convex/QuasiConvexFirstOrder.lean): first order conditions for quasi-convex functions.
- [`StronglyConvex.lean`](Optlib/Convex/StronglyConvex.lean): the properties of strongly convex functions. (Part of this has been merged into mathlib) (see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Analysis/Convex/Strong.lean)
- [`Subgradient.lean`](Optlib/Convex/Subgradient.lean): the basic definitions and the properties of subgradient.
- [`BanachSubgradient.lean`](Optlib/Function/BanachSubgradient.lean): the basic definitions of subgradient on a banach space.
- [`FiniteDimensionalConvexFunctionsLocallyLipschitz.lean`](Optlib/Function/FiniteDimensionalConvexFunctionsLocallyLipschitz.lean): the proof of the the contuity of convex functions on finite dimensional space
- [`ConicCaratheodory.lean`](Optlib/Convex/ConicCaratheodory.lean): the proof of the conic Caratheodory lemma
- [`Farkas.lean`](Optlib/Convex/Farkas.lean): the proof of the Farkas Lemma
- The definition and properties of line derivative for convex functions (todo)

### Function

- [`ClosedFunction.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Semicontinuous.lean): (now `Mathlib/Topology/Semicontinuous.lean`) the basic definitions and the properties of closed functions. (This file has been merged into mathlib4, see https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Semicontinuous.lean)
- [`Lsmooth.lean`](Optlib/Function/Lsmooth.lean): the properties of L-smooth functions.
- [`MinimaClosedFunction.lean`](Optlib/Function/MinimaClosedFunction.lean): Weierstrass theorem for closed functions.
- [`Proximal.lean`](Optlib/Function/Proximal.lean): the basic definitions and the properties of proximal operator
- [`KL.lean`](Optlib/Function/KL.lean): KL properties and uniform KL properties
- The definition and properties of proper functions
- The definition and properties of the closure of a function
- The definition and properties of conjugate functions

### Optimality

- [`OptimalityConditionOfUnconstrainedProblem.lean`](Optlib/Optimality/OptimalityConditionOfUnconstrainedProblem.lean): first order optimality conditions for unconstrained optimization problems.
- [`Constrained_Problem.lean`](Optlib/Optimality/Constrained_Problem.lean): the basic definitions of constrained optimization problems and the proof the KKT conditions under LICQ and linear constraint qualification
- [`Weak_Duality.lean`](Optlib/Optimality/Weak_Duality.lean): the formalization of the dual problem and the proof of the weak duality property
- KKT conditions for constrained convex problems under Slater Condition (Ongoing)  

### Algorithm

- [`GradientDescent.lean`](Optlib/Algorithm/GD/GradientDescent.lean): convergence rate of gradient descent algorithm for smooth convex functions.
- [`GradientDescentStronglyConvex.lean`](Optlib/Algorithm/GD/GradientDescentStronglyConvex.lean): convergence rate of gradient descent algorithm for smooth strongly convex functions.
- [`NesterovSmooth.lean`](Optlib/Algorithm/Nesterov/NesterovSmooth.lean): convergence rate of Nesterov accelerated gradient descent algorithm for smooth convex functions.
- [`SubgradientMethod.lean`](Optlib/Algorithm/SubgradientMethod.lean): convergence rate of subgradient method with different choices of stepsize for nonsmooth convex functions.
- [`ProximalGradient.lean`](Optlib/Algorithm/ProximalGradient.lean): convergence rate of the proximal gradient method for composite optimization problems.
- [`NesterovAccelerationFirst.lean`](Optlib/Algorithm/Nesterov/NesterovAccelerationFirst.lean): convergence rate of the first version of Nesterov acceleration method for composite optimization problems.
- [`NesterovAccelerationSecond.lean`](Optlib/Algorithm/Nesterov//NesterovAccelerationSecond.lean): convergence rate of the second version of Nesterov acceleration method for composite optimization problems.
- [`LASSO.lean`](Optlib/Algorithm/LASSO.lean): convergence rate of the LASSO algorithm for L1-regularized least squares problem.
- [`the BCD method`](Optlib/Algorithm/BCD/Convergence.lean): convergence analysis of the block coordinate descent method.
- [`the ADMM method`](Optlib/Algorithm/ADMM/Theroem_converge.lean): convergence analysis of the alternating direction method of multipliers.
- Primal-Dual Algorithms (todo)


## What we plan to do

### Convex Analysis

- First Order Conditions for Convex Functions (Done)
- Second Order Conditions for Convex Functions
- Definition and Properties of Proper Functions and Conjugate Functions (Ongoing)
- Definition and Properties of Strongly Convex Functions (Done)
- Definition and Properties of L-smooth Functions (Done)
- Definition and Properties of Subgradient and Proximal Operator(Done)
- Definition and Properties of Frechet Subdifferential (Done)
- Definition of KL properties (Done)
- Definition of semi-algebraic functions
- ......

### Optimality Conditions

- First Order Conditions for Constrained and Unconstrained Problems   
- Second Order Conditions for Constrained and Unconstrained Problems
- KKT Conditions for Constrained Problems under constraint qualifications 
- Slater Condition and KKT Conditions for convex optimization problems (Ongoing)
- ......

### Convergence of Optimization Algorithms

- Gradient Descent for Convex and Strongly Convex Functions 
- Line Search Methods
- Newton Method, Quasi-Newton Method, LBFGS Update
- Primal-Dual Algorithms
- Stochastic Gradient Descent and Stochastic Algorithms
- ......

### Integer Programming

### Many other things to be added ...

## References

- [Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. Formalization of Complexity Analysis of the First-order Optimization Algorithms](https://arxiv.org/abs/2403.11437)
- [H. Liu, J. Hu, Y. Li, Z. Wen, Optimization: Modeling, Algorithm and Theory (in Chinese)](http://faculty.bicmr.pku.edu.cn/~wenzw/optbook.html)
- [Rockafellar, R. Tyrrell, and Roger J-B. Wets. Variational analysis. Vol. 317. Springer Science & Business Media, 2009.](https://link.springer.com/book/10.1007/978-3-642-02431-3)
- [Nocedal, Jorge, and Stephen J. Wright, eds. Numerical optimization. New York, NY: Springer New York, 1999.](https://link.springer.com/chapter/10.1007/0-387-22742-3_18)
- [Nesterov, Yurii. Lectures on convex optimization. Vol. 137. Berlin: Springer, 2018.](https://link.springer.com/book/10.1007/978-3-319-91578-4)
- [Convex Analysis, Vol. 28 of Princeton Math. Series, Princeton Univ. Press, 1970](https://press.princeton.edu/books/paperback/9780691015866/convex-analysis)
- [Bolte, J., Sabach, S. & Teboulle, M. Proximal alternating linearized minimization for nonconvex and nonsmooth problems. Math. Program. 146, 459–494 (2014).](https://link.springer.com/article/10.1007/s10107-013-0701-9)
- [Maryam Fazel, Ting Kei Pong, Defeng Sun, and Paul Tseng. Hankel matrix rank minimization with applications to system identification and realization. SIAM Journal on Matrix Analysis and Applications, 34(3):946–977, 2013](https://epubs.siam.org/doi/abs/10.1137/110853996)
- ...

## The Team

We are a group of scholars and students with a keen interest in mathematical formalization.

### Members

- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)
- Chenyi Li, School of Mathematical Sciences, Peking University, CHINA (lichenyi@stu.pku.edu.cn)
- Zichen Wang, School of Mathematics and Statistics, Xi’an Jiaotong University, CHINA (princhernwang@gmail.com)
- Ziyu Wang, School of Mathematical Sciences, Peking University, CHINA (wangziyu-edu@stu.pku.edu.cn)

### Other Contributors

- Undergraduate students from Peking University:

  Hongjia Chen, Wanyi He, Yuxuan Wu, Shengyang Xu, Junda Ying, Penghao Yu, ...

- Undergraduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2023:

  Zhipeng Cao, Yiyuan Chen, Heying Wang, Zuokai Wen, Mingquan Zhang, Ruichong Zhang, ...

- Undergraduate and graduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2024:

  Yifan Bai, Yunxi Duan, Anqing Shen, Yuqing Gao, Pengfei Hao

- Other collaborators:

  Anjie Dong, ...

## Copyright

Copyright (c) 2025 Chenyi Li, Zichen Wang, Ziyu Wang, Zaiwen Wen. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.
