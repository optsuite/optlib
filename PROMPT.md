1. 只修改 Optlib/Algorithm/BCD/Convergence.lean , 不要改动其他lean文件.

2. 优先使用 `lean-lsp-mcp`

    (1) 所有与 Lean 的交互(如检查 goals, types, errors, completions)都应优先依赖 `lean-lsp-mcp`, 而不是频繁地通过命令行编译 Lean.
    (2) 如果 Lean LSP 工具超时或无响应, 应立即回退到 `lake env lean <file> --json` 进行编译检查, 不要无限期等待一个失效的 LSP.
    (3) 在插入或修改 Lean 声明之后, 应优先使用 `lean-lsp-mcp` 提供的 `diagnostics`, `local_search` 或 `completions` 来检查错误和类型信息. 在同一个 Lean 会话中持续修复错误, 直到 LSP 的诊断结果不再报告错误. 这就是所谓的“内循环”, 在不退出 Lean server 的前提下反复执行. 

3. 定理搜索
    (1) 绝不要使用本地文件搜索方法(如 `find`, `grep`, 手动浏览目录)来定位 Mathlib 中的定理. 这些方法效率低，而且无法捕捉语义信息. 
    (2) 始终优先使用语义搜索工具: `lean-lsp-mcp` 提供的 `lean_leansearch` 查询 mathlib 定理.
    示例查询: "continuous functions on compact sets is uniformly continuous", "definition of a metric space", "multiplication is commutative in a group"
    (3) 优先使用 `lean-lsp-mcp` 提供的 `lean_local_search` 查询本地项目的相关定理.
    查询示例: 比如想找 Finset.card 相关内容: `lean_local_search query="Finset.card"`

4. 我们的目标是做最小修改, 所以只允许在报错上下3行内进行修改, 每个修改增加行数不超过5行, 修改文件中的报错使得可以过编译, 禁止改变api接口, 禁止使用 `axiom` 或者 `admit`.
    (1) Step1. 优先解决import issues
    (2) Step2. 每次找到第一个error/warning, 逐点解决证明中的error/warning, 不要因为一个小点报错而删掉整段证明.
    (3) Step3. 再次编译确保第一个 error/warning 所在的 statement (包括theorem, lemma, instance, class, example ....) 完全正确 (即没有任何 error/warning), 才能去修复下一个error/warning.
    (4) Step4. 如果最后 lake env lean Optlib/Algorithm/BCD/Convergence.lean 成功编译, 没有任何 warning, 任务完成.