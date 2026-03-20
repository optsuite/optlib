1. 只修改 __________________ , 不要改动其他lean文件.

2. 我们的目标是只在报错上下3行内进行修改, 每个修改增加行数不超过5行的条件下, 修改文件中的报错使得可以过编译, 禁止改变api接口, 禁止使用axiom或者admit.

    (1) Step1. 阅读 Experence.md, 了解修复的相关经验
    
    (2) Step2. 有限解决import issues
    
    (3) Step3. 先只修改这个文件中的statement, 使得每个statement都没有报错, 先不要管证明.

    (4) Step4. 再逐点解决证明中的报错, 不要因为一个小点报错而删掉整段证明.

    (5) Step5. 最后 lake env lean __________________ 确保可以过编译, 并且没有warning.

    (6) Step6. 总结经验并放到 Experience.md 里面

3. 可以通过这几种方式搜索定理, grep, apply?搜索本地定理 / websearch 在 leansearch.net, moogle.ai 搜索mathlib中的定理.

4. 请你把总结的经验放到 Experience.md 里面
