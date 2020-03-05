# PropositionalCalculus

## 这是实现USTC2020春季学期数理逻辑课程中实现一项功能的python项目

## calculus.py实现了一个命题演算中的形式推理T|-p

## 环境

python 3

## 使用说明

### 由于搜索深度和广度的欠缺以及搜索剪枝的策略尚未完善，目前提供的是**初步的代码**，且使用的方法是直接证明，将在后期继续完善

具体使用方法如下：

```python
python calculus.py
```

根据命令提示不妨输入一个公式：

```
Input the T|-p:such as "|-p->~p"

p|-(p->p)->(p->p)
```

得到结果：

```
[[40, ['(p->p)->((p->p)->(p->p))', 'L1']], [6482, ['p->p', 1, 2, 'MP']], [6501, ['(p->p)->(p->p)', 6482, 40, 'MP']], [2, ['p->(p->p)', 'L1']]]
```
列表中元素与基本证明方法一致，此例中(1)为假定，即：
```
(1) p 假定
(2) p->(p->p) L1
(6482)  p->p (1),(2),MP
(40) (p->p)->((p->p)->(p->p)) L1
(6501) (p->p)->(p->p) (6482),(40),MP
```