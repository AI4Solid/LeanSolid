# Linear Elasticity 1 上游来源

本页记录 LeanSolid 如何使用 [raphos-com/lean-mechanics](https://github.com/raphos-com/lean-mechanics) 的代码。对应版本为 [7e41dfe34f43b0095be77a8ab85a2ae9def7adf2](https://github.com/raphos-com/lean-mechanics/tree/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2)，许可证为 [Apache-2.0](../LICENSE)。移植文件在源码开头保留来源，LeanSolid 的构建依赖为 Mathlib。

## 本轮采用

| 上游文件 | LeanSolid 落点 | 保留和调整 |
|---|---|---|
| [Kinematics/Rigid.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Kinematics/Rigid.lean) | [Rigid.lean](../LeanSolid/LinearElasticity/Rigid.lean) | 改编 Hessian 对称性、梯度反对称性与连通域上梯度恒定的证明。直接用内积表示反对称性。新增由各方向法向应变为零推出刚体位移的推论。 |
| [Kinematics/PoincareStar.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Kinematics/PoincareStar.lean) | [PoincareStar.lean](../LeanSolid/Math/Calculus/PoincareStar.lean) | 移植星形开域上闭一形式有原函数的证明。它是相容性充分性的积分工具。 |
| [Kinematics/SaintVenantStar.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Kinematics/SaintVenantStar.lean) 和 [Kinematics/SaintVenant.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Kinematics/SaintVenant.lean) | [Compatibility.lean](../LeanSolid/LinearElasticity/Compatibility.lean) | 移植两次积分的证明及旋转梯度辅助引理。使用 Mathlib 的实伴随算子。结论是星形开域上相容自伴应变的位移恢复。 |
| [Elastostatics/SaintVenantPrinciple.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/SaintVenantPrinciple.lean) | [条带定义](../LeanSolid/AntiPlane/Strip/Definitions.lean) 和 [条带定理](../LeanSolid/AntiPlane/Strip/Theorems.lean) | 移植反平面条带的有限模态、截面合力守恒及指数能量衰减。保留自平衡端部载荷、侧边无牵引及远端零功等前提。 |
| [Beams/String.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Beams/String.lean) 和 [Beams/Wirtinger.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Beams/Wirtinger.lean) | [条带导数辅助工具](../LeanSolid/AntiPlane/Strip/Partials.lean) 和 [Wirtinger.lean](../LeanSolid/Math/Calculus/Wirtinger.lean) | 选取条带证明所需的标量偏导、原函数、余弦积分及 Wirtinger 不等式。 |
| [Elastostatics/Airy.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Airy.lean) | [Airy/Corollaries.lean](../LeanSolid/Plane/Airy/Corollaries.lean) | 参考平面应力与平面应变的相容残差公式，使用 LeanSolid 的通用 Airy 定理证明两个材料参数特例。 |

## 此前采用

| 上游文件 | LeanSolid 落点 |
|---|---|
| [Elastostatics/Korn.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Korn.lean) | [Korn](../LeanSolid/Elastostatics/Korn/) 和 [偏导引理](../LeanSolid/Math/Calculus/Theorems.lean) |
| [Variational.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Variational.lean)、[H10.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/H10.lean)、[Existence.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Existence.lean) | [Sobolev 模型](../LeanSolid/Elastostatics/Sobolev/)。接入本库弱式，并用 Korn 恒等式放宽全固定问题的材料条件。 |
| [Elastostatics/LameCylinder.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/LameCylinder.lean) | [圆筒与球壳径向模型](../LeanSolid/Elastostatics/Radial/) |
| [Elastostatics/Airy.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Airy.lean)、[Galerkin.lean](https://github.com/raphos-com/lean-mechanics/blob/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics/Elastostatics/Galerkin.lean) | [Airy 平衡方程](../LeanSolid/Plane/Airy/Theorems.lean)、[Galerkin](../LeanSolid/Elastostatics/Galerkin.lean) |

[Cartesian 桥接](../LeanSolid/LinearElasticity/Cartesian.lean)使用本地 Mathlib 的 `PiLp.continuousLinearEquiv`、Fréchet 导数链式法则、`ContinuousLinearMap.adjoint_inner_right` 和标准基内积公式，证明坐标应变等于算子应变的分量，并由此直接对现有坐标位移场调用刚体定理。[Cartesian 相容性](../LeanSolid/LinearElasticity/CartesianCompatibility.lean)用 Mathlib 的矩阵到欧几里得算子等价、伴随与共轭转置公式、二阶导数链式法则和标准基外延性，双向证明分量相容条件与算子条件等价，再调用上游星形域证明恢复坐标位移。
