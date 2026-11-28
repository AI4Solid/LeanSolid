# LeanSolid 与 lean-mechanics 连续介质力学对照

对照使用与此前线弹性移植一致的 [raphos-com/lean-mechanics 7e41dfe](https://github.com/raphos-com/lean-mechanics/tree/7e41dfe34f43b0095be77a8ab85a2ae9def7adf2/ContinuumMechanics)。下表的覆盖判断针对这一快照。源文件注释注明 Apache-2.0 来源。上游的 Lean 版本为 4.34.1，本库在 4.36.0 上检查适配后的代码。

## LeanSolid 已有的结果

| 方向 | 在上游快照的对应范围和 LeanSolid 的补充 |
| --- | --- |
| 运动率和客观性 | 两边有观察者变换、应变和极分解。LeanSolid 进一步连接运动场的时空导数、$\dot F=LF$、应变与面积率，以及沿材料路径的 Jaumann 率和局部应力功率。[Rates](../LeanSolid/ContinuumMechanics/Rates.lean) · [GeometryRates](../LeanSolid/ContinuumMechanics/GeometryRates.lean) · [Objectivity](../LeanSolid/ContinuumMechanics/Objectivity.lean) |
| 区域与平衡 | 两边有 Cauchy、Piola 和局部平衡。在对照的上游文件中未找到 LeanSolid 这套变形盒域与匹配分片的 Reynolds 输运，以及用实际薄柱体和四面体面参数化连接合力平衡与牵引定理的证明。区域推广仍受两库各自的参数化和积分假设约束。[PatchTransport](../LeanSolid/ContinuumMechanics/PatchTransport.lean) · [EnergyBalance](../LeanSolid/ContinuumMechanics/EnergyBalance.lean) · [Tetrahedron](../LeanSolid/ContinuumMechanics/Tetrahedron.lean) |
| 有限应变本构及失稳 | 两边有 Saint Venant–Kirchhoff、neo-Hookean、Mooney–Rivlin 和线性化。LeanSolid 另有等容／体积分裂的显式导数、不可压缩约束应力、部分 Ogden 主伸长公式，以及 Biot 深度剖面、实轴 Fourier 分解和重构。[Hyperelasticity](../LeanSolid/ContinuumMechanics/Hyperelasticity) |
| 弱式和具体边值问题 | 两边有 Korn、Galerkin、全固定 Sobolev 弱式、Airy 和径向圆筒。LeanSolid 进一步构造底部固定矩形的顶部迹和部分牵引弱解，并有本征应变能量分解和球形夹杂界面匹配。[Sobolev](../LeanSolid/Elastostatics/Sobolev) · [Eigenstrain](../LeanSolid/Elastostatics/Eigenstrain.lean) · [SphericalInclusion](../LeanSolid/Elastostatics/SphericalInclusion.lean) |

## 本轮从上游接入

| 上游目录或文件 | LeanSolid 落点 | 接入内容 |
| --- | --- | --- |
| Stress/Mohr、Stress/Criteria | [Mohr](../LeanSolid/ContinuumMechanics/Mohr.lean)、[StressCriteria](../LeanSolid/ContinuumMechanics/StressCriteria.lean) | 平面应力旋转、Mohr 圆、主值和最大剪应力取到；采用现有偏量和双收缩定义三维 (J_2) 与 von Mises，验证有序主应力下与 Tresca 的双边界。 |
| Constitutive/Ellipticity | [Ellipticity](../LeanSolid/ContinuumMechanics/Ellipticity.lean) | 用 Mathlib 秩一算子表达声学张量。维数至少为二时，强椭圆性等价于 $\mu>0$ 且 $\lambda+2\mu>0$。包括声学特征值的纵横波分类。 |
| Constitutive/Viscoelastic、Constitutive/Composites | [Viscoelastic](../LeanSolid/ContinuumMechanics/Viscoelastic.lean)、[Composites](../LeanSolid/ContinuumMechanics/Composites.lean) | 线性黏弹性模型和标准线性固体；复合材料单层和层合刚度。 |
| Thermal/Thermoelastic | [Thermoelastic](../LeanSolid/ContinuumMechanics/Thermoelastic.lean) | 热应变、热应力和柔度相互恢复，自由膨胀和完全约束两个基准情形。复用本库 Lamé 应力及柔度。 |
| Fluids/Hydrostatics、Fluids/OpenChannel、Fluids/BoundaryLayer | [Hydrostatics](../LeanSolid/ContinuumMechanics/Hydrostatics.lean)、[OpenChannel](../LeanSolid/ContinuumMechanics/OpenChannel.lean)、[BoundaryLayer](../LeanSolid/ContinuumMechanics/BoundaryLayer.lean) | 静水压接入本库 Newtonian 动量式，并验证盒体浮力；开渠比能等关系和边界层积分模型。 |
| Geotechnics/Strength、Geotechnics/Seepage | [GeotechnicalStrength](../LeanSolid/ContinuumMechanics/GeotechnicalStrength.lean)、[Seepage](../LeanSolid/ContinuumMechanics/Seepage.lean) | Mohr–Coulomb 等强度结果；Darcy 流量、各向异性坐标伸缩化为 Laplace 方程、分层等效渗透率和 Dupuit 流。渗流用本库的 Cartesian 梯度、偏导和散度。 |

## 上游还有的内容

| 方向 | 可继续对照的内容 |
| --- | --- |
| 本构与应力 | 一般各向同性张量函数的 Rivlin–Ericksen 表示定理；塑性和硬化；直接由任意三维对称应力的有序谱定义 Tresca。 |
| 热、流体及地基 | 一维热传导及应用、热弹性圆筒和双层梁、闸板压力中心与浮体稳性、非稳态 Stokes 流、可压缩流、管网、润滑、渗流耗散最小原理和固结。 |
| 结构与专门模型 | 上游将梁、板壳、影响线、缆索、接触、断裂、疲劳、杆件弱式及若干专门弹性解也放在 ContinuumMechanics 下。进一步接入时适合独立模块，并逐项与已有线弹性、反平面和弱式库对齐。 |
