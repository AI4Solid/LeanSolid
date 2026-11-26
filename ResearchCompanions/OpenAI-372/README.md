# OpenAI 第 372 项 · 三维各向同性弹性反问题

- [论文 PDF](Global%20Uniqueness%20for%20the%20Smooth%20Isotropic%20Elasticity%20Inverse%20Problem.pdf)
- [官方范围说明](lean/docs/372.md)
- [实际证明入口](lean/OAI/MathematicalPhysics/Elasticity/Uniqueness.lean)
- [Comparator 题面](lean/ComparatorChallenges/ElasticityUniqueness.lean)与[配置](lean/ComparatorChallenges/ElasticityUniqueness.json)
- [上游提交](UPSTREAM_REVISION)与[许可](LICENSE)

论文的目标是从一个有界连通光滑三维域的完整静态位移到牵引映射恢复两个光滑 Lamé 参数的唯一性。系数满足 μ > 0 和 3λ + 2μ > 0。这里的恢复是可辨识性，不提供重建算法。

## 本地复核

从 `lean/` 执行 `lake exe cache get Mathlib` 和 `lake build OAI.MathematicalPhysics.Elasticity.Uniqueness`。独立构建配置使用原版 Lean 4.34.1、原版 Mathlib 提交及上游 `autoImplicit = false`。`lakefile.upstream.lean` 和 `lake-manifest.upstream.json` 保留官方全仓配置。源码保留原模块路径，收录主结论所需的 42 个上游 Lean 模块。Comparator 题面的 `sorry` 是待验证命题的位置，证明位于另一个模块。

## 与 LeanSolid 的差距和补库计划

1. **三维变系数正问题。** 复用 (H^1_0) 上的 Korn、Poincaré、Lax–Milgram、三维点态能量分解和已有的非齐次 Dirichlet 换元。新增全域 (H^1) 位移–梯度空间与零迹子空间之间的桥，构造有界空间变系数 Lamé 双线性型，并用紧闭包把逐点正性变成统一强制性。验收为全正定范围内、每个迹商类的三维 Dirichlet 解存在且唯一。参考 [Variational](lean/OAI/MathematicalPhysics/Elasticity/Variational.lean) 的 `physical_coercive`、`dirichlet_exists` 和 `dirichlet_unique`。
2. **定义可复用的边界观测。** 构造 (H^1/H^1_0) 变分迹商空间上的位移到牵引配对，证明代表元无关、连续性、互等性和不同系数解之间的 Alessandrini 型积分恒等式。可先用常系数仿射解检查边界配对。上游仅使用变分商空间，未识别为边界坐标中的分数阶 Sobolev 空间。参考 [Variational](lean/OAI/MathematicalPhysics/Elasticity/Variational.lean) 的 `energy_eq_of_sameTrace`、`DN_eq_energy` 和 `interior_physical_transfer`。
3. **边界恢复与共同外延。** 从 DN 相等推出 Lamé 参数的边界值及所有阶边界导数相等，再构造域外一致、远处为常数的光滑正定延拓。这里需要光滑边界坐标、局部高频近似解和误差估计。先验收一个半空间平坦边界模型，再推广到曲边界。参考 [BoundaryJets](lean/OAI/MathematicalPhysics/Elasticity/BoundaryJets.lean) 与 [CommonExterior](lean/OAI/MathematicalPhysics/Elasticity/CommonExterior.lean)。
4. **内部唯一性。** 逐项桥接增广 Lamé 系统、加权估计、复几何光学解（CGO）、共同输运标架及其刚性。先证明固定假设下的 CGO 到物理解的传递，再检查全结论能否通过 LeanSolid 接口调用。参考 [PhysicalCGO](lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean)、[Rigidity](lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean) 和 [Uniqueness](lean/OAI/MathematicalPhysics/Elasticity/Uniqueness.lean)。这部分复参数是三维 CGO 的工具，和二维 Airy 或复势表示解决的问题不同。

第一批交付范围是第 1 和第 2 步。独立数学工具放在 Math，变系数本构、弱式和 DN 观测放在力学模块。实际适配上游代码时记录精确提交、文件和定理。第 3 和第 4 步用于复现论文主结论。
本地题面检查可在主证明编译后运行 lake env lean CheckStatement.lean。该文件用独立命名空间保留题面定义，并将上游证明直接赋给原命题。

### Windows 实测

Lean 4.34.1 已安装。首次缓存下载后，单独运行 cache unpack 补齐了剩余编译缓存。目标构建实际启动了论文模块，Windows 原生 Lean 在导入 Mathlib 和 Lean 自身的编译产物时报告文件读取错误，涉及 Locally.olean.private 与 DiscrTree.ir.sig。用同一个环境单独运行 Basic.lean 已成功核验基础定义。原样 Lake 多模块构建遇到上述读取错误。随后按导入拓扑顺序将 42 个官方模块放进一个临时 Lean 文件，保留声明和证明、在模块间隔离 section，并只加载一次 Mathlib。Lean 4.34.1 单进程检查成功，原题面 MainClaim 可直接使用上游证明，检查结果只含 propext、Classical.choice、Quot.sound。此检查使用 Lean 内核，没有运行 Comparator 的独立工具链。独立构建配置不改动 LeanSolid 的工具链或项目依赖。

### LeanSolid 的实现进度

已补充 [变分 DN](../../LeanSolid/Elastostatics/BoundaryResponse.lean) 和 [变系数 Lamé 形式](../../LeanSolid/Elastostatics/Sobolev/VariableLam%C3%A9.lean)。前者用零迹子空间的强制性构造 Dirichlet 解，在迹商两端消去代表元，并证明 DN 相等蕴含 Alessandrini 型等式。后者用 L∞ 系数乘法实现 L² 上的连续双线性型，复用已有 Korn、Poincaré 与 Lax–Milgram，得到在已有统一应变能下界和给定域内延拓时的正问题。论文 §2 是数学参考，上游 Variational.lean 的 physical_coercive、dirichlet_exists、DN_eq_energy 和 interior_physical_transfer 用于对照接口，LeanSolid 的证明沿本库的位移–梯度空间独立推导。

已补齐三维正定到统一下界的链条：闭包紧致给出共同正裕量，逐点密度估计覆盖负 λ，积分得到应变下界。零迹试验场的梯度在域外几乎处处为零，因而弱式和强制性可回到物理域积分。对应 Lean 定理包括 uniform_lame_margin、lame_density_lower、bodyLameForm_coercive 和 existsUnique_bodyDirichlet。数学参考为论文 §1–2，以及固定上游提交中 Variational.lean 的 Admissible.uniform_positive、elasticity_density_lower 和 physical_coercive。

[DomainGraph](../../LeanSolid/Elastostatics/Sobolev/DomainGraph.lean) 已构造在域内取 L² 的 H¹ 图和零迹商，验证光滑紧支撑图的限制，证明 ambient H¹₀ 与域内零迹图的线性等距等价，并补齐分量零延拓。对照上游 Basic.lean 的 SmoothJets、TestJets、H1、SameTrace。

[DomainElasticity](../../LeanSolid/Elastostatics/Sobolev/DomainElasticity.lean) 已在域内 H¹ 图上核验 Lamé 能量积分、零迹强制性、每个给定迹类的 Dirichlet 弱解唯一存在，以及 DN 配对。数学参考为论文 §2，接口对照上游 Variational.lean 的 physical_coercive、dirichlet_exists、dirichlet_unique、DN_eq_energy。

[EuclideanCoordinates](../../LeanSolid/Elastostatics/Sobolev/EuclideanCoordinates.lean) 已证明两种坐标保持域内测度，并逐分量核验导数列换位。向量值 L² 与标量分量 L² 的连续线性等价将光滑图、紧支撑图及其闭包双向对应，进而给出 H¹ 以及变分边界迹商的双射。参考上游 Basic.lean 的 coordVector、coordDeriv、SmoothJets、TestJets 和 SameTrace。

[EuclideanEnergy](../../LeanSolid/Elastostatics/Sobolev/EuclideanEnergy.lean) 核验欧几里得列布局与本库的应变、散度和虚功的对应，且两种弱解谓词等价。对应的欧几里得弱 Dirichlet 问题也有唯一解。另有独立的 [TraceTransport](../../LeanSolid/Elastostatics/TraceTransport.lean)，证明保持能量和零迹的线性等价保持变分 DN。

[EuclideanEnergy](../../LeanSolid/Elastostatics/Sobolev/EuclideanEnergy.lean) 已进一步证明分项虚功积分与论文 Basic.lean 的单积分形式相等，使用两项平方可积性及有界系数。欧几里得 DN 独立选择唯一弱解，再用迹代表元计算能量。euclideanDN_eq_domainDN 核验每对边界数据的响应一致，dn_eq_iff_euclideanDN_eq 核验两套材料的整个 DN 映射相等这一条件在两种表示下等价。coefficients_equal_of_euclidean_uniqueness 已将任意相应欧几里得唯一性推论传回 LeanSolid 的坐标，仍需把上游实际主定理作为该推论的来源。

参考论文 §1–2 和固定提交中 Basic.lean 的 energy、WeakSolution、dirichletSolution 与 DN。实现通过已证正问题构造 DN，避免在定理内部重新展开嵌套零迹子空间的强制性和类型类。

LeanSolid 4.36 的全库构建已通过。对 euclideanDN_eq_domainDN 与 euclideanEnergy_eq_singleIntegral 执行了公理检查，二者只依赖 propext、Classical.choice、Quot.sound。

将同一份官方合并检查文件交给 LeanSolid 的 4.36.0 环境试编时，原样源码出现 API 不匹配。例如 Restriction.lean 中调用的 `memLp_indicator_iff_restrict` 在该环境要求 `NullMeasurableSet s μ`，旧调用传入 `MeasurableSet s`。这两种条件可用 `MeasurableSet.nullMeasurableSet` 桥接。试编也出现后续声明缺失和心跳超限，尚未逐项验证其独立原因。官方源码仍按固定提交保存，原主定理在 4.34.1 的内核验证和 LeanSolid 在 4.36.0 的接口验证分别记录。

### 官方定义与 LeanSolid 的直接对接

[LeanSolidBridge.lean](LeanSolidBridge.lean) 使用官方 Basic.lean 和 Variational.lean 的实际类型。两库的光滑图、试验图、H¹ 和迹商在欧几里得坐标下定义相容。官方解与 LeanSolid 所选择的解满足同一个迹和弱式，由唯一性得到两解一致，再利用单积分等式证明两个 DN 算子相等。该文件还证明官方 MainClaim 蕴含使用 LeanSolid 笛卡尔 DN 的逐点系数唯一性。

在 LeanSolid 项目根目录运行 `./ResearchCompanions/OpenAI-372/CheckLeanSolid.ps1 -BridgeOnly` 可复核接口。4.36.0 下已通过，公理检查结果为 `propext`、`Classical.choice` 和 `Quot.sound`。移除 `-BridgeOnly` 会生成含 42 个上游模块和最终 [LeanSolidUniqueness.lean](LeanSolidUniqueness.lean) 的内核检查文件。脚本按依赖顺序合并源码，将工具链适配限定在生成文件中。

4.36.0 下另对截至 Restriction.lean 的上游依赖前缀做了独立检查，使用上述可测性接口转换后通过。

完整移植试编已越过 Restriction.lean。4.36.0 下曾在 Carleman.lean 的 `physical_system_identity`、Regularity.lean 的 `l1_inverse_fourier_distribution` 和 Solvability.lean 的 `physical_adjoint` 触发归约超限。改用显式合同引理和等式传递后，`-ThroughModule Solvability` 的整个依赖分支已通过。完整试编另曾报告 CGO.lean 的 `quantitative_cutoff_gain` 归约超限。最终入口的验收以完整命令成功退出且 `coefficients_equal_of_cartesian_DN_eq` 的公理检查通过为准。

早期的完整 4.36.0 试编在截止估计、边界坐标链式法则和复能量积分展开处报错。生成文件和试编日志在 LeanSolid 的 `.lake` 下。`-ThroughModule CGO` 可单独检查 CGO，重跑时仍以固定的官方源码为输入。

脚本要求 Lean 成功退出，并逐项核对最终入口的公理列表。任一额外公理或缺失的公理检查都使脚本失败。这也涵盖一次失败的编译继续输出 `#print axioms` 且列表中出现 `sorryAx` 的情形。

随后在 4.36.0 下编译了 CGO 前的完整依赖前缀。用该编译产物单独核验 CGO.lean 时，将 `quantitative_cutoff_gain` 中的隐式等式替换改为显式对拉普拉斯取合同后，整份 CGO.lean 已通过。最终命题现在明确定义为 `CartesianUniqueness`，独立的 DN 对接与公理检查也已重新通过。

### 端到端核验通过

Lean 4.36.0 对 42 个上游模块及实际调用 `OAI.Elasticity.global_uniqueness` 的 LeanSolid 最终定理完成了端到端检查。检查分三段编译，后段导入前段的 `.olean`。各段退出码均为 0。最终 `coefficients_equal_of_cartesian_DN_eq` 只依赖 `propext`、`Classical.choice`、`Quot.sound`。

边界复能量的最后一处超限通过 [ComplexEnergyIntegral.lean](ComplexEnergyIntegral.lean) 解决。该引理先对四个一般的可积实函数证明复线性积分恒等式，再应用于弹性能量密度。边界坐标的光滑性使用 Mathlib 的 `contDiff_pi`。未修改固定提交中的原始上游文件。

三个核验输入保存在 `.lake/openai-372-checkpoint` 下，依次为 `OpenAI372Prefix.lean`、`OpenAI372BoundaryPrefix.lean`、`CheckFinalBoundaryAudit.lean`。去掉各段的导入和全局选项、忽略空行后，已检查的 29,323 行与 `CheckLeanSolid.ps1 -GenerateOnly` 生成的源码逐行一致。最终公理输出保存在 `.lake/openai-372-final-boundary-audit.log`。
