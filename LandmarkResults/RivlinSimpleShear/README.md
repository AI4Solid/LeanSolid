# Rivlin's Incompressible Simple Shear

<!-- metrics-paper: partial -->

**Primary reference.** R. S. Rivlin, *Large elastic deformations of isotropic materials IV. Further developments of the general theory*, *Philosophical Transactions of the Royal Society of London. Series A*, 241(835), 379–397 (1948). One application in the paper derives the surface forces needed for simple shear of a cuboid. [Original paper](https://doi.org/10.1098/rsta.1948.0024)

**Formalization status.** Verified classical result within the stated scope. Partial coverage of the paper.

## From the paper to Lean

Take the homogeneous deformation \(x_1=X_1+\gamma X_2,\ x_2=X_2,\ x_3=X_3\). LeanSolid verifies its stress formulas for the incompressible two-invariant energy
\(W=c_1(I_1-3)+c_2(I_2-3)\), using \(C=F^{\mathsf T}F\). The incompressibility multiplier \(p\) uses the library convention \(W-p(J-1)\).

Let \(d=2(c_1+2c_2)-p\) and \(\tau=2(c_1+c_2)\gamma\). The nominal stress is

\[
P=
\begin{pmatrix}
d & \tau & 0\\
(p-2c_2)\gamma & d & 0\\
0 & 0 & d+2c_2\gamma^2
\end{pmatrix}.
\]

The columns give force per unit reference area on the three positive cuboid faces. The corresponding negative faces carry the opposite tractions. With \(p=2(c_1+2c_2)\), the normal stress on the shear plane vanishes. The Cauchy shear is then \(\sigma_{12}=\tau\), and the normal stresses satisfy \(\sigma_{11}=\gamma\tau\) and \(\sigma_{33}=2c_2\gamma^2\).

| Quantity | LeanSolid representation |
| --- | --- |
| Homogeneous shear gradient and unit Jacobian | [simpleShearGradient and jacobian_simpleShearGradient](../../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L15) |
| Two-invariant stored energy and pressure multiplier | [mooneyRivlinEnergy and constrainedEnergy](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Incompressible.lean) |
| Nominal stress and reference traction | [rivlin_simpleShear_nominalStress](../../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L23), [rivlin_simpleShear_faceTraction](../../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L69) |
| Spatial stress with zero normal stress on the shear plane | [rivlin_simpleShear_cauchyStress](../../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L52) |

## Scope

This entry formalizes the homogeneous, incompressible Mooney–Rivlin specialization in modern notation. The input is the explicit shear gradient, and the proof derives the face loads from the stored energy using the existing first Piola and Cauchy stress interfaces. The paper's compressible and torsion examples and boundary-value uniqueness lie outside this entry.

```lean
import LeanSolid

#check LeanSolid.ContinuumMechanics.Hyperelasticity.rivlin_simpleShear_nominalStress
#check LeanSolid.ContinuumMechanics.Hyperelasticity.rivlin_simpleShear_cauchyStress
#check LeanSolid.ContinuumMechanics.Hyperelasticity.rivlin_simpleShear_faceTraction
```
