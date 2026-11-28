# Eshelby's Inclusion Problem — Circular Dilatation

<!-- metrics-paper: partial -->

**Primary reference.** J. D. Eshelby, *The determination of the elastic field of an ellipsoidal inclusion, and related problems*, *Proceedings of the Royal Society of London. Series A*, 241(1226), 376–396 (1957). The result associated with this entry is the uniform interior strain induced by a homogeneous transformation strain in an ellipsoidal inclusion. [Original paper](https://doi.org/10.1098/rspa.1957.0133)

## From the classical statement to Lean

LeanSolid verifies a circular plane-strain counterpart of Eshelby's uniformity result. The inclusion and the infinite matrix share Lamé moduli \(\lambda,\mu\). A uniform in-plane eigenstrain \(\alpha I_2\) is prescribed in the inclusion, with zero axial eigenstrain. For a disk of radius \(R\), take radial displacements \(u_{\mathrm{in}}(r)=Ar\) and \(u_{\mathrm{out}}(r)=B/r\). Matching displacement and radial traction at \(r=R\) gives

\[
AR=B/R,\qquad
2(\lambda+\mu)(A-\alpha)=-2\mu B/R^2.
\]

For \(R>0\) and \(\lambda+2\mu\ne0\), the unique pair of matching amplitudes is

\[
A=\frac{\lambda+\mu}{\lambda+2\mu}\alpha,\qquad B=AR^2.
\]

The radial and hoop components of total interior strain are both \(A\), obtained from \(u_{\mathrm{in}}'(r)\) and \(u_{\mathrm{in}}(r)/r\).

| Mechanical quantity or assumption | LeanSolid representation |
| --- | --- |
| Common isotropic Lamé moduli and in-plane eigenstrain amplitude | `lam mu α : ℝ` |
| Positive radius and nondegenerate amplitude denominator | `0 < R`, `lam + 2 * mu ≠ 0` |
| Interior and exterior radial amplitudes | `A B : ℝ` |
| Displacement and radial traction continuity | [`IsMatched lam mu α R A B`](../../LeanSolid/Plane/Eshelby/Definitions.lean#L15) |
| Interior total strain amplitude | [`amplitude lam mu α`](../../LeanSolid/Plane/Eshelby/Definitions.lean#L12) |

## Verified implementation

- [`matched_iff`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L18) gives the amplitude formulas, and [`circular_dilatation`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L90) proves existence and uniqueness of the matching pair.
- [`interior_strain`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L46) proves that both total normal strains equal \(A\) at nonzero radius. [`interior_stress_equilibrium`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L54) verifies constant interior stress and radial equilibrium.
- [`circular_interface`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L100) checks displacement and constitutive radial traction at the interface. [`exterior_equilibrium`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L69) and [`exterior_far_field`](../../LeanSolid/Plane/Eshelby/Corollaries.lean#L77) verify equilibrium and decay of the exterior branch.

The proof verifies the radial formulas away from the axis and gives uniqueness within the two-amplitude radial ansatz. The full three-dimensional ellipsoidal result and uniqueness among general displacement fields are outside the scope of these declarations.

```lean
import LeanSolid

#check LeanSolid.Plane.Eshelby.circular_dilatation
#check LeanSolid.Plane.Eshelby.interior_strain
#print axioms LeanSolid.Plane.Eshelby.circular_dilatation
#print axioms LeanSolid.Plane.Eshelby.interior_strain
```

Verified locally with Lean 4.36.0. The axiom reports list `propext`, `Classical.choice`, and `Quot.sound`.
