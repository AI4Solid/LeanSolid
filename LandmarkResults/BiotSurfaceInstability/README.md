# Biot's Surface Instability in Plane Strain

<!-- metrics-paper: partial -->

**Primary reference.** M. A. Biot, *Surface instability of rubber in compression*, *Applied Scientific Research, Section A*, 12, 168–182 (1963). This entry verifies the critical stretch criterion for a plane-strain surface mode in an incompressible neo-Hookean half-space. [Original paper](https://doi.org/10.1007/BF03184638)

**Formalization status.** Verified classical result within the stated scope. Partial coverage of the paper.

## From the classical statement to Lean

Let \(\lambda\) denote the stretch parallel to the free surface, with \(0<\lambda\leq 1\), and let \(k>0\) denote horizontal wavenumber. The half-space occupies \(y<0\). The depth profile \(f\) of the stream function decays as \(y\to-\infty\). Eliminating incremental pressure from the modal equilibrium equations gives

\[
f''''-(1+\lambda^4)k^2 f''+\lambda^4 k^4f=0.
\]

The zero incremental traction conditions at \(y=0\) become \(f''+k^2 f=0\) and \(f'''=(2+\lambda^4)k^2 f'\). A nonzero decaying profile requires strict compression and \(\lambda^4-2\lambda+1=0\). Conversely, the strict compression root gives such a profile at every positive \(k\). The root is unique in \((0,1)\) and lies in \((0.54368,0.54369)\).

| Mechanical quantity or assumption | LeanSolid representation |
| --- | --- |
| Surface-parallel stretch and horizontal wavenumber | `stretch k : ℝ` with `0 < stretch`, `stretch ≤ 1`, and `0 < k` |
| Depth profile and its derivative chain | `f f₁ f₂ f₃ f₄ : ℝ → ℝ`, with successive `HasDerivAt` hypotheses |
| Decay and free-surface conditions | `Tendsto f atBot (𝓝 0)` and the shear and normal traction equations |
| Horizontally integrable multiwavenumber perturbation | [BiotFourierProblem](../../LeanSolid/ContinuumMechanics/Hyperelasticity/BiotFourier.lean), with horizontal regularity and integrability, local control of depth derivatives, and depth decay |

## Verified implementation

- [Modal stress equilibrium](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Biot.lean#L1154) connects the incremental stress and surface conditions to the criterion. [Modal necessity](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Biot.lean#L948) takes an arbitrary decaying depth profile at a positive wavenumber. [Modal existence](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Biot.lean#L1011) proves the converse within that class.
- [Critical stretch](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Applications.lean#L90) gives the unique strictly compressed root and [rigorous decimal bounds](../../LeanSolid/ContinuumMechanics/Hyperelasticity/Applications.lean#L117).
- [Real-line Fourier decomposition and reconstruction](../../LeanSolid/ContinuumMechanics/Hyperelasticity/BiotFourier.lean#L133) is an additional LeanSolid result for the reduced stream-function equations. It derives modal equations from the physical-space bulk and boundary equations and recovers the original field pointwise. [Criticality for nonzero localized perturbations](../../LeanSolid/ContinuumMechanics/Hyperelasticity/BiotFourier.lean#L217) gives the same necessary stretch criterion.

The entry covers the stated two-dimensional incremental half-space model. The periodic Fourier series extension remains open. Three-dimensional disturbances and nonlinear post-bifurcation behavior are outside this entry.

```lean
import LeanSolid.ContinuumMechanics

#check LeanSolid.ContinuumMechanics.Hyperelasticity.biot_quartic_of_positiveWavenumber_profile
#check LeanSolid.ContinuumMechanics.Hyperelasticity.biot_exists_profile_of_quartic_positiveWavenumber
#check LeanSolid.ContinuumMechanics.Hyperelasticity.BiotFourierProblem.decompose
```
