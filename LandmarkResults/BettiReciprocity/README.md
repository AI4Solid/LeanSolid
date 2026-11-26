# Betti's Reciprocal Theorem

**Primary reference.** Enrico Betti, *Teoria della elasticità*, *Il Nuovo Cimento*, series 2, vols. 7–10 (1872–1873). Reprinted in *Opere matematiche*, vol. II (1913), pp. 291–378. The memoir develops mathematical elasticity and establishes reciprocity between two equilibrium states of the same elastic body. [Digitized collected edition](https://www.mm.bme.hu/~kossa/books/Betti%20-%201913%20-%20Opere%20Matematiche%20Vol%202.pdf)

## From the classical statement to Lean

Consider two load systems on the same linear-elastic body, with responses \(u\) and \(v\). If \(f\) and \(g\) are the corresponding load functionals, Betti's theorem says that the work of the first load on the second displacement equals the work of the second load on the first displacement:

\[
f(v)=g(u).
\]

For a continuum model with body forces and prescribed tractions, the load functional combines body-force work over the domain and traction work over the loaded boundary. In the library's weak formulation, the admissible space \(V\) encodes the homogeneous essential boundary conditions and each load is represented by a continuous linear functional on \(V\).

| Mechanical quantity or assumption | LeanSolid representation |
| --- | --- |
| Common admissible displacement space | `V`, a real normed vector space |
| Elastic bilinear form | `a : V →L[ℝ] V →L[ℝ] ℝ` |
| Material symmetry in the weak form | `∀ x y, a x y = a y x` |
| Equilibrium under each load | `IsWeakSolution a f u` and `IsWeakSolution a g v` |
| Reciprocal work | `f v = g u` |

## Verified implementation

- **Main result.** [`LeanSolid.Elastostatics.betti`](../../LeanSolid/Elastostatics/Corollaries.lean#L24) tests the two equilibrium equations with the other solution and uses symmetry: \(f(v)=a(u,v)=a(v,u)=g(u)\).
- **Weak equilibrium.** [`LeanSolid.Elastostatics.IsWeakSolution`](../../LeanSolid/Elastostatics/Definitions.lean#L12) defines the equilibrium equation against every admissible test displacement.
- **Elasticity instance.** [`LeanSolid.Elastostatics.Sobolev.variableLameForm_comm`](../../LeanSolid/Elastostatics/Sobolev/VariableLam%C3%A9.lean#L54) proves symmetry for the library's spatially varying isotropic Lamé form.

The verified claim is static reciprocity for two given weak solutions on a common admissible space. The proof needs symmetry and weak equilibrium. Existence and uniqueness of the responses and the identification of physical traction work with a chosen load functional belong to the particular boundary-value model.

The existing declaration is available through the public library:

```lean
import LeanSolid.Elastostatics

#check LeanSolid.Elastostatics.betti
#print axioms LeanSolid.Elastostatics.betti
```

Verified locally with Lean 4.36.0. The axiom report lists `propext`, `Classical.choice`, and `Quot.sound`.
