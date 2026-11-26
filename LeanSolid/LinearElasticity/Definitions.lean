module

public import LeanSolid.Math.Calculus.Definitions

@[expose] public section

namespace LeanSolid.LinearElasticity

open LeanSolid.Math

/-- Infinitesimal strain given the displacement gradient at a material point. -/
noncomputable def strain {n : ℕ} (gradient : Tensor n) : Tensor n :=
  symPart gradient

/-- Green–Lagrange strain for a Cartesian deformation gradient. -/
noncomputable def greenStrain {n : ℕ} (F : Tensor n) : Tensor n :=
  (1 / 2 : ℝ) • (F.transpose * F - 1)

/-- Three-dimensional bulk modulus associated with the Lamé pair. -/
noncomputable def bulkModulus (lam mu : ℝ) : ℝ := lam + 2 * mu / 3

/-- First Lamé coefficient in terms of Young's modulus and Poisson's ratio in 3D. -/
noncomputable def lameFromYoungPoisson (young poisson : ℝ) : ℝ :=
  young * poisson / ((1 + poisson) * (1 - 2 * poisson))

/-- Shear modulus in terms of Young's modulus and Poisson's ratio in 3D. -/
noncomputable def shearFromYoungPoisson (young poisson : ℝ) : ℝ :=
  young / (2 * (1 + poisson))

/-- Young's modulus in terms of the three-dimensional Lamé parameters. -/
noncomputable def youngFromLame (lam mu : ℝ) : ℝ :=
  mu * (3 * lam + 2 * mu) / (lam + mu)

/-- Poisson's ratio in terms of the three-dimensional Lamé parameters. -/
noncomputable def poissonFromLame (lam mu : ℝ) : ℝ :=
  lam / (2 * (lam + mu))

/-- Cartesian isotropic Hooke law, intended for symmetric strain inputs.
The Lamé parameters carry no restrictions in this definition. -/
noncomputable def stress {n : ℕ} (lam mu : ℝ) (ε : Tensor n) : Tensor n :=
  (lam * ε.trace) • (1 : Tensor n) + (2 * mu) • ε

/-- Quadratic strain-energy density for the isotropic law. -/
noncomputable def energyDensity {n : ℕ} (lam mu : ℝ) (ε : Tensor n) : ℝ :=
  lam * ε.trace ^ 2 / 2 + mu * contract ε ε

/-- Isotropic compliance. The inverse theorems specify when the denominators are nonzero. -/
noncomputable def compliance {n : ℕ} (lam mu : ℝ) (σ : Tensor n) : Tensor n :=
  (1 / (2 * mu)) •
    (σ - (lam * σ.trace / ((n : ℝ) * lam + 2 * mu)) • (1 : Tensor n))

/-- Physical strict positivity on the space of nonzero symmetric strains. -/
def EnergyPosDef3 (lam mu : ℝ) : Prop :=
  ∀ A : Tensor 3, A.transpose = A → A ≠ 0 → 0 < energyDensity lam mu A

/-- Effective in-plane Lamé coefficient obtained by eliminating the normal strain. -/
noncomputable def planeStressLame (lam mu : ℝ) : ℝ :=
  lam * (2 * mu) / (lam + 2 * mu)

/-- Out-of-plane normal strain for zero out-of-plane normal stress. -/
noncomputable def planeStressNormalStrain (lam mu inPlaneTrace : ℝ) : ℝ :=
  -(lam * inPlaneTrace) / (lam + 2 * mu)

/-- Enlarge the in-plane tensor in Cartesian coordinates with zero transverse shear. -/
noncomputable def planeBlock (A : Tensor 2) (normal : ℝ) : Tensor 3 :=
  Matrix.of ![![A 0 0, A 0 1, 0], ![A 1 0, A 1 1, 0], ![0, 0, normal]]

/-- Displacement gradient in the fixed Cartesian basis. -/
noncomputable def displacementGradient {n : ℕ} (u : Vector n → Vector n)
    (x : Vector n) : Tensor n :=
  Matrix.of fun i j => partialDeriv (fun y => u y i) j x

/-- Small strain of a displacement field. -/
noncomputable def strainField {n : ℕ} (u : Vector n → Vector n) (x : Vector n) : Tensor n :=
  strain (displacementGradient u x)

/-- Cauchy traction for a supplied normal. A physical unit normal is chosen by the caller. -/
noncomputable def traction {n : ℕ} (σ : Tensor n) (normal : Vector n) : Vector n :=
  Matrix.mulVec σ normal

/-- Pointwise static balance with body force, on the region where the fields are differentiable. -/
def IsEquilibriumOn {n : ℕ} (Ω : Set (Vector n)) (σ : Vector n → Tensor n)
    (body : Vector n → Vector n) : Prop :=
  IsOpen Ω ∧ (∀ i j, DifferentiableOn ℝ (fun x => σ x i j) Ω) ∧
    ∀ x ∈ Ω, tensorDivergence σ x + body x = 0

end LeanSolid.LinearElasticity
