import LeanSolidBridge
import OAI.MathematicalPhysics.Elasticity.Uniqueness

namespace LeanSolid.Elastostatics.Sobolev.Domain

/-- Full-data uniqueness for the Cartesian LeanSolid DN map under the paper's
smoothness and positivity hypotheses. -/
theorem coefficients_equal_of_cartesian_DN_eq : CartesianUniqueness :=
  coefficients_equal_of_upstream_mainClaim OAI.Elasticity.global_uniqueness

#print axioms coefficients_equal_of_cartesian_DN_eq

end LeanSolid.Elastostatics.Sobolev.Domain
