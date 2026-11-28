# Landmark Results

This index connects classical results in theoretical solid mechanics to the declarations that already prove them in LeanSolid. Each entry gives the historical reference, states the result in modern notation, and links directly to the verified Lean declaration.

| Classical result | Primary reference | LeanSolid declaration |
| --- | --- | --- |
| [Betti's reciprocal theorem](BettiReciprocity/README.md) | Enrico Betti, *Teoria della elasticità* (1872–1873) | [`LeanSolid.Elastostatics.betti`](../LeanSolid/Elastostatics/Corollaries.lean#L24) |
| [Eshelby's circular inclusion under uniform dilatation](EshelbyInclusion/README.md) | J. D. Eshelby, *The determination of the elastic field of an ellipsoidal inclusion, and related problems* (1957) | [`circular_dilatation`](../LeanSolid/Plane/Eshelby/Corollaries.lean#L90), [`interior_strain`](../LeanSolid/Plane/Eshelby/Corollaries.lean#L46) |
| [Rivlin's incompressible simple shear](RivlinSimpleShear/README.md) | R. S. Rivlin, *Large elastic deformations of isotropic materials IV* (1948) | [`rivlin_simpleShear_nominalStress`](../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L23), [`rivlin_simpleShear_cauchyStress`](../LeanSolid/ContinuumMechanics/Hyperelasticity/RivlinShear.lean#L52) |
| [Biot's surface instability in plane strain](BiotSurfaceInstability/README.md) | M. A. Biot, *Surface instability of rubber in compression* (1963) | [Modal criterion](../LeanSolid/ContinuumMechanics/Hyperelasticity/Biot.lean#L948), [Fourier decomposition and reconstruction](../LeanSolid/ContinuumMechanics/Hyperelasticity/BiotFourier.lean#L133) |

Each row records a verified classical result. The individual entries state how much of the original publication is covered. Rivlin and Biot each represent a partial paper formalization.

For each new entry, identify the particular result within the paper, map its quantities and assumptions to Lean, and describe the scope of the existing proof. Link to the library declaration as the source of the proof. These entries are documentation and require no additional Lean imports.
