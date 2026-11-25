# LeanSolid

LeanSolid is a pre-alpha project for formalizing solid mechanics in Lean 4 with Mathlib. It aims to make modeling assumptions explicit, express constitutive laws as reusable definitions, verify derivations, and support AI-assisted reasoning with Lean as the proof checker.

## Implemented

- `LeanSolid.Constitutive.Uniaxial` defines scalar Hooke's law and quadratic elastic strain energy density. It proves the half-stress-times-strain identity and energy nonnegativity under a nonnegative Young's modulus.
- `LeanSolid.Examples.Uniaxial` proves that stress determines strain uniquely when Young's modulus is strictly positive.

## Build

Install [Elan](https://github.com/leanprover/elan), then run these commands from the repository root.

```sh
lake exe cache get
lake build
```

The Lean toolchain and Mathlib revision are pinned. The build treats project warnings as errors, including warnings for unfinished proofs.

## Roadmap

The v0.1 target is December 9, 2026. The initial milestone is a reproducible build and a small set of documented, checked linear-elastic examples. The broader roadmap covers the following areas.

- **Linear elasticity.** Extend the scalar example to small-strain kinematics and tensor constitutive laws with explicit material assumptions.
- **Fracture.** Formalize energy release and selected Griffith-type derivations.
- **Interfaces.** Specify traction–separation laws and assumptions behind interface conditions.
- **Instability.** Work through energy-based stability and elementary bifurcation examples.

## Related work

Thanks to the [lean-mechanics contributors](https://github.com/raphos-com/lean-mechanics). Their Lean 4 and Mathlib library spans classical, continuum, and discrete mechanics, including constitutive theory, fracture, contact, and stability. LeanSolid starts with small constitutive examples and focuses on expressing assumptions and checking individual derivations, including those developed with AI assistance.

## Maintainer

Created and maintained by Siyuan Song ([@ssong26](https://github.com/ssong26)), a postdoctoral researcher in solid mechanics at Brown University.

Interested in collaborating on formalizing solid mechanics in Lean? Feel free to [open a GitHub issue](https://github.com/ssong26/LeanSolid/issues).

## License

[Apache-2.0](LICENSE).
