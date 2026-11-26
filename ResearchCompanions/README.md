# Research Companions

This directory follows developments in theoretical solid mechanics through Lean companions to selected research papers. New entries are added as papers are selected. Each entry collects the paper or its source link, the claims and assumptions being formalized, the Lean integration code, and instructions for reproducing the checks. Record the upstream revision when reusing an existing formalization, along with the verification results and any open steps.

Companions are standalone examples and applications. They can import LeanSolid. The default `import LeanSolid` and library build are independent of the companions.

## Current companions

- **OpenAI #372** covers the inverse boundary problem for three-dimensional isotropic elasticity. The companion connects the official uniqueness proof to LeanSolid's Dirichlet-to-Neumann map and records the completed verification. [OpenAI #372](OpenAI-372/README.md)
