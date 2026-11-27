# Associated Problem Collections and Sources

This preliminary review focuses on sources relevant to elasticity, solid mechanics, and their PDEs. It records where the questions came from and what each source can establish about a candidate for Lean formalization.

## J. M. Ball, *Some Open Problems in Elasticity* (2002)

Ball's chapter in *Geometry, Mechanics, and Dynamics* presents numbered research questions in nonlinear elasticity, including existence and regularity of minimizers, weak equilibrium, fracture and self-contact, and dimension reduction. It also contains results under additional hypotheses. This makes the chapter a primary source for both the original questions and some of their known special cases. For example, §2.4, Problem 5 asks when energy minimizers satisfy the weak Euler–Lagrange equations. A Lean statement needs to specify the growth assumptions on the stored energy and the topology used for local minimality. The chapter provides the original formulation and its 2002 context. [Oxford publication record](https://ora.ox.ac.uk/objects/uuid%3Ac32ec402-84e3-490b-b070-4a053525a282) · [Author's full text](https://people.maths.ox.ac.uk/ball/Articles%20in%20Conference%20Proceedings%20and%20Books/JMB%202002%20re%20Marsden%2060th.pdf)

## AMR Problem Lists

AMR's *Problem Lists* page is a subject-organized directory of published lists and surveys. Its Analysis section links directly to Ball's chapter. It also points to collections in applied mathematics and mathematical physics. A LeanSolid entry can cite the original work and retain the AMR directory link as a route by which the problem was found. [AMR Problem Lists](https://amathr.org/problems/)

## UnsolvedMath

UnsolvedMath, published by Ulam, brings together individual entries from existing collections, including lists indexed by AMR. It provides searchable identifiers, literature notes, and status labels. For example, `AMR-019-0005` refers to Ball's weak Euler–Lagrange question and is labeled *Partially Solved* in the archive. Ball's original chapter, the AMR directory, and this UnsolvedMath entry therefore point to the same question. The archive label is useful for triage. A claim about a specific variant should identify the paper and its exact hypotheses. [Ball entries in UnsolvedMath](https://www.unsolvedmath.com/problems?category=9&difficulty=3&set=13) · [Dataset and provenance](https://huggingface.co/datasets/ulamai/UnsolvedMath)

## GenMech Lab, *Open Problems in Mechanics*

Curated by Bo Ni, this versioned collection covers selected mechanics questions, including elasticity, fracture, plasticity, contact, and structural mechanics. Its first release contains ten problems and lists September 30, 2026 as the literature review date. The entries describe the scope of existing research and the questions that remain. For example, CO01 separates general three-dimensional Coulomb contact from sharp two-dimensional time-incremental existence results. Dimension, friction conditions, and the distinction between incremental equilibrium and continuous evolution each affect the Lean statement. [Open Problems in Mechanics](https://generativemechanicslab.github.io/mechanics-open-problems/) · [Ballard and Iurlano's two-dimensional result](https://arxiv.org/abs/2303.16298)

## MathDB

MathDB is a broad community database of mathematical definitions, theorems, conjectures, and open problems. It provides a discovery route for related mathematics, particularly when a mechanics question appears in the literature under an analytical formulation. This review has yet to identify a direct MathDB record for Ball's Problem 5. [MathDB](https://mathdb.com/)

## OpenAI mathematics release, item 372

Item 372 in the OpenAI mathematics release concerns global uniqueness for the smooth three-dimensional isotropic elasticity inverse problem. Under the stated domain, smoothness, and positivity assumptions, equality of the full displacement-to-traction maps implies equality of both Lamé moduli. The scope is uniqueness of the coefficients. The LeanSolid research companion records the upstream proof, its hypotheses, and an end-to-end check of the connection to LeanSolid's boundary map. Item 372 is a worked example of how to record a formalized result with an exact scope and reproducible verification. [OpenAI release](https://openai.com/index/sharing-ai-progress-in-mathematics/) · [Upstream scope at the pinned revision](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/372.md) · [LeanSolid research companion](../ResearchCompanions/OpenAI-372/README.md)
