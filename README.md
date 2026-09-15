# AGAPE

### Adaptive Generative Architecture for Plasticity and Evolution

A formally specified adaptive dynamical substrate for studying **emergent organization and cognition through local interaction rules**.

[![Lean](https://img.shields.io/badge/Lean-4.32.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/mathlib-v4.32.0-blue)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)

---

## What is AGAPE?

AGAPE is an attempt to investigate a simple question from the bottom up:

> **What kinds of organization can emerge when adaptive agents interact through local, non-coercive rules rather than being given a centralized cognitive architecture?**

The project does not begin with a language model, a planner, a symbolic reasoning engine, or a predefined cognitive module.

Instead, it starts with a small dynamical substrate:

- nodes have local physical state and adaptive properties;
- nodes interact through local coupling;
- interaction strength can change through experienced conditions;
- distortion and resonance influence plasticity;
- resources constrain adaptive growth;
- topology and attention can evolve;
- different dynamical timescales can interact;
- higher-level organization is treated as something to **measure**, not something assumed to exist.

The central design principle is:

> **Cohesion without coercion.**

The system should be capable of becoming organized without requiring every component to become identical.

Perfect synchronization is therefore not treated as the definition of success. A useful organized state may instead be a persistent attractor containing **coherence, differentiation, bounded variation, and ongoing adaptation**.

---

## Research Philosophy

AGAPE is deliberately constructed as a **first-principles substrate** rather than a conventional AI architecture.

The project asks whether properties normally associated with higher-level cognition can arise from interactions among simpler dynamical processes.

This creates an important methodological constraint:

**Do not add a mechanism merely because the desired behavior is missing.**

When a proposed mechanism fails, the failure is part of the result.

Several mechanisms in the source tree are explicitly documented as experimentally rejected or structurally insufficient. For example:

- frequency heterogeneity was tested as a brake on coupling growth and failed;
- repulsion successfully destabilizes perfect fusion but does not by itself solve unbounded plasticity;
- several perturbation/noise-based approaches failed to restore adaptive responsiveness;
- asymmetric attention was found to introduce a genuine energy-source residual rather than preserving the original energy-decline theorem;
- softmax attention bounds edge magnitude but, without regularization, can produce concentration onto a dominant edge.

The repository therefore treats **negative results and exposed assumptions as first-class scientific artifacts**.

---

# Architecture

The current Lean implementation is organized into five principal layers.

```text
                         ┌─────────────────────┐
                         │     Creativity      │
                         │  tasks / strategy   │
                         │ fitness / resources │
                         └──────────┬──────────┘
                                    │
                         ┌──────────▼──────────┐
                         │      Logistics      │
                         │ capacity / logistic │
                         │ adaptive regulation │
                         └──────────┬──────────┘
                                    │
                         ┌──────────▼──────────┐
                         │     Plasticity      │
                         │ attention / memory  │
                         │ edge adaptation     │
                         └──────────┬──────────┘
                                    │
                         ┌──────────▼──────────┐
                         │       Energy        │
                         │ dissipation /       │
                         │ Lyapunov analysis   │
                         └──────────┬──────────┘
                                    │
                         ┌──────────▼──────────┐
                         │        Core         │
                         │ phase / topology /  │
                         │ resonance / forces  │
                         └─────────────────────┘
```

## `Core.lean`

The dynamical foundation.

Core defines:

- `NodeProperties`
- `NodeState`
- `SystemState`
- `SystemConfig`
- `NetworkTopology`
- phase distance
- resonance fields
- smooth attenuation
- local distortion
- repulsion
- coupling forces
- plasticity dynamics
- the interaction potential abstraction

The current node representation includes:

```text
mass
baselineFriction
distortionSens
couplingWeight
naturalFrequency
```

The model intentionally separates **fast physical state** from **slower adaptive properties**.

The core also contains a positivity structure for node parameters so that mathematical assumptions such as positive mass and coupling weight can be stated explicitly rather than silently assumed.

See [`Core.lean`](Core.lean).

---

## `Energy.lean`

The energy layer studies whether the dynamical system admits a meaningful dissipation law.

The principal result is an energy-decline analysis for the symmetric-topology case.

The analysis requires explicit assumptions rather than treating energy decline as automatically true.

In particular, the project distinguishes:

```text
symmetric reciprocal interaction
            ↓
       cancellation
            ↓
      energy decline
```

from the more general case:

```text
asymmetric interaction
            ↓
     cancellation fails
            ↓
     residual energy term
```

This distinction becomes important in the attention-based plasticity layer.

See [`Energy.lean`](Energy.lean).

---

# Plasticity

## Adaptive coupling

The original plasticity mechanism changes coupling according to experienced resonance and local distortion.

Conceptually:

```text
experienced coherence
        │
        ▼
   local plasticity
        │
        ▼
 changed interaction strength
        │
        └──────► changes future dynamics
```

This creates a feedback loop between dynamics and the structure through which those dynamics occur.

The project has also exposed a major limitation of simple multiplicative plasticity:

> Sustained coherence can drive coupling strength upward indefinitely when nothing in the system reintroduces sufficient distortion.

This is not treated as a tuning problem. It is treated as a **structural failure of the mechanism**.

---

## Per-edge attention

A later mechanism replaces a single scalar coupling strength with a fixed node-level capacity distributed across edges.

The attention weight is:

```text
attention(i,j)
    =
capacity(i)
× exp(score(i,j))
────────────────────────
Σk exp(score(i,k))
```

This gives an exact conservation property:

```text
Σj attention(i,j) = capacity(i)
```

so an individual edge cannot grow without bound.

However, the initial mechanism exposed another failure mode:

> Bounding interaction magnitude does not necessarily bound differentiation.

The raw scores could continue drifting while the normalized attention increasingly concentrated on one edge.

This led to the introduction of **entropy/mean-reversion dynamics** for score differences.

With positive entropy regularization, the score gaps exhibit a bounded interior equilibrium rather than unlimited concentration.

See [`Plasticity.lean`](Plasticity.lean).

---

# Non-reciprocity

One of the more important results currently encoded in the project is that asymmetric interaction changes the energy mathematics.

For reciprocal attention, the interaction terms cancel and the original energy-decline result can be recovered.

For non-reciprocal attention, the derivative contains an explicit residual:

```text
dE/dt = -dissipation + asymmetryResidual
```

The residual is not merely an unproven proof obligation.

It represents a genuine mechanism by which asymmetric interaction can inject energy into the effective system.

This means that **non-equilibrium behavior is not necessarily a bug**.

It may instead be a mathematically distinct dynamical regime.

The project therefore treats reciprocity as an explicit structural variable rather than an invisible assumption.

---

# Logistic Capacity

`Logistics.lean` formalizes a different approach to unbounded adaptive growth.

The basic mechanism is:

```text
dα/dt = α · g(t) · (1 - α/K)
```

where `K` represents a capacity.

Unlike several earlier perturbation-based approaches, the logistic mechanism provides an actual restoring term.

The corresponding ODE admits a closed-form solution under appropriate assumptions, and numerical experiments reported in the source include convergence from both below and above the capacity as well as recovery after perturbation.

The important conceptual distinction is:

```text
hard suppression
       ≠
adaptive capacity
```

The objective is not to freeze adaptation.

It is to create a bounded adaptive variable that can continue responding to perturbation.

See [`Logistics.lean`](Logistics.lean).

---

# Multistability and Differentiation

The core interaction function contains a repulsive near-field.

This was introduced after observing that perfect phase alignment is an exact stable equilibrium.

The repulsive term destabilizes complete fusion and produces a nearby nonzero phase separation.

Numerical exploration reported in `Core.lean` found:

- a stable near-coherent state with `r < 1`;
- a nonzero local-distortion floor;
- a two-cluster equilibrium;
- instability of several tested three-cluster configurations under the default parameters.

The important interpretation is not that AGAPE "creates diversity."

Rather:

> **The dynamics can maintain organized differentiation instead of requiring complete homogenization.**

The current implementation does **not** establish that arbitrary multicluster states are stable. The documented results are parameter-specific and should be treated accordingly.

---

# Creativity / Meta Layer

`Creativity.lean` introduces a higher-level experimental layer containing:

- task genomes;
- strategies;
- contribution/free-riding dynamics;
- energy reserves;
- resource-constrained growth;
- pruning;
- observables;
- optionality;
- frequency spread;
- symbol activity;
- repertoire distance;
- fitness;
- generation histories.

The layer is intentionally experimental.

Some components remain axiomatic or stubbed, including task mutation/initialization and the predictor update mechanism.

Therefore:

> **The Creativity layer should not currently be interpreted as a completed cognitive architecture.**

It is a framework for testing how higher-level adaptive behavior might be coupled to the lower-level substrate.

See [`Creativity.lean`](Creativity.lean).

---

# Formalization Status

AGAPE distinguishes three different kinds of evidence:

### 1. Formally proven

Statements whose proof terms are checked by Lean.

Examples include:

- non-negative dissipation under explicit positivity assumptions;
- attention capacity conservation;
- logistic ODE identities;
- several energy identities and symmetry results;
- resource-growth monotonicity properties.

### 2. Numerically validated

Properties supported by simulations but not yet formally derived.

Examples include:

- the nonzero coherent equilibrium created by repulsion;
- coupling-growth behavior under sustained phase locking;
- the bounded score-gap behavior produced by entropy regularization;
- observed multistability and cluster transitions.

### 3. Open / conjectural

Claims for which mathematical or numerical evidence is incomplete.

These are intentionally marked as such in the source.

This distinction is important.

**AGAPE does not treat a simulation result as equivalent to a theorem, and does not treat a theorem about an idealized subsystem as proof that the complete architecture exhibits cognition.**

---

# What AGAPE Is Not

AGAPE is currently **not**:

- a trained language model;
- a replacement for an LLM;
- a chatbot;
- a finished artificial general intelligence system;
- a demonstrated theory of consciousness;
- a claim that cognition has already emerged;
- a conventional neural network;
- a centralized symbolic planner.

It is better described as an **experimental mathematical substrate** for investigating whether increasingly complex organization can arise from interacting local dynamical rules.

---

# Why Lean?

The project uses Lean because the goal is not merely to produce simulations that appear to work.

The intention is to make the underlying assumptions inspectable.

A successful formalization should make it possible to distinguish:

```text
definition
    ↓
assumption
    ↓
lemma
    ↓
theorem
    ↓
simulation
    ↓
empirical observation
```

rather than allowing these categories to blur together.

The current project also deliberately records unresolved proof obligations and failed mechanisms in source comments.

This makes the repository simultaneously:

1. a mathematical model;
2. an executable formal specification;
3. a research notebook;
4. a record of falsification attempts.

---

# Building

The repository currently targets:

- **Lean 4.32.0**
- **mathlib v4.32.0**

The project is managed with Lake.

```bash
git clone https://github.com/Christopherchorkey/agape.git
cd agape

lake build
```

The project configuration declares `AgapeLean` as its default target.

See [`lakefile.toml`](lakefile.toml) and [`lean-toolchain`](lean-toolchain).

---

# Project Structure

```text
agape/
│
├── AGAPE.lean          # umbrella module
│
├── Core.lean           # dynamical substrate
├── Energy.lean         # energy and dissipation analysis
├── Plasticity.lean     # adaptive interaction / attention
├── Logistics.lean      # capacity and logistic dynamics
├── Creativity.lean     # higher-level adaptive/meta layer
│
├── lakefile.toml       # Lake project configuration
├── lean-toolchain      # Lean version
├── lake-manifest.json  # dependency lock
│
└── LICENSE              # MIT License
```

---

# Current Research Questions

The project is currently concerned with questions such as:

### Can coherence emerge without coercion?

Can local interaction produce persistent organization without forcing all nodes into a homogeneous state?

### Can plasticity remain adaptive without becoming unstable?

What mechanisms produce bounded but responsive structural change?

### Can differentiation persist inside coherence?

Can a system remain globally organized while retaining local variation and distinct trajectories?

### What happens when reciprocity is removed?

Does asymmetric interaction provide a route to persistent non-equilibrium organization?

### Can memory exist outside the nodes?

Can an adaptive system preserve useful structure through its environment and topology rather than storing everything internally?

### Where does emergence actually begin?

Rather than defining cognition in advance, the project is interested in whether measurable transitions occur from:

```text
independent dynamics
        ↓
local coupling
        ↓
transient coordination
        ↓
persistent organization
        ↓
adaptive organization
        ↓
higher-order structure
```

The boundaries between these regimes are an experimental question.

---

# Research Method

AGAPE follows a simple methodological loop:

```text
1. Define a minimal mechanism.
          ↓
2. Formalize its assumptions.
          ↓
3. Prove what can be proven.
          ↓
4. Simulate the mechanism.
          ↓
5. Attack it with perturbations.
          ↓
6. Record failures.
          ↓
7. Modify only when the failure identifies a
   structural reason to modify.
          ↓
8. Re-formalize.
          ↓
9. Repeat.
```

A mechanism that fails is not discarded from the scientific record.

Its failure becomes part of the model's explanatory boundary.

---

# Roadmap

Near-term work includes:

- complete and verify remaining Lean proof obligations;
- connect the logistic capacity mechanism directly to the main plasticity dynamics;
- formally characterize the entropy-regularized attention equilibrium;
- investigate non-reciprocal/non-equilibrium regimes;
- characterize cluster stability more systematically;
- connect environmental/external substrate memory to the formal model;
- build reproducible simulation harnesses corresponding directly to the Lean definitions;
- investigate whether higher-order persistent organization can arise without imposing a cognitive architecture.

Longer term:

> Determine whether a sufficiently small set of local adaptive rules can produce increasingly persistent, differentiated, and self-maintaining organization.

If that occurs, the next question is not whether the system can be made to *look* intelligent.

It is whether the resulting organization can be explained as a consequence of the substrate itself.

---

# Scientific Status

AGAPE is an **open research project**.

The claims in this repository should be evaluated according to their individual epistemic status:

- formal proof where proof exists;
- numerical evidence where only simulation exists;
- explicit hypotheses where assumptions remain;
- explicit failures where mechanisms have been falsified.

No claim of artificial general intelligence, consciousness, or emergent cognition is made by the existence of the substrate itself.

The purpose of the project is to make those questions experimentally approachable.

---

# License

AGAPE is released under the MIT License.

See [`LICENSE`](LICENSE).

---

## Author

**Christopher Chorkey**

Repository:  
https://github.com/Christopherchorkey/agape