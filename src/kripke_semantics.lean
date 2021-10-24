import data.nat.basic
import syntax
import tactic.basic
set_option pp.notation true
attribute [instance] classical.prop_decidable


-- Kripke semantics
universe u

structure frames := {W : Sort u} (R : W → W → Prop)

#print frames
-- Some examples of frames. Natural numbers with the usual ordering.
example : frames := @frames.mk ℕ nat.lt 

-- Also a singleton set, which here can be denoted by a unit type forms a frame with the universal relation and with the empty relation
example : frames := @frames.mk unit (λ a b, true)

-- Next, we define models, which are frames + valuations
structure model extends frames := (V : ℕ → W → Prop)

open model

-- Definition of truth 

@[simp]
def tr (M : model) : M.W → bmod_form →  Prop
| w (p n) := M.V n w
| _ ⊥ := false
| w (! φ) := ¬ (tr w φ)
| w (φ ⋀ ψ) := tr w φ ∧ tr w ψ
| w (◇ φ) := ∃ (u : M.to_frames.W), (model.to_frames M).R w u ∧ tr w φ

-- Notation
notation M ` - ` w ` ⊨ ` φ : 50 := tr M w φ
-- We can check what the abbreviations look like
variables (φ ψ : bmod_form) (M : model) (w : M.W)
#check M - w ⊨ φ

example (φ ψ : bmod_form) (M : model) (w : M.W) :M - w ⊨ (φ ⋁ ψ) = (M - w ⊨ φ ∨ M - w ⊨ ψ) :=
begin
  apply propext,
  simp,
  tauto,
end

