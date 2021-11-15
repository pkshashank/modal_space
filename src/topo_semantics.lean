import syntax
import topology.basic
import tactic.basic
set_option pp.notation true

universe u
-----------------------------------------------

/- Topo-models -/
structure topo_model {X : Type u} := (T : topological_space X) (V : ℕ → X → Prop)

#print topo_model.mk

open topological_space

/- Truth with respect to topological semantics-/
@[simp]
def top_tr {X : Type u} (M : topo_model) : X → bmod_form → Prop
| w (p n) := M.V n w
| _ ⊥ := false
| w (! φ) := ¬ (top_tr w φ)
| w (φ ⋀ ψ) := top_tr w φ ∧ top_tr w ψ
| w (◇ φ) := ∀ (U : set X), (M.T.is_open U → w ∈ U → (∃ (y ∈ U), top_tr y φ))


/- We could choose the notation ⊨, but I am not sure whether
that will be a problem later, because we have already used this
notation. I choose ⊩ as the notation -/
notation M ` - ` w ` ⊩ ` φ  : 50 := top_tr M w φ

/- A simple example  -/
example {X : Type u} (M : @topo_model X) (w : X) (φ : bmod_form) : M - w ⊩ φ → M - w ⊩ ◇ φ :=
begin
  intros h0,
  simp only [top_tr, exists_prop],
  intros U h1 h2,
  exact ⟨w,⟨h2,h0⟩⟩,
end

/- The set of points where ◇ φ is true, is the closure of the set 
of points where φ is true  -/

example (X : Type u) (M : @topo_model X) (φ : bmod_form) [M.T : topological_space X] : closure {w ∈  | M - w ⊩ φ} = { w ∈ M.T | M - w ⊩ ◇ φ} :=


