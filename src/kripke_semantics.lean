import data.nat.basic
import syntax
import tactic.basic
set_option pp.notation true
attribute [instance] classical.prop_decidable

---------------------------------------------------------
-- Kripke semantics
universe u

structure frames := {W : Sort u} (R : W → W → Prop)

-- Some examples of frames. Natural numbers with the usual ordering.
example : frames := ⟨nat.lt⟩

-- Also a singleton set, which here can be denoted by a unit type forms a frame with the universal relation and with the empty relation
example : frames := @frames.mk unit (λ a b, true)

-- Next, we define models, which are frames + valuations
structure model extends frames := (V : ℕ → W → Prop)

open model

-- Definition of truth 

@[simp]
def tr (M : model) : M.W → bmod_form → Prop
| w (p n) := M.V n w
| _ ⊥ := false
| w (! φ) := ¬ (tr w φ)
| w (φ ⋀ ψ) := tr w φ ∧ tr w ψ
| w (◇ φ) := ∃ (u : M.to_frames.W), (model.to_frames M).R w u ∧ tr u φ

-- The usual notation for truth
notation M ` - ` w ` ⊨ ` φ  : 50 := tr M w φ

----------------------------------------------

section abbreviations

variables (φ ψ : bmod_form) (M : model) (w : M.W)
include φ ψ M w

-- We can check what the abbreviations look like
example : M - w ⊨ (φ ⋁ ψ) = (M - w ⊨ φ ∨ M - w ⊨ ψ) :=
begin
  simp, -- Lean's simplifier does most of the job here.
  tauto, -- We are proving a propositional tautology
end

-- It is important to see how truth of boxed formulas is interpreted
example : (M - w ⊨ □ φ) = ∀ (u : M.W), (M.R w u → M - u ⊨ φ) := by simp

-- Similarly for other abbreviations we have the following.

example : (M - w ⊨ (φ ⇒ ψ)) = (M - w ⊨ φ → M - w ⊨ ψ) := by simp
example : (M - w ⊨ ⊤) := 
begin
  iterate 2 {rw tr},
  trivial,
end

end abbreviations

---------------------------------------------------------

-- Next, we define validity with respect to a frame
def valid (φ : bmod_form) (F : frames) : Prop := ∀ (v : ℕ → F.W → Prop), ∀ (w : F.W), ⟨F,v⟩-w ⊨ φ

-- Class of frames
def valid_class (φ : bmod_form) (clF : frames → Prop) := ∀ (F : frames), clF F → valid φ F

-- Note : I could have used a set membership instead of valid_class being a `guarded` kind of formula, but that was giving some error.

-- Next, we have an example, which says that the formula p → ◇ p is valid on the class of all reflexive frames.

variables (α : Sort u) (rel : α → α → Prop) (hr : reflexive rel) 

-- We first try to create the object `the class of all reflexive frames`, which we call as rel_cl
def rel_cl (f : frames) : Prop := reflexive f.R

example : valid_class (p 1 ⇒ ◇ p 1) (rel_cl) :=
begin
  rw valid_class,
  unfold rel_cl,
  intros F hr,

  rw valid,
  intros val w,
  let M := model.mk F val,
  show M - w ⊨ (p 1 ⇒ ◇ p 1),
  simp [tr],

  intro hw,
  existsi w,
  split,
  exact hr w,
  assumption,
end

-------------------------------------------------------------
