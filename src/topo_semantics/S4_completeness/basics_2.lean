import topo_semantics.topo_sound_complete
import data.nat.basic

/-- Identifying a natural number with the corresponding
prop_form and bmod_form, i.e. n with p' n -/
instance : has_coe ℕ prop_form := ⟨λ n, p' n⟩
instance : has_coe ℕ bmod_form := ⟨λ n, 'p n⟩

/-- The coercion from α to β can be lifted to their lists -/
instance {α β : Type*} [has_coe α β] : has_coe (list α) (list β) := ⟨λ l, list.rec_on l [] (λ a la lb, (a : β) :: lb )⟩

/-- 'And' for a list of modal formulas-/
@[simp]
def and_list_bmods : list bmod_form → bmod_form
| [] := '⊤
| (φ :: l) := φ '⋀ and_list_bmods l

/-- 'And' for a list of propositional formulas-/
@[simp]
def and_list_pfs : list prop_form → prop_form
| [] := !' ⊥'
| (φ :: l) := φ ⋀' (and_list_pfs l)

-- Simplified notation for and_list functions
notation `& ` B := and_list_bmods B
notation `& ` B := and_list_pfs B

/-- List seen as a set -/
def list_to_set {α : Type*} : list α → set α
| [] := ∅
| (a :: l) := {a} ∪ list_to_set l

instance list_coe_to_set {α : Type*} : has_coe (list α) (set α) :=
⟨list_to_set⟩

/-- Definintion of Γ being Λ-consistent-/
def consistent (Γ Λ : set bmod_form) := ¬ ∃ (B : list bmod_form),
↑B ⊆ Γ ∧ ((& B) '⇒ '⊥) ∈ Λ

/-- Definition of Γ being maximally Λ-consistent (MCS)-/
def mcs (Γ Λ : set bmod_form) := consistent Γ Λ ∧ ¬ ∃
Ω, (consistent Ω Λ ∧ Γ ⊂ Ω)

/-- Delete every occurence of an element in a list -/
noncomputable def list.delete_every {α : Type*} (a : α) : list α → list α
| [] := []
| (b :: l) := if a = b then list.delete_every l else b :: list.delete_every l

/-- Delete every occurance of an element from a list and add
it in front -/
noncomputable def list.headed {α : Type*} (as : list α) (a : α) := a :: as.delete_every a

/-- Given a modal formula B = [ψₙ, ..., ψ₁] and a modal
formula ψ, list_prop_form ψ B produces a list of prop_forms 
[mₙ, ..., m₁] such that if ψᵢ is ψ then mᵢ = p' 0, else
mᵢ = p' i. For example, list_prop_form φ [φ, ψ4, ψ3, φ, ψ1] 
equals [0, 4, 3, 0, 1] -/
noncomputable def list_prop_form (ψ : bmod_form) : list bmod_form → list prop_form
| [] := []
| (φ :: l) := if (φ = ψ) then p' 0 :: list_prop_form l else p' l.length :: list_prop_form l

/- Need to prove: for any logic Λ, and any list of modal formulas B, if ψ in B, because of the 'sub_list' and 'list_taut' (&B ⇒ ⊥) ⇒ (& B.remove_list_prop_forms ψ ⇒ ⊥) is
in KΓ Λ -/
/- For that we first prove that ((& list_prop_form ψ B) ⇒' ⊥') ⇒' ((& (list_prop_form ψ B).headed 0) ⇒' ⊥')) is a
propositional tautology-/


lemma lem1 {v : ℕ → bool} {P : list prop_form} {φ : prop_form}
(hin : φ ∈ P) :
prop_eval v (& P) = prop_eval v & (P.headed φ) :=
begin
  rw list.headed,
  induction P with ψ pl hyp,
    {
      simp only [list.not_mem_nil] at hin,
      contradiction,
    },
  simp only [list.mem_cons_iff] at hin,
  cases hin,
    {
      rw hin,
      
    }
end

lemma lem {B : list bmod_form} {ψ : bmod_form} (hs : ψ ∈ B):
prop_taut (((& list_prop_form ψ B) ⇒' ⊥') ⇒' ((& (list_prop_form ψ B).headed (p' 0)) ⇒' ⊥')) :=
begin
  rw prop_taut,
  intro,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, bool.bnot_band, prop_eval, bool.bnot_false, bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  cases htB : prop_eval v (& list_prop_form ψ B),
    {
      simp only [false_or],
      
    },
  squeeze_simp,
    
end
