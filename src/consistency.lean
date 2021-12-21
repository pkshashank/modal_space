import topo_sound_complete

-----------------------------------------------------------
/- We need a coercion from list to sets to define consistency -/
def list_to_set {α : Type*} : list α → set α
| [] := ∅
| (a :: l) := {a} ∪ list_to_set l

instance {α : Type*} : has_coe (list α) (set α) :=
⟨list_to_set⟩

instance {α β : Type*} [has_coe α β] : has_coe (list α) (list β) :=
⟨λ as, list.rec_on as [] (λ a l lb, ↑a :: lb)⟩

/- 'And' for the whole lists, for modal formulas-/
def and_list_bmods : list bmod_form → bmod_form
| [] := ⊤
| (φ :: l) := φ ⋀ and_list_bmods l

/- and for propositional formulas-/
def and_list_pfs : list prop_form → prop_form
| [] := prop_form.neg prop_form.bot
| (φ :: l) := prop_form.and φ (and_list_pfs l)

/-Simplified notation for and_list functions-/
notation `& ` B := and_list_bmods B
notation `& ` B := and_list_pfs B

/- Lifting and_lifts_pfs gives and_list_bmods -/
lemma and_list_preserves (B : list prop_form) : ↑ (and_list_pfs B) = & (↑ B) :=
begin
  induction B with b l hyp,
  refl,
  rw and_list_pfs,
  have hc : ↑(b.and (& l)) = (↑b ⋀ ↑(& l)), refl,
  have hl : ↑(b :: l) = (↑b) :: (l : list bmod_form), refl,
  rw [hc, hyp, hl, and_list_bmods],
end

/-Definintion of Γ being Λ-consistent-/
def consistent (Γ Λ : set bmod_form) := ¬ ∃ (B : list bmod_form),
↑B ⊆ Γ ∧ ((& B) ⇒ ⊥) ∉ Λ

/-Definition of Γ being maximally Λ-consistent (MCS)-/
def mcs (Γ Λ : set bmod_form) := consistent Γ Λ ∧ ¬ ∃
Ω, (consistent Ω Λ ∧ Γ ⊂ Ω)

/- Being in a list as a set is the same as being in a list -/
lemma in_list_eqv {α : Type*} (as : list α) (a : α) : a ∈ as ↔ a ∈ (↑as : set α) :=
begin
  induction as with h l hyp,
  refl,
  unfold_coes at hyp ⊢,
  rw list_to_set,
  simp only [set.mem_insert_iff, set.singleton_union, list.mem_cons_iff],
  rw hyp,
end

/- A function which creates a new list from another list by appending a specific
element at the last, if it is present in the original list. This deletes the
occurence of a variable-/
noncomputable def del {α : Type*} (a : α): list α → list α
| [] := []
| (b :: l) := if b = a then del l else b :: del l

/- This concatenates the deleted variable in the front-/
noncomputable def headed_list {α : Type*} (as : list α) (a : α) (hal : a ∈ as) :
list α := [a] ++ del a as

/- For a list l of propositional formulas, if lp is a headed list,
the (&l ⇒' ⊥) ⇒' (&lp ⇒' ⊥) is a propositional tautology -/
lemma lem (l : list prop_form) (a : prop_form) (hal : a ∈ l) :
((&l ⇒' ⊥') ⇒' (& (headed_list l a hal) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw prop_taut,
  simp only [set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, bool.bnot_band, prop_eval, bool.bnot_false, 
  bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  induction l with b bl hyp,
    {
      exfalso,
      simp only [list.not_mem_nil] at hal,
      exact hal,
    },
  simp only [list.mem_cons_iff] at hal,
  cases hal with hab habl,
    {
      sorry,
    },
  sorry,
end


/-Properties of MCSs-/
lemma gamm_union_cons (Γ Λ: set bmod_form) (hng: ∃ (A : set bmod_form), Λ = KΓ A) 
(hlmcs: mcs Γ Λ) (φ ψ: bmod_form) (hpg: φ ∈ Γ) (hpmsg: (φ ⇒ ψ) ∈ Γ) :
consistent (Γ ∪ {ψ}) Λ :=
begin
  by_contra,
  rw consistent at h,
  simp only [not_exists, exists_prop, not_and, set.not_not_mem, not_forall] at *,
  rcases h with ⟨B, hbgs, hbinc⟩,
  have hsb : ψ ∈ ↑B,
    {
      by_contra,
      have hbg : ↑B ⊆ Γ,
        {
          intros χ hχb,
          specialize hbgs hχb,
          cases hbgs, assumption,
          exfalso,
          simp only [set.mem_singleton_iff] at hbgs,
          rw hbgs at hχb,
          exact h hχb,
        },
    cases hlmcs with hcons hneg,
    rw consistent at hcons,
    simp only [not_exists, not_and, set.not_not_mem] at hcons,
    specialize hcons B hbg,
    exact hbinc hcons,
    },
  rw ←in_list_eqv at hsb,
  let B' := headed_list B ψ hsb,
  sorry,
end

theorem mcs_preserve_mp (Γ Λ: set bmod_form) (hng : ∃ A, Λ = KΓ A)
(hlmcs : mcs Γ Λ) (φ ψ : bmod_form) (hpg : φ ∈ Γ) (hpmsg : (φ ⇒ ψ) ∈ Γ) :
ψ ∈ Γ :=
begin
  simp only at *,
  suffices hgp : consistent (Γ ∪ {ψ}) Λ,
    {
      by_contra,
      have hpsub : Γ ⊂ (Γ ∪ {ψ}),
        {
          refine (set.ssubset_iff_of_subset _).mpr _,
          exact set.subset_union_left Γ {ψ},
          have H : ψ ∈ Γ ∪ {ψ}, exact set.mem_union_right Γ rfl,
          exact ⟨ψ,H,h⟩,
        },
      have hgscon := and.intro hgp hpsub,
      rw mcs at hlmcs,
      cases hlmcs with hgcons hneg,
      exact hneg ⟨Γ ∪ {ψ}, hgscon⟩,
    },
  apply gamm_union_cons Γ Λ hng hlmcs φ ψ hpg hpmsg,
end
