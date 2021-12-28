import topo_sound_complete

-----------------------------------------------------------
/- We need a coercion from list to sets to define consistency -/
def list_to_set {α : Type*} : list α → set α
| [] := ∅
| (a :: l) := {a} ∪ list_to_set l

instance list_coe_set {α : Type*} : has_coe (list α) (set α) :=
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
↑B ⊆ Γ ∧ ((& B) ⇒ ⊥) ∈ Λ

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
list α := a :: del a as

/- This lemma is helpful in using and_lists, and making assertions about truth -/
lemma val_head_list (l: list prop_form) (a : prop_form) (v: ℕ → bool) :
prop_eval v a = tt → prop_eval v (& del a l) = tt → prop_eval v (& l) = tt :=
begin
  induction l with b bl hyp,
    {
      rw and_list_pfs,
      simp only [implies_true_iff, eq_self_iff_true, prop_eval, bool.bnot_false],
    },
  intros ha hda,
  rw del at hda,
  rw and_list_pfs,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt, prop_eval],
  specialize hyp ha,
  split_ifs at hda,
    {
      rw [h, ha],
      simp only [true_and, eq_self_iff_true],
      exact hyp hda,
    },
  rw and_list_pfs at hda,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt, prop_eval] at hda,
  exact ⟨hda.1, hyp hda.2⟩,
end

/- For a list l of propositional formulas, if lp is a headed list,
the (&l ⇒' ⊥) ⇒' (&lp ⇒' ⊥) is a propositional tautology -/
lemma headed_taut (l : list prop_form) (a : prop_form) (hal : a ∈ l):
((&l ⇒' ⊥') ⇒' (& (headed_list l a hal) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw prop_taut,
  simp only [set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, bool.bnot_band, prop_eval, 
  bool.bnot_false, 
  bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  rw headed_list,
  rw and_list_pfs,
  simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
  cases hl : prop_eval v (&l),
    { 
      apply or.intro_right, -- prop_eval v (&l) = ff
      cases ha : prop_eval v a,  
      apply or.intro_left, refl,
      apply or.intro_right, -- prop_eval v a = tt
      by_contra,
      simp only [eq_tt_eq_not_eq_ff] at h,
      have hff := val_head_list l a v ha h,
      rw hl at hff,
      simp only at hff,
      assumption,
    },
  apply or.intro_left,
  refl,
end

/- A list of propositional formulas of the form [p0, p1, ...] of a 
given length n -/
def list_pns : ℕ → list prop_form
| 0 := []
| (n + 1) := p'(n) :: list_pns n

/- p' 0 is in a nonempty list -/
lemma pz_in_nonempty_list {n : ℕ} (hnz: n > 0) : p' 0 ∈ list_pns n :=
begin
  induction n with k ih,
  {
    simp only [nat.not_lt_zero, gt_iff_lt] at hnz,
    contradiction,
  },
  rw list_pns,
  simp only [list.mem_cons_iff],
  have hk :  0 = k ∨ k > 0,
    {
      omega,
    },
  cases hk,
  apply or.intro_left, assumption,
  apply or.intro_right, exact ih hk,
end

/- Non-empty lists have positive lengths -/
lemma nonemp_list_pos_len {α : Type*} (a : α) (l : list α)
(hal : a ∈ l) : l.length > 0 :=
begin
  revert a,
  induction l with b hl hyp,
  intros a hal,
  simp only [list.not_mem_nil] at hal, contradiction,
  intros a habl,
  simp only [nat.succ_pos', gt_iff_lt, list.length],
end

/- A propositional tautology that will be used later -/
lemma needed_taut : (((p' 0 ⋀' p' 1) ⇒' ⊥') ⇒'
((p' 2 ⋀' ((p' 2 ⇒' p' 0) ⋀' p' 1)) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw [prop_taut, set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band,
  bool.bnot_bor, prop_eval, bool.bnot_false, bool.band_assoc, bnot_bnot,
  band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  cases h0 : v 0,
  cases h1 : v 1,
  cases h2 : v 2,
  simp only [false_or, false_and, or_self],
  simp only [false_or, eq_self_iff_true, and_self, or_self],
  simp only [and_true, false_or, eq_self_iff_true, or_false],
  cases v 2,
  simp only [or_false],
  simp only [false_or],
  simp only [true_and, false_or, eq_self_iff_true, and_false],
  cases v 1,
  simp only [eq_self_iff_true, or_true],
  simp only [true_or, eq_self_iff_true],
end

noncomputable def needed_sub (φ ψ Φ : bmod_form) (n : ℕ) : bmod_form :=
match n with
| 0 := ψ
| 1 := Φ
| 2 := φ
| _ := ⊥
end

/- A needed substitution instance -/
lemma needed_subs_inst (φ ψ Φ : bmod_form) : subs_inst
(((ψ ⋀ Φ) ⇒ ⊥) ⇒ ((φ ⋀ ((φ ⇒ ψ) ⋀ Φ)) ⇒ ⊥))
(((p' 0 ⋀' p' 1) ⇒' ⊥') ⇒' ((p' 2 ⋀' ((p' 2 ⇒' p' 0) ⋀' p' 1)) ⇒' ⊥')) :=
begin
  simp only,
  rw subs_inst,
  existsi needed_sub φ ψ Φ,
  unfold_coes,
  simp only [and_true, and_self_left, subs, eq_self_iff_true],
  repeat {split},
  repeat {unfold needed_sub},
end

/- A needed lemma -/
lemma ppmsib_in_gam {φ ψ Φ : bmod_form} (Γ : set bmod_form)
(hcond : ((ψ ⋀ Φ) ⇒ ⊥) ∈ KΓ Γ) : ((φ ⋀ ((φ ⇒ ψ) ⋀ Φ)) ⇒ ⊥) ∈ KΓ Γ :=
begin
  simp only at *,
  apply KΓ.mp,
  apply KΓ.subst,
  exact needed_subs_inst φ ψ Φ,
  apply KΓ.taut_cond,
  exact needed_taut,
  exact hcond,
end

/- A lemma about list containment in sets, as sets -/
lemma list_in_set_eqv {α : Type*} (a : α) (l : list α) (A : set α)
: ↑(a :: l) ⊆ A ↔ ((↑l ⊆ A) ∧ (a ∈ A)) :=
begin
  split,
    {
      intros ha,
      split,
        {
          intros b hbl,
          have hb : b ∈ ↑(a :: l),
            {
              refine (in_list_eqv (a :: l) b).mp _,
              refine (list.mem_cons_iff b a l).mpr _,
              apply or.intro_right,
              exact (in_list_eqv l b).mpr hbl,
            },
          exact ha hb,
        },
      apply ha,
      exact set.mem_insert a (list_to_set l),
    },
  intros hla c hcal,
  cases hcal,
    {
      simp only [set.mem_singleton_iff] at hcal,
      rw hcal,
      exact hla.2,
    },
  apply hla.1,
  exact hcal,
end

/- The deleted formula doesn't occur in the tail -/
lemma not_in_tail (A : list bmod_form) (Γ : set bmod_form) (ψ : bmod_form) (hag : ↑A ⊆ Γ ∪ {ψ})
: ↑(del ψ A) ⊆ Γ :=
begin
  induction A with b bl hyp,
    {
      rw del,
      exact set.empty_subset Γ,
    },
  rw del,
  have hbsubbl : (↑bl : set bmod_form) ⊆ ↑(b :: bl), exact set.subset_insert b ↑bl,
  split_ifs,
    {
      apply hyp,
      transitivity,
      exact hbsubbl,
      exact hag,
    },
  refine (list_in_set_eqv b (del ψ bl) Γ).mpr _,
  split,
    {
      apply hyp,
      transitivity,
      exact hbsubbl,
      exact hag,
    },
  have hb : b ∈ ↑(b :: bl), exact set.mem_insert b (list_to_set bl),
  specialize hag hb,
  cases hag,
  exact hag,
  simp only [set.mem_singleton_iff] at hag,
  contradiction,
end

/- The same lemma as above but in a more usable form -/
lemma headed_list_tail (B : list bmod_form) (Γ : set bmod_form) (ψ : bmod_form) (hsb : ψ ∈ B) 
(hbg : ↑B ⊆ Γ ∪ {ψ}) : ↑(headed_list B ψ hsb).tail ⊆ Γ :=
begin
  rw [headed_list, list.tail],
  apply not_in_tail,
  exact hbg,
end

/-A lemma which is the meat of the next proof-/
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
      contradiction,
    },
  rw ←in_list_eqv at hsb,
  let B' := headed_list B ψ hsb, -- need to prove (&B ⇒ ⊥) ⇒ (&B' ⇒ ⊥) ∈ Λ
  let P := list_pns B.length,
  have hpl := headed_taut P (p' 0) (pz_in_nonempty_list (nonemp_list_pos_len ψ B hsb)),
  rcases hng with ⟨A, hla⟩,
  set P' := headed_list P (p' 0) (pz_in_nonempty_list (nonemp_list_pos_len ψ B hsb)),
  have hplg := @KΓ.taut_cond A _ hpl,
  set pform : bmod_form := ↑((& P ⇒' ⊥') ⇒' (& P' ⇒' ⊥')),
  set bform : bmod_form := (((& B) ⇒ ⊥) ⇒ ((& B') ⇒ ⊥)),
  suffices hsub : subs_inst bform pform,
    {
      have hbfg := KΓ.subst hsub hplg,
      rw hla at hbinc,
      have headlis_gamm :((& B') ⇒ ⊥) ∈ KΓ A, exact KΓ.mp hbfg hbinc,
      set Φ := & list.tail (B'),
      have b'cond : (& B') = (ψ ⋀ Φ), refl,
      rw b'cond at headlis_gamm,
      simp only at headlis_gamm,
      have hgcons := hlmcs.1,
      rw consistent at hgcons,
      simp only [not_exists, not_and] at hgcons,
      set pmslist := φ :: (φ ⇒ ψ) :: list.tail B',
      specialize hgcons pmslist,
      suffices hpm_in_gamm : ↑pmslist ⊆ Γ,
        {
          specialize hgcons hpm_in_gamm,
          have hlΦ : (& pmslist) = (φ ⋀ ((φ ⇒ ψ) ⋀ Φ)), refl,
          rw hlΦ at hgcons,
          simp only at hgcons,
          simp only at hlΦ,
          rw hla at hgcons,
          have hend := @ppmsib_in_gam φ _ _ A headlis_gamm,
          simp only at hend,
          exact hgcons hend,
        },
      apply (list_in_set_eqv φ ((φ ⇒ ψ) :: B'.tail) Γ).mpr,
      rw and.comm,
      apply and.intro hpg,
      apply (list_in_set_eqv (φ ⇒ ψ) B'.tail Γ).mpr,
      rw and.comm,
      apply and.intro hpmsg,
      refine headed_list_tail _ _ _ _ hbgs,
    },
  sorry,
end

/-Properties of MCSs-/
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
