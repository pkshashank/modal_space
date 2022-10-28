import topo_semantics.S4_completeness.consistency_basics

/- A propositional tautology that will be used later -/
lemma needed_taut : (((p' 0 ⋀' p' 1) ⇒' ⊥') ⇒'
((p' 2 ⋀' ((p' 2 ⇒' p' 0) ⋀' p' 1)) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw [prop_taut,set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, band_eq_true_eq_eq_tt_and_eq_tt, bool.bnot_band, bool.bnot_bor, prop_eval, bool.bnot_false,
  bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  finish,
end

noncomputable def needed_sub (φ ψ Φ : bmod_form) (n : ℕ) : bmod_form :=
match n with
| 0 := ψ
| 1 := Φ
| 2 := φ
| _ := '⊥
end

/- The formula (((ψ '⋀ Φ) '⇒ '⊥) '⇒ ((φ '⋀ ((φ '⇒ ψ) '⋀ Φ)) '⇒ 
'⊥))  is a substitution instance of a propositional tautology. 
We will use this fact to prove that the formula is in any 
normal logic. -/
lemma subs_inst_of_taut (φ ψ Φ : bmod_form) : subs_inst (((ψ '⋀ Φ) '⇒ '⊥) '⇒ ((φ '⋀ ((φ '⇒ ψ) '⋀ Φ)) '⇒ '⊥)) ((('p 0 '⋀ 'p 1) '⇒ '⊥) '⇒ (('p 2 '⋀ (('p 2 '⇒ 'p 0) '⋀ 'p 1)) '⇒ '⊥)) :=
begin
  rw subs_inst,
  existsi needed_sub φ ψ Φ,
  simp only [and_true, subs, eq_self_iff_true],
  repeat {split},
  repeat {unfold needed_sub},
end

/- Putting previous lemmas together to prove that the modal
formula is in every normal logic. -/
lemma modal_form_in_nl (Γ : set bmod_form) (φ ψ Φ : bmod_form) : (((ψ '⋀ Φ) '⇒ '⊥) '⇒ ((φ '⋀ ((φ '⇒ ψ) '⋀ Φ)) '⇒ '⊥)) ∈ KΓ Γ :=
begin
  apply KΓ.subst (subs_inst_of_taut φ ψ Φ),
  apply KΓ.taut_cond needed_taut,
  -- note that Lean figures out the 'needed_taut' coercion itself.
end

----------------------------------------------------------

/-A lemma which is the meat of the next proof-/
lemma gamm_union_cons (Γ Λ: set bmod_form)
(hng: ∃ (A : set bmod_form), Λ = KΓ A) (hlmcs: mcs Γ Λ)
(φ ψ: bmod_form) (hpg: φ ∈ Γ) (hpmsg: (φ '⇒ ψ) ∈ Γ) :
consistent (Γ ∪ {ψ}) Λ :=
begin
  -- Assume that Γ ∪ {ψ} is not consistent
  by_contra,
  -- Then there are formulas φ1,...,φn such that
  --φ1 '⋀ ...'⋀ φn '⇒ '⊥ ∈ Λ
  rw consistent at h,
  simp only [not_exists, exists_prop, not_and, set.not_not_mem, not_forall] at h,
  -- We call the list Φ
  rcases h with ⟨Φ,hpsub,hinc⟩,
  -- Then ψ is in Φ, becuase if not, then Γ is inconsistent.
  have psi_in_list : ψ ∈ Φ,
    {
      by_contra,
      apply not_in_makes_incons hpsub hinc h,
      rw mcs at hlmcs,
      exact hlmcs.1,
    },
  -- So Φ is of the form [φ0,..., φ(N-1), ψ, φ(N+1),...].
  -- Let the normal logic be KΓ A.
  cases hng with A hnorm,
  rw hnorm at hinc,
  -- As (p' 1 ⋀' ... p' n ⇒' ⊥') ⇒' p' (Φ.r_index ψ) ⋀' p' 1
  -- ⋀' ... p' n ⇒' ⊥' is a propositional tautology,
  have htaut := list_tauts (r_index_le_length psi_in_list),
  -- by uniform substitution
  sorry,
end

/-The needed property of MCSs-/
theorem mcs_preserve_mp (Γ Λ: set bmod_form) (hng : ∃ A, Λ = KΓ A)
(hlmcs : mcs Γ Λ) (φ ψ : bmod_form) (hpg : φ ∈ Γ) (hpmsg : (φ '⇒ ψ) ∈ Γ) :
ψ ∈ Γ :=
begin
  -- It suffices to prove that Γ ∪ {ψ} is consistent.
  -- To see this, assume that Γ ∪ {ψ} is consistent.
  suffices hgp : consistent (Γ ∪ {ψ}) Λ,
    {
      -- Assume ψ ∉ Γ,
      by_contra,
      -- Then Γ ⊂ Γ ∪ {ψ}.
      have hpsub : Γ ⊂ (Γ ∪ {ψ}),
        {
          refine (set.ssubset_iff_of_subset _).mpr _,
          exact set.subset_union_left Γ {ψ},
          have H : ψ ∈ Γ ∪ {ψ}, exact set.mem_union_right Γ rfl,
          exact ⟨ψ,H,h⟩,
        },
      -- Then Γ ∪ {ψ} is consistent, so Γ is not maximally consistent, a contradiction.
      have hgscon := and.intro hgp hpsub,
      rw mcs at hlmcs,
      cases hlmcs with hgcons hneg,
      exact hneg ⟨Γ ∪ {ψ}, hgscon⟩,
    },
  -- This part proves that Γ ∪ {ψ} is consistent.
  apply gamm_union_cons Γ Λ hng hlmcs φ ψ hpg hpmsg,
end
