import topo_sound_complete
import data.nat.basic
-----------------------------------------------------------
/- We need a coercion from list to sets to define consistency -/
def list_to_set {α : Type*} : list α → set α
| [] := ∅
| (a :: l) := {a} ∪ list_to_set l

instance list_coe_to_set {α : Type*} : has_coe (list α) (set α) :=
⟨list_to_set⟩

/- The inclusion in the list (seen as a set) is the same
as inclusion in the original list -/
lemma in_list_same_in_set {α : Type*} (a : α) (as : list α):
a ∈ as ↔ a ∈ (↑as : set α) :=
begin
  induction as with b l hyp,
  refl,
  have hcoe : (↑(b :: l) : set α) = {b} ∪ ↑l, refl,
  rw hcoe,
  simp only [set.mem_insert_iff, set.singleton_union, list.mem_cons_iff],
  rw hyp,
end

instance up_to_list {α β : Type*} [has_coe α β] : has_coe (list α) (list β) :=
⟨λ as, list.rec_on as [] (λ a l lb, ↑a :: lb)⟩

/- 'And' for the whole lists, for modal formulas-/
def and_list_bmods : list bmod_form → bmod_form
| [] := '⊤
| (φ :: l) := φ '⋀ and_list_bmods l

/- and for propositional formulas-/
def and_list_pfs : list prop_form → prop_form
| [] := !' ⊥'
| (φ :: l) := φ ⋀' (and_list_pfs l)

/-Simplified notation for and_list functions-/
notation `& ` B := and_list_bmods B
notation `& ` B := and_list_pfs B

/- Lifting and_lifts_pfs gives and_list_bmods -/
lemma and_list_preserved (B : list prop_form) : ↑ (and_list_pfs B) = & (↑ B) :=
begin
  induction B with φ bl hyp,
  refl,
  rw and_list_pfs,
  have hcoe : (↑(φ :: bl) : list bmod_form) = ↑φ :: ↑bl, refl,
  rw [hcoe, and_list_bmods, ←hyp],
  refl,
end

/-Definintion of Γ being Λ-consistent-/
def consistent (Γ Λ : set bmod_form) := ¬ ∃ (B : list bmod_form),
↑B ⊆ Γ ∧ ((& B) '⇒ '⊥) ∈ Λ

/-Definition of Γ being maximally Λ-consistent (MCS)-/
def mcs (Γ Λ : set bmod_form) := consistent Γ Λ ∧ ¬ ∃
Ω, (consistent Ω Λ ∧ Γ ⊂ Ω)

/- If the list which makes Γ ∪ {ψ} inconsistent does not
contain ψ, then Γ is itself inconsistent -/
lemma not_in_makes_incons {Φ : list bmod_form} {ψ : bmod_form}
{Γ Λ : set bmod_form} (hpsub: ↑Φ ⊆ Γ ∪ {ψ})
(hinc: (& Φ '⇒ '⊥) ∈ Λ) (hpsi : ψ ∉ Φ) : ¬ consistent Γ Λ :=
begin
  rw consistent,
  simp only [not_exists, exists_prop, not_and, set.not_not_mem, not_forall],
  existsi Φ,
  split,
    {
      intros φ hplist,
      specialize hpsub hplist,
      simp only [set.mem_insert_iff, set.union_singleton] at hpsub,
      cases hpsub,
        {
          rw ←hpsub at hpsi,
          rw ←in_list_same_in_set at hplist,
          contradiction,
        },
      exact hpsub,
    },
  exact hinc,
end

/- A list of propositional formulas of the form [p0, p1, ...] of a 
given length n -/
def list_pns : ℕ → list prop_form
| 0 := []
| (n + 1) := p'(n) :: list_pns n

/- Same list for modal formulas -/
def list_pns_bforms : ℕ → list bmod_form
| 0 := []
| (n + 1) := 'p n :: list_pns_bforms n

---------------------------------------------------------------
/- We next prove that ((p' n ⋀' ... ⋀' p' 0) ⇒' ⊥') ⇒'  
(p' i ⋀' p' n ⋀' ... ⋀' p' i+1 ⋀' p' i-1 ⋀' ... ⋀' p'0 ⇒' ⊥')
is a propositional tautology, where i is a special number of
our choice -/
lemma list_tauts {n i : ℕ} (hi : i < n) : (((& list_pns n) ⇒' ⊥') ⇒' ((& ((p' i)::(list_pns n))) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw prop_taut,
  simp only [set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, bool.bnot_band, prop_eval, bool.bnot_false, bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  induction n with k ih,
    {
      apply or.intro_left,
      rw [list_pns, and_list_pfs],
      simp only [prop_eval, bool.bnot_false],
    },
  have hori : i < k ∨ i = k, exact nat.lt_succ_iff_lt_or_eq.mp hi,
  cases hori,
    {
      specialize ih hori,
      rw list_pns,
      repeat {rw and_list_pfs},
      simp only [band_eq_true_eq_eq_tt_and_eq_tt, prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
      cases ih,
        {
          cases v k,
            {
              apply or.intro_right,
              simp only [true_or, eq_self_iff_true, or_true],
            },
          apply or.intro_left,
          simp only [true_and, eq_self_iff_true],
          exact ih,
        },
      rw and_list_pfs at ih,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff] at ih,
      cases ih,
      repeat {tauto},
    },
  rw list_pns,
  repeat {rw and_list_pfs},
  simp only [band_eq_true_eq_eq_tt_and_eq_tt, prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
  rw hori,
  simp only [or_self_left],
  cases hksuc : prop_eval v (& list_pns (k+1)),
    {
      apply or.intro_right,
      rw [list_pns, and_list_pfs] at hksuc,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff] at hksuc,
      exact hksuc,
    },
  apply or.intro_left,
  rw [list_pns, and_list_pfs] at hksuc,
  simp only [band_eq_true_eq_eq_tt_and_eq_tt, prop_eval] at hksuc,
  exact hksuc,
end

-------------------------------------------------------------
/- The index from right of anything appearing in the list is 
less than the length of the list -/
lemma index_right_le_length {α : Type*} (A : list α) (a : α) 
(ha : a ∈ A): A.length - A.index_of a - 1 < A.length :=
begin
  induction A with b bl hyp,
  simp only [list.not_mem_nil] at ha, contradiction,
  simp only [list.length],
  simp only [list.mem_cons_iff] at ha,
  rw [list.index_of, list.find_index],
  split_ifs,
    {
      simp only [tsub_zero, nat.add_succ_sub_one, add_zero, lt_add_iff_pos_right, list.length, nat.lt_one_iff],
    },
  rw [list.index_of] at hyp,
  simp only [nat.succ_sub_succ_eq_sub, list.length],
  rw or_iff_not_imp_left at ha,
  specialize ha h,
  specialize hyp ha,
  exact nat.lt.step hyp,
end

/- This is the substitution function which maps 
'p n-1, ..., p' 0 to φ 0,...,φ n-1 respectively  -/
def subs_func_list_bmod (B : list bmod_form) (n : ℕ):
bmod_form :=
match (B.nth (B.length - n - 1)) with
| some ψ := ψ
| none := '⊥
end

/- The index of any element of a list is less than the
length of the list (because indices start from zero!) -/
lemma index_lt_length {α : Type*} {A : list α} {a : α}
(ha : a ∈ A) : A.index_of a < A.length :=
begin
  induction A with b bl hyp,
  simp only [list.not_mem_nil] at ha, contradiction,
  rw [list.index_of, list.find_index],
  split_ifs,
  simp only [nat.succ_pos', list.length],
  rw [list.mem_cons_iff, or_iff_not_imp_left] at ha,
  specialize ha h,
  specialize hyp ha,
  rw [list.length, ←list.index_of],
  exact nat.lt_succ_iff.mpr hyp,
end

/- In a list containing 'a', the element at the index of 'a'
is 'a' itself. The proof is oddly similar to
'index_lt_length' -/
lemma nth_at_index {α : Type*} {A : list α} {a : α} (ha : a ∈ A) : A.nth (list.index_of a A) = some a :=
begin
  induction A with b bl hyp,
  simp only [list.not_mem_nil] at ha, contradiction,
  rw [list.index_of, list.find_index],
  split_ifs,
  rw h, refl,
  rw [list.mem_cons_iff, or_iff_not_imp_left] at ha,
  specialize ha h,
  specialize hyp ha,
  rw [list.nth, ←list.index_of, hyp],
end

/- 'subs_func_list_bmod B' maps each number to the formula 
whose index from the right in B is the number itself. For 
example if B is [φ0,...,φ n-1], then the substitution function 
maps 0 to φ n-1, 1 to φ n-2,..., and n-1 to φ 0. Where other 
numbers are being mapped doesn't concern us -/
lemma subs_maps_rindex {B : list bmod_form} {ψ : bmod_form} (hs : ψ ∈ B)
: subs_func_list_bmod B (B.length - list.index_of ψ B - 1) = ψ :=
begin
  rw subs_func_list_bmod,
  have hlen := index_lt_length hs,
  have hcalc : B.length - (B.length - list.index_of ψ B - 1) - 1 = B.index_of ψ, omega,
  rw [hcalc, nth_at_index hs],
  refl,
end


/- For a formula in which the only propositonal variables
are p1,...,pn, if n is lesser than the length of a list B,
then subs_func_list_bmod is the same for B and any list
which B is a tail of. -/
lemma same_on_intial_pfs {B : list bmod_form} {φ : bmod_form}
{n : ℕ} (hn : n ≤ B.length) : subs (subs_func_list_bmod B)
(& list_pns_bforms n) = subs (subs_func_list_bmod (φ :: B))
(& list_pns_bforms n) :=
begin
  induction n with k ih,
  refl,
  rw [list_pns_bforms, and_list_bmods],
  simp only [subs],
  split,
    {
      repeat {rw subs_func_list_bmod},
      simp only [list.length],
      have hcalc : B.length + 1 - k - 1 = B.length - k - 1 + 1, omega,
      rw [hcalc, list.nth],
    },
  have hk : k ≤ B.length, exact le_of_lt hn,
  exact ih hk,
end

/- Our subs_func_list_bmod behaves nicely, in the sense that
it maps 'p1 ⋀ ... ⋀ 'pn to &B, where B is our initial list
using which subs_func_list_bmod has been defined. -/
lemma and_blist_eq_subbed_pf_list {B : list bmod_form}:
(& B) = subs  (subs_func_list_bmod B)
(& list_pns_bforms B.length) :=
begin
  induction B with φ bl hyp,
    {
      rw [list.length, list_pns_bforms, and_list_bmods],
      simp only [subs],
    },
  rw [list.length, list_pns_bforms, and_list_bmods],
  rw and_list_bmods,
  simp only [subs],
  split,
    {
      rw subs_func_list_bmod,
      simp only [add_tsub_cancel_left, list.length, list.nth],
      refl,
    },
  rw hyp,
  apply same_on_intial_pfs, refl,
end

/- Under 'subs_func_list_bmod', the modal formula (& B '⇒ '⊥ '⇒
(& ψ :: B '⇒ '⊥)) is a substitution instance of a 
propositional tautology  -/
lemma bmod_form_is_subs_inst {B : list bmod_form} {ψ : bmod_form} (hp : ψ ∈ B) {N I : ℕ} (hi : I = B.length - B.index_of ψ - 1) (hn : N = B.length) :
subs_inst (& B '⇒ '⊥ '⇒ (& ψ :: B '⇒ '⊥)) (& list_pns_bforms N '⇒ '⊥ '⇒ (& 'p I :: list_pns_bforms N '⇒ '⊥)) :=
begin
  rw subs_inst,
  existsi subs_func_list_bmod B,
  simp only [and_true, subs, eq_self_iff_true],
  split,
  rw hn,
  exact and_blist_eq_subbed_pf_list,
  repeat {rw and_list_bmods},
  simp only [subs],
  split,
  symmetry,
  rw hi,
  exact subs_maps_rindex hp,
  rw hn,
  exact and_blist_eq_subbed_pf_list,
end

/- This is what the propositional tautology looks like as a modal formula -/
lemma prop_taut_as_modal {n i : ℕ} : ↑(& list_pns n ⇒' ⊥' ⇒' (& p' i :: list_pns n ⇒' ⊥')) = ((& list_pns_bforms n '⇒ '⊥) '⇒ (& 'p i :: list_pns_bforms n '⇒ '⊥)) :=
begin
  rw [and_list_pfs, and_list_bmods],
  have h_coe_list : ∀ m, (↑(& list_pns m) : bmod_form) = & list_pns_bforms m,
    {
      intros m,
      induction m with k ih,
      refl,
      rw [list_pns, list_pns_bforms, and_list_pfs, and_list_bmods],
      have hcoe : (↑(p' k ⋀' & list_pns k) : bmod_form ) = ('p k '⋀ (↑(& list_pns k)) : bmod_form), refl,
      rw [hcoe, ih],
    },
  specialize h_coe_list n,
  have hcoe : (↑(& list_pns n ⇒' ⊥' ⇒' (p' i ⋀' & list_pns n ⇒' ⊥')) : bmod_form) = (((↑(& list_pns n) : bmod_form) '⇒ '⊥) '⇒ ('p i '⋀ (↑(& list_pns n) : bmod_form) '⇒ '⊥)), refl,
  rw [hcoe, h_coe_list],
end

/-For any list of modal formulas [φ1,...,φn], the formula
(φ1 '⋀...'⋀ φn '⇒ '⊥) '⇒ (φi '⋀ φ1 '⋀...'⋀ φn '⇒ '⊥) belongs
in every normal logic-/
lemma and_list_as_taut_in_normal_logic (B : list bmod_form) (ψ : bmod_form) (Γ : set bmod_form) (hp : ψ ∈ B) :
((&B '⇒ '⊥) '⇒ (& (ψ :: B) '⇒ '⊥)) ∈ KΓ Γ :=
begin
  have htaut := list_tauts (index_right_le_length B ψ hp),
  set I := B.length - B.index_of ψ - 1 with hi,
  set N := B.length with hn,
  have htaut_in_gamm := @KΓ.taut_cond Γ _ htaut,
  have hsub := bmod_form_is_subs_inst hp hi hn,
  apply KΓ.subst hsub,
  have htaut_coe := @KΓ.taut_cond Γ _ htaut,
  rw prop_taut_as_modal at htaut_coe,
  exact htaut_coe,
end
--------------------------------------------------------------
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
  -- Then ψ is in Φ
  have psi_in_list : ψ ∈ Φ,
    {
      by_contra,
      apply not_in_makes_incons hpsub hinc h,
      rw mcs at hlmcs,
      exact hlmcs.1,
    },
  set N := Φ.index_of ψ,
  -- So Φ is of the form [φ0,..., φ(N-1), ψ, φ(N+1),...]
  sorry
end

/-The needed property of MCSs-/
theorem mcs_preserve_mp (Γ Λ: set bmod_form) (hng : ∃ A, Λ = KΓ A)
(hlmcs : mcs Γ Λ) (φ ψ : bmod_form) (hpg : φ ∈ Γ) (hpmsg : (φ '⇒ ψ) ∈ Γ) :
ψ ∈ Γ :=
begin
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
