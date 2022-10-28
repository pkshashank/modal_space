import topo_semantics.topo_sound_complete
import data.nat.basic

-- First we have some definitions and basic api
/-- In a list containing 'a', the element at the index of 'a'
is 'a' itself. -/
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

/-- The index of any element of a list is less than the
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

/-- List seen as a set -/
def list_to_set {α : Type*} : list α → set α
| [] := ∅
| (a :: l) := {a} ∪ list_to_set l

instance list_coe_to_set {α : Type*} : has_coe (list α) (set α) :=
⟨list_to_set⟩

/-- The inclusion in the list (seen as a set) is the same
as inclusion in the original list -/
lemma in_list_iff_in_set {α : Type*} (a : α) (as : list α):
a ∈ as ↔ a ∈ (↑as : set α) :=
begin
  induction as with b l hyp,
  refl,
  have hcoe : (↑(b :: l) : set α) = {b} ∪ ↑l, refl,
  rw hcoe,
  simp only [set.mem_insert_iff, set.singleton_union, list.mem_cons_iff],
  rw hyp,
end

/-- Erase every particular entry from a list -/
noncomputable def list.erase_all {α} : list α → α → list α
| []     b := []
| (a::l) b := if b = a then l.erase_all b else a :: l.erase_all b

/-- If an element is not in a list, erasing that element from
the list does nothing to the list -/
lemma list_erase_is_list {α : Type*} {A : list α} {a : α} (han : a ∉ A) : A.erase_all a = A :=
begin
  induction A with h l hyp,
  {refl,},
  rw list.erase_all,
  simp only [list.mem_cons_iff] at han,
  rw or_iff_not_and_not at han,
  simp only [exists_prop, not_not] at han,
  cases han with haeqh hanl,
  rw if_neg haeqh,
  simp only [true_and, eq_self_iff_true],
  exact hyp hanl,
end

/-- Delete every occurance of an element from a list and add
it in front -/
@[simp]
noncomputable def list.headed {α : Type*} (as : list α) (a : α) := a :: as.erase_all a

/-- Gives a list of indices from the right, at which the 
element can be found in the list -/
@[simp]
noncomputable def list.r_indices {α : Type*} (a : α) : list α → list ℕ
| [] := []
| (b :: B) := if (b = a) then (B.length :: list.r_indices B) else list.r_indices B

/-- Index of an element from the right in a list -/
noncomputable def list.r_index {α : Type*} (as : list α) (a : α) := as.length - as.index_of a - 1

/-- The r_index of the head is same as the length of the tail.-/
@[simp]
lemma head_cons_r_index_eq_len {α} {A : list α} {a : α} : (a :: A).r_index a = A.length :=
begin
  rw list.r_index,
  simp only [tsub_zero, nat.add_succ_sub_one, add_zero, list.length, list.index_of_cons_self],
end

/-- The index from right of anything appearing in the list is 
less than the length of the list -/
lemma r_index_le_length {α : Type*} {A : list α} {a : α} 
(ha : a ∈ A): A.r_index a < A.length :=
begin
  rw list.r_index,
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

/-- Definintion of Γ being Λ-consistent-/
def consistent (Γ Λ : set bmod_form) := ¬ ∃ (B : list bmod_form),
↑B ⊆ Γ ∧ ((& B) '⇒ '⊥) ∈ Λ

/-- Definition of Γ being maximally Λ-consistent (MCS)-/
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
          rw ←in_list_iff_in_set at hplist,
          contradiction,
        },
      exact hpsub,
    },
  exact hinc,
end

/- This is the substitution function which maps 
n-1, ..., 0 to φ 0,...,φ n-1 respectively  -/
def sub_list (B : list bmod_form) (n : ℕ):
bmod_form :=
match (B.nth (B.length - n - 1)) with
| some ψ := ψ
| none := '⊥
end

/- 'sub_list B' behaves as expected on each particular natural
number. -/
@[simp]
lemma subs_maps_rindex {B : list bmod_form} {ψ : bmod_form} (hs : ψ ∈ B)
: sub_list B (B.r_index ψ) = ψ :=
begin
  rw [list.r_index,sub_list],
  have hlen := index_lt_length hs,
  have hcalc : B.length - (B.length - list.index_of ψ B - 1) - 1 = B.index_of ψ, omega,
  rw [hcalc, nth_at_index hs],
  refl,
end

/-- List of propositional formulas of the form [p'0, p'1, ...] 
of a given length n -/
@[simp]
def list_pns : ℕ → list prop_form
| 0 := []
| (n + 1) := p'(n) :: list_pns n

/- Erasing an index which is not in the list of pns 
brings no change in the list -/
lemma list_erased_eq_list_pfs {n m : ℕ} (hm : m ≥ n): (list_pns n).erase_all (p' m) = list_pns n :=
begin
  induction n with k ih,
  {refl},
  rw [list_pns, list.erase_all],
  simp only,
  have hk_neq_m : k ≠ m, exact ne_of_lt hm,
  rw if_neg,
  work_on_goal 1 {exact (ne.symm hk_neq_m).elim,},
  simp only [true_and, eq_self_iff_true],
  apply ih, exact (ne.le_iff_lt hk_neq_m).mpr hm,
end

/-- List of modal formulas of the form ['p0, 'p1, ...] 
of a given length n -/
@[simp]
def list_pns_b : ℕ → list bmod_form
| 0 := []
| (n + 1) := 'p(n) :: list_pns_b n

/-- The propositional variable 'p m doesn't occur in list_pns_b
 n if m ≥ n. -/
lemma index_ge_n_not_in_list_pns_b_n {m n : ℕ} (hmn : m ≥ n) : 'p m ∉ list_pns_b n :=
begin
  induction n with k ih,
  simp only [list.not_mem_nil, list_pns_b, not_false_iff],
  rw list_pns_b,
  simp only [list.mem_cons_iff],
  rw or_iff_not_and_not,
  simp only [exists_prop, not_not],
  split,
    {
      apply ne_of_gt,
      exact hmn,
    },
  apply ih,
  exact le_of_lt hmn,
end

/- 'sub_list' is the same for B and φ :: B, for the disjuncted
list containing only B.length many initial propositonal
variables -/
lemma sub_list_same {B : list bmod_form} {φ : bmod_form} {n : ℕ} (hn : n ≤ B.length) :
subs (sub_list B) (& list_pns_b n) = 
subs (sub_list (φ :: B)) (& list_pns_b n) :=
begin
  induction n with k ih,
  { simp only [list_pns_b, subs, and_list_bmods] },
  simp only [list_pns_b, subs, and_list_bmods],
  split,
    {
      repeat {rw sub_list},
      rw list.length,
      have hcalc : B.length + 1 - k - 1 = B.length - k - 1 + 1, omega,
      rw hcalc,
      simp only [list.nth],
    },
  apply ih,
  exact le_of_lt hn,
end

/- 'sub_list' by behaves as expected, not just on each natural
number, but also on the whole disjuncted list. -/
lemma sub_list_on_list_pns_b {B : list bmod_form}: (& B) = subs (sub_list B) (& list_pns_b B.length) :=
begin
  induction B with φ bl hyp,
  { refl, },
  simp only [list.length, list_pns_b, subs, and_list_bmods],
  split,
    {
      rw sub_list,
      simp only [add_tsub_cancel_left, list.length, list.nth],
      refl,
    },
  rw hyp,
  apply sub_list_same, refl,
end

/- We next prove that ((p' n ⋀' ... ⋀' p' 0) ⇒' ⊥') ⇒'  
(p' i ⋀' p' n ⋀' ... ⋀' p' i+1 ⋀' p' i-1 ⋀' ... ⋀' p'0 ⇒' ⊥')
is a propositional tautology, where i is a special number of
our choice -/
lemma list_tauts {n i : ℕ} (hi : i < n) : (((& list_pns n) ⇒' ⊥') ⇒' ((& (list_pns n).headed (p' i)) ⇒' ⊥')) ∈ prop_taut :=
begin
  rw prop_taut,
  simp only [set.mem_set_of_eq],
  intro v,
  rw prop_true,
  simp only [bnot_eq_true_eq_eq_ff, bool.bnot_band, prop_eval, bool.bnot_false, bnot_bnot, band_tt, bor_eq_true_eq_eq_tt_or_eq_tt],
  cases hln : prop_eval v (& list_pns n),
    {
      apply or.intro_right,
      induction n with k ih,
        {
          rw [list_pns, and_list_pfs] at hln,
          simp only [prop_eval, bool.bnot_false] at hln,
          contradiction,
        },
      rw [list_pns, list.headed, and_list_pfs],
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
      rw [list_pns, and_list_pfs] at hln,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff] at hln,
      have hieqk_or_lt : i < k ∨ i = k, exact nat.lt_succ_iff_lt_or_eq.mp hi,
      rw [list.headed, and_list_pfs] at ih,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff] at ih,
      rw list.erase_all,
      split_ifs with hp hk,
        {
          rw hk,
          rw list_erased_eq_list_pfs, work_on_goal 1 { exact rfl.ge },
          exact hln,
        },
      repeat {simp only at hp, contradiction},
      have h_i_lt_k : i < k,
        {
          rw or_iff_not_imp_right at hieqk_or_lt,
          have h_i_neq_k : i ≠ k, exact h,
          exact hieqk_or_lt h_i_neq_k,
        },
      specialize ih h_i_lt_k,
      rw and_list_pfs,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
      tauto,
    },
  simp only [true_or, eq_self_iff_true],
end


/- Need to prove: for any logic Λ, and any list of modal formulas B, if ψ in B, because of the 'sub_list' and 'list_taut' (&B ⇒ ⊥) ⇒ (& B.headed ψ ⇒ ⊥) is in KΓ Λ -/
/- For that we first prove that it is a substitution instance -/

lemma lem1 {B : list bmod_form} {ψ : bmod_form} (hs : ψ ∈ B) :
(& B.erase_all ψ) = subs (sub_list B) (& (list_pns_b B.length).erase_all ('p (B.r_index ψ))) :=
begin
  induction B with φ bl hyp,
  refl,
  rw list.erase_all,
  split_ifs,
    {
      rw h,
      rw list.length,
      rw list_pns_b,
      rw list.erase_all,
      simp only [if_true, eq_self_iff_true, head_cons_r_index_eq_len],
      have hl : (list_pns_b bl.length).erase_all ('p bl.length) = list_pns_b bl.length,
        {
          rw list_erase_is_list,
          apply index_ge_n_not_in_list_pns_b_n,
          exact rfl.ge,
        },
      rw hl,
    }
end

lemma lem {B : list bmod_form} {ψ : bmod_form} (hs : ψ ∈ B):
subs_inst ((& B '⇒ '⊥) '⇒ (& B.headed ψ '⇒ '⊥))
(((& list_pns_b B.length) '⇒ '⊥) '⇒ ((& (list_pns_b B.length).headed ('p (B.r_index ψ))) '⇒ '⊥)) :=
begin
  rw subs_inst,
  existsi sub_list B,
  simp only [and_true, subs, eq_self_iff_true],
  split,
  exact sub_list_on_list_pns_b,
  repeat {rw list.headed},
  simp only [subs, and_list_bmods],
  split,
    {
      symmetry,
      exact subs_maps_rindex hs,
    },
  sorry,
end
