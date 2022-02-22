import topo_semantics.topo_sound_complete
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

noncomputable def list.erase_all {α} : list α → α → list α
| []     b := []
| (a::l) b := if a = b then l.erase_all b else a :: l.erase_all b

/- Delete an element from the list and add it in front -/
noncomputable def list.headed {α : Type*} (as : list α) (a : α) := a :: as.erase_all a

/- Index of an element from the right -/
noncomputable def list.r_index {α : Type*} (as : list α) (a : α) := as.length - as.index_of a - 1
---------------------------------------------------------------
/- If a propositional variable doesn't appear in the formula,
then deleting it from the list has no effect -/
lemma list_erased_eq_list_pfs {n m : ℕ} (hm : m ≥ n): (list_pns n).erase_all (p' m) = list_pns n :=
begin
  induction n with k ih,
  {refl},
  rw [list_pns, list.erase_all],
  simp only,
  have hk_neq_m : k ≠ m, exact ne_of_lt hm,
  rw if_neg,
  work_on_goal 1 {exact hk_neq_m,},
  simp only [true_and, eq_self_iff_true],
  apply ih, exact (ne.le_iff_lt hk_neq_m).mpr hm,
end

/- A lemma similar to the previous one, but for modal formulas -/
lemma list_erased_eq_list_bmods {n m : ℕ} (hm : m ≥ n): (list_pns_bforms n).erase_all ('p m) = list_pns_bforms n :=
begin
  induction n with k ih,
  {refl},
  rw [list_pns_bforms, list.erase_all],
  simp only,
  have hk_neq_m : k ≠ m, exact ne_of_lt hm,
  rw if_neg,
  work_on_goal 1 {exact hk_neq_m,},
  simp only [true_and, eq_self_iff_true],
  apply ih, exact (ne.le_iff_lt hk_neq_m).mpr hm,
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
          rw ←hk,
          rw list_erased_eq_list_pfs, work_on_goal 1 { exact rfl.ge },
          exact hln,
        },
      repeat {simp only at hp, contradiction},
      have h_i_lt_k : i < k,
        {
          rw or_iff_not_imp_right at hieqk_or_lt,
          have h_i_neq_k : i ≠ k, exact ne.symm h,
          exact hieqk_or_lt h_i_neq_k,
        },
      specialize ih h_i_lt_k,
      rw and_list_pfs,
      simp only [prop_eval, band_eq_false_eq_eq_ff_or_eq_ff],
      tauto,
    },
  simp only [true_or, eq_self_iff_true],
end

-------------------------------------------------------------
/- The index from right of anything appearing in the list is 
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
: subs_func_list_bmod B (B.r_index ψ) = ψ :=
begin
  rw [list.r_index,subs_func_list_bmod],
  have hlen := index_lt_length hs,
  have hcalc : B.length - (B.length - list.index_of ψ B - 1) - 1 = B.index_of ψ, omega,
  rw [hcalc, nth_at_index hs],
  refl,
end

/- A helper lemma which is a pain if not done by omega  -/
lemma helper2 {m n : ℕ} : n < m → m + 1 - n - 1 = m - n - 1 + 1 := by omega

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

/- A lemma similar to the previous one, but for erased formulas -/
lemma same_on_initial_pfs_erased {B : list bmod_form} {φ ψ : bmod_form}
{n : ℕ} (hn : n ≤ B.length) (hs : ψ ∈ B) : subs (subs_func_list_bmod B) (& (list_pns_bforms n).erase ('p (B.r_index ψ))) = subs (subs_func_list_bmod (φ :: B)) (& (list_pns_bforms n).erase ('p (B.r_index ψ))) :=
begin
  sorry,
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

/- A trivial helper lemma about naturals which uses omega in
the proof, unfortunately. Putting this inside a theorem
slows down the machine a lot, hence, writing it as a seperate
lemma. -/
lemma helper1 {m n : ℕ} : m = m + 1 - n - 1 → n < m + 1 → n = 0 :=
begin
  intros h1 h2,
  omega,
end

/- A lemma similar to the previous one, but with ψ erased from B -/
lemma and_erased_list_eq_erased_sub {B : list bmod_form} {ψ : bmod_form} (hp : ψ ∈ B)
: (& B.erase_all ψ) = subs (subs_func_list_bmod B)
(& (list_pns_bforms B.length).erase_all ('p (B.r_index ψ))) :=
begin
  induction B with φ bl hyp,
  -- Base case is vacuous because of 'hp'
  simp only [list.not_mem_nil] at hp, contradiction,
  simp only [list.mem_cons_iff] at hp,
  have hsp := classical.em (ψ = φ),
  cases hsp with hspeq hspneq,
    { 
      -- Case : ψ = φ
      rw [hspeq, list.length, list_pns_bforms, list.erase_all,
      list.erase_all],
      simp only [if_true, list.length, subs, eq_self_iff_true],
      have r_index_eq_len : (φ :: bl).r_index φ = bl.length,
      {
        rw list.r_index,
        simp only [tsub_zero, nat.add_succ_sub_one, add_zero, list.length, list.index_of_cons_self],
      },
      rw [r_index_eq_len],
      simp only [if_true, eq_self_iff_true],
      rw list_erased_eq_list_bmods,
      work_on_goal 1 { exact rfl.ge,},
      -- wait
      rw same_on_initial_pfs,
      
    },
  -- Case : ψ ≠ φ
  have hsbl : ψ ∈ bl, tauto, -- Heavy automation
  rw list.erase,
  -- Needed for a rewrite in ite, verbose
  have hpsneq : φ ≠ ψ,
    {
      by_contra,
      exact hspneq (eq.symm h),
    },
  rw [if_neg hpsneq, list.length, list_pns_bforms, list.erase],
  have r_index_neq_bl_len : 'p bl.length ≠ 'p ((φ :: bl).r_index ψ),
    {
      by_contra,
      simp only at h,
      rw [list.r_index, list.length] at h,
      have hin_le_len : list.index_of ψ (φ :: bl) < bl.length + 1,
        {
          apply index_lt_length,
          simp only [list.mem_cons_iff],
          exact hp,
        },
    have hpeqs : list.index_of ψ (φ :: bl) = 0,
    apply helper1 h hin_le_len,
    rw [list.index_of, list.find_index, if_neg hspneq] at hpeqs,
    simp only [nat.succ_ne_zero] at hpeqs,
    contradiction,
    },
  rw [if_neg r_index_neq_bl_len, and_list_bmods, and_list_bmods],
  simp only [subs],
  split,
    { 
      rw subs_func_list_bmod,
      simp only [add_tsub_cancel_left, list.length, list.nth],
      refl,
    },
  specialize hyp hsbl,
  -- Index from right is the same in a list and its "superlist"
  have hr_index_eq : (φ :: bl).r_index ψ = bl.r_index ψ,
    {
      repeat {rw list.r_index},
      simp only [list.length],
      rw [list.index_of, list.find_index, if_neg hspneq],
      simp only [nat.succ_sub_succ_eq_sub],
    },
  rw [hr_index_eq, hyp],
  apply same_on_initial_pfs_erased, refl, exact hsbl,
end

/- Under 'subs_func_list_bmod', the modal formula (& B '⇒ '⊥ '⇒
(& B.headed ψ '⇒ '⊥)) is a substitution instance of a 
propositional tautology  -/
lemma bmod_form_is_subs_inst {B : list bmod_form} {ψ : bmod_form} (hp : ψ ∈ B):
subs_inst (& B '⇒ '⊥ '⇒ (& B.headed ψ '⇒ '⊥)) (& list_pns_bforms B.length '⇒ '⊥ '⇒ (& (list_pns_bforms B.length).headed ('p (B.r_index ψ)) '⇒ '⊥)) :=
begin
  rw subs_inst,
  -- 'subs_func_list_bmod B' is the needed substitution
  -- instance. 
  existsi subs_func_list_bmod B,
  simp only [and_true, subs, eq_self_iff_true],
  split,
  -- Reduces to 2 goals. First is that '&B' is a substitution 
  -- instance of '& list_pns_bforms B.length'
  exact and_blist_eq_subbed_pf_list,
  -- Second is 'B.headed ψ' is a substitution index of '& 
  -- list_pns_bforms B.length', but with the propositional
  -- variable corresponding to 'ψ' placed in front and deleted
  -- from 'list_pns_bforms B.length'.
  repeat {rw [list.headed, and_list_bmods]},
  simp only [subs],
  -- The variable correspondig to the 'r_index' of 'ψ' is
  -- mapped to ψ itself
  split, apply (subs_maps_rindex hp).symm,
  apply and_erased_list_eq_erased_sub hp,
end

/- This is what the propositional tautology looks like as a modal formula -/
lemma prop_taut_as_modal {n i : ℕ} : ↑(& list_pns n ⇒' ⊥' ⇒' (& (list_pns n).headed (p' i) ⇒' ⊥')) = ((& list_pns_bforms n '⇒ '⊥) '⇒ (& (list_pns_bforms n).headed ('p i) '⇒ '⊥)) :=
begin
  have h_coe_list : ∀ m, (↑(& list_pns m) : bmod_form) = & list_pns_bforms m,
    {
      intros m,
      induction m with k ih,
      refl,
      rw [list_pns, list_pns_bforms, and_list_pfs, and_list_bmods],
      have hcoe : (↑(p' k ⋀' & list_pns k) : bmod_form ) = ('p k '⋀ (↑(& list_pns k)) : bmod_form), refl,
      rw [hcoe, ih],
    },
  rw [list.headed, list.headed, and_list_pfs, and_list_bmods],
  have h_coe_erased : ∀ m,  (↑(& (list_pns m).erase (p' i)) : bmod_form) = & (list_pns_bforms m).erase ('p i),
    {
      intros m,
      induction m with k ih, refl,
      rw [list_pns, list_pns_bforms, list.erase, list.erase],
      split_ifs with hp hk_eq_i,
      exact h_coe_list k,
      repeat {simp only at hp, contradiction},
      rw [and_list_pfs, and_list_bmods],
      have h_coe_help : (↑(p' k ⋀' & (list_pns k).erase (p' i)) : bmod_form) =  (('p k) '⋀ ↑(& (list_pns k).erase (p' i))), refl,
      rw [h_coe_help, ih],
    },
  specialize h_coe_erased n,
  rw [←h_coe_erased, ←(h_coe_list n)], refl,
end

/-For any list of modal formulas [φ1,...,φn], the formula
(φ1 '⋀...'⋀ φn '⇒ '⊥) '⇒ (φi '⋀ φ1 '⋀ φ i-1 '⋀ φ i+1 '⋀...'⋀ φn '⇒ '⊥) belongs in every normal logic-/
lemma and_list_as_taut_in_normal_logic {B : list bmod_form} {ψ : bmod_form} {Γ : set bmod_form} (hp : ψ ∈ B) :
((&B '⇒ '⊥) '⇒ (& B.headed ψ '⇒ '⊥)) ∈ KΓ Γ :=
begin
  -- The formula is a substitution instance of another one
  apply KΓ.subst,
  -- which is the list_bforms tautology
  apply bmod_form_is_subs_inst hp,
  have htaut := list_tauts (r_index_le_length hp),
  -- The tautology as a modal formula is in the normal
  --logic
  have htaut_in_gamm := @KΓ.taut_cond Γ _ htaut,
  rw prop_taut_as_modal at htaut_in_gamm,
  exact htaut_in_gamm,
end

/- If a set is consistent, then for any list Ψ in the set, &Ψ '⇒ '⊥ is not derviable in the normal logic. -/
lemma extended_list_not_derivable {Γ Λ : set bmod_form} {Φ : list bmod_form} {φ ψ : bmod_form} (hp : φ ∈ Γ) (hmp : (φ '⇒ ψ) ∈ Γ) (hphi : ↑Φ ⊆ Γ) (hcons : consistent Γ Λ) :
(φ '⋀ ((φ '⇒ ψ) '⋀ & Φ) '⇒ '⊥) ∉ Λ :=
begin
  by_contra,
  rw consistent at hcons,
  simp only [not_exists, not_and] at hcons,
  specialize hcons (φ :: (φ '⇒ ψ) :: Φ),
  have hexl_sub : ↑(φ :: (φ '⇒ ψ) :: Φ) ⊆ Γ,
    {
      have hcoe : (↑(φ :: (φ '⇒ ψ) :: Φ) : set bmod_form) = {φ} ∪ ↑((φ '⇒ ψ) :: Φ), refl,
      rw hcoe,
      refine set.union_subset_iff.mpr _,
      split,
      exact set.singleton_subset_iff.mpr hp,
      have hcoe2 : (↑((φ '⇒ ψ) :: Φ) : set bmod_form) = {φ '⇒ ψ} ∪ ↑Φ, refl,
      rw hcoe2,
      refine set.union_subset _ hphi,
      exact set.singleton_subset_iff.mpr hmp,
    },
  specialize hcons hexl_sub,
  repeat {rw and_list_bmods at hcons},
  contradiction,
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

lemma lem0 {α : Type*} {A : list α} {a b : α} : (a :: A).erase b = ite (a = b) (A.erase b) (a :: A.erase b) :=
begin
  
end

lemma lem {α : Type*} {A : list α} {S : set α} {a : α}
(hinc :↑A ⊆ S ∪ {a}) : ↑(A.erase a) ⊆ S :=
begin

  induction A with b bl hyp,
  exact set.empty_subset S,
  rw list.erase,
  split_ifs,
    {
      sorry,
    }
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
  -- Then ψ is in Φ
  have psi_in_list : ψ ∈ Φ,
    {
      by_contra,
      apply not_in_makes_incons hpsub hinc h,
      rw mcs at hlmcs,
      exact hlmcs.1,
    },
  -- So Φ is of the form [φ0,..., φ(N-1), ψ, φ(N+1),...]
  cases hng with A hnorm,
  rw hnorm at hinc,
  have h_and_l:= @and_list_as_taut_in_normal_logic _ _ A psi_in_list,
  -- By modus ponens '& Φ.headed ψ '⇒ '⊥' is in the normal
  -- logic
  have h_and_l_ant := KΓ.mp h_and_l hinc,
  rw [list.headed, and_list_bmods] at h_and_l_ant, 
  set ρ := Φ.erase ψ with ρ_def,
  
  sorry,
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
