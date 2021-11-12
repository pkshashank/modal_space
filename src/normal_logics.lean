import syntax
import kripke_semantics

----------------------------------------------------------

--We define uniform substitution
@[simp]
def subs (var_sub : ℕ → bmod_form) : bmod_form → bmod_form
| (p n) := var_sub n
| ⊥ := ⊥
| (! φ) := ! (subs φ)
| (φ ⋀ ψ) := (subs φ) ⋀ (subs ψ)
| (◇ φ) := ◇ (subs φ)

-- Next, we define a relation between modal formula, namely of being a substitution instance.

def subs_inst : bmod_form → bmod_form → Prop := λ ψ φ, (∃ (v : ℕ → bmod_form), ψ = subs v φ)

-- As an example, we see that ((□ p 1 ⋁ p 2) ⋀ (! p 3 ⇒ □ p 4)) ⋁ p 5 is a substitution instance of ((p 1 ⋀ p 2) ⋁ p 3).
--For that we need to show the existence of an appropriate var_sub.

example : subs_inst (((□ p 1 ⋁ p 2) ⋀ (! p 3 ⇒ □ p 4)) ⋁ p 5) ((p 1 ⋀ p 2) ⋁ p 3) :=
begin
  rw subs_inst,
  let v : ℕ → bmod_form := λ n, match n with
    | 0 := bmod_form.var 0
    | 1 := (□ p 1 ⋁ p 2)
    | 2 := (! p 3 ⇒ □ p 4)
    | 3 := p 5
    | (a + 4) := bmod_form.var (a + 4)
  end,
  
  existsi v,
  simp only [subs],
  repeat {split},
end

--Next, we define normal modal logics as an inductive type.
--We first define the modal formulas K and Dual.
def K : bmod_form := (□ (p 1 ⇒ p 2))⇒ ((□ p 1) ⇒ □ p 2)
def Dual : bmod_form:= ◇ (p 1) ⇔ ! □ ! p 1

-- We present some helper definitions.
-- The construction will be bottom up.
-- We will start with a base set and construct the normal logic by taking a closure
-- under needed functions.

-- This will be the starting set
def base (Γ : set bmod_form) := Γ ∪ prop_taut ∪ {Dual, K}

-- mp_set s is exactly the formulas that can be obtained from s by applying modus ponens to elements in s
def mp_set (s :  set bmod_form) : set bmod_form := { φ | ∃ φ1 φ2 ∈ s, (φ2 = (φ1 ⇒ φ))}

-- A similar definition for generalisation
def gen_set (s : set bmod_form) : set bmod_form := { φ | ∃ ψ ∈ s, (φ = □ ψ) }

-- And a similar one for substituion instances
def subst_set (s : set bmod_form) : set bmod_form := { φ | ∃ ψ ∈ s, subs_inst φ ψ }

-- Next, we construct the sets and in the end take the union 
def C (Γ : set bmod_form) : ℕ → set bmod_form
| 0 := base Γ 
| (n + 1) := (C n) ∪ mp_set (C n) ∪ gen_set (C n) ∪ subst_set (C n)

-- Once, we have the family, we take its union and define it to be KΓ
-- We do this in two steps, first we make a set containing the family
def set_Cs (Γ : set bmod_form) : set (set bmod_form) := { D | ∃ n, D = C Γ n }

-- Finally we take the union on this set containing the family to obtain the normal logic KΓ
def KΓ (Γ : set bmod_form) := ⋃₀ set_Cs Γ

-- All such KΓs are normal logics
def normal_logic : set (set bmod_form) := { N | ∃ Γ, N = KΓ Γ }

--Next, we have some examples, but before that we need a helper lemma to use in one of our examples.
lemma gam_sub_normal : ∀ (Γ : set bmod_form), Γ ⊆ KΓ Γ :=
begin
  intro Γ,
  have h0 : Γ ⊆ base Γ ,
    {begin
      rw base,
      refine set.subset_union_of_subset_left _ {Dual, K},
      exact set.subset_union_left Γ ↑prop_taut,
    end},
  have h1 : base Γ = C Γ 0 , refl,
  have h2 : base Γ ⊆ KΓ Γ,
    {begin
      rw KΓ,
      rw set_Cs,
      rw h1,
      refine {D : set bmod_form | ∃ (n : ℕ), D = C Γ n}.subset_sUnion_of_subset _ _ _,
      -- using mathlib heavily to simplify stuff (using suggest)
      exact C Γ 0,
      refl,
      existsi 0,
      refl,
    end},
  transitivity,
  exact h0,
  exact h2,
end


-- We next prove that the set of all modal formulas formulas  forms a normal logic
example {All : set bmod_form} (ha : ∀ φ, φ ∈ All) : normal_logic All :=
begin
  rw normal_logic,
  existsi All,
  apply funext,
  intro ψ,
  apply propext,

  split,
  intro hp,
  apply gam_sub_normal,
  assumption,

  intro hkp,
  exact (ha ψ),
end

/-We have defined normal logics as set which starting from a 
base set, are built up step by step. Thus, they are contain K, 
Dual, the proposition tautologies and are closed under modus 
ponens, generalisation and uniform substitution. So, every such 
set is a normal logic. What about the converse? Does every set 
which contains K, Dual, propostional tautologies and is closed 
under above mentioned operations a normal logic? The next 
theorem answers in the affirmative.-/

-- This lemma says essentially that KΓ Γ is the union of C Γs.
lemma kg_iff_cn {Γ : set bmod_form} {φ : bmod_form} : φ ∈ KΓ Γ ↔ ∃ n, φ ∈ C Γ n :=
begin
  split,
  {
    intros h0,
    rw [KΓ,set_Cs] at h0,
    rw set.mem_set_of_eq at h0,
    simp only [exists_prop, set.mem_set_of_eq] at h0,
    rcases h0 with ⟨D,h1,h2⟩,
    cases h1 with m h1,
    existsi m,
    rw ←h1,
    exact h2,
  },
  
  {
    intro hn,
    cases hn with n hn,
    have h0 : C Γ n ⊆ KΓ Γ,
      {
        rw [KΓ, set_Cs],
        intros ψ h0,
        simp only [exists_prop, set.mem_set_of_eq],
        existsi C Γ n,
        split,
          {
            existsi n,
            refl,
          },
        exact h0,
      },
    tauto,
  }
end

--This lemma says that for m > n , C Γ n ⊆ C Γ m
lemma cn_subset_cnk {Γ : set bmod_form} {n k : ℕ} : C Γ n ⊆ (C Γ (k + n)) :=
begin
  induction k with k ik,
  {
    rw zero_add,
  },
  transitivity,
  exact ik,
  have h0 : (k + 1) + n = (k + n) + 1,
  {
    rw add_assoc,
    rw add_comm 1 n,
    rw add_assoc,
  },
  rw h0,
  intros φ h1,
  rw C,
  repeat {apply or.intro_left},
  exact h1,
end

lemma mgn_imp_cn_in_cm {m n : ℕ} {Γ : set bmod_form} : m ≥ n → C Γ n ⊆ C Γ m :=
begin
  intro h0,
  have h1 : m = (m - n) + n, by omega,
  rw h1,
  apply cn_subset_cnk,
end

--More helper lemmas
lemma mp_contain {A B : set bmod_form} : A ⊆ B → mp_set A ⊆ mp_set B :=
begin
  intros h0 φ h1,
  rw mp_set at h1 ⊢,
  simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1 ⊢,
  rcases h1 with ⟨ψ1,ψ2,h2,h3,h4⟩,
  existsi ψ1,
  existsi ψ2,
  exact ⟨h0 h2, ⟨h0 h3, h4⟩⟩,
end

lemma gen_set_contain {A B : set bmod_form} : A ⊆ B → gen_set A ⊆ gen_set B :=
begin
  intros h0 φ h1,
  rw gen_set at h1 ⊢,
  simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1 ⊢,
  rcases h1 with ⟨ψ1,h2,h3⟩,
  existsi ψ1,
  exact ⟨h0 h2, h3⟩,
end

lemma subst_set_contain {A B : set bmod_form} : A ⊆ B → subst_set A ⊆ subst_set B :=
begin
  intros h0 φ h1,
  rw subst_set at h1 ⊢,
  simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h1 ⊢,
  rcases h1 with ⟨ψ1,h2,h3⟩,
  existsi ψ1,
  exact ⟨h0 h2, h3⟩,
end

/-This needs a pause. The proofs of the preceeding two lemmas are 
identical except a term. A better formalization would have a
general lemma from which these two results would follow by substituting
 gen_set or subst_set. The sets should ideally have been defined as
images set of a function, and not as functions on sets itself.
Defining them as image sets would have encapsulated more information
into them. The problem I encountered was that mp_set is the image
under a partial function, and I don't know how do define a partial 
function without using 'option'. Maybe something can be done using option
without breaking much stuff here.
-/

theorem normal_is_closed {D : set bmod_form} : D ∈ normal_logic ↔ (({Dual, K} ∪ ↑prop_taut ⊆ D) ∧ mp_set D ⊆ D ∧ gen_set D ⊆ D ∧ subst_set D ⊆ D) :=
begin
  
  split,

  intro hd,
  rw normal_logic at hd,
  simp only [set.mem_set_of_eq] at hd,
  cases hd with Γ hd,
  have hc0 : C Γ 0 ⊆ KΓ Γ,
  {
    intros φ h0,
    rw kg_iff_cn,
    existsi 0,
    exact h0,
  },
  repeat {split},
  refine set.union_subset_iff.mpr _,
  split,
  {
    rw hd,
    transitivity,
    have h0 : {Dual, K} ⊆ C Γ 0,
      {
        rw [C,base],
        intros φ h0,
        apply or.intro_right,
        exact h0,
      },
    exact h0,
    exact hc0,
  },
  {
    rw hd,
    transitivity,
    have h0 : ↑prop_taut ⊆ C Γ 0, 
    {
      rw [C,base],
      intros φ h0,
      apply or.intro_left,
      apply or.intro_right,
      exact h0,
    },
    exact h0,
    exact hc0,
  },
  {
   rw hd,
   intros φ h0,
   rw kg_iff_cn,
   rw mp_set at h0,
   simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq] at h0,
   rcases h0 with ⟨ψ, h1⟩,
   cases h1 with ψ1 h2,
   rcases h2 with ⟨h2,h3,h4⟩,
   rw kg_iff_cn at h2 h3,
   cases h2 with n1 h2,
   cases h3 with n2 h3,
   apply or.elim (classical.em (n1 ≥ n2)),
    {
      intro h5,
      existsi n1 + 1,
      have h6 : ψ ∈ C Γ n1,
        {
          apply mgn_imp_cn_in_cm,
            {
              exact h5,
            },
          exact h3,
        },
      rw C,
      iterate 2 {apply or.intro_left},
      apply or.intro_right,
      rw mp_set,
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq],
      existsi ψ,
      existsi ψ1,
      repeat {split},
      repeat {assumption},
    },
    intro h5,
      existsi n2 + 1,
      have h7 : n2 ≥ n1,
        {
          exact le_of_not_ge h5,
        },
      have h6 : ψ1 ∈ C Γ n2,
        {
          apply mgn_imp_cn_in_cm,
            {
              exact h7,
            },
        assumption,
        },
      rw C,
      iterate 2 {apply or.intro_left},
      apply or.intro_right,
      rw mp_set,
      simp only [exists_prop, exists_eq_right, exists_and_distrib_left, set.mem_set_of_eq],
      existsi ψ,
      existsi ψ1,
      repeat {split},
      repeat {assumption},
  },
  {
    intros φ h0,
    rw gen_set at h0,
    simp only [exists_prop, set.mem_set_of_eq] at h0,
    rw [hd,kg_iff_cn],
    rcases h0 with ⟨ψ,h0,h1⟩,
    rw [hd,kg_iff_cn] at h0,
    cases h0 with n h0,
    existsi n + 1,
    rw C,
    apply or.intro_left,
    apply or.intro_right,
    rw gen_set,
    simp only [exists_prop, set.mem_set_of_eq],
    existsi ψ,
    exact and.intro h0 h1,
    },
    {
    intros φ h0,

    rw subst_set at h0,
    simp only [exists_prop, set.mem_set_of_eq] at h0,
    rw [hd,kg_iff_cn],
    rcases h0 with ⟨ψ,h0,h1⟩,
    rw [hd,kg_iff_cn] at h0,
    cases h0 with n h0,
    existsi n + 1,
    rw C,
    apply or.intro_right,
    rw subst_set,
    simp only [exists_prop, set.mem_set_of_eq],
    existsi ψ,
    exact and.intro h0 h1,
    },
  intro h0,
  have h1 : ∀ n, C D n ⊆ D,
    {
      intro n,
      induction n with k ih,
        {
          rw [C,base],
          rcases h0 with ⟨h0,h1,h2,h3⟩,
          intros φ h4,
          simp only [set.union_subset_iff] at h0,
          cases h0 with h0 h5,
          iterate 2 {cases h4},
          iterate 3 {tauto},
        },
      rw C,
      intros φ h1,
      rcases h0 with ⟨h2,h3,h4,h5⟩,
      iterate 3 {cases h1},
      exact ih h1,
      exact h3 (mp_contain ih h1),
      exact h4 (gen_set_contain ih h1),
      exact h5 (subst_set_contain ih h1),
    },
  rw normal_logic,
  simp only [set.mem_set_of_eq],
  existsi D,
  rw set.subset.antisymm_iff,
  split,
    {exact gam_sub_normal D},
    intros φ h2,
    rw kg_iff_cn at h2,
    cases h2 with n h2,
    exact (h1 n) h2,
end

/- The above theorem gives an easy way to prove that the set of 
all modal formulas is a normal logic. -/
