import topo_semantics
import top_down_proofs

/- Defining soundness and completeness with respect to a class of topological spaces-/

def tsound {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
Γ ∈  normal_logic ∧ Γ ⊆ top_class_valid_form cl

def tcomplete {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
Γ ∈  normal_logic ∧ top_class_valid_form cl ⊆ Γ

/- The next result is S4 is sound with respect to the class of all topological spaces -/

/--the class of all topological spaces based on type `X`-/
def all {X : Type*} : set (topological_space X) := λ T, true

def Ax_T := p 1 ⇒ ◇ (p 1)
def Ax_4 := ◇ ◇ (p 1) ⇒ ◇ (p 1)

/- The logic `S4` -/
def S4 := KΓ {Ax_T,Ax_4}

/- `S4` with the top-down definiton  -/
lemma S4_top_down : S4 = nl {Ax_T,Ax_4} :=
by rw [S4, nls_are_KΓs]

/- `Ax_T` is valid on every topological space -/
lemma Ax_T_tvalid {X : Type*} {T : topological_space X} : tvalid Ax_T T :=
begin
  rw valid_full_set,
  intros M,
  rw Ax_T,
  simp only [neg_is_compl, and_is_inter, diamond_is_closure],
  simp only [top_tr, compl_compl],
  refine (list.mem_pure set.univ (set_of (M.V 1) ∩ (closure (set_of (M.V 1)))ᶜ)ᶜ).mp _
end

/- `Ax_4` is valid on every topological space -/
lemma Ax_4_tvalid {X : Type*} {T : topological_space X} : tvalid Ax_4 T :=
begin
  sorry
end


example {X : Type*} : tsound S4 (@all X) :=
begin
  rw tsound,
  split,
    {
      rw S4_top_down,
      exact nls_are_normal {Ax_T,Ax_4},
    },
    rw [S4,KΓ,set_Cs],
    simp only [forall_exists_index, forall_eq_apply_imp_iff', set.sUnion_subset_iff, set.mem_set_of_eq],
    intros n,
    induction n with k ih,
      {
        rw [C,base],
        repeat{rw set.union_subset_iff, split},
          {
            sorry,
          },
        sorry,
        sorry,
      },
    sorry,
end
