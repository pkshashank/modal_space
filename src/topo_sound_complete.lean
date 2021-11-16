import topo_semantics
import top_down_proofs

/- Defining soundness and completeness with respect to a class of topological spaces-/

def tsound {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
Γ ∈  normal_logic ∧ Γ ⊆ top_class_valid_form cl

def tcomplete {X : Type*} (Γ : set bmod_form) (cl : set (topological_space X)) :=
Γ ∈  normal_logic ∧ top_class_valid_form cl ⊆ Γ

/- The next result is S4 is valid with respect to the class of all topological spaces -/

/--the class of all topological spaces based on type `X`-/
def all (X : Type*) : set (topological_space X) := λ T, true

def T := p 1 ⇒ ◇ (p 1)
def Ax_4 := ◇ ◇ (p 1) ⇒ ◇ (p 1)

/- The logic `S4` -/
def S4 := KΓ {T,Ax_4}

/- `S4` with the top-down definiton  -/
lemma S4_top_down : S4 = nl {T,Ax_4} :=
by rw [S4, nls_are_KΓs]

example {X : Type*} : tsound S4 (all X) :=
begin
  sorry,
end

