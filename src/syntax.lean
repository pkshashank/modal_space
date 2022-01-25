import prop_syntax
set_option pp.coercions false

---------------------------------------------------

-- Syntax of the basic modal language
inductive bmod_form : Type
| var (n : ℕ) : bmod_form
| bot : bmod_form
| neg : bmod_form → bmod_form
| and : bmod_form → bmod_form → bmod_form
| dia : bmod_form → bmod_form

--Notations
notation ` '⊥` := bmod_form.bot
notation `'!` φ := bmod_form.neg φ
notation `'p` := bmod_form.var
notation φ ` '⋀ ` ψ  := bmod_form.and φ ψ
notation `'◇` φ := bmod_form.dia φ

-- Common Abbreviations
notation φ ` '⋁ ` ψ := '!('!φ '⋀ '!ψ)
notation φ ` '⇒ ` ψ := ('!φ) '⋁ ψ
notation φ ` '⇔ ` ψ := (φ '⇒ ψ) '⋀ (ψ '⇒ φ)
notation `'⊤` := '! '⊥
notation `'□ ` φ := '!('◇('!φ))


--------------------------------------------------------

-- We will use coercion to formalize that every basic propositional formula is a basic modal formula

instance prop_to_modal : has_coe prop_form bmod_form :=
⟨λ φ, prop_form.rec_on φ (λ n, 'p n) ('⊥) (λ ψ γ, '!γ) (λ ψ1 ψ2 γ1 γ2, γ1 '⋀ γ2)⟩

-- A similar coercion for the respective sets, using the 
-- above coercion
instance props_to_modals : has_coe (set prop_form) (set bmod_form) := ⟨λ props, prop_to_modal.coe ''(props)⟩
-------------------------------------------------
