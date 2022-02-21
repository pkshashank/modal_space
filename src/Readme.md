# Contents 

## syntax
1. **prop_syntax.lean** : It contains the syntax for the propositional language. It is needed because we will use propositional tautologies to define normal logics.
2. **modal_syntax.lean** : It contains the syntax for the basic modal language, and how the propositional language is a sublanguage of the basic modal language.

## kripke_semantics
1. **truth_and_validity.lean** : It defines truth and validity
2. **normal_logics.lean** : It defines normal logics from the 'bottom-up' approach and contains basic results about them. It also describes the 'top-down' approach of defining normal logics.
3. **soundness_and_completeness.lean** : It defines soundness and completeness for normal logics under the Kripke semantics, and constains some basic examples.

## topo_semantics
1. **basics.lean** : It defines the topological semantics and topological validity.
2. **topo_sound_complete.lean** : It defines soundness and completeness with respect to the topological semantics, and contains a proof of the fact that S4 is sound with respect to any class of topological spaces.
3. S4_completeness
    1. **temp.lean** : In progress
