# Contents 

## syntax
1. **prop_syntax.lean** : It contains the syntax for the propositional language. It is needed because we will use propositional tautologies to define normal logics.
2. **syntax.lean** : It contains the syntax for the basic modal language, and how the propositional language is a sublanguage of the basic modal language.
3. **kripke_semantics.lean** : It defines truth and validity
4. **normal_logics.lean** : It defines normal logics from the 'bottom-up' approach and contains basic results about them. It also describes the 'top-down' approach of defining normal logics.
5. **soundness_and_completeness.lean** : It defines soundness and completeness for normal logics under the Kripke semantics, and constains some basic examples.
6. **topo_semantics.lean** : It defines the topological semantics and topological validity.
7. **topo_sound_complete.lean** : It defines soundness and completeness with respect to the topological semantics, and contains a proof of the fact that S4 is sound with respect to any class of topological spaces.
