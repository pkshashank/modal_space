import top_down_proofs

-----------------------------------------------
/- Soundness -/

def sound (log : set bmod_form) (cl : set frames) := log ∈ normal_logic → log ⊆ frame_logic cl


