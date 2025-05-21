
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Appendix.lean'>Code</a> for this chapter</span>
 # Useful Theorems 
```lean
theorem not_empty_to_exists {A : Type u} {S : Set A} : S ≠ ∅ → ∃ x, x ∈ S := by
   intro h
   by_contra h'
   simp at h'
   exact h (Set.eq_empty_iff_forall_not_mem.mpr h')

theorem not_empty_set_diff {A : Type u} {X Y : Set A} (h : ¬X ⊆ Y)
  : X \ Y ≠ ∅ := by
  simp[Set.instSDiff,Set.diff]
  by_contra hx
  simp at hx
  exact h hx
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
