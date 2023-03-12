import tactic

variable { T : Type}

lemma singleton_eq_append_implies_empty (a b: list T) (c d : T) : ([d] = a ++ [c] ++ b) → (a = [] ∧ b = [] ∧ c=d) := by
  {
    intro h,
    have h1 : a=[] := by
    {
      rw [←list.length_eq_zero, ←le_zero_iff],
      apply_fun list.length at h,
      simp only [list.length_append, list.length_singleton, list.append_assoc, list.singleton_append] at h,
      apply le_of_add_le_add_right,
      rw [←h],
      simp,
    },
    have h2 : b=[] := by
    {
      simp [h1] at h,
      rw [eq_comm],
      exact and.elim_right h,
    },
    have h3 : c=d := by
    {
      simp [h1, h2] at h,
      simp [eq_comm, h],
    },
    exact and.intro h1 (and.intro h2 h3),
  }