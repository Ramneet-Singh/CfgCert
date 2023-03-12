import Basic
import Utils

variables {NT T : Type}

constant fresh : (list NT) → NT
constant isFresh (α : list NT) (A = fresh α) : A ∉ α

def StartTransform (g1 : CFG NT T) (g2 : CFG NT T) : Prop :=
  ∃ SNew : NT,
       (¬ (CFG_NonTerms g1 SNew))
      ∧((g2.start = SNew)
      ∧(g2.rules = g1.rules ∪ { (SNew, [Symbol.NonTerminal g1.start]) }))

lemma StartSoundness1 (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) →
  (∀ w_1 : list (Symbol NT T), ∀ w_2 : list (Symbol NT T),
  CFG_Derives_1_Step g1 w_1 w_2 → CFG_Derives_1_Step g2 w_1 w_2
  ) :=
  begin
    intro hTrans,
    intros w1 w2,
    intro h1,
    unfold CFG_Derives_1_Step at h1,
    cases h1 with r h2,
    have h3 : r ∈ g1.rules := and.elim_left h2,
    unfold StartTransform at hTrans,
    cases hTrans with _ hTrans,
    have h4 : r ∈ g2.rules := 
    begin
      have h5 : g2.rules = g1.rules ∪ {(hTrans_w, [Symbol.NonTerminal g1.start])} := and.elim_right (and.elim_right hTrans),
      rw h5,
      apply (iff.elim_right (set.mem_union r g1.rules {(hTrans_w, [Symbol.NonTerminal g1.start])})),
      apply or.intro_left,
      exact h3,
    end,
    unfold CFG_Derives_1_Step,
    use r,
    exact and.intro h4 (and.elim_right h2),
  end

lemma StartSoundness2 (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) →
  (∀ w_1 : list (Symbol NT T), ∀ w_2 : list (Symbol NT T),
  CFG_Derives g1 w_1 w_2 → CFG_Derives g2 w_1 w_2
  ) := by
  {
    intros hTrans w1 w2,
    intro h1,
    unfold CFG_Derives at h1,
    induction h1 with α β h2 h3,
    {
      unfold CFG_Derives,
    },
    {
      have h4 : CFG_Derives_1_Step g2 α β := StartSoundness1 g1 g2 hTrans α β h3,
      unfold CFG_Derives at h1_ih,
      unfold CFG_Derives,
      exact relation.refl_trans_gen.tail h1_ih h4,
    },
  }

lemma StartSoundness3 (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) →
  (∀ w : list T,
  CFG_Generates g1 w → CFG_Generates g2 w
  ) := by
  {
    intros hTrans w h1,
    unfold CFG_Generates at h1,
    have hTransOrig := hTrans,
    unfold StartTransform at hTrans,
    cases hTrans with SNew hTrans,
    have h2 : CFG_Derives g2 [Symbol.NonTerminal SNew] [Symbol.NonTerminal g1.start] := by
    {
      unfold CFG_Derives,
      apply relation.refl_trans_gen.single,
      unfold CFG_Derives_1_Step,
      use (SNew, [Symbol.NonTerminal g1.start]),
      split,
      {
        rw (and.elim_right (and.elim_right hTrans)),
        have h3 : (SNew, [Symbol.NonTerminal g1.start]) ∈ {(SNew, [Symbol.NonTerminal g1.start])} := by
        {refine set.mem_singleton (SNew, [Symbol.NonTerminal g1.start]), exact nat,},
        exact g1.rules.mem_union_right rfl,
      },
      {
        use ([]),
        use ([]),
        split,
        {
          exact rfl,
        },
        {
          exact rfl,
        },
      },
    },
    have h5 := StartSoundness2 g1 g2 hTransOrig [Symbol.NonTerminal g1.start] (liftWordToSf w NT) h1,
    unfold CFG_Derives at h2 h5,
    have h6 := relation.refl_trans_gen.trans h2 h5,
    have h7 := (and.elim_left (and.elim_right hTrans)),
    rw ← h7 at h6,
    unfold CFG_Generates, unfold CFG_Derives, exact h6,
  }

lemma StartCompleteness2 (g1 : CFG NT T) (g2 : CFG NT T) (α : list (Symbol NT T)):
  (StartTransform g1 g2) → (CFG_Derives_1_Step g2 [Symbol.NonTerminal g2.start] α) → α = [Symbol.NonTerminal g1.start] := by
  {
    intros hTrans h1,
    unfold CFG_Derives_1_Step at h1,
    cases h1 with r h2,
    have h3 := and.elim_left h2,
    have h4 := and.elim_right h2,
    cases h4 with a h5,
    cases h5 with c h6,
    have h7 := and.elim_left h6,
    have h8 := and.elim_right h6,
    have h9 : (a = []) ∧ (c = []) ∧ (Symbol.NonTerminal r.fst = Symbol.NonTerminal g2.start) := by 
    {
      exact singleton_eq_append_implies_empty a c (Symbol.NonTerminal r.fst) (Symbol.NonTerminal g2.start) h7,
    },
    have h10 := and.elim_left h9, have h11 := and.elim_left (and.elim_right h9), have h12 := and.elim_right (and.elim_right h9),
    simp [h10, h11] at h8,
    simp at h12,
    have h13 : r.snd = [Symbol.NonTerminal g1.start] := by
    {
      unfold StartTransform at hTrans,
      cases hTrans with SNew,
      have h13 := and.elim_left hTrans_h, have h14 := and.elim_left (and.elim_right hTrans_h), have h15 := and.elim_right (and.elim_right hTrans_h),
      simp [h15] at h3,
      rw [← h14] at h3 h13,
      cases h3,
      {
        simp [h3],
      },
      {
        exfalso,
        have h16 : CFG_NonTerms g1 r.fst := by
        {
          unfold CFG_NonTerms,
          apply or.inr,
          use r,
          split,
          exact h3,
          unfold RuleNonTerms,
          simp,
        },
        rw [h12] at h16,
        exact h13 h16,
      },
    },
    simp [h13, h8],
  }

lemma StartCompleteness3 (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) →
(∀ α β: list (Symbol NT T), 
(∀ A : NT, ((Symbol.NonTerminal A) ∈ α  → CFG_NonTerms g1 A)) → CFG_Derives g2 α β → (∀ A : NT, ((Symbol.NonTerminal A) ∈ β → CFG_NonTerms g1 A))
) := by
{
  intros hTrans α β h1 h2,
  unfold CFG_Derives at h2,
  induction h2 with γ δ hγ hδ,
  {
    exact h1,
  },
  {
    unfold CFG_Derives_1_Step at hδ,
    cases hδ with r,
    have h3 := and.elim_left hδ_h, have h4 := and.elim_right hδ_h,
    unfold StartTransform at hTrans,
    cases hTrans with SNew,
    have h5 := and.elim_right (and.elim_right hTrans_h),
    rw [h5] at h3,
    cases h3,
    {
      intros A h7,
      cases h4 with a h4,
      cases h4 with c h4,
      have h8 := and.elim_left h4, have h9 := and.elim_right h4,
      -- use h2_ih h3 h7 h8 h9
      simp [h9] at h7,
      cases h7,
      {
        have h10 : Symbol.NonTerminal A ∈ γ := by { rw [h8], refine list.mem_append.mpr _, apply or.inl, refine list.mem_append.mpr _, apply or.inl, exact h7, },
        exact h2_ih A h10,
      },
      {
        cases h7,
        {
          unfold CFG_NonTerms,
          apply or.inr,
          use r,
          unfold RuleNonTerms,
          split, { exact h3, }, { exact or.inr h7, },
        },
        {
          have h10 : Symbol.NonTerminal A ∈ γ := by { rw [h8], refine list.mem_append.mpr _, exact or.inr h7, },
          exact h2_ih A h10,
        },
      },
    },
    {
      simp at h3,
      cases h4 with a h4,
      cases h4 with c h4,
      have h8 := and.elim_left h4, have h9 := and.elim_right h4,
      -- use h8, h9, h3, h2_ih
      intros A h10,
      simp [h9] at h10,
      cases h10,
      {
        have h10 : Symbol.NonTerminal A ∈ γ := by { rw [h8], refine list.mem_append.mpr _, apply or.inl, refine list.mem_append.mpr _, apply or.inl, exact h10, },
        exact h2_ih A h10,
      },
      {
        cases h10,
        {
          simp [h3] at h10,
          simp [h10], unfold CFG_NonTerms, apply or.inl, refl,
        },
        {
          have h11 : Symbol.NonTerminal A ∈ γ := by { rw [h8], refine list.mem_append.mpr _, exact or.inr h10, },
          exact h2_ih A h11,
        },
      },
    },
  },
}

lemma StartCompleteness4 (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) →
(∀ α : list (Symbol NT T), 
(∀ A : NT, ((Symbol.NonTerminal A) ∈ α  → CFG_NonTerms g1 A)) → (∀ β : list (Symbol NT T), 
  CFG_Derives g2 α β → CFG_Derives g1 α β
)) := by
{
  intros hTrans α hNT β h1,
  unfold CFG_Derives at h1,
  induction h1 with γ δ h1_γ h1_δ,
  {
    unfold CFG_Derives,
  },
  {
    have h2 : (∀ A : NT, ((Symbol.NonTerminal A) ∈ γ → CFG_NonTerms g1 A)) := StartCompleteness3 g1 g2 hTrans α γ hNT h1_γ,
    have h3 : CFG_Derives_1_Step g1 γ δ := by
    {
      unfold CFG_Derives_1_Step at h1_δ,
      cases h1_δ with r,
      have h4 := and.elim_left h1_δ_h, have h5 := and.elim_right h1_δ_h,
      unfold StartTransform at hTrans,
      cases hTrans with SNew,
      have h6 := and.elim_right (and.elim_right hTrans_h),
      rw [h6] at h4,
      cases h4,
      {
        unfold CFG_Derives_1_Step,
        use r,
        exact and.intro h4 h5,
      },
      {
        exfalso,
        cases h5 with a h5,
        cases h5 with c h5,
        have h7 := and.elim_left h5,
        have h8 : r= (SNew, [Symbol.NonTerminal g1.start]) := by {
          exact set.mem_singleton_iff.mp h4,
        },
        simp [h8] at h7,
        have h9 := h2 SNew,
        simp [h7] at h9,
        have h10 := and.elim_left hTrans_h,
        exact h10 h9,
      },
    },
    exact relation.refl_trans_gen.tail h1_ih h3,
  },
}

theorem StartCompleteness (g1 : CFG NT T) (g2 : CFG NT T) : (StartTransform g1 g2) → ∀ w : list T, (CFG_Generates g2 w) → (CFG_Generates g1 w) := by
{
  intros hTrans w h1,
  unfold CFG_Generates at *,
  unfold CFG_Derives at h1,
  have h2 := relation.refl_trans_gen.cases_head h1,
  cases h2,
  {
    unfold liftWordToSf at h2,
    exfalso,
    apply_fun (λ l : list (Symbol NT T), ( Symbol.NonTerminal g2.start ) ∈ l) at h2,
    simp at h2,
    cases h2,
    have h3 := and.elim_right h2_h,
    unfold liftTermToSymbol at h3,
    simp at h3,
    exact h3,
  },
  {
    cases h2,
    have h3 := StartCompleteness2 g1 g2 h2_w hTrans (and.elim_left h2_h),
    have h4 : (∀ A : NT, ((Symbol.NonTerminal A) ∈ h2_w  → CFG_NonTerms g1 A)) := by
    {
      intro A,
      simp [h3],
      intro h4,
      unfold CFG_NonTerms,
      apply or.inl, exact h4,
    },
    have h5 := StartCompleteness4 g1 g2 hTrans h2_w h4 (liftWordToSf w NT) (and.elim_right h2_h),
    simp [h3] at h5,
    exact h5,
  },
}

-- noncomputable def StartTransform (g : CFG NT T) : CFG (NT ⊕ T ⊕ 
-- ( Σ r : NT × list (Symbol NT T), fin (r.snd.length) )
--  ) T :=
--   let
--     N := CFG_NonTerms g,
--     SNew := fresh N
--   in
--     (CFG.mk
--       ([ (SNew, [ Symbol.NonTerminal g.start ]) ] ++ g.rules)
--       SNew
--     )





























-- def newNT (NT : Type) (T : Type) : Type :=
--   option ( (NT ⊕ T) ⊕ 
-- ( Σ r : NT × list (Symbol NT T), fin (r.snd.length) )
--  )

-- def WrapNonTerminal (A : NT) : newNT NT T := option.some (sum.inl(sum.inl(A)))

-- def WrapSymbol (X : Symbol NT T) : Symbol (newNT NT T) T :=
--   match X with
--     Symbol.Terminal a := Symbol.Terminal a
--     | Symbol.NonTerminal A := Symbol.NonTerminal (WrapNonTerminal A)
--   end

-- def WrapGrammar (g : CFG NT T) : CFG (newNT NT T) T :=
--     (CFG.mk
--       (
--         [(none, [Symbol.NonTerminal (WrapNonTerminal g.start)])]
--         ++
--         (list.map 
--         (λ r : NT × list (Symbol NT T),
--           (WrapNonTerminal r.fst, list.map WrapSymbol r.snd)
--         )
--       g.rules)
--       )
--       (none)
--     )

