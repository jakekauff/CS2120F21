-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h, 
  -- cases works because case analysis that there 
  -- are 0 ways to build a proof of 0 = 1.
end

--2
example: 0 ≠ 0 → 2 = 3 :=
begin 
  assume h,
  exact false.elim(h (eq.refl 0)), 
  -- apply false elimination rule to a proof of false.
  -- get that proof of false by applying h to 0 = 0, 
  -- or in lean eq.refl 0.
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
-- Prof. Sullivan's way
begin 
  assume P,
  assume(p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h, 
  apply h p,
end
/- My Way
begin 
  assume p,
  assume p1,
  apply not.intro,
  assume notp,
  exact notp p1,
end
-/

-- law of the excluded middle
axiom em : ∀ (p : Prop), p ∨ ¬ p

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin 
  assume (p : Prop),
  assume nnp,
  -- negation elimination rule
      -- allows you to eliminate double negations
  -- independent axiom
  have pornp := classical.em p,
  cases pornp with p pn,
  --p 
    exact p,
  --pn
    contradiction, --or you can derive a proof of false and apply false.elim 
end