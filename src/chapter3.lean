import logic.function.basic
import tactic.basic

section exercises


example {A B : Prop} (h: A ∧ B) : B ∧ A :=
begin
  show B ∧ A, from and.intro h.right h.left
end

example {Q R: Prop} (h: Q): (Q → R) → R :=
begin
  assume h₁, 
  from h₁ h
end

/--
  assume A and B introduces A and B, we use its negation (h) to eliminate
  the negation
  C :=  A ∧ B
  elimination
  ¬ C          C 
  --------------
      false

  then, proving not B is done by means of 
  have ¬ B, and the false we derive from eliminating ¬(A ∧ B)
  which is introducing ¬ B
  ¬ B
    |
    |
  false
  ----
    B
-/
example {A B : Prop} : ¬(A ∧ B) → (A → ¬ B) :=
begin
  assume h, assume : A, assume : B, 
  show false, from h ⟨‹A›, ‹B›⟩,
end

example {P Q R S T: Prop} (h₁: (P ∧ Q) ∧ R) (h₂: S ∧ T): Q ∧ S :=
begin
  from and.intro (h₁.left).right h₂.left
end

example {A B C : Prop} : (A → C) ∧ (B → ¬ C) → ¬ (A ∧ B) :=
begin
  assume h, assume ab,
  show false, from h.right ab.right (h.left ab.left)
end

example {A B C : Prop} : (A ∧ B) → ((A → C) → ¬(B → ¬ C)) :=
begin
  assume h₁, assume h₂, assume h₃,
  show false, from h₃ h₁.right (h₂ h₁.left)
end

example {A B : Prop} : (A ∨ B) → (B ∨ A) :=
begin
 assume h,
 from or.elim h
  (assume h₁ : A, show B ∨ A, from or.inr h₁ )
  (assume h₁ : B, show B ∨ A, from or.inl h₁ )
end

example {A B : Prop} : ¬ A ∧ ¬ B → ¬ (A ∨ B) :=
begin
 assume h₁, 
 assume h₂,
 from or.elim h₂
  (assume h: A, show false, from h₁.left h)
  (assume h: B, show false, from h₁.right h)
end

example {A B : Prop} : ¬ A ∨ ¬ B → ¬ (A ∧ B) :=
begin
 assume h₁,
 assume h₂,
 from or.elim h₁
    (assume h: ¬ A, show false, from h h₂.left)
    (assume h: ¬ B, show false, from h h₂.right)
end

example {A B : Prop} : ¬ (A ↔ ¬ A) :=
begin
  assume h₁,
  -- whenever there's a negation
  -- you can assume the hypothesis
  -- remember A := A → false
  -- which means you can assume A always
  have h₂ : ¬ A,
    from assume h₃: A,
      show false, from h₁.mp h₃ h₃,
    from h₂ (h₁.mpr h₂)
end

example {A B : Prop} (h: A ↔ B) : (¬ A ↔ ¬ B) :=
begin
split,
  {
    assume : ¬ A,
    assume : B,
      show false, from ‹¬ A› (h.mpr ‹B›),
  },
  {
    assume : ¬ B,
    assume : A,
      show false, from ‹¬ B› (h.mp ‹A›),
  }
end

example {P Q R : Prop} (h : (P ∨ Q) → R) : P → R :=
begin
  assume : P,
  have : P ∨ Q,
    from or.inl ‹P›,
  show R, from h ‹P ∨ Q›
end

example {A B C : Prop} (h: A ∨ B) : C → (A ∨ B) ∧ C :=
begin
  assume : C,
  show (A ∨ B) ∧ C, from and.intro h ‹C›
end

example {W Y X Z : Prop} (h: W → X) (h₁ : Y → Z) : W ∨ Y → X ∨ Z :=
begin
  assume h₂,
  from or.elim h₂
    (assume : W, show X ∨ Z, from or.inl (h ‹W› ))
    (assume : Y, show X ∨ Z, from or.inr (h₁ ‹Y›))
end

example {A B : Prop} : (A ∨ (B ∧ A)) → A :=
begin
  assume h,
  from or.elim h
    (assume : A, show A, from ‹A›)
    (assume : (B ∧ A), show A, from and.right ‹B ∧ A›)
end


end exercises