open classical

-- by_contra example
example {A B : Prop } (h : ¬ (A ∧ ¬ B)) : A → B :=
begin
  assume : A,
  show B, from
    by_contradiction
      (assume : ¬ B,
        have A ∧ ¬ B, from and.intro ‹A› this,
        show false, from h this)
end

-- using excluded middle to show RAA
-- false implies anything (false.elim <>)
-- exercise 1
example {A B : Prop} : (¬A → false) → A :=
begin
  assume h₁,
  from or.elim (em A)
    (assume : A, show A, from ‹A›)
    (assume : ¬A, show A, from false.elim (h₁ ‹¬A›))
end

-- aux lemma for ex2 w RAA
lemma dn {A : Prop} (h1 : ¬¬A) : A := 
    show A, from by_contradiction 
      (assume h2 : ¬A,
      show false, from h1 h2)

--ex2 w RAA
example {A B : Prop} : ¬A ∨ ¬B → ¬(A ∧ B) :=
begin
  assume h,
  show ¬(A ∧ B), from
    by_contradiction
      (assume h₁ : ¬ (¬ (A ∧ B)),
        have h₂ : A ∧ B, from dn h₁,
        or.elim h
          (assume : ¬A, show false, from ‹¬A› h₂.left)
          (assume : ¬B, show false, from ‹¬B› h₂.right))
end

--ex2 wo RAA
example {A B : Prop} : ¬A ∨ ¬B → ¬(A ∧ B) :=
begin
  assume h1,
  assume h2,
  from or.elim h1
    (assume : ¬A, show false, from ‹¬A› h2.left)
    (assume : ¬B, show false, from ‹¬B› h2.right)
end

--ex3
-- fucking demorgan
lemma aux_contr {A B : Prop} (_: ¬(A ∧ B)) (_: ¬(¬A ∨ ¬B)) : ¬A ∨ ¬B  :=
begin
  have : ¬A,
    assume : A,
      -- prove ¬A with ¬B and ¬(A ∧ B)
      have : ¬B,
        assume : B,
          show false, from ‹¬(A ∧ B)› ⟨‹A›, ‹B›⟩,
      have : ¬A ∨ ¬B, from or.inr ‹¬B›, 
    show false, from ‹¬(¬A ∨ ¬B)› ‹¬A ∨ ¬B›,
  from or.inl ‹¬ A›
end

example {A B : Prop} : ¬(A ∧ B) → ¬A ∨ ¬B :=
begin
  assume h,
  show ¬A ∨ ¬B,
    from by_contradiction
      (assume h₁ : ¬(¬ A∨ ¬B),
        show false, from h₁ (aux_contr h h₁))
end

--ex4
example {P Q R : Prop} (h: ¬ P → (Q ∨ R)) (_: ¬Q) (_: ¬R) : P :=
begin
  show P, 
    from by_contradiction
      (assume : ¬ P, 
        or.elim (h ‹¬ P›)
          (assume : Q, show false, from ‹¬Q› ‹Q›) 
          (assume : R, show false, from ‹¬R› ‹R›))
end

--ex5
example {A B : Prop} : (A → B) → ¬A ∨ B := 
begin
  assume h : A → B,
  from or.elim (em A)
    (assume : A, show (¬A ∨ B), from or.inr (h ‹A›))
    (assume : ¬ A, show ¬A ∨ B, from or.inl ‹¬A›)
end

--ex6
example {A B : Prop } : A → ((A ∧ B) ∨ (A ∧ ¬B)) := 
begin
  assume h,
  from or.elim (em B)
    (assume : B, show  ((A ∧ B) ∨ (A ∧ ¬B)), from or.inl ⟨h, ‹B›⟩)
    (assume : ¬B, show  ((A ∧ B) ∨ (A ∧ ¬B)), from or.inr ⟨h, ‹¬B›⟩)
end
 
--ex8 is ex3

--ex9
open classical

example {A B C : Prop} (h : ¬ B → ¬ A) : A → B :=
begin
  assume : A,
  show B,
  from by_contradiction
    (assume : ¬ B,
      show false, from (h ‹¬ B›) ‹A›)
end
