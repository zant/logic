-- exercises are at the bottom! --
import logic.function.basic
import tactic.basic

variables p q : Prop

example : p ∧ (p → q) → p ∧ q :=
begin
  assume h,
  split,
  { from and.left h },
  { from (and.right h) (and.left h) }
end

universes u

class semigroup (G : Type) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

section deduction

variables A B : Prop

-- implication introduction
example : A → B :=
assume h : A,
show B, from sorry

-- implication elimination
section 
  variable h1 : A → B
  variable h2 : A
  example : B := h1 h2
end

-- conjuction introduction
section
  variables (h1: A) (h2 : B)
  example : A ∧ B := and.intro h1 h2
end

-- conjuction elimination
section 
  variable h : A ∧ B 
  example : A := and.left h
  example : B := and.right h
end

-- discution introduction
section
  variable h : A
  example : A ∨ B := or.inl h
end

section
  variable h : B
  example : A ∨ B  := or.inr h
end

-- disjuction elimination
section
  variables C : Prop
  variable h : A ∨ B
  variables (ha : A → C) (hb : B → C)
  example : C :=
  or.elim h
    (assume h1 : A, show C, from ha h1)
    (assume h1 : B, show C, from hb h1)
end

-- negation introduction
section
  example : ¬ A :=
  begin
  assume h : A,
  show false, from sorry
  end
end

-- negation elimination
section
  variable h1 : ¬ A
  variable h2 : A

  example : false := h1 h2
end

-- truth and falsisity
section 
  variable h : false
  example : A := false.elim h
end

example : true := trivial


-- bi implication
section
example : A ↔ B :=
iff.intro
  (assume h : A, show B, from sorry)
  (assume h : B, show A, from sorry)
end

-- bi-implication elim
section
  variable h1 : A ↔ B
  variable h2 : A
  example : B := iff.mp h1 h2
end

section
  variable h1 : A ↔ B
  variable h2 : B
  example : A := iff.mpr h1 h2
end

-- RAA
section
  open classical
  example : A :=
  by_contra
    (assume h: ¬A, show false, from sorry)
end

end deduction

section examples

variables A B C : Prop

example : (A → B) → (B → C) → (A → C) :=
begin
  assume h1 : A → B,
  assume h2 : B → C,
  assume h,
  show C, from h2 (h1 h)
end

example (A B C : Prop) : (A → (B → C)) → (A ∧ B → C) :=
begin
  assume h1 : A → (B → C),
  assume h2 : A ∧ B,
  show C, from (h1 (and.left h2) (and.right h2))
end

example (A B C: Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
begin
  assume h : A ∧ (B ∨ C),
  from or.elim (and.right h)
    (assume h1 : B, 
      show (A ∧ B) ∨ (A ∧ C), 
        from or.inl (and.intro (and.left h) h1))
    (assume h1 : C, 
      show (A ∧ B) ∨ (A ∧ C), 
        from or.inr (and.intro (and.left h) h1))
end

end examples

section forward_reasoning

-- cute one!
example (A B C : Prop) : A ∧ (B ∨ C)  → (A ∧ B) ∨ (A ∧ C) :=
begin
  assume h,
  have : A, from h.left,
  have: B ∨ C, from h.right,
  from or.elim ‹B ∨ C› 
    (assume : B, 
      have (A ∧ B), from ⟨‹A›, ‹B›⟩,
      show (A ∧ B) ∨ (A ∧ C), 
      from or.inl ‹A ∧ B›)
    (assume : C,
      have (A ∧ C), from ⟨‹A›, ‹C›⟩ ,
      show (A ∧ B) ∨ (A ∧ C), 
      from or.inr ‹A ∧ C›)
end

-- false from absurd
variables A B : Prop
variable h1 : ¬A
variable h2 : A
#check false.elim (h1 h2)

end forward_reasoning

section reusability

-- false implies everything
lemma or_resolve_left {A B : Prop} (h1 : A ∨ B) (h2: ¬A) : B :=
or.elim h1
  (assume ha: A, show B, from false.elim (h2 ha))
  (assume hb: B, show B, from hb)

variables A B : Prop
variable h1 : A ∨ B
variable h2 : ¬A
#check or_resolve_left h1 h2

lemma or_resolve_right {A B : Prop} (_ : A ∨ B) (_ : ¬B) : A :=
or.elim ‹A ∨ B›  
  (assume : A, show A, from ‹A›)
  (assume : B, show A, from false.elim (‹¬B›‹B›))

variable h3 : ¬B 
#check or_resolve_right h1 h3

lemma and_commute {A B : Prop} (h : A ∧ B) : B ∧ A :=
⟨h.right , h.left⟩

variable h₄ : A ∧ B
#check and_commute h₄

end reusability

section exercises

variables A B C D : Prop

example : A ∧ (A → B) → B :=
begin
  assume h,
  from h.right h.left
end

example : A → ¬ (¬ A ∧ B) :=
begin
  assume : A,
  assume h : ¬ A ∧ B,
  show false,
    from h.left ‹A›  
end

example : ¬ (A ∧ B) → (A → ¬ B) :=
begin
  assume h,
  assume : A,
  have  : ¬ B, 
    from assume : B,
        show false, from h ⟨‹A›, ‹B›⟩,
  assumption,
end

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
begin
  from or.elim h₁ 
    (assume : A, show C ∨ D, from or.inl (h₂ ‹A›))
    (assume : B, show C ∨ D, from or.inr (h₃ ‹B›))
end

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
begin
  have : ¬ A, from h.left,
  have : ¬ B, from h.right,
  assume : A ∨ B, 
  from or.elim ‹A ∨ B› 
    (assume : A, show false, from ‹¬A› ‹A›)
    (assume : B, show false, from ‹¬B› ‹B›)
end

example : ¬ (A ↔ ¬ A) :=
begin
  assume h,
  have : (A → ¬A), from h.mp,
  have : (¬A → A), from h.mpr,
  have : ¬ A, 
    from assume : A,
      show false, from (‹(A → ¬A)› ‹A›) ‹A›,
  from ‹¬A› (‹(¬A → A)› ‹¬A›)
end

end exercises