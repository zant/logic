import data.set.basic

section examples
open set

variable {U : Type}
variables A B C : set U
variable x : U

#check x ∈ A 
#check A ∪ B
#check B \ C
#check C ∩ A
#check Cᶜ
#check ∅ ⊆ A
#check B ⊆ univ

--union
example : A ⊆ B :=
begin
  assume x,
  assume h : x ∈ A,
  show x ∈ B, from sorry
end

example : A = B := 
begin
  from eq_of_subset_of_subset
    (assume x,
      assume h : x ∈ A,
      show x ∈ B, from sorry)
    (assume x,
      assume h : x ∈ B,
      show x ∈ A, from sorry)
end


example : A \ B ⊆ Bᶜ :=
begin
  assume x,
  assume h,
  have : x ∉ B, from and.right h,
  from this,
end



example : A ∩ B ⊆ B ∩ A :=
begin
  assume x,
  assume h : x ∈ A ∩ B,
  from and.intro h.right h.left
end

end examples

section
open set
  example {U : Type} {A B C : set U} : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  begin
    from eq_of_subset_of_subset
      (assume x,
        assume h : x ∈ A ∩ (B ∪ C), 
        have x ∈ B ∪ C, from and.right h,
        or.elim ‹x ∈ B ∪ C›
          (assume : x ∈ B,
            have x ∈ (A ∩ B), from and.intro h.left ‹x ∈ B›,
            show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inl ‹x ∈ (A ∩ B)›)
          (assume : x ∈ C, 
            have x ∈ (A ∩ C), from and.intro h.left ‹x ∈ C›,
            show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inr (‹x ∈ (A ∩ C)›)))
      (assume x,
        assume h : x ∈ (A ∩ B) ∪ (A ∩ C),
        or.elim h
          (assume h1 : x ∈ (A ∩ B), 
            show x ∈ A ∩ (B ∪ C), 
            from and.intro h1.left (or.inl h1.right))
          (assume h1 : x ∈ (A ∩ C), 
            show x ∈ A ∩ (B ∪ C), 
            from and.intro h1.left (or.inr h1.right)))
      end
end

theorem inter_union_subset {U : Type} {A B C : set U} : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  assume x,
  assume h : x ∈ A ∩ (B ∪ C),
  have : x ∈ (B ∪ C), from h.right,
  from or.elim ‹x ∈ B ∪ C›
    (assume : x ∈ B, 
      have x ∈ (A ∩ B), from and.intro h.left ‹x ∈ B›,
      show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inl ‹x ∈ (A ∩ B)›)
    (assume : x ∈ C,
      have x ∈ (A ∩ C), from and.intro h.left ‹x ∈ C›,
      show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inr ‹x ∈ (A ∩ C)›)
end

theorem inter_union_inter_subset {U : Type} {A B C : set U} : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) :=
begin
  assume x,
  assume h : x ∈ (A ∩ B) ∪ (A ∩ C),
  from or.elim h
    (assume h1 : x ∈ (A ∩ B),
      show x ∈ (A ∩ (B ∪ C)), 
      from ⟨h1.left, (or.inl h1.right)⟩)
    (assume h1 : x ∈ (A ∩ C),
      show x ∈ (A ∩ (B ∪ C)), 
      from ⟨h1.left, (or.inr h1.right)⟩)
end

section

open set
example {U : Type} {A B C : set U} : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  from eq_of_subset_of_subset inter_union_subset inter_union_inter_subset
end

end

section
variables {I U : Type}

-- def Union (A : I → set U) : set U := { x | ∃ i : I, x ∈ A i}
-- def Inter (A : I → set U) : set U := { x | ∀ i : I, x ∈ A i}

variables (x : U) (A : I → set U)

-- example (h : x ∈ Union A) : ∃ i, x ∈ A i := h
-- example (h : x ∈ Inter A) : ∀ i, x ∈ A i := h

end
section
-- notation `⋃` binders `, ` r:(scoped f, Union f) := r
-- notation `⋂` binders `, ` r:(scoped f, Inter f) := r

variables {I U : Type}

variables (A : I → set U) (x : U)
open set

-- example (h: x ∈ ⋃ i, A i) : ∃ i, x ∈ A i := h
-- example (h: x ∈ ⋂ i, A i) : ∀ i, x ∈ A i := h

end

--exercises
--ex1 

example {U : Type} {A B C : set U} : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
begin
  assume x,
  assume h,
  from or.inl (h.left)
end

example {U : Type} {A B C : set U} : ∀ x, x ∈ (A ∪ B)ᶜ → x ∈ Aᶜ :=
begin
  intros x h1 h2,
  have : x ∈ A ∪ B, from or.inl h2,
  from h1 ‹x ∈ A ∪ B›
end

--ex2
section
variable {U : Type}

/- defining "disjoint" -/
def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
  disj A B :=
begin
  assume x,
  assume h1 : x ∈ A,
  assume h2 : x ∈ B,
  have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
  show false, from h x h3
end

-- notice that we do not have to mention x when applying
--   h : disj A B
example (A B : set U) (h1 : disj A B) (x : U)
    (h2 : x ∈ A) (h3 : x ∈ B) :
  false :=
h1 h2 h3

-- the same is true of ⊆
example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
  x ∈ B :=
h h1

example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
    (h3 : D ⊆ B) :
  disj C D :=
begin
  intros x h4 h5,
  have : x ∈ A, from h2 h4,
  have : x ∈ B, from h3 h5,
  show false, from h1 ‹x ∈ A› ‹x ∈ B› 
end
end


section

variables {I U : Type}
variables {A : I → set U} 

def Union (A : I → set U) : set U := { x | ∃ i : I, x ∈ A i}
def Inter (A : I → set U) : set U := { x | ∀ i : I, x ∈ A i}

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

end

--ex3
section
variables {I U : Type}
variables {A : I → set U} (B : I → set U) (C : set U)

--utils
theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
by simp; assumption

@[elab_simple]
theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
by simp at h; apply h

theorem Union.intro {x : U} (i : I) (h : x ∈ A i) :
  x ∈ ⋃ i, A i :=
by {simp, existsi i, exact h}

theorem Union.elim {b : Prop} {x : U}
(h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
by {simp at h₁, cases h₁ with i h, exact h₂ i h}

example (x : U) (i : I) (h : x ∈ ⋂ i, A i) : x ∈ A i :=
Inter.elim h i


example (x : U) (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
Union.intro i h

example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
begin
  intros x h,
  have : x ∈ ⋂ i, A i, from h.left,
  have : x ∈ ⋂ i, B i, from h.right,
  from Inter.intro
    (assume i,
      show x ∈ A i ∩ B i, from
        have x ∈ A i, from Inter.elim h.left i,
        have x ∈ B i, from Inter.elim h.right i,
        and.intro ‹ x ∈ A i › ‹ x ∈ B i›)
end

example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
begin
  assume x,
  assume h,
  from Union.elim h.right
    (assume i, assume h1 : x ∈ A i,
      have x ∈ C ∩ A i, from ⟨h.left, h1⟩,
      show x ∈ ⋃ i, C ∩ A i, from Union.intro i ‹x ∈ C ∩ A i›)
end


end

section

open set
-- BEGIN
variable  {U : Type}
variables A B C : set U

-- For this exercise these two facts are useful
example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
subset.trans h1 h2

example : A ⊆ A :=
subset.refl A

example (h : A ⊆ B) : 𝒫 A ⊆ 𝒫 B :=
begin
  assume A',
  assume h1 : A' ∈ 𝒫 A,
  assume x,
  assume h2 : x ∈ A',
  have : x ∈ A, from h1 h2,
  from h ‹x ∈ A›
end

example (h : 𝒫 A ⊆ 𝒫 B) : A ⊆ B :=
begin
  assume x,
  assume : x ∈ A,
  have : A ∈ 𝒫 A, from subset.refl A,  
  have : A ∈ 𝒫 B, from h ‹A ∈ 𝒫 A›,
  from ‹A ∈ 𝒫 B› ‹x ∈ A›  
end

end




