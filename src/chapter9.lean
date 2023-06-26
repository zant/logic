import data.int.basic

--∀ introduction
example {U : Type} {P: U → Prop} (h : ∀ x, P x): ∀ x, P x :=
begin
  assume x,
  show P x, from h x
end


--∀ elimination
example {U : Type} {P: U → Prop} (h: ∀ x, P x) (a : U) : P a :=
show P a, from h a

--∃ introduction
example {U : Type} {P: U → Prop} (y : U) (h: P y) : ∃ x, P x := 
begin
  from exists.intro y h
end

--∃ elimination
example {U : Type} {P : U → Prop} {Q : Prop} (h : ∃ x, P x) (h': ∀ x, P x → Q) : Q :=
begin
  from exists.elim h 
    (assume (x : U) (h : P x),
      show Q, from h' x h)
end


example {U : Type} {A B : U → Prop} : (∃ x, A x ∨ B x) → (∃ x, A x) ∨ (∃ x, B x) :=
begin
  assume h,
  from exists.elim h
    (assume (x : U) (h : A x ∨ B x),
      or.elim h
        (assume : A x, 
          show ((∃ x, A x) ∨ (∃ x, B x)), 
          from or.inl $ exists.intro x ‹A x›)
        (assume : B x, 
          show ((∃ x, A x) ∨ (∃ x, B x)), 
          from or.inr $ exists.intro x ‹B x›))
end

example {U : Type} {A B : U → Prop} : (∀ x, A x) → (∀ x, B x) → (∀ x, A x ∧ B x) :=
begin
  assume hA : ∀ x, A x,
  assume hB : ∀ x, B x,
  assume y,
  have : A y, from hA y,
  have : B y, from hB y,
  from ⟨‹A y› , ‹B y›⟩ 
end


example {U : Type} {A B : U → Prop} : (∀ x, A x → ¬ B x) → ¬ ∃ x, A x ∧ B x :=
begin
  assume h1 : ∀ x, A x → ¬ B x,
  assume h2 : ∃ x, A x ∧ B x,  
  from exists.elim h2 (
    assume (x : U) (h: A x ∧ B x),
    have h1 : ¬ B x, from h1 x (h.left),
    show false, from h1 h.right)
end


--equality and calculation
example {U : Type } {x y z : U} : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
show x = z,
by rw [←h1, h2]

example {U : Type } {x y z : U} : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
calc
  x = y : eq.symm h1
  ... = z : h2

example (x y z : int) : (x + y) + z = (x + z) + y :=
begin
  calc
    (x + y) + z = x + (y + z) : by rw add_assoc x y z
    ... = x + (z + y) : by rw add_comm z y
    ... = (x + z) + y : by rw add_assoc
end

--exercises

--ex1
section
  variable A : Type
  variable f : A → A
  variable P : A → Prop

  -- Show the following:
  example (h : ∀ x, P x → P (f x)) : ∀ y, P y → P (f (f y)) :=
  begin
    assume y h1, -- introduce the variables y and h1 (P y)
    have h2 : P (f y), from h y h1,
    have h3 : P (f (f y)), from h (f y) h2,
    assumption,
  end
end

--ex2
section
  variable U : Type
  variables A B : U → Prop

  example : (∀ x, A x ∧ B x) → ∀ x, A x :=
  begin
    assume h,
    assume x,
    from and.left (h x)
  end
end

--ex3
section
  example {U :Type} {A B C : U → Prop}
          (h1 : ∀ x, A x ∨ B x) (h2 : ∀ x, A x → C x) (h3 : ∀ x, B x → C x) : 
          ∀ x, C x :=
  begin
    assume x,
    have h : A x ∨ B x, from h1 x,
    from or.elim h
      (assume : A x, show C x, from h2 x ‹A x›)
      (assume : B x, show C x, from h3 x ‹B x›)
  end
end

--ex4
open classical   -- not needed, but you can use it

-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x

  -- Show the following:
  example  : false :=
  have h1 : shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  not_iff_not_self (shaves barber barber) h1
end

--ex5
section
  variable U : Type
  variables A B : U → Prop

  example : (∃ x, A x) → ∃ x, A x ∨ B x :=
  begin
    assume h1,
    from exists.elim h1
      (assume (x : U) (h : A x),
        have h2 : A x ∨ B x, from or.inl h,
        show ∃ x, A x ∨ B x, from exists.intro x h2)
  end
end

--ex6
section
  variable U : Type
  variables A B : U → Prop

  variable h1 : ∀ x, A x → B x
  variable h2 : ∃ x, A x

  example : ∃ x, B x :=
  exists.elim h2
    (assume (x : U) (h : A x),
      show ∃ x, B x, from exists.intro x (h1 x h))
end


--ex7
section 
  variable  U : Type
  variables A B C : U → Prop

  example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
      ∃ x, A x ∧ C x :=
  begin
    from exists.elim h1
      ( assume (x : U) (h : A x ∧ B x),
        have C x, from h2 x (and.right h),
        exists.intro x ⟨h.left, ‹C x›⟩)
  end
end

--ex8
section
  variable  U : Type
  variables A B C : U → Prop

  example : (¬ ∃ x, A x) → ∀ x, ¬ A x :=
  begin
    assume h, 
    assume x,
    assume h1,
    apply h,
    from exists.intro x h1
  end

  example : (∀ x, ¬ A x) → ¬ ∃ x, A x :=
  begin
    assume h,
    assume h1,
    from exists.elim h1
      (assume (x : U) (h2 : A x),
        show false, from (h x) h2)
  end
end

--ex9
variable  U : Type
variables R : U → U → Prop

example : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y :=
begin
  intros h,
  assume y,
  from exists.elim h 
    (assume (x : U) (h : ∀ y, R x y),
      show ∃ x, R x y, from exists.intro x (h y))
end

--ex10
theorem foo {A : Type} {a b c : A} : a = b → c = b → a = c :=
begin
  assume h1,
  assume h2,
  rw h1,
  rw h2
end

-- notice that you can now use foo as a rule. The curly braces mean that
-- you do not have to give A, a, b, or c

section
  variable A : Type
  variables a b c : A

  example (h1 : a = b) (h2 : c = b) : a = c :=
  foo h1 h2
end

section
  variable {A : Type}
  variables {a b c : A}

  -- replace the sorry with a proof, using foo and rfl, without using eq.symm.
  theorem my_symm (h : b = a) : a = b :=
  foo rfl h

  -- now use foo and my_symm to prove transitivity
  theorem my_trans (h1 : a = b) (h2 : b = c) : a = c :=
  foo h1 (my_symm h2)
end

-- these are the axioms for a commutative ring

#check @add_assoc
#check @add_comm
#check @add_zero
#check @zero_add
#check @mul_assoc
#check @mul_comm
#check @mul_one
#check @one_mul
#check @left_distrib
#check @right_distrib
#check @add_left_neg
#check @add_right_neg
#check @sub_eq_add_neg

variables x y z : int

theorem t1 : x - x = 0 :=
calc
x - x = x + -x : by rw sub_eq_add_neg
    ... = 0      : by rw add_right_neg

theorem t2 (h : x + y = x + z) : y = z :=
calc
y     = 0 + y        : by rw zero_add
    ... = (-x + x) + y : by rw add_left_neg
    ... = -x + (x + y) : by rw add_assoc
    ... = -x + (x + z) : by rw h
    ... = (-x + x) + z : by rw add_assoc
    ... = 0 + z        : by rw add_left_neg
    ... = z            : by rw zero_add

theorem t3 (h : x + y = z + y) : x = z :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = (z + y) + -y : by rw h
    ... = z + (y + -y) : by rw add_assoc
    ... = z + 0        : by rw add_right_neg
    ... = z            : by rw add_zero

theorem t4 (h : x + y = 0) : x = -y :=
calc
x     = x + 0        : by rw add_zero
    ... = x + (y + -y) : by rw add_right_neg
    ... = (x + y) + -y : by rw add_assoc
    ... = 0 + -y       : by rw h
    ... = -y           : by rw zero_add

theorem t5 : x * 0 = 0 :=
have h1 : x * 0 + x * 0 = x * 0 + 0, from
calc
    x * 0 + x * 0 = x * (0 + 0) : by rw ←left_distrib
            ... = x * 0       : by rw add_zero
            ... = x * 0 + 0   : by rw add_zero,
show x * 0 = 0, from t2 _ _ _ h1

theorem t6 : x * (-y) = -(x * y) :=
have h1 : x * (-y) + x * y = 0, from
calc
    x * (-y) + x * y = x * (-y + y) : sorry
                ... = x * 0        : sorry
                ... = 0            : by rw t5 x,
show x * (-y) = -(x * y), from t4 _ _ h1

theorem t7 : x + x = 2 * x :=
calc
x + x = 1 * x + 1 * x : by rw one_mul
    ... = (1 + 1) * x   : by rw right_distrib
    ... = 2 * x         : rfl