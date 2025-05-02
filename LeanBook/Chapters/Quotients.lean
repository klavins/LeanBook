import Mathlib

/- # Quotients

## A Nonstandard Point Type

To motivate the case for quotients, let's consider a simple, easy to understand, but nonstandard, way of defining pairs of natural numbers. Instead of taking the cross product of Nat with itself, let's define a new inductive type `Walk` as follows: -/

inductive Walk where
  | zero : Walk
  | up : Walk → Walk
  | right : Walk → Walk

open Walk

/- The idea is that starting at (0,0) we can walk up or to the right to get to another point. Clearly, we have multiple ways to represent the same endpoint though. For example, we want to think of the following as equivalent: -/

#check zero.up.right
#check zero.right.up

/- The point of quotients is to allow us to talk about points up to equivalence, and not worry about which representative of a particular set of equivalent points we are talking about.

To start, we define the coordinates of a given walk. Let's do this first, and then define two Walks as equivalent if they give the same coordinates. -/

def Walk.x (p : Walk) : Nat := match p with
  | zero => 0
  | up q => x q
  | right q => 1 + x q

def Walk.y (p : Walk) : Nat := match p with
  | zero => 0
  | up q => 1 + y q
  | right q => y q

def a := zero.right.up.up.up.right
def b := zero.up.right.up.right.up

#eval (a.x,a.y)
#eval (b.x,b.y)

/- Now we define what it means for two points to be equivalent. -/

def eq (p q: Walk) := p.x = q.x ∧ p.y = q.y

example : eq a b := by
  exact ⟨ rfl, rfl ⟩

/- This seems great, but now imagine we defined addition on Walk and had a theorem like `a+b=b+a` where `a` and `b` are Walks. We would have to state the theorem as `eq (a+b) (b+a)`. This is actually weaker than what we could say. In fact, we could say that for every `x` equivalent to  `a` and every `y` equivalent to `b`, that `eq (a+b) (y+x)`. Even better, we could define the **equivalence class** ⟦a⟧ of all Walks `x` such that `eq a x`. And then prove `⟦a+b⟧ = ⟦b+a⟧` where the `=` in this statement is set equality.

The idea behind quotients is to `lift` our `eq` relation to actual equality, make proving these kinds of statements straightfoward.

## Equivalence Relations and Setoids

An **equivalence relation** is a relation that is reflexive, symmetric, and transitive. To define a decent quotient space, we need to first show our relation has these properties. This is pretty easy. -/

theorem eq_refl (p: Walk) : eq p p := by
  exact ⟨ rfl, rfl ⟩

theorem eq_symm {p q: Walk} : eq p q → eq q p := by
  intro ⟨ h1, h2 ⟩
  exact ⟨ h1.symm, h2.symm ⟩

theorem eq_trans {p q r: Walk} : eq p q → eq q r → eq p r := by
  intro ⟨ h1, h2 ⟩ ⟨ h3, h4 ⟩
  exact ⟨ Eq.trans h1 h3, Eq.trans h2 h4 ⟩

/- With these theorems in place, we can claim `eq` is a proper equivalence relation. -/

instance eq_equiv : Equivalence eq :=
  ⟨ eq_refl, eq_symm, eq_trans ⟩

instance walk_has_equiv : HasEquiv Walk :=
  ⟨ eq ⟩

/- This allows us to use the Lean standard library notation `≈` defined for equivalence relations. -/

#check a ≈ b     -- notation for eq a b

/- A **setoid** is a set `X` along with an equivalence relation `∼` and in the literature is written `(X,∼)`. For Lean, a setoid is a step along the path to a quotient space. For Point we can simply write the following. -/

instance walk_setoid : Setoid Walk :=
  ⟨ eq, eq_equiv ⟩

/- ## Quotients

Given a setoid `(X,∼)`, we can form the *quotient* of `X`, which is the set of all equivalence classes of elements in `X` with respect to `~`. We denote this class `X/~` in the literature. In Lean we use the `Quotient` type.  -/

#check Quotient          -- Construct a quotient space from a Setoid
#check Quotient.mk       -- Make an equivalence class

/- For our extended example, we can form the quotient and a constructor `p` as follows: -/

def Point := Quotient walk_setoid
def p (w : Walk) : Point := Quotient.mk walk_setoid w

#check Point
#check p a      -- all walks equivalent to a
#check p b      -- all walks equivalent to b

example : (p a) = (p b) := by
  apply Quot.sound
  simp[walk_setoid,eq]
  exact ⟨ rfl, rfl ⟩

/- # Lifting

We can define functions on the underlying space Walk and **lift** them to the quotient space as long as the function respects equality. That is, we require that if a ≈ b then f a ≈ f b. The work is then done by `Quotient.lift`.-/

#check Quotient.lift     -- Extend a function on `X` to a function on `X/~`

/- Obvious first candidates for lifting are the coordinate functions Walk.x and Walk.y. Let's show those respect equivalence. -/

theorem walk_x_respects : ∀ a b, a ≈ b → x a = x b := by
  intro a b hab
  exact hab.left

theorem walk_y_respects : ∀ a b, a ≈ b → y a = y b := by
  intro a b hab
  exact hab.right

/- Now we can lift the coordinate functions to Point. -/

def X (a: Point) : ℕ := Quotient.lift x walk_x_respects a
def Y (a: Point) : ℕ := Quotient.lift x walk_x_respects a

#eval X (p a)
#eval Y (p a)


/- TODO: SHOW A THEOREM USING X AND Y-/

/- Here is another example in which we define a function `swap` that swaps all ups with rights and _vice verse_. We also show a simple theorem showing that walk_swap composed with itself is the identity. Our goal will be to lift both of these to the quotient space. -/

def walk_swap (a : Walk) : Walk := match a with
  | zero => a
  | up b => right (walk_swap b)
  | right b => up (walk_swap b)

theorem walk_swap_swap (a : Walk) : walk_swap (walk_swap a) = a := by
  induction a with
  | zero => rfl
  | up b hb =>
    conv =>
      right
      rw[←hb]
    rfl
  | right b hb =>
    conv =>
      right
      rw[←hb]
    rfl

/- To lift walk_swap to Points, we need to show it respects equilvalence and then use `Quotient,lift`. -/

theorem swap_respects : ∀ a b, a ≈ b → walk_swap a = walk_swap b := sorry

-- Question: Is this helping somehow with the axiom of choice? Because I could
-- define swap x = p (walk_swap a) for some a, but I don't know how to choose the a?
def swap (x: Point) : Point := p (Quotient.lift walk_swap swap_respects x)

theorem swap_swap (x : Point) : swap (swap x) = x := by
  unfold swap p swap_respects

  sorry

/- We can also lift binary functions. For example, we define a notion of adding two walks together that simply concatenates the moves from each walk.  -/

def walk_add (a b : Walk) : Walk := match a with
  | zero => b
  | up c => up (walk_add c b)
  | right c => right (walk_add c b)

/- Next we prove a theorem showing add respects equivalence. -/

theorem add_resepcts {c: Walk} : ∀ a b, a ≈ b → walk_add c a = walk_add c b := sorry

def add := Quotient.lift

#check Quotient.sound    -- Relate equivalence class equality to member equality
#check Quotient.ind      -- Induction for quotients
