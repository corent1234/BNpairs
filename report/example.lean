import Mathlib.Algebra.Group.Subgroup.Basic

/-Check typing-/
#check 4 --4 : ℕ
#check true -- true : Bool
#check ∃ (n : ℕ), 3 ≤ n --∃ n, 3 ≤ n : Prop

/-Define objects-/
def one : ℕ := 1
def vrai : Bool := true

def α : Type := ℕ
def one' : α := one 

def two := 2
#check two --ℕ

/-Evaluate expressions-/
#eval 4 + 3 --7
#eval one --1
#eval one' --1
#eval vrai && false --false

/-Types of function-/
#check Bool.not -- Bool → Bool 
#check Nat.add -- ℕ → ℕ → ℕ

/-Create functions-/
#check fun n : ℕ => n + 2 -- ℕ → ℕ
#check fun (b : Bool) => ¬ b -- Bool → Bool

#check fun (x : ℕ) (b : Bool) => if not b then x else x + 1   -- ℕ → Bool → ℕ
#check fun x b => if not b then x else x + 1   -- ℕ → Bool → ℕ

/-Evaluate functions-/
#eval Nat.add 2 3 --5
#eval (fun n => n + 2) 3 -- 5


/-Defs of function-/
def add_two (n : ℕ) : ℕ := n + 2
def add (n m : ℕ) : ℕ := n + m

#eval add_two 3 -- 5
#eval add 4 3-- 7

/-Def of function with types-/
def identity (α : Type*) (a : α) := a
#check identity ℕ -- ℕ → ℕ

#eval identity ℕ 2 --2
#eval identity Bool true --true

/-Implicit arguments-/
def identity' {α : Type*}  (a : α) := a
#check identity' 2 -- ℕ 
#eval identity' 2 --2

#eval identity' true-- true
#check identity' true-- Bool

/-Variables-/
variable (n : ℕ)
def add_two' := n + 2
def add' (m : ℕ) := n + m

#eval add_two 3 -- 5
#eval add 4 3-- 7

/-Implicits-/
variable {α : Type*} (a : α)

def identity'' := a
#eval identity'' 2 --2
#eval identity'' true-- true


/-Structure-/
structure Point where
  x : ℕ 
  y : ℕ

def point1 : Point where
  x := 5
  y := 3

structure Prod' (α β : Type*) where
  fst : α
  snd : β

def point1' : Prod' ℕ ℕ where
  fst := 5
  snd := 3

#eval point1.x --5
#eval point1'.fst --5 



/-Class instances-/
variable {G : Type*} [Group G]
variable (g g' g'': G) 

#check g*g' -- G
#check g⁻¹ -- G
#check (1 : G) --G

example : g * g⁻¹ = 1 := mul_inv_cancel g
example : (g * g') * g'' = g * (g' * g'' ):= mul_assoc g g' g''



/-Prop-/
#check ∀ n : ℕ, n = 0 ∨ ∃ k : ℕ, n = k + 1 --Prop
#check ∀ n : ℕ, n > 1 → n ≠ 1 -- Prop

theorem eq_zero_or_succ: ∀ n : ℕ, n = 0 ∨ ∃ k : ℕ, n = k + 1 := 
  fun n => Or.elim Nat.eq_zero_or_eq_sub_one_add_one (fun h => Or.inl h) fun h => Or.inr ⟨n-1, h⟩

lemma ne_one_of_le_one : ∀ n : ℕ, n > 1 → n ≠ 1:= fun _ h => ne_of_gt h


/-This is how the results are written in the report (raise errors)-/
--theorem eq_zero_or_succ: ∀ n : ℕ, n = 0 ∨ ∃ k : ℕ, n = k + 1
--lemma ne_one_of_le_one : ∀ n : ℕ, n > 1 → n ≠ 1
structure EvenNumber where 
  n : ℕ
  even_n : ∃ k, n = 2 * k

/-How it appears in the code-/
def two_even : EvenNumber where
 n := 2
 even_n := ⟨1,mul_one 2⟩

/-How it is written in the report (raises errors)-/
--def two_even : EvenNumber where
--  n := 2
--  ...
/-Syntax-/
lemma ne_one_of_le_one' (n : ℕ) : n > 1 → n ≠ 1 := fun h => ne_of_gt h
lemma ne_one_of_le_one'' (n : ℕ) (h : n > 1) : n ≠ 1 := ne_of_gt h
variable (n : ℕ)
lemma ne_one_of_le_one''' :  n > 1 → n ≠ 1 := fun h => ne_of_gt h
lemma ne_one_of_le_one''''  (h : n > 1) : n ≠ 1 := ne_of_gt h

/-Some more implicit arguments-/
lemma ne_one_of_le_one''''' {n : ℕ} (h : n > 1) : n ≠ 1 := ne_of_gt h
variable (h : n > 1)
#check ne_one_of_le_one n h --n ≠ 1
#check ne_one_of_le_one''''' h --n ≠ 1



/-Subgroups-/
structure Subgroup' (G : Type*) [Group G] where
  carrier : Set G
  mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem' : 1 ∈ carrier
  inv_mem' : ∀ {x : G}, x ∈ carrier → x⁻¹ ∈ carrier

def trivial' (G : Type*) [Group G] : Subgroup G where 
  carrier := {1}
  mul_mem' := by simp
  one_mem' := by simp
  inv_mem' := by simp

variable (G : Type*) [Group G] 

example : ∀ H K : Subgroup G, (H ⊓ K).carrier = H.carrier ∩ K.carrier := Subgroup.coe_inf

example : ∀ g : G, g ∈ (⊤ : Subgroup G) := Subgroup.mem_top

example : (⊥ : Subgroup G).carrier = {1} := Subgroup.coe_bot
