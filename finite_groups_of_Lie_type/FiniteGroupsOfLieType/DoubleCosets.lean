import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.Group

open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] (B:Subgroup G)
section DoubleCoset
attribute [local simp] Set.mem_mul
/-- A double coset of a subgroup B by an element n of G is the set BnB.-/
def DoubleCoset (n : G) : Set G := {b.1 * n * b.2 | b : (B × B)}
/-- Notation for DoubleCoset-/
notation "C"  => DoubleCoset

/-to mathlib?-/
lemma set_mul_assoc (r s t : Set G): r * s * t = r * (s*t) := by
  ext
  simp [mul_assoc]

lemma Set.mul_of_mul_image_of_MulHom (M N : Type u_11) [Mul M] [Mul N] {f : M→ₙ* N} {s t : Set M} : 
    f '' (s * t) = f '' s * (f '' t):=by
  ext
  simp [Set.mem_mul] 

lemma Set.mul_of_mul_image_of_MulEquiv {M N : Type u_11} [Mul M] [Mul N] (f : M≃* N) (s t : Set M) : 
    f '' (s * t) = f '' s * (f '' t):=by
  ext
  simp [Set.mem_mul] 
theorem doubleCoset_one : DoubleCoset B 1 = B.carrier := by
  simp [DoubleCoset]
  ext x
  apply Iff.intro
    (fun ⟨b , binB, b' , b'inB, xeqbb'⟩ => xeqbb' ▸ (B.mul_mem binB b'inB))
    fun xinB => ⟨ x, xinB, 1, B.one_mem, mul_one x⟩

theorem doubleCoset_quotient {w w' : G} (a a' : B) (h : w = a*w'*a') :
    DoubleCoset B w = DoubleCoset B w':= by
  simp [DoubleCoset, h]
  ext x
  apply Iff.intro
   (fun ⟨b, binB, b', b'inB,h⟩ =>
    ⟨b*a ,B.mul_mem binB a.2, a'*b', B.mul_mem a'.2 b'inB,by rw [← h] ; group ⟩)
    fun ⟨b, binB, b', b'inB,h⟩ =>
    ⟨ b*a⁻¹, B.mul_mem binB (B.inv_mem a.2), a'⁻¹ *b', B.mul_mem (B.inv_mem a'.2) b'inB,
      by simp [← h] ;group ⟩

--Double coset C B w = BwB
theorem DoubleCoset.self_mem {w : G} : w ∈ C B w:= by
  simp [DoubleCoset]
  exact ⟨1, B.one_mem, 1, B.one_mem, by simp⟩

lemma DoubleCoset.sub_of_gen_mem {w w' :G} (h : w ∈ C B w') : C B w ⊆ C B w':=by
  intro x h'
  simp [DoubleCoset] at *
  rcases h' with ⟨b,binB,b',b'inB, hx⟩
  rcases h with ⟨a,ainB,a',a'inB, hw⟩
  exact ⟨b*a, B.mul_mem binB ainB, a'*b', B.mul_mem a'inB b'inB, by simp [← hx, ← hw] ; group ⟩


theorem DoubleCoset.disjoint_of_neq (w w' :G) (h : C B w ≠ C B w') : Disjoint (C B w) (C B w') := by
  revert h
  contrapose!
  intro h
  simp [DoubleCoset, Set.not_disjoint_iff] at h
  rcases h with ⟨b1,b1inB,b1',b1'inB, b2, b2inB, b2', b2'inB, h⟩
  apply subset_antisymm
  · apply sub_of_gen_mem
    simp [DoubleCoset]
    have :w = b1⁻¹ * b2* w' * (b2' * b1'⁻¹) :=
    calc
      w = b1⁻¹ * (b1 *w * b1') * b1'⁻¹ := by group
      _ = b1⁻¹  * b2 * w' * (b2' * b1'⁻¹) := by simp [← h] ; group
    exact
    ⟨b1⁻¹ * b2, B.mul_mem (B.inv_mem b1inB) b2inB, b2'*b1'⁻¹, B.mul_mem b2'inB (B.inv_mem b1'inB),this.symm⟩
  · apply sub_of_gen_mem
    simp [DoubleCoset]
    have :w' = b2⁻¹ * b1 * w * (b1' * b2'⁻¹) :=
    calc
      w' = b2⁻¹ * (b2 *w' * b2') * b2'⁻¹ := by group
      _ = b2⁻¹  * b1 * w * (b1' * b2'⁻¹) := by simp [h] ; group
    exact
    ⟨b2⁻¹ * b1, B.mul_mem (B.inv_mem b2inB) b1inB, b1'*b2'⁻¹, B.mul_mem b1'inB (B.inv_mem b2'inB),this.symm⟩

theorem DoubleCoset.eq_of_gen_mem {w w' :G} (h : w ∈ C B w') : C B w = C B w':=by
  have h' := disjoint_of_neq B w w'
  by_contra h₀
  apply Set.disjoint_right.mp (h' h₀) h
  simp [DoubleCoset]
  exact ⟨1,B.one_mem, 1, B.one_mem, by simp⟩



theorem DoubleCoset.mul_apply (w w' :G) : (C B w) * (C B w') = {(b.1  * w * b.2.1 * w' * b.2.2 :G)| b : (B × B × B)} := by
  ext
  simp [DoubleCoset, Set.mem_mul]
  constructor
  · intro ⟨a, ainB, a',a'inB,b,binB,b',b'inB, h⟩
    use a; apply And.intro ainB
    use a'*b ; apply And.intro (B.mul_mem a'inB binB)
    use b' ; apply And.intro b'inB
    rw [← h]
    group
  intro ⟨b, binB, b',b'inB, b'',b''inB, h⟩
  exact ⟨b, binB, b', b'inB, 1, B.one_mem, b'', b''inB,by rw [← h] ; group ⟩

theorem DoubleCoset.mul_one (w : G) : (DoubleCoset B w) * (DoubleCoset B 1) = DoubleCoset B w  :=by
  rw [mul_apply]
  simp [DoubleCoset]
  ext x
  constructor
  · intro ⟨b,binB,b',b'inB,b'',b''inB,h⟩
    use b ; apply And.intro binB
    use b'*b'' ; apply And.intro (B.mul_mem b'inB b''inB)
    rw [← mul_assoc]
    assumption
  intro ⟨b,binB,b',b'inB,h⟩
  use b ; apply And.intro binB
  use 1 ; simp [B.one_mem]
  use b'

theorem DoubleCoset.one_mul (w : G) : (C B 1) * (C B w) = C B w  :=by
  rw [mul_apply]
  simp [DoubleCoset]
  ext x
  constructor
  · intro ⟨b,binB,b',b'inB,b'',b''inB,h⟩
    use b*b' ; apply And.intro (B.mul_mem binB b'inB)
    use b''
  intro ⟨b,binB,b',b'inB,h⟩
  use b ; apply And.intro binB
  use 1 ; simp [B.one_mem]
  use b'

theorem doubleCoset_mul (w w': G) :
    DoubleCoset B (w*w')⊆  (DoubleCoset B w) * (DoubleCoset B w') := by
  rw [DoubleCoset.mul_apply]
  simp [DoubleCoset]  --use ⟨b, binB, 1, B.one_mem, b', b'inB,1, B.one_mem, b', b'inB, by {rw [← h] ; group} ⟩

  intro x b binB b' b'inB h
  use b; apply And.intro binB
  use 1; apply And.intro B.one_mem
  use b'; apply And.intro b'inB
  rw [← h]
  group

theorem doubleCosetInv (w :G) : (DoubleCoset B w)⁻¹ = DoubleCoset B w⁻¹ := by
  simp [DoubleCoset]
  ext x
  constructor <;>
  · intro ⟨b,binB,b',b'inB,h⟩
    use b'⁻¹; apply And.intro <| B.inv_mem b'inB
    use b⁻¹ ; apply And.intro <| B.inv_mem binB
    apply_fun fun x ↦ x⁻¹ at h
    simp at h
    simp [← h]
    group

/-The first side of the equivalence is the same as the prop4 of a `BNMphiQuadruplet`-/
theorem prop4_doubleCoset_iff (s:G) (w:G):
    {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) ↔
      (DoubleCoset B s) * (DoubleCoset B w) ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) := by
  constructor
  · simp [DoubleCoset]
    intro h x
    simp [Set.mem_mul]
    intro a ainB a' a'inB b binB b' b'inB  h'
    have :s*a'*b*w ∈ {x | ∃ a ∈ B, s * a * w = x} := ⟨a'*b, B.mul_mem a'inB binB,by simp [mul_assoc]⟩
    obtain ⟨c,cinB, c',c'inB, h⟩| ⟨c,cinB, c',c'inB, h⟩:= h this
    on_goal 1 => left
    on_goal 2 => right
    all_goals
    · use a * c  ; apply And.intro  <| B.mul_mem ainB cinB
      use c' * b'; apply And.intro <| B.mul_mem c'inB b'inB
      rw [← h', ← mul_assoc, mul_assoc (a*c), mul_assoc a, ← mul_assoc c, h]
      group
  intro h x ⟨b,hb⟩
  suffices h₀ : x ∈  (DoubleCoset B s) * (DoubleCoset B w) from h h₀
  simp [DoubleCoset, Set.mem_mul]
  use 1 ; apply And.intro B.one_mem
  use 1 ; apply And.intro B.one_mem
  use b.val ; apply And.intro b.2
  use 1 ; apply And.intro B.one_mem
  simp [← hb, mul_assoc]

theorem doubleCoset_mul1 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)))
    (h2 :DoubleCoset B w ⊆  (DoubleCoset B s) * (DoubleCoset B w)):
    (DoubleCoset B s) * (DoubleCoset B w) = DoubleCoset B w ∪ (DoubleCoset B (s*w)) :=
  le_antisymm ((prop4_doubleCoset_iff B s w).1 h1) <| Set.union_subset h2 (doubleCoset_mul B s w)


theorem doubleCoset_mul2 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)))
    (h2 : ¬DoubleCoset B w ⊆  (DoubleCoset B s) *(DoubleCoset B w)):
       (DoubleCoset B s) * (DoubleCoset B w) = DoubleCoset B (s*w) := by
  apply le_antisymm
  · have : ∀ x ∈ (DoubleCoset B w), x ∉ ( (DoubleCoset B s) * (DoubleCoset B w)) := by
      rw [DoubleCoset.mul_apply]
      simp [DoubleCoset]
      intro x b binB b' b'inB h a ainB a' a'inB a'' a''inB h'
      apply h2
      rw [DoubleCoset.mul_apply]
      simp [DoubleCoset]
      intro y b2 b2inB b2' b2'inB h2
      have : w = b⁻¹ * x * b'⁻¹:= by rw [← h] ; group
      rw [this, ← h'] at h2
      use b2*b⁻¹*a
      simp [b2inB, binB, ainB, B.mul_mem, B.inv_mem]
      use a' ; apply And.intro a'inB
      use a''*b'⁻¹ *b2'
      simp [b2'inB, b'inB, a''inB, B.mul_mem, B.inv_mem, ← h2]
      group
    intro x hx
    obtain h|h := (prop4_doubleCoset_iff B s w).mp h1 hx
    · exfalso
      exact this x h hx
    exact h
  exact (doubleCoset_mul B s w)

 lemma B_neq_doubleCoset_squarred {s:G} (h:¬ {(s * b * s : G)| b : B} ⊆ B.carrier):
    B.carrier ≠ (DoubleCoset B s) * (DoubleCoset B s) :=by
  intro h'
  apply h
  intro x ⟨b,h⟩
  simp [h', DoubleCoset.mul_apply]
  use 1 ; apply And.intro B.one_mem
  use b ; apply And.intro b.2
  use 1 ; apply And.intro B.one_mem
  simp [h]

theorem simples_doubleCoset_square {s : G} (hs : s*s = 1) (h: {s*b*s | b : B} ⊆ C B s ∪ (C B (s*s)))
    (h' :¬ {s*b*s | b:B} ⊆ B.carrier) :  (C B s) * (C B s) = B.carrier ∪ (C B s) := by
  have : C B s ⊆ (C B s) * (C B s) :=by
    by_contra h''
    have := doubleCoset_mul2 B h h''
    simp [hs, doubleCoset_one] at this
    apply B_neq_doubleCoset_squarred B h' this.symm
  rw [doubleCoset_mul1 B h this, hs, doubleCoset_one, Set.union_comm]

/--B ∪ BsB-seen as subgroup of G, for s simple-/
def B_union_C_of_simple {s : G} (hs : s*s = 1) (h: {s*b*s | b : B} ⊆ C B s ∪ (C B (s*s)))
    (h' :¬ {s*b*s | b:B} ⊆ B.carrier) : Subgroup G where
  carrier := B.carrier ∪ (C B s)
  one_mem' := Or.intro_left (1 ∈ C B s) B.one_mem
  mul_mem' := by
    intro x y xinH yinH
    obtain hx|hx := xinH
    · obtain hy|hy := yinH
      · left ;exact B.mul_mem hx hy
      right
      simp [DoubleCoset]  at *
      rcases hy with ⟨b,binB,b',b'inB,hy⟩
      use x*b ; apply And.intro (B.mul_mem hx binB)
      use b' ; apply And.intro b'inB
      simp [← hy]
      group
    obtain hy|hy := yinH
    · right
      simp [DoubleCoset]  at *
      rcases hx with ⟨b,binB,b',b'inB,hx⟩
      use b ; apply And.intro binB
      use b'*y ; apply And.intro (B.mul_mem b'inB hy)
      simp [← hx]
      group
    rw [← simples_doubleCoset_square B hs h h']
    exact Set.mul_mem_mul hx hy
  inv_mem' := by
    simp
    intro x h
    cases h
    · left ; assumption
    right
    suffices C B s = C B (s⁻¹) by
     rw [this, ← doubleCosetInv B s]
     simpa
    have :s⁻¹ =s:=
      calc
        s⁻¹ = s⁻¹ * (s*s) := by simp [hs]
        _   = s := by group
    rw [this]

/--The product over the elements of a function will disapear.-/
def grouprod {q : Nat} (s : Fin q → G) : G := (List.map s (Fin.list q)).prod


lemma prodpushright (s : Fin (q + 1)→ G) :grouprod s = s 0 * (grouprod  (s ∘ Fin.succ)):=by
  induction' q with q hq
  · simp [grouprod, Fin.list_succ, Fin.list_zero]
  simp [grouprod] at hq ⊢
  rw [Fin.list_succ_last q, Fin.list_succ_last, Fin.last, Fin.last]
  simp [← mul_assoc]
  simp [hq (s ∘ Fin.castSucc)]
  suffices ((s ∘ Fin.castSucc) ∘ Fin.succ) = ((s ∘ Fin.succ) ∘ Fin.castSucc) by simp [*]
  ext i
  have :i.succ.castSucc = i.castSucc.succ :=by
    apply Fin.eq_of_val_eq
    simp
  simp [this]

theorem prodthing {q : Nat} {s : Fin q → G} (hs : s*s = 1) (w : G)
    (h: ∀(i : Fin q) (w' : G), {s i *b*w' | b : B} ⊆ C B w' ∪ (C B (s i*w')))
      (h' :∀i, ¬ {(s i)*b*(s i) | b:B} ⊆ B.carrier):
        C B (grouprod s) * (C B w) ⊆
          ⋃ l ∈ { l : List (Fin q) | l.Sublist (Fin.list q)}, (C B ((List.map s l).prod * w)) := by
  induction' q with q hq
  · simp [grouprod, DoubleCoset.one_mul]
    rfl
  repeat rw [grouprod]
  let s' : (Fin q) → G := s ∘ Fin.succ
  have : C B (grouprod s) ⊆ C B (s 0) * (C B (grouprod s'))  := by
    simp [prodpushright, s']
    apply doubleCoset_mul
  apply le_trans <| Set.mul_subset_mul_right this --(C B w)
  have : (C B (grouprod s')) * (C B w) ⊆
      ⋃ l ∈ { l : List (Fin q) | l.Sublist (Fin.list q)}, (C B ((List.map s' l).prod * w)) := by
    apply hq
    · ext i ;
      calc
        (s' *s') i = (s*s) i.succ := by simp [s']
        _          = 1 := by rw [hs] ; simp
    · intro i
      simp [s'] at h ⊢
      exact h i.succ
    · intro i
      simp [s'] at h' ⊢
      apply h' i.succ
  clear hq
  rw [set_mul_assoc]
  apply le_trans
  · apply Set.mul_subset_mul_left this --(C B (s 0))
  intro x
  simp
  intro y hy z l hl hz hx
  have :x ∈  (C B (s 0))* (C B ((List.map s' l).prod*w))  := by
    simp
    use y ; simp [hy]
    use z
  have :=(prop4_doubleCoset_iff B (s 0) ((List.map s' l).prod*w)).mp (h 0 ((List.map s' l).prod*w)) this
  obtain h|h := this
  · use l.map Fin.succ
    simp
    constructor
    · apply List.Sublist.trans
      apply List.Sublist.map Fin.succ hl
      simp [Fin.list_succ]
    · simp [s'] at h
      assumption
  · use 0::(l.map Fin.succ)
    simp
    constructor
    · simp [Fin.list_succ]
      exact List.Sublist.map Fin.succ hl
    · simp [s',← mul_assoc] at h
      assumption



end DoubleCoset
#lint
