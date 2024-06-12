import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.Group

open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] (B:Subgroup G) 
section DoubleCoset

def DoubleCoset (n : G) : Set G := {b.1 * n * b.2 | b : (B × B)}
notation "C"  => DoubleCoset

def set_mul (s t : Set G) : Set G := {(u.1*u.2 : G)| u : s × t }

lemma set_mul_le_set_mul_right {s t :Set G} (h : s⊆ t) (r:Set G): set_mul s r ⊆ set_mul t r := sorry
lemma set_mul_le_set_mul_left  {s t :Set G} (h : s⊆ t) (r:Set G): set_mul r s ⊆ set_mul r t := sorry
lemma set_mul_assoc {s t r : Set G} : set_mul s (set_mul t r) = set_mul (set_mul s t) r  := sorry
lemma set_mul_le_mem_one {s t : Set G} (h1 : 1 ∈ t) : s ⊆ set_mul s t  := sorry
lemma set_mul_le_one_mem {s t : Set G} (h1 : 1 ∈ t) : s ⊆ set_mul t s  := sorry
theorem doubleCoset_one : DoubleCoset B 1 = B.carrier := by
  simp [DoubleCoset]
  ext x
  constructor
  · intro ⟨b,binB,b',b'inB, xeqbb'⟩
    simp [← xeqbb',B.mul_mem binB, b'inB] 
  intro xinB
  use x;apply And.intro xinB
  use 1; simp [B.one_mem]

theorem doubleCoset_quotient {w w' : G} (a a' : B) (h : w = a*w'*a') : 
  DoubleCoset B w = DoubleCoset B w':= by
  simp [DoubleCoset, h] 
  ext x
  constructor
  · intro ⟨b, binB, b', b'inB,h⟩
    use b*a ; apply And.intro (B.mul_mem binB a.2)
    use a'*b'; apply And.intro (B.mul_mem a'.2 b'inB)
    rw [← h]
    group
  intro ⟨b, binB, b', b'inB,h⟩ 
  use b*a⁻¹ ; apply And.intro (by simp [binB, a.2, B.mul_mem])
  use a'⁻¹ *b'; apply And.intro (by simp [b'inB, B.mul_mem, a'.2])
  simp [← h]
  group

theorem DoubleCoset.mul_apply (w w' :G) : set_mul (DoubleCoset B w) (DoubleCoset B w') = {(b.1  * w * b.2.1 * w' * b.2.2 :G)| b : (B × B × B)} := by
  simp [DoubleCoset, set_mul]
  ext
  constructor
  · intro ⟨a, ainB, a',a'inB,b,binB,b',b'inB, h⟩
    use a; apply And.intro ainB
    use a'*b ; apply And.intro (B.mul_mem a'inB binB)
    use b' ; apply And.intro b'inB
    rw [← h]
    group
  intro ⟨b, binB, b',b'inB, b'',b''inB, h⟩
  use b ; apply And.intro binB
  use b' ; apply And.intro b'inB
  use 1 ; apply And.intro B.one_mem
  use b'' ; apply And.intro b''inB
  rw [← h] ; group

theorem DoubleCoset.mul_one (w : G) : set_mul (DoubleCoset B w) (DoubleCoset B 1) = DoubleCoset B w  :=by
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

theorem DoubleCoset.one_mul (w : G) : set_mul (C B 1) (C B w) = C B w  :=by
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
    DoubleCoset B (w*w')⊆ set_mul (DoubleCoset B w) (DoubleCoset B w') := by
  rw [DoubleCoset.mul_apply]
  simp [DoubleCoset]
  intro x b binB b' b'inB h 
  --use ⟨b, binB, 1, B.one_mem, b', b'inB,1, B.one_mem, b', b'inB, by {rw [← h] ; group} ⟩
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



theorem prop4_doubleCoset_iff (s:G) (w:G): 
    {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) ↔ 
      set_mul (DoubleCoset B s) (DoubleCoset B w) ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) := by

  constructor
  · simp [DoubleCoset, set_mul] 
    intro h x ⟨a,ainB,a',a'inB,b,binB,b',b'inB, h'⟩

    have :s*a'*b*w ∈ {x | ∃ a ∈ B, s * a * w = x} := 
        ⟨a' * b, B.mul_mem a'inB binB,by simp [mul_assoc]⟩

    obtain ⟨c,cinB, c',c'inB, h⟩| ⟨c,cinB, c',c'inB, h⟩:= h this 
    
    on_goal 1 => left
    on_goal 2 => right
    all_goals
    · use a * c  ; apply And.intro  <| B.mul_mem ainB cinB
      use c' * b'; apply And.intro <| B.mul_mem c'inB b'inB
      rw [← h', ← mul_assoc, mul_assoc (a*c), mul_assoc a, ← mul_assoc c, h]
      group
  intro h x ⟨b,hb⟩
  suffices h₀ : x ∈ set_mul (DoubleCoset B s) (DoubleCoset B w) from h h₀ 
  simp [DoubleCoset, set_mul]
  use 1 ; apply And.intro B.one_mem
  use 1 ; apply And.intro B.one_mem
  use b.val ; apply And.intro b.2
  use 1 ; apply And.intro B.one_mem
  simp [← hb, mul_assoc]

theorem doubleCoset_mul1 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w))) 
    (h2 :DoubleCoset B w ⊆ set_mul (DoubleCoset B s) (DoubleCoset B w)):  
    set_mul (DoubleCoset B s) (DoubleCoset B w) = DoubleCoset B w ∪ (DoubleCoset B (s*w)) := 
  le_antisymm ((prop4_doubleCoset_iff B s w).1 h1) <| union_subset h2 (doubleCoset_mul B s w) 

   
theorem doubleCoset_mul2 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w))) 
    (h2 : ¬DoubleCoset B w ⊆ set_mul (DoubleCoset B s) (DoubleCoset B w)):
      set_mul (DoubleCoset B s) (DoubleCoset B w) = DoubleCoset B (s*w) := by
  apply le_antisymm
  · have : ∀ x ∈ (DoubleCoset B w), x ∉ (set_mul (DoubleCoset B s) (DoubleCoset B w)) := by
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
    B.carrier ≠ set_mul (DoubleCoset B s) (DoubleCoset B s) :=by
  intro h'
  apply h
  intro x ⟨b,h⟩
  simp [h', DoubleCoset.mul_apply]
  use 1 ; apply And.intro B.one_mem
  use b ; apply And.intro b.2
  use 1 ; apply And.intro B.one_mem
  simp [h]

theorem simples_doubleCoset_square {s : G} (hs : s*s = 1) (h: {s*b*s | b : B} ⊆ C B s ∪ (C B (s*s)))
    (h' :¬ {s*b*s | b:B} ⊆ B.carrier) : set_mul (C B s) (C B s) = B.carrier ∪ (C B s) := by
  have : C B s ⊆ set_mul (C B s) (C B s) :=by
    by_contra h''
    have := doubleCoset_mul2 B h h''
    simp [hs, doubleCoset_one]  at this 
    apply B_neq_doubleCoset_squarred B h' this.symm
  rw [doubleCoset_mul1 B h this, hs, doubleCoset_one, union_comm] 

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
    rw [← simples_doubleCoset_square B hs h h', set_mul]
    use (⟨x,hx⟩, ⟨y,hy⟩)
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

variable {n : Type*} [Fintype n] [LinearOrder n] 
def grouprod {q : Nat} (s : Fin q → G) : G := (List.map s (Fin.list q)).prod

lemma succ_last (n:Nat) : Fin.list (n + 1) = List.map Fin.castSucc (Fin.list n) ++ [Fin.last n] :=sorry

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

theorem prodthing {q : Nat} [Inhabited (Fin q)] {s : Fin q → G} (hs : s*s = 1) (w : G)
    (h: ∀(i : Fin q) (w' : G), {s i *b*w' | b : B} ⊆ C B w' ∪ (C B (s i*w')))
      (h' :∀i, ¬ {(s i)*b*(s i) | b:B} ⊆ B.carrier): 
        set_mul (C B (grouprod s)) (C B w) ⊆ 
          ⋃ l ∈ { l : List (Fin q) | l.Sublist (Fin.list q)}, (C B ((List.map s l).prod * w)) := by
  induction' q with q hq
  · simp [grouprod, DoubleCoset.one_mul]
    rfl
  repeat rw [grouprod]
  let s' : (Fin q) → G := s ∘ Fin.succ
  have : C B (grouprod s) ⊆ set_mul (C B (s 0)) (C B (grouprod s'))  := by
    simp [prodpushright, s']
    apply doubleCoset_mul
  apply le_trans <| set_mul_le_set_mul_right this (C B w)
  have : set_mul (C B (grouprod s')) (C B w) ⊆  
      ⋃ l ∈ { l : List (Fin q) | l.Sublist (Fin.list q)}, (C B ((List.map s' l).prod * w)) := by
    apply hq
    · ext i ;
      calc 
        (s' *s') i = (s*s) i.succ := by simp [s'] 
        _          = 1 := by rw [hs] ; simp
    · intro i
      simp [s'] at h ⊢
      apply h i.succ
    · intro i
      simp [s'] at h' ⊢ 
      apply h' i.succ
  clear hq
  rw [← set_mul_assoc]
  apply le_trans
  · apply set_mul_le_set_mul_left this (C B (s 0))
  simp [set_mul] 
  intro x ⟨y,hy, z, ⟨l,hl,hz⟩, hx⟩
  simp
  have :x ∈ set_mul (C B (s 0)) (C B ((List.map s' l).prod*w))  := by
    simp [set_mul]
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
