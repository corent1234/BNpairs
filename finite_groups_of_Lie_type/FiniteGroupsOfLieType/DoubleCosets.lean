import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.Group
import FiniteGroupsOfLieType.aux
/-!
Throughout this file `G` is group, `B : Subgroup G` a subgroup of G.

Given an element $w ∈ G$ the double coset of $w$ following $w$ (`DoubleCoset.DoubleCoset w B`) is the
subset $BwB$ of $G$.
-/
open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] (B:Subgroup G)

section DoubleCoset
attribute [local simp] Set.mem_mul
/-- A double coset of a subgroup B by an element n of G is the set BnB.-/
abbrev DoubleCoset (w : G) : Set G := {x | ∃ b  b' : B, b * w * b' = x}
/-- Notation for DoubleCoset-/
notation "C"  => DoubleCoset

lemma DoubleCoset.mem_iff {B : Subgroup G} {w x: G} :x ∈ C B w ↔ ∃ b ∈ B, ∃ b' ∈ B, b*w*b'=x := by
  simp

lemma doubleCoset_eq_doubleProd_singleton (w :G) : DoubleCoset B w = B.carrier * {w} * B.carrier:=by
  ext x
  constructor
  · intro ⟨b,b',hx⟩
    use b*w
    simp
    use b', b'.2
  · intro ⟨a,ainBw,b, binB,hx⟩
    simp at ainBw
    use ⟨a*w⁻¹ ,ainBw⟩, ⟨b,binB⟩
    simp [← hx]

theorem doubleCoset_one : DoubleCoset B 1 = B.carrier := Set.ext fun x => Iff.intro
    (fun ⟨b, b',x_eq_bb'⟩ => x_eq_bb' ▸ B.mul_mem (B.mul_mem b.2 B.one_mem) b'.2)
    fun xinB => ⟨⟨ x, xinB⟩, 1, by simp⟩

theorem doubleCoset_quotient {w w' : G} (a a' : B) (h : w = a*w'*a') :
    DoubleCoset B w = DoubleCoset B w':= h ▸ Set.ext fun x => Iff.intro
   (fun ⟨b, b',h⟩ => ⟨b*a , a'*b', by simp [← h] ; group ⟩)
    fun ⟨b, b',h⟩ => ⟨ b*a⁻¹, a'⁻¹ *b', by simp [← h] ;group ⟩


theorem DoubleCoset.self_mem {w : G} : w ∈ C B w:= ⟨1,1, by simp⟩

theorem DoubleCoset.self_mem' (w : G) : w ∈ C B w:= ⟨1,1, by simp⟩

lemma DoubleCoset.sub_of_gen_mem {w w' :G} (h : w ∈ C B w') : C B w ⊆ C B w':=
  fun x h' => match h', h with
  | ⟨b,b', hx⟩, ⟨a,a', hw⟩ =>
    ⟨b * a, a' * b', by simp [← hx, ← hw] ; group ⟩


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
    have :w' = b2⁻¹ * b1 * w * (b1' * b2'⁻¹) :=
    calc
      w' = b2⁻¹ * (b2 *w' * b2') * b2'⁻¹ := by group
      _ = b2⁻¹  * b1 * w * (b1' * b2'⁻¹) := by simp [h] ; group
    apply mem_iff.mpr ⟨b2⁻¹ * b1, B.mul_mem (B.inv_mem b2inB) b1inB, b1'*b2'⁻¹,
      B.mul_mem b1'inB (B.inv_mem b2'inB),this.symm⟩

theorem DoubleCoset.eq_of_gen_mem {w w' :G} (h : w ∈ C B w') : C B w = C B w':=by
  by_contra h₀
  exact Set.disjoint_right.mp (disjoint_of_neq B w w' h₀) h ⟨1, 1, by simp⟩

theorem DoubleCoset.mul_apply (w w' :G) :
    (C B w) * (C B w') = {x :G| ∃ b1 : B,∃ b2 : B, ∃ b3 : B, b1 * w * b2 * w' * b3 =x} := by
  apply Set.ext fun x => by
    apply Iff.trans
    · apply Set.mem_mul
    apply Iff.intro
      (fun ⟨x1, ⟨a,a',hx1⟩, x2, ⟨b,b',hx2⟩,h⟩  => ⟨a, a'*b, b', by simp [← h, ← hx1, ← hx2] ; group⟩ )
      (fun ⟨b,b', b'', h⟩ => ⟨b*w*b',⟨ b, b', by simp⟩, 1*w'*b'', ⟨ 1, b'', by simp ⟩, by rw [← h] ; group ⟩)

@[simp]
theorem DoubleCoset.mul_one (w : G) : (DoubleCoset B w) * (DoubleCoset B 1) = DoubleCoset B w  :=by
  rw [mul_apply]
  ext x
  constructor
  · intro ⟨b,b',b'',h⟩
    use b, b'*b''
    simp [← mul_assoc, ← h]
  intro ⟨b,b',h⟩
  use b,1, b'
  simp [← h]

@[simp]
theorem DoubleCoset.one_mul (w : G) : (C B 1) * (C B w) = C B w  :=by
  rw [mul_apply]
  ext x
  constructor
  · intro ⟨b,b',b'',h⟩
    use b*b', b''
    simp [← h]
  intro ⟨b,b',h⟩
  use b, 1,b'
  simp [← h]

@[simp]
theorem doubleCoset_mul_le_mul (w w': G) :
    DoubleCoset B (w*w') ⊆ (DoubleCoset B w) * (DoubleCoset B w') := by
  rw [DoubleCoset.mul_apply]
  intro x ⟨b, b', h⟩
  use b, 1, b'
  simp [← h]
  group


theorem doubleCosetInv (w :G) : (DoubleCoset B w)⁻¹ = DoubleCoset B w⁻¹ := by
  ext x
  constructor <;>
  · intro ⟨b,b',h⟩
    use b'⁻¹, b⁻¹
    apply_fun fun x ↦ x⁻¹ at h
    simp at h
    simp [← h]
    group

/-The first side of the equivalence is the same as the prop4 of a `BNMphiQuadruplet`-/
theorem prop4_doubleCoset_iff (s:G) (w:G):
    {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) ↔
      (DoubleCoset B s) * (DoubleCoset B w) ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)) := by
  constructor
  · intro h x
    rw [DoubleCoset.mul_apply]
    intro ⟨a, a', b, h'⟩
    have : s*a'*w ∈ {x | ∃ a : B, s * a * w = x} := ⟨a', by simp [mul_assoc]⟩
    obtain ⟨c, c', h⟩| ⟨c, c', h⟩:= h this
    on_goal 1 => left
    on_goal 2 => right
    all_goals
    · use a * c, c' * b
      simp [← h', mul_assoc a.val,  ← h ]
      group
  intro h x ⟨b,hb⟩
  suffices h₀ : x ∈ (DoubleCoset B s) * (DoubleCoset B w) from h h₀
  rw [DoubleCoset.mul_apply]
  use 1, b, 1
  simp [← hb, mul_assoc]

theorem doubleCoset_mul1 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)))
    (h2 :DoubleCoset B w ⊆  (DoubleCoset B s) * (DoubleCoset B w)):
    (DoubleCoset B s) * (DoubleCoset B w) = DoubleCoset B w ∪ (DoubleCoset B (s*w)) :=
  le_antisymm ((prop4_doubleCoset_iff B s w).1 h1) <| Set.union_subset h2 (doubleCoset_mul_le_mul B s w)


theorem doubleCoset_mul2 {s:G} {w:G} (h1 : {s*b*w | b : B} ⊆ DoubleCoset B w ∪ (DoubleCoset B (s*w)))
    (h2 : ¬DoubleCoset B w ⊆  (DoubleCoset B s) *(DoubleCoset B w)):
       (DoubleCoset B s) * (DoubleCoset B w) = DoubleCoset B (s*w) := by
  apply le_antisymm
  · have : ∀ x ∈ (DoubleCoset B w), x ∉ ( (DoubleCoset B s) * (DoubleCoset B w)) := by
      rw [DoubleCoset.mul_apply]
      simp
      intro x b binB b' b'inB h a ainB a' a'inB a'' a''inB h'
      apply h2
      simp [DoubleCoset.mul_apply]
      intro y b2 b2inB b2' b2'inB h2
      have : w = b⁻¹ * x * b'⁻¹:= by rw [← h] ; group
      rw [this, ← h'] at h2
      use b2*b⁻¹*a
      simp [b2inB, binB, ainB, B.mul_mem, B.inv_mem]
      use a', a'inB, a''*b'⁻¹ *b2'
      simp [b2'inB, b'inB, a''inB, B.mul_mem, B.inv_mem, ← h2]
      group
    intro x hx
    obtain h|h := (prop4_doubleCoset_iff B s w).mp h1 hx
    · exfalso
      exact this x h hx
    exact h
  exact doubleCoset_mul_le_mul B s w

 lemma B_neq_doubleCoset_squarred {s:G} (h:¬ {(s * b * s : G)| b : B} ⊆ B.carrier):
    B.carrier ≠ (DoubleCoset B s) * (DoubleCoset B s) :=by
  intro h'
  apply h
  intro _ ⟨b,h⟩
  rw [h', DoubleCoset.mul_apply]
  use 1, b, 1
  simp [h]

theorem simples_doubleCoset_square {s : G} (hs : s*s = 1) (h: {s*b*s | b : B} ⊆ C B s ∪ (C B (s*s)))
    (h' :¬ {s*b*s | b:B} ⊆ B.carrier) :  (C B s) * (C B s) = B.carrier ∪ (C B s) := by
  have : C B s ⊆ (C B s) * (C B s) :=by
    by_contra h''
    have := doubleCoset_mul2 B h h''
    simp [hs, doubleCoset_one] at this
    apply B_neq_doubleCoset_squarred B h' this.symm
  rw [doubleCoset_mul1 B h this, hs, doubleCoset_one, Set.union_comm]

/--%B ∪ BsB%-seen as subgroup of `G`, for %s% of order 2.-/
def B_union_C_of_simple {s : G} (hs : s*s = 1) (h: {s*b*s | b : B} ⊆ C B s ∪ (C B (s*s)))
    (h' :¬ {s*b*s | b:B} ⊆ B.carrier) : Subgroup G where
  carrier := B.carrier ∪ (C B s)
  one_mem' := Or.intro_left (1 ∈ C B s) B.one_mem
  mul_mem' := by
    intro x y xinH yinH
    obtain hx|hx := xinH
    · obtain hy|⟨b,b',hy⟩ := yinH
      · left ;exact B.mul_mem hx hy
      right
      use ⟨x,hx⟩ * b, b'
      simp [← hy]
      group
    obtain hy|hy := yinH
    · right
      rcases hx with ⟨b,b',hx⟩
      use b, b' * ⟨y, hy⟩
      simp [← hx]
      group
    rw [← simples_doubleCoset_square B hs h h']
    exact Set.mul_mem_mul hx hy
  inv_mem' := by
    intro x h
    obtain h|⟨b,b',h⟩  := h
    · left ; simp [Subgroup.mem_carrier.mp h]
    · right
      have :s⁻¹ =s:=
        calc
          s⁻¹ = s⁻¹ * (s*s) := by simp [hs]
          _   = s := by group
      use b'⁻¹, b⁻¹
      simp [← h, this]
      group

theorem simple_prodsubset_union_of_simples (w : G) {ls : List G} (hs :∀ s ∈ ls, s*s = 1)
    (h: ∀ s ∈ ls, ∀ w' : G, {s * b * w' | b : B} ⊆ C B w' ∪ C B (s*w'))
      (h' :∀ s ∈ ls, ¬ {s * b * s | b:B} ⊆ B.carrier):
        C B ls.prod * C B w ⊆ ⋃ l ∈ { l : List G | l.Sublist ls}, C B (l.prod * w) := by
  induction' ls with hd t hls
  · simp [DoubleCoset.one_mul]
  simp
  have : C B (hd*t.prod) ⊆ C B hd * C B t.prod  := by simp
  apply subset_trans <| Set.mul_subset_mul_right this --(C B w)
  have : C B t.prod * (C B w) ⊆ ⋃ l ∈ { l : List G | l.Sublist t}, C B (l.prod * w) := by
    apply hls <;>
    · intro s s_in_t
      first | apply hs | apply h s|apply h' s
      simp [s_in_t]
  clear hls
  rw [set_mul_assoc]
  apply le_trans
  · apply Set.mul_subset_mul_left this
  intro x ⟨y, ⟨a,a',hy⟩, z,hz ,hx⟩
  simp at hx hz
  rcases hz with ⟨l,lsubt,b, binB, b',b'inB,hz⟩
  have :x ∈  C B hd * C B (l.prod * w)  := by
    rw [DoubleCoset.mul_apply]
    use a,a' * ⟨b,binB⟩, ⟨b',b'inB⟩
    simp [← hx, ← hy, ← hz]; group

  have :=(prop4_doubleCoset_iff B hd (l.prod*w)).mp (h hd (by simp ) (l.prod*w)) this
  simp
  obtain h|h := this
  · use l
    constructor
    · exact List.Sublist.trans lsubt (List.sublist_cons hd t)
    · simp [DoubleCoset] at h
      assumption
  · use hd::l
    constructor
    · simp [lsubt]
    · simp [← mul_assoc] at h ⊢
      assumption


end DoubleCoset
#lint
