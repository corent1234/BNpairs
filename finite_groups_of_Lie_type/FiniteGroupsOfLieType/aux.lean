import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.Perm.Sign
open scoped Pointwise

variable {G : Type*} [Group G] (B : Subgroup G)

lemma set_mul_assoc (r s t : Set G): r * s * t = r * (s*t) := by
  ext
  simp [mul_assoc]

lemma Set.mul_of_mul_image_of_MulHom (M N : Type*) [Mul M] [Mul N] {f : M→ₙ* N} {s t : Set M} :
    f '' (s * t) = f '' s * (f '' t):=by
  ext
  simp [Set.mem_mul]

lemma Set.mul_of_mul_image_of_MulEquiv {M N : Type*} [Mul M] [Mul N] (f : M≃* N) (s t : Set M) :
    f '' (s * t) = f '' s * (f '' t):=by
  ext
  simp [Set.mem_mul]

lemma Set.mul_mul_singleton (w w' : G) (s : Set G) : s * {w} * {w'} = s * {w*w'}:=by
  ext
  simp [mul_assoc]

lemma Set.mul_singleton_injective (w : G) {r s : Set G} (h : s * {w} = r * {w}) : s = r  :=by
  ext x
  calc
    x ∈ s ↔ x * w ∈ s * {w} := by simp
    _     ↔ x  ∈ r := by simp [h]

lemma Set.subset_mul_one_mem {s t :Set G} (one_mem : 1 ∈ t) : s ⊆ s*t :=
  fun x xins ↦ Set.mem_mul.mpr ⟨x,xins,1,one_mem, mul_one x⟩

lemma Set.subset_one_mem_mul {s t :Set G} (one_mem : 1 ∈ t) : s ⊆ t*s :=
  fun x xins ↦ Set.mem_mul.mpr ⟨1,one_mem, x, xins, one_mul x⟩

lemma subgroup_mul : B.carrier * B.carrier = B.carrier :=by
  ext x
  constructor
  · intro ⟨_,binB,_,b'inB,h⟩
    rw [← h]
    simp
    exact B.mul_mem binB b'inB
  · intro xinB
    use  x, xinB, 1, B.one_mem
    simp
lemma Fintwo_ne_iff {i j : Fin 2} (h : i ≠ j) : i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0   :=by
  match i, j with
  |0,0 => simp at h
  |1,1 => simp at h
  |0,1 => simp
  |1,0 => simp

lemma Perm.perm_fin_two (f : Equiv.Perm (Fin 2)) {P : Equiv.Perm (Fin 2) → Prop}
  (hP : P =  fun f ↦  f = 1 ∨ f = Equiv.swap 0 1) : P f :=by
  apply Equiv.Perm.swap_induction_on'
  · simp [hP]
  · intro f i j hij Pf
    simp [hP] at Pf ⊢
    obtain h|h := Fintwo_ne_iff hij
    · simp [h]
      obtain h|h := Pf <;> simp [h]
    · simp [h]
      obtain h|h := Pf
      · simp [h]
        rw [Equiv.swap_comm]
      · simp [h]
        rw [Equiv.swap_comm, Equiv.swap_mul_self]
