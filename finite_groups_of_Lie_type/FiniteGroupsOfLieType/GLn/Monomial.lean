import Mathlib.Algebra.Group.Units
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Logic.Equiv.Defs

open Equiv
open Matrix
open Subgroup
variable {n : Type*} [Fintype n]  [DecidableEq n] {R : Type*} [CommRing R] {F : Type*} [Field F] [DecidableEq F]
section Monomial

/-- A monomial matrix is a matrix with one and only one nonzero coefficient per line and column. -/
def Matrix.Monomial (M : Matrix n n F) : Prop := (∀ i, ∃! j, M i j ≠ 0) ∧ ∀ j, ∃! i, M i j ≠ 0

/-- An explicit definition of the inverse of a `Monomial` matrix. -/
def MonomialInverse (M : Matrix n n F) : Matrix n n F :=
    Matrix.of (fun i j ↦ if M j i ≠ 0 then 1/(M j i) else 0)

/--The `MonomialInverse` of a monomial matrix is `Monomial` -/
theorem monomial_of_monomialInverse {M : Matrix n n F} (h : Monomial M) : Monomial (MonomialInverse M) := by
  rw [Monomial] at h ⊢
  constructor
  on_goal 1 =>
    intro j
    rcases h.2 j with ⟨i,h₁, h₂⟩
  on_goal 2 =>
    intro j
    rcases h.1 j with ⟨i,h₁, h₂⟩
  all_goals
    use i
    constructor
    · simpa [MonomialInverse] using h₁
    · intro i'
      simpa [MonomialInverse] using h₂ i'

lemma no_other_column {M : Matrix n n F} {i j : n} (h : Monomial M) (h2 : M i j ≠ 0) :
    ∀ j' ≠ j, M i j' =0 := by
  intro j'
  rw [Monomial] at h
  contrapose
  intro Mij'neq0
  rcases (h.1 i) with ⟨_, _ , h'⟩
  simp [h' j h2]
  exact h' j' Mij'neq0

lemma no_other_line {M : Matrix n n F} {i j : n} (h : Monomial M) (h2 : M i j ≠ 0) :
    ∀ i' ≠ i, M i' j =0 := by
  intro i'
  contrapose
  intro Mij'neq0
  rw [Monomial] at h
  rcases (h.2 j) with ⟨ _, _ , h' ⟩
  simp [h' i h2]
  exact h' i' Mij'neq0

lemma monmomial_exists_apply {M : Matrix n n F} (i₀ j :n )  (h: Monomial M) :
    (∀ i ≠ i₀, M i j =0) → M i₀ j ≠ 0 := by
  contrapose
  simp
  intro h'
  rcases h.2 j with ⟨ i', h₁, _ ⟩
  use i'
  constructor
  · intro i'eqi₀
    rw [← i'eqi₀] at h'
    exact h₁ h'
  assumption

/--The `MonomialInverse` of a `Monomial` matrix is its right inverse.-/
theorem monomialInverse_is_left_inverse {M : Matrix n n F} (h : Monomial M) :
    MonomialInverse M * M =1 := by
  ext i j
  rw [mul_apply, one_apply]
  rw [Monomial] at h
  by_cases h' : (i = j)
  · rcases h.2 j with ⟨i₀, h₁, _⟩
    have : (fun k : n ↦  if k = i₀ then (1:F) else 0) = fun j_1 ↦ MonomialInverse M j j_1 * M j_1 j  := by
      ext k
      by_cases h'' : (k = i₀) <;> simp [h'', MonomialInverse, h₁]
      simp [no_other_line h h₁ k h'']
    simp [h',← this]
  · rcases h.2 j with ⟨i₀, h₁, _⟩
    have : (fun (_:n) ↦ (0:F)) = fun j_1 ↦ MonomialInverse M i j_1 * M j_1 j  := by
      ext k
      simp
      by_cases h'' : (k = i₀)
      · simp [h'', MonomialInverse, h₁, no_other_column h h₁ i h']
      · simp [no_other_line h h₁ k h'']
    simp [h', ← this]

/--A `Monomial` matrix is invertible-/
theorem monomial_invertible {M : Matrix n n F} (hM : M.Monomial): IsUnit M :=
  isUnit_of_left_inverse <| monomialInverse_is_left_inverse hM

/--The inverse of a `Monomial` matrix is `Monomial`-/
theorem monomial_inv_of_Monomial {M : Matrix n n F} (h : Monomial M) : Monomial M⁻¹ :=
  have : Invertible M := invertibleOfLeftInverse M (MonomialInverse M) <| monomialInverse_is_left_inverse h
  have :  MonomialInverse M = M⁻¹  :=
    left_inv_eq_right_inv (monomialInverse_is_left_inverse h) (mul_inv_of_invertible M)
  this ▸ (monomial_of_monomialInverse h)

/-- The product of two `Monomial` matrices is `Monomial`-/
theorem monomial_mul {M : Matrix n n F} {N : Matrix n n F} (hM :Monomial M) (hN : Monomial N) :
    Monomial (M*N) := by
  rw [Monomial] at hM hN ⊢
  constructor
  · intro i
    rcases hM.1 i with ⟨ki, h₁, _ ⟩
    rcases hN.1 ki with ⟨jki, h₁', _⟩
    use jki
    constructor
    · have: (fun (k:n) ↦ if k=ki then  M i ki * N ki jki  else  (0:F)) = fun k ↦ M i k * N k jki := by
        ext k
        by_cases h : (k=ki)
        · simp [h]
        · simp [h, no_other_column hM h₁ k h]
      simp [mul_apply,← this]
      exact ⟨h₁,h₁'⟩
    intro j
    contrapose
    intro jeqjki
    have : (fun _ => (0:F)) = fun k ↦ M i k * N k j := by
      ext k
      by_cases h : (k = ki)
      · simp [h, no_other_column hN h₁' j jeqjki]
      · simp [no_other_column hM h₁ k h]
    simp [← this,mul_apply]
  · intro j
    rcases hN.2 j with ⟨kj, h₁, _ ⟩
    rcases hM.2 kj with ⟨ikj, h₁', _⟩
    use ikj
    constructor
    ·
      have: (fun (k:n) ↦ if k=kj then  M ikj kj * N kj j  else  (0:F)) = fun k ↦ M ikj k * N k j := by
        ext k
        by_cases h : (k=kj)
        · simp [h]
        · simp [h,no_other_line hN h₁ k h]
      simp [mul_apply, ← this]
      exact ⟨h₁',h₁⟩
    intro i
    contrapose
    intro ieqikj
    have : (fun _ => (0:F)) = fun k ↦ M i k * N k j := by
      ext k
      by_cases h : (k = kj)
      · simp [h,no_other_line hM h₁' i ieqikj]
      · simp [no_other_line hN h₁ k h]
    simp [mul_apply,← this]



lemma isUnit_d_of_invertible_diagonal (d : n -> R)  [Invertible (diagonal d)]:
  ∀ k, IsUnit (d k) := by
  intro k
  have Invd : Invertible d := by apply invertibleOfDiagonalInvertible
  have : Invertible (d k) := by
    use (Invertible.invOf d) k
    calc
      ⅟d k * d k = (⅟d * d) k := by simp
      _               =  (1 : n -> R) k := by rw [Invertible.invOf_mul_self]
      _               = 1  := by simp
    calc
      d k * ⅟d k = (d * ⅟d) k := by simp
      _          =  (1 : n -> R) k := by rw [Invertible.mul_invOf_self]
      _          = 1 := by simp
  exact isUnit_of_invertible (d k)

lemma noncancel_d_of_invertible_diagonal (d : n -> F)  [Invertible (diagonal d)]:
  ∀ k, d k ≠ 0 := by
  intro k
  rcases isUnit_d_of_invertible_diagonal d k with ⟨u, h ⟩
  rw [← h]
  apply Units.ne_zero


/-- An `Invertible` diagonal matrix is `Monomial`-/
theorem monomial_of_inv_diagonal  {d : n -> F} (h : Invertible (diagonal d)):
    Monomial (diagonal d) := by
  constructor <;>
  · intro i
    use i
    constructor
    · simp [noncancel_d_of_invertible_diagonal]
    · intro j
      contrapose
      simp
      intro h
      apply diagonal_apply_ne
      first | symm ; assumption | assumption

/-- The `One` matrix is monomial.-/
theorem monomial_one : Monomial (1 : Matrix n n F) := by
  apply monomial_of_inv_diagonal
  apply invertibleOfRightInverse (1: Matrix n n F) (1: Matrix n n F)
  simp

/-- The subgroup of `GL n F` made of invertible `n` by `n` `F`-matrices that
coerce to `Monomial` matrices. -/
def MonomialGroup : Subgroup (GL n F) where
  carrier :=  {M : GL n F | Monomial (M : Matrix n n F) }
  mul_mem' := monomial_mul
  inv_mem' := by intro M ; simp; have := M.invertible; apply monomial_inv_of_Monomial
  one_mem' := monomial_one

/-- An element of the `MonomialGroup` coerce to a `Monomial` matrix.-/
theorem monomial_of_monomialGroup (M : (MonomialGroup : Subgroup (GL n F)) ):
  Monomial (M.val : Matrix n n F) := M.2

/--The `Subgroup` of diagonal matrices-/
def DiagonalGroup :  Subgroup (GL n R) where
  carrier :=  {M : GL n R | ∃ d : n-> R, M.val = diagonal d}
  mul_mem' := fun ⟨d₁, h₁'⟩ ⟨d₂, h₂'⟩ ↦  ⟨d₁ * d₂, by simp [h₁', h₂'] ⟩
  inv_mem' := by
    intro M ⟨d, h⟩
    have : Invertible (M.val) := M.invertible
    rw [h] at this
    have : Invertible d := invertibleOfDiagonalInvertible d
    use Invertible.invOf d
    simp [h, inv_diagonal]
  one_mem' := ⟨fun (_:n) => 1,diagonal_one⟩
section Perm

/-- `DiagonalGroup` is a subgroup of `MonomialGroup`.-/
theorem diagonalGroup_le_monomialGroup :
    DiagonalGroup ≤ (MonomialGroup : Subgroup (GL n F)) := by
  intro x ⟨_, h⟩
  simp [MonomialGroup, h]
  apply monomial_of_inv_diagonal
  simp [← h]
  exact x.invertible

section MonomialtoPerm


/-- The permutation associed to a `Monomial` matrix seen as a function.-/
noncomputable
def Matrix.toPermFun {M : Matrix n n F} (hM : Monomial M) : n → n :=
  fun j ↦ Classical.choose (hM.2 j).exists

lemma coeff_zero_of_index_neq_toPermFun {M : Matrix n n F} {hM : Monomial M} {i j: n}
    (h : i ≠ toPermFun hM j  ): M i j =0 :=
  no_other_line hM (Exists.choose_spec (hM.2 j).exists) i h

--Maybe change the name ?
lemma toPermFun_universal_property {M : Matrix n n F} (hM : Monomial M) {i j: n} (h : M i j ≠0 ):
    i = toPermFun hM j := by
  contrapose h
  simp
  exact coeff_zero_of_index_neq_toPermFun h

lemma zero_of_toPermFun {M : Matrix n n F} (hM : Monomial M) (j : n) : M (toPermFun hM j) j ≠  0 :=
  match hM.2 j with
  | ⟨_, hM₁, _⟩ => by simpa [← toPermFun_universal_property hM hM₁]

/--Explicit calculation of the product of two `Monomial` matrices.-/
theorem monomial_mul'{M : Matrix n n F} {N : Matrix n n F} (hM :Monomial M) (hN : Monomial N) :
    M*N = Matrix.of (fun i j ↦ M i (toPermFun hN j) * N (toPermFun hN j) j) := by
  ext i j
  simp [mul_apply]
  by_cases h : i = toPermFun hM (toPermFun hN j)
  · simp [h]
    have : (fun x ↦ if x = toPermFun hN j then M i x * N x j else 0 ) =  fun x ↦ M i x * N x j := by
      ext x
      simp
      intro h
      simp [coeff_zero_of_index_neq_toPermFun h]
    simp [← h,← this]
  have: M i (toPermFun hN j) * N (toPermFun hN j) j =0 := by
    simp [h]
    rw [← ne_eq] at h
    left
    apply coeff_zero_of_index_neq_toPermFun h
  rw [this]
  have: (fun _ ↦ (0:F)) = fun j_1 ↦ M i j_1 * N j_1 j := by
    ext x
    by_cases h' : x = toPermFun hN j
    · rw [h', this]
    rw [← ne_eq] at h'
    simp [coeff_zero_of_index_neq_toPermFun h']
  simp [← this]

/--Function `toPermFun` is multiplicative-/
theorem PermFun_mul {M : Matrix n n F} (hM : Monomial M) {N : Matrix n n F} (hN : Monomial N) :
    toPermFun (monomial_mul hM hN) = toPermFun hM  ∘ (toPermFun hN)  := by
  ext j
  rw [Monomial] at hM hN
  rcases hN.2 j with ⟨ i, hN₁, hN₂ ⟩
  rcases hM.2 i with ⟨ k, hM₁, hM₂ ⟩
  simp [hN₂ (toPermFun hN j)  (zero_of_toPermFun hN j),
        hM₂ (toPermFun hM i) (zero_of_toPermFun hM i),monomial_mul' hM hN]
  symm
  apply toPermFun_universal_property
  simp [toPermFun_universal_property hN hN₁] at hN₁ hM₁ ⊢
  exact ⟨hM₁, hN₁⟩

theorem one_permFun : id = toPermFun (monomial_one : Monomial (1: Matrix n n F))  := by
  ext j
  apply toPermFun_universal_property
  simp

/--The permutation associed to a `Monomial` matrix.-/
noncomputable
def Matrix.toPerm {M : Matrix n n F} (hM : Monomial M) : Perm n where
  toFun := Matrix.toPermFun hM
  invFun := Matrix.toPermFun (monomial_of_monomialInverse hM)
  left_inv := by
    rw [Function.LeftInverse]
    intro i
    calc
      toPermFun (monomial_of_monomialInverse hM) (toPermFun hM i) =
        (toPermFun (monomial_of_monomialInverse hM) ∘ (toPermFun hM) ) i := by rfl;
      _                                                           =
        toPermFun (monomial_mul (monomial_of_monomialInverse hM) hM) i := by
          rw [PermFun_mul (monomial_of_monomialInverse hM) hM]
      _                                                           = i := by
          simp [monomialInverse_is_left_inverse hM, ← one_permFun]
  right_inv := by
    have: Invertible M := invertibleOfLeftInverse M (MonomialInverse M) <| monomialInverse_is_left_inverse hM
    rw [Function.RightInverse]
    intro i
    calc
      toPermFun hM (toPermFun (monomial_of_monomialInverse hM) i) =
        (toPermFun hM ∘ (toPermFun (monomial_of_monomialInverse hM)) ) i := by rfl;
      _                                                           =
        toPermFun (monomial_mul hM (monomial_of_monomialInverse hM) ) i := by
          rw [PermFun_mul hM (monomial_of_monomialInverse hM) ]
      _                                                           = i := by
        simp [← inv_eq_left_inv (monomialInverse_is_left_inverse hM), ← one_permFun]

theorem one_perm: toPerm (monomial_one : Monomial (1: Matrix n n F)) = 1 := by
  ext j
  simp [toPerm,← one_permFun]

/--`toPerm` seen as a group homomorphism form `MonomialGroup` to `Perm n`-/
noncomputable
def toPermHom : (MonomialGroup : Subgroup (GL n F)) →* Perm n where
  toFun := fun M => toPerm M.2
  map_one' := one_perm
  map_mul' := fun M N => by
    ext
    simp [toPerm, PermFun_mul M.2 N.2]

end MonomialtoPerm


section PermtoMonomial

/--The permutation matrix associated to a permutation `f`.-/
def Matrix.PermMatrix (f : Perm n) : Matrix n n R :=
  Matrix.of (fun i j ↦ if i = f j then 1 else 0)

lemma PermMatrix_map_one : PermMatrix 1 = (1 : Matrix n n R)  :=by
  simp [PermMatrix, ← diagonal_one, diagonal, Perm.coe_one]

lemma PermMatrix_mul_PermMatrix (f g : Perm n) : PermMatrix (f * g) = PermMatrix f * (PermMatrix g : Matrix n n R) := by
  simp [PermMatrix]
  ext i j
  simp [mul_apply]

lemma PermMatrix_mul (f : Perm n) (M : Matrix n n R):
    PermMatrix f * M = Matrix.of fun i j ↦  M (f⁻¹ i) j  :=by
  ext i j
  simp [mul_apply, PermMatrix]
  have :(fun x ↦ if i = f x then M x j else 0) = fun x ↦ if x = f⁻¹ i then M (f⁻¹ i) j else 0 := by
    ext x
    by_cases h : i = f x
    · simp [h]
    · simp [h]
      rw [← Perm.inv_eq_iff_eq, ← ne_eq] at h
      symm at h
      simp [h]
  simp [this]

lemma mul_PermMatrix (f : Perm n) (M : Matrix n n R):
    M * PermMatrix f  = Matrix.of fun i j ↦  M i (f j)  :=by
  ext i j
  simp [mul_apply, PermMatrix]

/-- PermMatrix seen as a monoid homomorphisme from `Perm n` to `Matrix n n R`-/
def _PermMatrix_Hom : Perm n →* Matrix n n R where
  toFun := fun f ↦ PermMatrix f
  map_one' := PermMatrix_map_one
  map_mul':= PermMatrix_mul_PermMatrix

/-- The group homomorphism version of `_PermMatrix_Hom`-/
def Matrix.PermMatrix_Hom : Perm n →* GL n R := (_PermMatrix_Hom : Perm n →* Matrix n n R ).toHomUnits

/-- The Group of permutation matrices.-/
abbrev PermMatrixGroup : Subgroup (GL n R) := PermMatrix_Hom.range
/--The PermMatrix seen as a group homomorphism from `Perm n` to `PermMatrixGroup`-/
def Matrix.PermMatrix_Hom' : Perm n →* (PermMatrixGroup :Subgroup (GL n R)) :=
  PermMatrix_Hom.rangeRestrict

theorem PermMatrixGroup_mem_iff (x : GL n R) :
    x ∈ PermMatrixGroup ↔ ∃ f : Perm n, x.val = PermMatrix f := by
  simp [PermMatrixGroup, PermMatrix_Hom, _PermMatrix_Hom, PermMatrix]
  constructor
  · intro ⟨f, h⟩
    use f
    simp [← h]
  intro ⟨f, h ⟩
  use f
  ext
  simp [h]

@[simp]
theorem PermMatrix_Hom'coe {f : Perm n} : (PermMatrix_Hom' f).val = (PermMatrix_Hom f : GL n F) := by
  simp [PermMatrix_Hom']

@[simp]
theorem PermMatrix_Homcoe {f:Perm n} : (PermMatrix_Hom f).val = (PermMatrix f: Matrix n n R) := by
  simp [PermMatrix_Hom, _PermMatrix_Hom]


theorem PermMatrix_le_MonomialGroup : PermMatrixGroup ≤ (MonomialGroup : Subgroup (GL n F)) := by
  intro x
  simp [PermMatrixGroup_mem_iff, MonomialGroup, Monomial]
  intro f h
  rw [← h]
  constructor
  · intro i
    use f⁻¹ i
    simp [PermMatrix, PermMatrix_Hom, _PermMatrix_Hom]
    intro j' h
    simp [h]
  intro j
  use f j
  simp [PermMatrix, PermMatrix_Hom, _PermMatrix_Hom]

/-- `toPermHom` is a right section of `PermMatrix_Hom'`.-/
theorem permMatrixGroup_sect :
    toPermHom ∘ Subgroup.inclusion (PermMatrix_le_MonomialGroup :  PermMatrixGroup ≤ (MonomialGroup : Subgroup (GL n F)))
      ∘ PermMatrix_Hom'=  MonoidHom.id (Perm n) := by
  ext f j
  symm
  apply toPermFun_universal_property
  apply monomial_of_monomialGroup
  simp[PermMatrix_Hom']
  simp [PermMatrix_Hom, _PermMatrix_Hom, PermMatrix]

theorem permMatrixGroup_sect' (n : Type*) [DecidableEq n] [Fintype n] (F : Type u_3) [Field F] [DecidableEq F]:
    (toPermHom ∘ Subgroup.inclusion (PermMatrix_le_MonomialGroup :  PermMatrixGroup ≤ (MonomialGroup : Subgroup (GL n F))))
       ∘ PermMatrix_Hom'=  MonoidHom.id (Perm n) := by
  ext f j
  symm
  apply toPermFun_universal_property
  apply monomial_of_monomialGroup
  simp[PermMatrix_Hom']
  simp [PermMatrix_Hom, _PermMatrix_Hom, PermMatrix]


theorem diagonalGroup_is_ker_permMatrixGroup :
    (DiagonalGroup.subgroupOf MonomialGroup) = (toPermHom : (MonomialGroup : Subgroup (GL n F)) →* Perm n).ker  := by
  ext x
  simp [DiagonalGroup, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, toPermHom]
  constructor
  · intro h
    rcases h with ⟨d, hd ⟩
    have inv_diagonal: Invertible (diagonal d) := by
      rw [← hd]
      apply x.val.invertible
    ext j
    simp [hd]
    symm
    apply toPermFun_universal_property (monomial_of_inv_diagonal inv_diagonal)
    simp [diagonal]
    apply noncancel_d_of_invertible_diagonal
  intro h
  use diag x.val.val
  ext i j
  simp [diagonal]
  by_cases h' : (i =j)
  · simp [h']
  · simp  [h']
    have: toPermFun x.2 j = toPerm x.2 j  := by simp [toPerm]
    apply no_other_line x.2
    apply zero_of_toPermFun x.2
    simpa [this, h]

lemma trivial_inf_diagonalGroup_permMatrixGroup :
    DiagonalGroup ⊓ PermMatrixGroup = (⊥ : Subgroup (GL n F)) := by
  apply le_antisymm
  · intro x ⟨⟨d,hd⟩,⟨f,hf⟩⟩
    ext i j
    have : x i j = 0 ∨ x i j =1 := by
      simp [← hf, PermMatrix_Hom, _PermMatrix_Hom, PermMatrix]
      tauto
    have : ¬ x i j = 0 → x i j =1 := by
      intro h
      obtain h'|h' := this
      · exfalso
        exact h h'
      assumption
    by_cases h: i=j
    swap
    · simp [hd,h]
    simp [hd,h]
    simp [hd,h, diagonal] at this
    apply this
    have := x.invertible
    rw [hd] at this
    apply noncancel_d_of_invertible_diagonal
  simp

theorem permMatrixtoPermHom_inj :
    Function.Injective (toPermHom.restrict ((PermMatrixGroup : Subgroup (GL n F)).subgroupOf MonomialGroup )) := by
  simp [← MonoidHom.ker_eq_bot_iff, ← diagonalGroup_is_ker_permMatrixGroup]
  rw [Subgroup.disjoint_def]
  intro x xdiag xPerm
  have : x ∈ (DiagonalGroup ⊓ PermMatrixGroup).subgroupOf (MonomialGroup : Subgroup (GL n F)):=by
    simp [Subgroup.mem_subgroupOf] at xdiag xPerm ⊢
    constructor <;> assumption
  simp [trivial_inf_diagonalGroup_permMatrixGroup] at this
  assumption

theorem permMatrixtoPermHom_inj' {M N:MonomialGroup} (hM : M.val ∈ PermMatrixGroup)
    (hN : N.val ∈ (PermMatrixGroup : Subgroup (GL n F))) (hperm : toPermHom M = toPermHom N) : M=N:= by
  suffices (⟨M,hM⟩ : PermMatrixGroup.subgroupOf MonomialGroup) = ⟨N,hN⟩ by
    simp at this
    assumption
  have : ∀P : (MonomialGroup : Subgroup (GL n F)), (h : P.val ∈ PermMatrixGroup) →
      toPermHom.restrict (PermMatrixGroup.subgroupOf MonomialGroup) ⟨P,h⟩ = toPermHom P := by simp
  rw [← this N hN, ← this M hM] at hperm
  apply permMatrixtoPermHom_inj hperm


/-- A `Monomial` matrix can be written as -/
theorem monomial_decomposition (M : MonomialGroup) :
    ∃ P ∈ PermMatrixGroup, ∃ D ∈ DiagonalGroup,  (M.val : GL n F) = (P : GL n F) * (D : GL n F) := by
  let P : (PermMatrixGroup : Subgroup (GL n F)) := (PermMatrix_Hom' ∘ toPermHom) M
  let D : MonomialGroup := (Subgroup.inclusion PermMatrix_le_MonomialGroup P⁻¹) * M
  use P
  simp at D ⊢
  use D
  constructor
  · have : ∀ f : Perm n,
    toPermHom (Subgroup.inclusion (PermMatrix_le_MonomialGroup :  PermMatrixGroup ≤ (MonomialGroup : Subgroup (GL n F))) (PermMatrix_Hom' f)) = f := by
      intro f
      calc
        toPermHom ((Subgroup.inclusion PermMatrix_le_MonomialGroup) (PermMatrix_Hom' f ))
          = (toPermHom ∘ (Subgroup.inclusion PermMatrix_le_MonomialGroup) ∘ PermMatrix_Hom') f := by simp ; rfl
        _ = f := by rw [permMatrixGroup_sect] ; simp
    have: D ∈ (DiagonalGroup.subgroupOf MonomialGroup) :=
      by simp [diagonalGroup_is_ker_permMatrixGroup, MonoidHom.mem_ker, D, P, this]
    rw [Subgroup.mem_subgroupOf] at this
    assumption
  simp [D]

theorem monomial_decomposition' (M:(MonomialGroup : Subgroup (GL n F))) :
    ∃ D : DiagonalGroup, M = Subgroup.inclusion PermMatrix_le_MonomialGroup (PermMatrix_Hom' (toPermHom M)) *
      (Subgroup.inclusion diagonalGroup_le_monomialGroup D) := by
  let P : (PermMatrixGroup : Subgroup (GL n F)) := (PermMatrix_Hom' ∘ toPermHom) M
  let D : MonomialGroup := (Subgroup.inclusion PermMatrix_le_MonomialGroup P⁻¹) * M

  have : ∀ f : Perm n,
      toPermHom (Subgroup.inclusion (PermMatrix_le_MonomialGroup :  PermMatrixGroup ≤ (MonomialGroup : Subgroup (GL n F))) (PermMatrix_Hom' f)) = f := by
    intro f
    calc
      toPermHom ((Subgroup.inclusion PermMatrix_le_MonomialGroup) (PermMatrix_Hom' f ))
          = (toPermHom ∘ (Subgroup.inclusion PermMatrix_le_MonomialGroup) ∘ PermMatrix_Hom') f
              := by simp ; rfl
      _   = f := by rw [permMatrixGroup_sect] ; simp
  have: D ∈ (DiagonalGroup.subgroupOf MonomialGroup) :=
    by simp [diagonalGroup_is_ker_permMatrixGroup, MonoidHom.mem_ker, D, P, this]
  rw [Subgroup.mem_subgroupOf] at this
  use ⟨D,this⟩
  apply Subgroup.subtype_injective -- most wonderfull lemma ever
  simp [D,P]

theorem monomial_decomposition_unique
    {P P' : (PermMatrixGroup : Subgroup (GL n F))}
      {D D' : DiagonalGroup} (h:P.val * D.val = P'.val*D'.val): P=P' ∧ D=D':= by
  have : P'.val⁻¹ * P.val =D'.val* D.val⁻¹ := by
    rw [← mul_inv_cancel_right P.val D.val, h]
    group
  let I : MonomialGroup :=
    ⟨(P'⁻¹ * P).val, Subgroup.inclusion.proof_1 PermMatrix_le_MonomialGroup (P'⁻¹ * P)⟩ ;
  have Iker:
    (toPermHom : (MonomialGroup : Subgroup (GL n F))→* Perm n) I  = (1 : Perm n):=by
    simp [I, this,← MonoidHom.mem_ker, ← diagonalGroup_is_ker_permMatrixGroup, mem_subgroupOf]
    exact DiagonalGroup.mul_mem D'.2 <| DiagonalGroup.inv_mem D.2
  have : I = 1 :=by
    apply permMatrixtoPermHom_inj'
    simp [I,PermMatrixGroup.mul_mem, PermMatrixGroup.one_mem]
    exact PermMatrixGroup.one_mem
    simp [Iker]
  have : P =P' :=
    have : P'⁻¹ * P = 1 := by
      apply subtype_injective PermMatrixGroup
      simp [I] at this
      simp [this]
    calc
      P = P'*P'⁻¹*P := by group
      _ = P':= by rw [mul_assoc,this, mul_one]
  apply And.intro this
  simp [this] at h;
  exact h

end PermtoMonomial

end Perm
end Monomial

#lint
