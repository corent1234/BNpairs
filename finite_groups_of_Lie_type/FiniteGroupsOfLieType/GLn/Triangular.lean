import Mathlib.Algebra.Group.Units
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import FiniteGroupsOfLieType.GLn.Monomial

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {R : Type*} [CommRing R]
variable {F :Type*} [Field F] [DecidableEq F]

open Matrix
open Units

section Triangular

variable {α : Type*} [LinearOrder α]
/-- The group of invertible `BlockTriangular`matrices.-/
def BlockTriangularGroup (b : n -> α ) : Subgroup (GL n R) where
  carrier :=  {M : GL n R | BlockTriangular M.val b }
  mul_mem' := fun h₁ h₂ => BlockTriangular.mul h₁ h₂
  inv_mem' := by
    intro M h
    simp
    have : Invertible (M.val) := M.invertible
    apply blockTriangular_inv_of_blockTriangular h
  one_mem' := blockTriangular_one


theorem blockTriangular_of_diagonal (d : n -> R) (b : n-> α ): BlockTriangular (diagonal d) b :=
  Matrix.blockTriangular_diagonal d

/--The group of triangular matrices.-/
def TriangularGroup [LinearOrder n] : Subgroup (GL n R):= BlockTriangularGroup id

lemma diag_invertible_of_triangularGroup (M : GL n R) :
    M ∈ TriangularGroup → ∀ i : n, IsUnit (M.val i i) :=by
  intro h i
  let u := M⁻¹.val i i
  have : (fun k ↦ M.val i k * M⁻¹.val k i) =
      fun k:n ↦ if k = i then M.val i i * (M⁻¹).val i i else 0 := by
    have := M.invertible ;have := h
    simp [TriangularGroup, BlockTriangularGroup] at this
    ext k
    obtain h|h := le_or_lt k i
    · obtain h|h := lt_or_eq_of_le h
      · simp  [this h,  ne_of_lt h ]
      rw [h]
      simp
    simp  [blockTriangular_inv_of_blockTriangular this h, ne_of_gt h ]
  have: 1 = M.val i i * u := by
    calc
      1 = (1 : GL n R) i i :=by simp
      _ = (M.val * M⁻¹.val) i i := by simp
      _ = Finset.univ.sum fun k ↦ M.val i k * (M⁻¹).val k i := mul_apply
      _ = M.val i i * M⁻¹.val i i := by rw [this] ; simp
      _ = M.val i i * u := by simp [u]
  apply isUnit_of_mul_eq_one
  rw [this.symm]

end Triangular


section diagonal
variable {α : Type*} [LinearOrder α]
/-- The group of invertible scalar `n` by `n` matrices over `R`.-/
def ScalarGroup : Subgroup (GL n R) :=  (Units.map (scalar n).toMonoidHom).range

theorem scalarGroup_mem_iff : ∀M : GL n R, M ∈ ScalarGroup ↔ ∃ r : Rˣ, M.val = (scalar n) r.val := by
  intro M
  constructor <;>
  { intro ⟨ r, hᵣ⟩
    use r
    try apply Units.ext
    simp [← hᵣ]}

theorem scalarGroup_eq_GLnCenter : ScalarGroup = Subgroup.center (GL n R) := by
  obtain _|_ := isEmpty_or_nonempty n
  · apply Subsingleton.elim
  ext M
  simp [ Subgroup.mem_center_iff, scalarGroup_mem_iff]
  constructor
  · intro ⟨ r,h ⟩ N
    have : N.val* M.val = M.val * N.val → N*M = M *N := fun h => by ext; simp [Units.val_mul, h]
    apply this
    symm
    rw [h, ← commute_iff_eq]
    apply scalar_commute r.val (fun r' ↦ (commute_iff_eq r.val r').2 (mul_comm r.val r'))
  · intro h
    have: M.val ∈ Set.range ⇑(Matrix.scalar n) := by
      rw [mem_range_scalar_iff_commute_transvectionStruct]
      intro t
      have: IsUnit t.toMatrix := by
        rw [isUnit_iff_exists]
        use t.inv.toMatrix
        simp [TransvectionStruct.inv_mul, TransvectionStruct.mul_inv]
      rcases this with ⟨ t',h' ⟩
      rw [commute_iff_eq, ← h', ← Units.val_mul, ← Units.val_mul, h t']
    simp at this
    rcases this with ⟨r, h ⟩
    have : Invertible (diagonal (fun _:n => r)) := by rw [h]; apply Units.invertible
    inhabit n
    have: IsUnit r := isUnit_d_of_invertible_diagonal (fun _:n => r) default
    rcases this with ⟨r', h' ⟩
    use r'
    simp [h', ← h]

theorem scalarGroup_le_diagonalGroup :  ScalarGroup ≤ (DiagonalGroup : Subgroup (GL n R))  := by
  intro
  rw [scalarGroup_mem_iff]
  intro ⟨r, h'⟩
  use (fun _:n => r)
  simp[h']

theorem scalarGroup_le_monomialGroup : ScalarGroup ≤ (MonomialGroup : Subgroup (GL n F)) :=
  le_trans scalarGroup_le_diagonalGroup diagonalGroup_le_monomialGroup

theorem diagonalGroup_le_blockTriangularGroup (b : n -> α ):
  DiagonalGroup ≤ (BlockTriangularGroup b : Subgroup (GL n R)) := by
    intro _ ⟨d,h⟩
    simp [BlockTriangularGroup,h]
    exact blockTriangular_of_diagonal d b

theorem ScalarGroupSubgroupOfBlockTriangularGroup (b : n -> α ):
  ScalarGroup ≤ (BlockTriangularGroup b  : Subgroup (GL n F)) :=
   le_trans scalarGroup_le_diagonalGroup (diagonalGroup_le_blockTriangularGroup b)

theorem diagonalGroup_eq_inf_triangularGroup_monomialGroup:
    DiagonalGroup = TriangularGroup  ⊓ (MonomialGroup : Subgroup (GL n F) ) := by
  ext x
  simp [TriangularGroup,BlockTriangularGroup, MonomialGroup, DiagonalGroup]
  constructor
  · rintro ⟨ d, h⟩
    rw [h]
    constructor
    · exact blockTriangular_of_diagonal d id
    have : Invertible (diagonal d) := by rw [← h]; apply x.invertible
    exact monomial_of_inv_diagonal this
  intro ⟨ xTriangular, xMonomial⟩
  use diag x.val
  ext i j
  simp [diagonal]
  by_cases h : i=j
  · simp [h]
  · simp[h]
    rcases diag_invertible_of_triangularGroup (x : GL n F) xTriangular j with ⟨u, h'⟩
    apply no_other_line xMonomial
    rw [← h']
    apply Units.ne_zero
    assumption

end diagonal
