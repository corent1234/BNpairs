import Mathlib.Algebra.Group.Units
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import FiniteGroupsOfLieType.GLn.Monomial
import FiniteGroupsOfLieType.Basic

variable {n : Type*}  [Fintype n] [DecidableEq n] [LinearOrder n] {R : Type*} [CommRing R]
variable {F :Type*} [Field F] [DecidableEq F]
variable {α : Type*} [LinearOrder α]

open Matrix
open Units

section Triangular

/-- The group of invertible `BlockTriangular`matrices.-/
def BlockTriangularGroup (b : n -> α ) : Subgroup (GL n R) where
  carrier :=  {M : GL n R | BlockTriangular M.val b }
  mul_mem' := by
    intro _ _ h₁ h₂ ;
    simp at h₁ h₂ ⊢
    apply BlockTriangular.mul h₁ h₂
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
  let d := diag x.val
  use d
  ext i j
  simp [diagonal]
  by_cases h : i=j
  · simp [h, d]
  · simp[h]
    rcases diag_invertible_of_triangularGroup (x : GL n F) xTriangular j with ⟨u, h'⟩
    apply no_other_line xMonomial
    rw [← h']
    apply Units.ne_zero
    assumption

end diagonal

variable (A : Type*)
open Equiv
/--Some Coxeter Matrix.-/
def M : CoxeterMatrix A := sorry
/--The Coxeter System from M to `Perm`.-/
def perm_coxeterSystem : CoxeterSystem (M A) (Perm n) := sorry
/--The group homomorphism from `MonomialGoup` to the group of M.-/
noncomputable
def MonomialCoxeterHom : (MonomialGroup : Subgroup (GL n F)) →* (M A).Group :=
    (perm_coxeterSystem A).mulEquiv.toMonoidHom.comp toPermHom

lemma M_simples_are_swaps (n:Type*) [DecidableEq n] (a : A):
    ∃ i j :n, i≠j ∧ (perm_coxeterSystem A).mulEquiv.symm.toMonoidHom ((M A).simple a) = swap i j:= by
  sorry

theorem diagonalGroup_is_ker_monomialCoexeterHom :
    (DiagonalGroup.subgroupOf MonomialGroup)
      = (MonomialCoxeterHom A : (MonomialGroup : Subgroup (GL n F)) →* (M A).Group).ker :=by
  ext x
  simp [MonoidHom.mem_ker, MonomialCoxeterHom, diagonalGroup_is_ker_permMatrixGroup]

theorem monomialCoxeterHom_surj :
  Function.Surjective (MonomialCoxeterHom A : (MonomialGroup : Subgroup (GL n F)) →* (M A).Group) := by
  apply Function.Surjective.comp
  simp [MonomialCoxeterHom]
  apply Function.Surjective.of_comp
  rw [permMatrixGroup_sect, Function.Surjective]
  repeat exact fun b ↦ ⟨b, by simp⟩

/--The prop 4 of a BNMphiQuadruplet applies to GLn.-/
theorem prop4GL {Ma : MonomialGroup} {a : A} (h : MonomialCoxeterHom A Ma = (M A).simple a):
    ∃ Da : DiagonalGroup, ∃ i j : n, i≠j ∧ Ma.val = (PermMatrix_Hom' (swap i j)).val*(Da.val : GL n F)  := by
  rcases monomial_decomposition' Ma with ⟨Da, Ma_eq_PaDa⟩
  let Pa : (MonomialGroup : Subgroup (GL n F)) :=
    (Subgroup.inclusion PermMatrix_le_MonomialGroup) (PermMatrix_Hom' (toPermHom Ma))
  use Da
  rcases M_simples_are_swaps A n a with ⟨i,j, ineqj, h' ⟩
  use i ;use j
  simp [ineqj]
  rw [Ma_eq_PaDa]
  simp [Pa]
  have : toPermHom Ma = swap i j := by
    simp [← h', MulEquiv.eq_symm_apply,← h, MonomialCoxeterHom]
  rw [this]

/--The lower triangular matrix with only one as diagonal and subdiagonal coefficients.-/
def T₀  :=  Matrix.of fun i j :n ↦ if i ≤ j then (1:F) else 0

lemma detT_eq_one: det (T₀ : Matrix n n F) = 1 := by
  rw [Matrix.det_of_upperTriangular]
  repeat simp [BlockTriangular, T₀]

lemma invdetT : IsUnit (T₀ : Matrix n n F).det := by
  simp [← ne_eq];
  apply ne_zero_of_eq_one (detT_eq_one )

/--The matrix T₀ seen as an element of `GL n F`.-/
noncomputable
def T : GL n F := GeneralLinearGroup.mk'' (T₀ : Matrix n n F) invdetT

lemma Tcoe : T.val = Matrix.of fun i j :n ↦ if i ≤ j then (1:F) else 0 := by
  simp [T,T₀, GeneralLinearGroup.mk'', Matrix.nonsingInvUnit]
lemma triangularT : (T : GL n F) ∈ TriangularGroup := by
  simp [TriangularGroup, BlockTriangularGroup, BlockTriangular,Tcoe]

theorem prop4GL' {Ma : MonomialGroup } {a:A} (h: MonomialCoxeterHom A Ma = (M A).simple a) :
    {Ma * (b.val: GL n F) * (Ma.val : GL n F) | b :  TriangularGroup} ≠ (TriangularGroup : Subgroup (GL n F)).carrier := by
  simp [Set.ext_iff]
  use Ma * (T :GL n F) * Ma
  push_neg
  left
  constructor
  · use T
    exact ⟨triangularT, rfl⟩
  simp [TriangularGroup, BlockTriangularGroup, BlockTriangular]
  rcases prop4GL A h with  ⟨⟨Da,d,diagdeqDa⟩,i,j,ineqj,h' ⟩
  have : Invertible (diagonal d) := by rw [← diagdeqDa] ; apply Da.invertible
  obtain hij|hij := ne_iff_lt_or_gt.1 ineqj
  · use j ; use i
    simp [hij, h', PermMatrix_mul, mul_PermMatrix, diagdeqDa, diagonal,mul_apply,Tcoe]
    have: (fun x ↦
        if (swap i j) x = i then
          (Finset.univ.sum fun x_1 ↦ if x_1 ≤ x then if i = x_1 then d i else 0 else 0) * d ((swap i j) x)
          else 0 )= fun x ↦ if x =j then
            (Finset.univ.sum fun x_1 ↦ if x_1 ≤ x then if i = x_1 then d i else 0 else 0) * d ((swap i j) x)
              else 0 :=by
      ext x
      by_cases h: x=j
      · simp [h]
      have : ¬ swap i j x = i := by apply_fun (swap i j); simp [h]
      simp [h, this]
    simp [this]
    constructor
    · have : (fun k ↦ if k ≤ j then if i = k then d i else 0 else 0) =
          fun k ↦ if k=i then d i else 0 := by
        ext k
        by_cases h : k=i
        · simp [h] ;intro h ; exfalso ; apply not_lt_of_gt hij h
        · simp [h] ; intro _ not_h ; exfalso;  exact h not_h.symm
      simp [this]
      apply noncancel_d_of_invertible_diagonal
    · apply noncancel_d_of_invertible_diagonal
  · use i ; use j
    simp [hij, h', PermMatrix_mul, mul_PermMatrix, diagdeqDa, diagonal,mul_apply,Tcoe]
    have: (fun x ↦
        if (swap i j) x = j then
          (Finset.univ.sum fun x_1 ↦ if x_1 ≤ x then if j = x_1 then d j else 0 else 0) * d ((swap i j) x)
          else 0 )= fun x ↦ if x =i then
            (Finset.univ.sum fun x_1 ↦ if x_1 ≤ x then if j = x_1 then d j else 0 else 0) * d ((swap i j) x)
              else 0 :=by
      ext x
      by_cases h: x=i
      · simp [h]
      have : ¬ swap i j x = j := by
        apply_fun (swap i j)
        simp [h]
      simp [h, this]
    simp [this]
    constructor
    · have : (fun k ↦ if k ≤ i then if j = k then d j else 0 else 0) =
          fun k ↦ if k=j then d j else 0 := by
        ext k
        by_cases h : k=j
        · simp [h]
          intro h
          exfalso
          apply not_lt_of_gt hij h
        simp [h]
        intro _ not_h
        exfalso
        exact h not_h.symm
      simp [this]
      apply noncancel_d_of_invertible_diagonal
    apply noncancel_d_of_invertible_diagonal





/--The `BNMphiQuadruplet`  structure over `GL n F`.-/
noncomputable
def GL' : BNMphiQuadruplet (GL n F) A where
  B := TriangularGroup
  N := MonomialGroup
  M := M A
  phi := MonomialCoxeterHom A
  prop1 := sorry
  prop2 := monomialCoxeterHom_surj A
  prop3 := by simp [← diagonalGroup_is_ker_monomialCoexeterHom,diagonalGroup_eq_inf_triangularGroup_monomialGroup ]
  prop4 := fun _ _ => prop4GL' A
  prop5 := sorry


#lint
