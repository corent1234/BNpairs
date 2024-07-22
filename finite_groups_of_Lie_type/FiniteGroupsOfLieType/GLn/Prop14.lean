import FiniteGroupsOfLieType.GLn.Triangular
import FiniteGroupsOfLieType.Basic

variable {n : Type*}  [Fintype n] [DecidableEq n] [LinearOrder n]
variable {F :Type*} [Field F] [DecidableEq F]

open Equiv
open Matrix

section Bruhat

lemma transvection_swap_eq_swap_conjug {i0 j0 : n} (hneq : j0 ≠ i0) (c:F) :
    ((PermMatrix_Hom' (swap i0 j0)).val.val : Matrix n n F) * (transvection i0 j0 c) *
      (PermMatrix_Hom' (swap i0 j0))⁻¹.val.val = transvection j0 i0 c :=by
  rw [ ← MonoidHom.map_inv]
  simp [ PermMatrix_Hom', PermMatrix_mul, mul_PermMatrix]
  ext i j
  by_cases hi : i=i0
  · by_cases hj : j=j0
    · simp [hi,hj, transvection, hneq, one_apply, ← ne_eq]
    · simp [hi, hj,hneq,Equiv.swap_apply_def]
      by_cases hji0 : j=i0
      · simp [*, transvection, stdBasisMatrix, ← ne_eq, hneq.symm]
      · simp [*, transvection, stdBasisMatrix,hneq.symm, one_apply, ← ne_eq]
        rw [← ne_eq] at hj hji0
        simp [hj.symm,hji0.symm]
  · rw [← ne_eq ] at hi
    by_cases hj : j=j0
    · simp [hj, transvection, stdBasisMatrix, one_apply, hneq]
      intro _ h
      symm at h
      contradiction
    · simp [hj]
      by_cases hji0: j=i0
      · simp [*, transvection, stdBasisMatrix, one_apply, Equiv.swap_apply_def, hneq.symm]
        by_cases hij0: i=j0
        · simp [*,hneq.symm]
        · simp [*, hi.symm, ((ne_eq i j0) ▸ hij0).symm ]
      · simp [*, transvection, stdBasisMatrix, one_apply, Equiv.swap_apply_def, hneq.symm]
        by_cases hij0: i =j0
        · rw [← ne_eq] at hj
          simp [*, hj.symm, ((ne_eq j i0) ▸ hji0).symm]
        · simp [*, hi.symm]
          intro h
          symm at h
          contradiction

theorem transvection_mem_sup_Monomial_Triangular {T : GL n F} {t:TransvectionStruct n F}
    (hT: ↑T = t.toMatrix): T ∈ MonomialGroup ⊔ TriangularGroup  := by
  obtain h|h := ne_iff_lt_or_gt.mp t.hij
  · apply Subgroup.mem_sup_right
    simp [TriangularGroup, BlockTriangularGroup,hT]
    apply  Matrix.blockTriangular_transvection (by simp [le_of_lt h])
  · let M : (PermMatrixGroup : Subgroup (GL n F)) := PermMatrix_Hom' (swap t.j t.i)
    let t' : TransvectionStruct n F := {i := t.j, j := t.i, hij := t.hij.symm, c := t.c}
    let T' : GL n F:=
      ⟨t'.toMatrix, t'.inv.toMatrix,TransvectionStruct.mul_inv t', TransvectionStruct.inv_mul t' ⟩
    have : T  = M * T' * M⁻¹ := by
      simp [hT, Units.ext_iff, TransvectionStruct.toMatrix_mk t.i t.j t.hij t.c, M]
      rw [← transvection_swap_eq_swap_conjug t.hij t.c]
      simp  [PermMatrix_Hom'coe, TransvectionStruct.inv, t']
    rw [this]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mem_sup_left (PermMatrix_le_MonomialGroup M.2)
      · apply Subgroup.mem_sup_right
        simp [TriangularGroup, BlockTriangularGroup]
        apply  Matrix.blockTriangular_transvection (by simp [le_of_lt h])
    · apply Subgroup.mem_sup_left
      apply PermMatrix_le_MonomialGroup
      simp [PermMatrixGroup.inv_mem M.2]

lemma transvection_prod_mem_sup_Monomial_Triangular {l : List (TransvectionStruct n F)} {l' : List (GL n F)}
    (h: (List.map TransvectionStruct.toMatrix l) = List.map (fun x => x.val) l')
       :  l'.prod ∈ MonomialGroup ⊔ TriangularGroup := by
  let P : GL n F → Prop := fun M => M ∈  MonomialGroup ⊔ TriangularGroup
  suffices P l'.prod by simp [P] at this ; exact this
  apply List.prod_induction
  · simp [P]
    intro _ _
    apply Subgroup.mul_mem
  · simp [P]
    apply Subgroup.one_mem
  · simp [P]
    intro M h'
    have : M.val ∈ List.map TransvectionStruct.toMatrix l := by
      simp [h]
      exact ⟨M,h',  rfl⟩
    rw [List.mem_map] at this
    rcases this with ⟨t,_,ht⟩
    apply transvection_mem_sup_Monomial_Triangular ht.symm

theorem BruhatDecomposition : (⊤ : Subgroup (GL n F)) = MonomialGroup ⊔ TriangularGroup := by
  apply le_antisymm
  swap
  · simp
  intro M _
  rcases Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.val with ⟨l, l', d,h⟩
  have : IsUnit (diagonal d) :=by
    apply_fun Matrix.det at h
    simp [-det_diagonal] at h
    simp [isUnit_iff_isUnit_det, ← h, ← ne_eq, -det_diagonal] ;
    exact det_ne_zero_of_right_inverse M.3
  rcases this with ⟨D0,hD0⟩
  let D :DiagonalGroup := ⟨D0,d,hD0⟩

  /-Coerce an element `t:TransvectionStruct n F` into a element of type `GL n F` -/
  let Unitise : TransvectionStruct n F→ GL n F := fun t => ⟨t.toMatrix, t.inv.toMatrix,
    TransvectionStruct.mul_inv t,TransvectionStruct.inv_mul t⟩
  let L := List.map Unitise l
  let L' := List.map Unitise l'
  have listeq: (List.map TransvectionStruct.toMatrix l) = List.map (Units.coeHom (Matrix n n F)) L
      ∧ (List.map TransvectionStruct.toMatrix l') = List.map (Units.coeHom (Matrix n n F)) L' :=by
    have : Units.coeHom (Matrix n n F) ∘ Unitise = fun t => t.toMatrix := by ext t ; simp
    constructor <;> simp [L,L',this]

  have : M = List.prod L * D *  List.prod L' := by
    apply Units.ext
    simp [h, listeq.1, listeq.2, List.prod_hom, hD0]
  rw [this]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact (transvection_prod_mem_sup_Monomial_Triangular listeq.1)
    · exact Subgroup.mem_sup_right <| diagonalGroup_le_blockTriangularGroup id D.2
  · exact transvection_prod_mem_sup_Monomial_Triangular listeq.2

lemma BruhatDecomposition' : (⊤ : Subgroup (GL n F)) = TriangularGroup ⊔ MonomialGroup:=by
  rw [sup_comm]
  exact BruhatDecomposition

end Bruhat




variable (A : Type*)

/--Some Coxeter Matrix.-/
def CM : CoxeterMatrix A := sorry
/--The Coxeter System from M to `Perm`.-/
def perm_coxeterSystem : CoxeterSystem (CM A) (Perm n) := sorry
/--The group homomorphism from `MonomialGoup` to the group of M.-/
noncomputable
def MonomialCoxeterHom : (MonomialGroup : Subgroup (GL n F)) →* (CM A).Group :=
    (perm_coxeterSystem A).mulEquiv.toMonoidHom.comp toPermHom

lemma M_simples_are_swaps (n:Type*) [DecidableEq n] (a : A):
    ∃ i j :n, i≠j ∧ (perm_coxeterSystem A).mulEquiv.symm ((CM A).simple a) = swap i j:= by
  sorry
lemma M_simples_are_swaps' (n:Type*) [DecidableEq n] [LinearOrder n] (a : A):
    ∃ i j :n, i < j ∧ (perm_coxeterSystem A).mulEquiv.symm ((CM A).simple a) = swap i j:= by
  rcases M_simples_are_swaps A n a with ⟨i,j, ineqj, h⟩
  obtain hij|hji := lt_or_gt_of_ne ineqj
  · use i, j, hij, h
  · use j, i, hji, Equiv.swap_comm i j ▸ h

theorem diagonalGroup_is_ker_monomialCoexeterHom :
    (DiagonalGroup.subgroupOf MonomialGroup)
      = (MonomialCoxeterHom A : (MonomialGroup : Subgroup (GL n F)) →* (CM A).Group).ker :=by
  ext x
  simp [MonoidHom.mem_ker, MonomialCoxeterHom, diagonalGroup_is_ker_permMatrixGroup]

theorem prop3 :
    (MonomialCoxeterHom A).ker = TriangularGroup.subgroupOf (MonomialGroup : Subgroup (GL n F)) := by
  simp [← diagonalGroup_is_ker_monomialCoexeterHom,diagonalGroup_eq_inf_triangularGroup_monomialGroup ]

theorem monomialCoxeterHom_surj :
  Function.Surjective (MonomialCoxeterHom A : (MonomialGroup : Subgroup (GL n F)) →* (CM A).Group) := by
  apply Function.Surjective.comp
  simp [MonomialCoxeterHom]
  apply Function.Surjective.of_comp
  rw [permMatrixGroup_sect, Function.Surjective]
  repeat exact fun b ↦ ⟨b, by simp⟩

theorem swapPerm_mapsto_simple {i j : n}
    (h: (perm_coxeterSystem A).mulEquiv.symm ((CM A).simple a) = swap i j):
      MonomialCoxeterHom A (PermMatrix_Hom_to_Monomial (swap i j): (MonomialGroup :Subgroup (GL n F)))
        = (CM A).simple a := by
  simp [MonomialCoxeterHom,MulEquiv.apply_eq_iff_symm_apply,h,permMatrixGroup_sect']


/--The prop 4 of a BNMphiQuadruplet applies to GLn.-/
theorem swap_diagonal_of_map_simple {Ma : MonomialGroup} {a : A}
    (h : MonomialCoxeterHom A Ma = (CM A).simple a):
      ∃ Da : DiagonalGroup, ∃ i j : n, i≠j ∧ Ma.val = (PermMatrix_Hom' (swap i j)).val*(Da.val : GL n F)  := by
  rcases monomial_decomposition' Ma with ⟨Da, Ma_eq_PaDa⟩
  let Pa : (MonomialGroup : Subgroup (GL n F)) := (PermMatrix_Hom_to_Monomial (toPermHom Ma))
  use Da
  rcases M_simples_are_swaps A n a with ⟨i,j, ineqj, h' ⟩
  use i ;use j
  simp [ineqj]
  rw [Ma_eq_PaDa]
  simp [Pa]
  have : toPermHom Ma = swap i j := by
    simp [← h', MulEquiv.eq_symm_apply,← h, MonomialCoxeterHom]
  rw [this, PermMatrix_Hom_to_Monomial, MonoidHom.comp_apply]
  simp [PermMatrix_Hom']


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

theorem prop4GL' {Ma : MonomialGroup } {a : A} (h : MonomialCoxeterHom A Ma = (CM A).simple a) :
    {Ma * (b.val: GL n F) * (Ma.val : GL n F) | b :  TriangularGroup} ≠ (TriangularGroup : Subgroup (GL n F)).carrier := by
  simp [Set.ext_iff]
  use Ma * (T :GL n F) * Ma
  push_neg
  left
  constructor
  · exact ⟨T,triangularT, rfl⟩
  simp [TriangularGroup, BlockTriangularGroup, BlockTriangular]
  rcases swap_diagonal_of_map_simple A h with  ⟨⟨Da,d,diagdeqDa⟩,i,j,ineqj,h' ⟩
  have : Invertible (diagonal d) := by rw [← diagdeqDa] ; apply Da.invertible
  obtain hij|hij := ne_iff_lt_or_gt.1 ineqj
  · use j, i
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

#lint
