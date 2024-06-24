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

theorem prop4GL' {Ma : MonomialGroup } {a:A} (h: MonomialCoxeterHom A Ma = (CM A).simple a) :
    {Ma * (b.val: GL n F) * (Ma.val : GL n F) | b :  TriangularGroup} ≠ (TriangularGroup : Subgroup (GL n F)).carrier := by
  simp [Set.ext_iff]
  use Ma * (T :GL n F) * Ma
  push_neg
  left
  constructor
  · use T
    exact ⟨triangularT, rfl⟩
  simp [TriangularGroup, BlockTriangularGroup, BlockTriangular]
  rcases swap_diagonal_of_map_simple A h with  ⟨⟨Da,d,diagdeqDa⟩,i,j,ineqj,h' ⟩
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



lemma transvection_swap_eq_swap_conjug {i0 j0 : n} (hneq : j0 ≠ i0) (c:F) :
    ((PermMatrix_Hom' (swap i0 j0)).val.val : Matrix n n F) * (transvection i0 j0 c) * (PermMatrix_Hom' (swap i0 j0))⁻¹.val.val = transvection j0 i0 c :=by
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
  match Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M.val with
  | ⟨l, l', d,h⟩ =>
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
      · exact transvection_prod_mem_sup_Monomial_Triangular listeq.1
      · exact Subgroup.mem_sup_right <| diagonalGroup_le_blockTriangularGroup id D.2
    · exact transvection_prod_mem_sup_Monomial_Triangular listeq.2

lemma BruhatDecomposition' : (⊤ : Subgroup (GL n F)) = TriangularGroup ⊔ MonomialGroup:=by
  rw [sup_comm]
  exact BruhatDecomposition

open scoped Pointwise
lemma prop5' {G : Type*} [Group G] (B B': Subgroup G) {N : Subgroup G} (w' w: N) 
    (hB' : B' = ConjugatedSubgroup ↑w B) 
        (h' : {w'.val} * B.carrier ⊆ B*B' ∪ B * {w'.val} * B') : 
          {w' * b.val *w | b : B} ⊆ C B (w' * w) ∪ (C B w) :=by
  intro x ⟨b₀,h⟩
  have : x * ↑w⁻¹ ∈ {↑w'} * B.carrier := by simp [← h]
  obtain h'|h' := h' this 
  on_goal 1 => right
  on_goal 2 => left
  all_goals
  · simp [Set.mem_mul, hB'] at h' 
    rcases h' with ⟨z,hz,y,hy,h'⟩
    simp [ConjugatedSubgroup]  at hy 
    simp [DoubleCoset] 
    first | use z ;  exact⟨hz,(↑w)⁻¹ * (y * ↑w),hy,by group ; simp [h']⟩
            | use z * (↑w')⁻¹ ; exact⟨hz,(↑ w)⁻¹ * (y * ↑w),hy,by group ; simp [h']⟩

def  GL2toMn (i j :n) : GL (Fin 2) F →* Matrix n n F where
  toFun := fun M => Matrix.of fun  k l =>
      if (k,l) = (i,i) then M 0 0
      else if (k,l) = (i,j) then M 0 1
      else if (k,l) = (j,i) then M 1 0
      else if (k,l) = (j,j) then M 1 1
      else if k = l then 1
      else 0
  map_mul' := sorry
  map_one' := by 
    simp [one_apply]
    sorry




        
/-
def g (M : GL (Fin 2) F) (i : n) (j : n) : Matrix n n F := Matrix.of fun 
      | i,i => M 0 0
      | i,j => M 0 1
      | j,i => M 1 0
      | j,j => M 1 1
      | m,m => 1
      | _ => 0-/



def G2ij (i : n) (j : n): Subgroup (GL n F) := sorry
  --carrier := { M : GL n F | ∀ k l : n, {k, l} ∉ {i, j} → (k = l →  M.val k l =1) ∧ k ≠ l → M.val k l=0}

def GL2toG2ij (i j :n) : GL (Fin 2) F ≃* (G2ij i j : Subgroup (GL n F)) := sorry

lemma Gij_comm_B (i j :n) : (G2ij i j : Subgroup (GL n F)).carrier * TriangularGroup.carrier ⊆ 
    TriangularGroup.carrier * (G2ij i j).carrier:=
  sorry

lemma SwapMatrixij_mem_Gij {i j :n}:
    ((PermMatrix_Hom' (swap i j)).val : GL n F) ∈ G2ij i j :=by
  sorry

lemma GijTriangular_map_GL2Triangular (i j : n) (F : Type*) [Field F] : 
    (TriangularGroup.subgroupOf (G2ij i j)).map (GL2toG2ij i j).symm.toMonoidHom
      = (TriangularGroup : Subgroup (GL (Fin 2) F))  :=by
    sorry

lemma GijTriangular_map_GL2Triangular' (i j : n) (F : Type*) [Field F] : 
    (GL2toG2ij i j).symm '' (TriangularGroup.subgroupOf (G2ij i j)).carrier  = 
      (TriangularGroup : Subgroup (GL (Fin 2) F)).carrier  :=by
  have h:= GijTriangular_map_GL2Triangular i j F
  rw [← h]
  ext
  constructor 
  · intro ⟨y,hy,hy'⟩
    use y
    simp [← hy', Subgroup.mem_carrier.mp hy]
  · intro ⟨y,hy,hy'⟩
    use y
    simp [← hy', Subgroup.mem_carrier.mp hy] 



      
    

theorem GLprop5 : ∀ (M Ma : MonomialGroup) (a : A), MonomialCoxeterHom A Ma = (CM A).simple a ->
    {(Ma.val * b.val * M.val : GL n F) | b : TriangularGroup} ⊆
      DoubleCoset TriangularGroup (Ma * M).val∪ DoubleCoset TriangularGroup M.val := by
  intro M Ma a
  revert Ma
  apply (prop5_iff TriangularGroup (monomialCoxeterHom_surj A) (prop3 A) M a).mpr
  rcases M_simples_are_swaps A n a with  ⟨i,j,ineqj, h⟩
  let Pij : (MonomialGroup : Subgroup (GL n F)) := PermMatrix_Hom_to_Monomial (swap i j)
  use Pij, swapPerm_mapsto_simple A h
  let N : Subgroup (GL n F):= MonomialGroup
  let B : Subgroup (GL n F):= TriangularGroup
  let B': Subgroup (GL n F):= ConjugatedSubgroup ↑M B
  let Gij : Subgroup (GL n F) := G2ij i j
  apply prop5' B B' Pij M (by simp [B']) 
  suffices B.carrier * Gij.carrier ⊆ B*B' ∪ B*{↑Pij} * B' by
    apply subset_trans
    swap
    · exact this
    · simp [Set.singleton_mul,Set.mem_mul]
      intro x h
      simp at h 
      apply Gij_comm_B
      use Pij, SwapMatrixij_mem_Gij, Pij⁻¹ * x, h
      simp
  suffices h : ↑Gij ⊆ ↑(B ⊓ Gij) * (B' ⊓ Gij).carrier ∪ ↑(B ⊓ Gij) * {↑Pij} * ↑(B' ⊓ Gij) by
    have:↑Gij ⊆ B.carrier * ↑B' ∪ ↑B * {↑Pij} * ↑B' → ↑B * Gij.carrier ⊆ ↑B * ↑B' ∪ ↑B * {↑Pij} * ↑B':= by
      intro h x ⟨b,binB,g,ginGij,hx⟩
      obtain ⟨b2,b2inB,b',b'inB',hg ⟩|⟨b2,b2inB,b',b'inB,hg⟩:= h ginGij 
      · left 
        simp [← hg] at hx 
        use b*b2, B.mul_mem binB b2inB, b', b'inB'
        simp [← hx, mul_assoc]
      · right
        simp [← hg] at hx b2inB 
        use b*(b2*(↑Pij)⁻¹) * Pij 
        simp [B.mul_mem binB b2inB]
        use b', b'inB
        simp [← hx, mul_assoc] 
    apply this
    apply subset_trans h
    apply Set.union_subset_union <;>
    · apply Set.mul_subset_mul <;>
      · try apply Set.mul_subset_mul_right 
        try simp [Subgroup.coe_inf, Set.inter_subset_left]
        try exact Set.inter_subset_left
  let B2 := B.subgroupOf Gij
  let B2' := B'.subgroupOf Gij
  let Pij' : Gij := ⟨Pij.val, SwapMatrixij_mem_Gij ⟩
  suffices ↑(⊤ : Subgroup Gij) = ↑B2 * B2'.carrier ∪  ↑B2 * {Pij'} * ↑B2' by
    intro x h 
    obtain ⟨b,binB2,b',b'inB2',h⟩| ⟨b,binB2,b',b'inB2',h⟩ := subset_of_eq this (Subgroup.mem_top ⟨x,h⟩)
    · left
      simp [B2,B2', Subgroup.mem_subgroupOf] at binB2 b'inB2' 
      use b.val, ⟨binB2,b.2⟩, b'.val, ⟨b'inB2',b'.2⟩
      apply_fun Subgroup.subtype Gij at h
      simp at h
      assumption
    · right
      simp [Subgroup.coe_inf, Set.mem_mul]
      simp [B2,B2', Subgroup.mem_subgroupOf] at binB2 b'inB2' 
      use b, ⟨binB2,Gij.mul_mem b.2 SwapMatrixij_mem_Gij⟩, b', ⟨b'inB2',b'.2⟩
      apply_fun Subgroup.subtype Gij at h
      simp at h
      assumption
  let GL2toGij : GL (Fin 2) F ≃* Gij := GL2toG2ij i j
  apply_fun (GL2toGij.symm '' · )
  swap
  · sorry
  have :(fun (x : Set Gij) ↦ GL2toGij.symm '' x) ↑(⊤: Subgroup Gij) = (Set.univ: Set (GL (Fin 2) F)) :=
  Set.ext fun x => Iff.intro
    (fun _ => Set.mem_univ x)
    fun _ => ⟨GL2toGij x, by simp⟩ 
  rw [this]
  
  have : (fun x ↦ ⇑GL2toGij.symm '' x : Set Gij → Set (GL (Fin 2) F)) (↑B2 * B2'.carrier ∪ ↑B2 * {Pij'} * ↑B2') = 
    ↑(TriangularGroup : Subgroup (GL (Fin 2) F)) * (GL2toGij.symm '' ↑B2') ∪ ↑(TriangularGroup : Subgroup (GL (Fin 2) F)) * { GL2toGij.symm Pij' } * (GL2toGij.symm '' ↑B2') := 
    calc 
      (fun x ↦ ⇑GL2toGij.symm '' x : Set Gij → Set (GL (Fin 2) F)) (↑B2 * B2'.carrier ∪ ↑B2 * {Pij'} * ↑B2')
    _ = GL2toGij.symm '' (↑B2 * B2'.carrier ∪ ↑B2 * {Pij'} * ↑B2') := by simp
    _ = GL2toGij.symm '' (↑B2 * B2'.carrier) ∪ (GL2toGij.symm '' (↑B2 * {Pij'} * ↑B2')) := by rw [← Set.sUnion_pair, Set.image_sUnion]; simp
    _ = ↑(TriangularGroup : Subgroup (GL (Fin 2) F)) * (GL2toGij.symm '' ↑B2') ∪ ↑(TriangularGroup : Subgroup (GL (Fin 2) F)) * { GL2toGij.symm Pij' } * (GL2toGij.symm '' ↑B2') := by rw [Set.mul_of_mul_image_of_MulEquiv GL2toGij.symm ] 
    
  




        


        





     
/--The `BNMphiQuadruplet`  structure over `GL n F`.-/
noncomputable
def GL' : BNMphiQuadruplet (GL n F) A where
  B := TriangularGroup
  N := MonomialGroup
  M := CM A
  phi := MonomialCoxeterHom A
  prop1 := BruhatDecomposition'
  prop2 := monomialCoxeterHom_surj A
  prop3 := prop3 A
  prop4 := fun _ _ => prop4GL' A
  prop5 := sorry


#lint
