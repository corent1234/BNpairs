import FiniteGroupsOfLieType.Basic
import FiniteGroupsOfLieType.GLn.Prop14

variable {n : Type*}  [Fintype n] [DecidableEq n] [LinearOrder n] (A : Type*)
variable {F :Type*} [Field F] [DecidableEq F]

open Matrix Units Subgroup Equiv

open scoped Pointwise
lemma prop5' {G : Type*} [Group G] (B B': Subgroup G) {N : Subgroup G} (w' w: N)
    (hB' : B' = ConjugatedSubgroup B ↑w)
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

variable {i j : n} (hij : i < j)
abbrev sij (i j :n):= {x : n // x = i ∨ x = j}
abbrev sij_compl (i j :n):= {x : n //¬  (x = i ∨ x = j)}

def equiv2_ij : Fin 2 ≃ sij i j  where
  toFun :=fun x =>  match x with
    |0 => ⟨i,by simp⟩
    |1 => ⟨j,by simp⟩
  invFun := fun x => if x = i then 0 else 1
  left_inv :=by
    intro x
    match x with
    | 0 => simp
    | 1 => simp [(ne_of_lt hij).symm]
  right_inv := by
    intro x
    obtain h|h := x.2 <;> simp [h, (ne_of_lt hij).symm, ← Subtype.val_inj]

def e2_ij  : Fin 2 ⊕ sij_compl i j ≃ n:=
  Equiv.trans
   (Equiv.sumCongr (equiv2_ij hij) (Equiv.refl (sij_compl i j)))
    (Equiv.sumCompl (fun x => x=i ∨ x =j))


def  M2toMn : Matrix (Fin 2) (Fin 2) F →* Matrix n n F where
  toFun := fun M => Matrix.reindexAlgEquiv F (e2_ij hij)
    <|Matrix.fromBlocks M 0 0 (1 : Matrix (sij_compl i j) (sij_compl i j) F)
  map_mul' := by
    intro M N
    simp [Matrix.fromBlocks_multiply]
  map_one' := by simp

def  GL2toGLn : GL (Fin 2) F →* GL n F := Units.map (M2toMn hij)

lemma GL2toGLn_inj :  Function.Injective (GL2toGLn hij : GL (Fin 2) F →* GL n F) :=by
  simp [← MonoidHom.ker_eq_bot_iff]
  ext M
  simp [MonoidHom.mem_ker, GL2toGLn,M2toMn]
  constructor
  · intro h
    apply_fun fun  x => x.val at h
    apply_fun Matrix.reindex (e2_ij hij).symm (e2_ij hij).symm at h
    simp [← Matrix.fromBlocks_one] at h
    assumption
  · intro h
    apply Units.ext
    simp [h]

lemma GL2toG2ij_bij : Function.Bijective (GL2toGLn hij: GL (Fin 2) F →* GL n F).rangeRestrict :=by
  constructor
  · apply MonoidHom.rangeRestrict_injective_iff.mpr
    apply GL2toGLn_inj
  · apply MonoidHom.rangeRestrict_surjective

def G2ij : Subgroup (GL n F) := (GL2toGLn hij).range

lemma G2ij_mem (M : GL n F) : M ∈ G2ij hij ↔ ∃ M2 : GL (Fin 2) F, M.val = M2toMn hij M2.val:=by
  simp [G2ij, GL2toGLn]
  constructor
  · intro ⟨x,hx⟩
    apply_fun fun x => x.val at hx
    simp at hx
    use x
    exact hx.symm
  · intro ⟨x,hx⟩
    use  x
    apply Units.ext
    simp [← hx]

lemma not_ij_or_diag_of_mem_G2ij (M: G2ij hij) {k l : n} (hkl : ¬ ((k =i ∨ k=j) ∧ (l=i ∨ l = j))) :
    M.val.val k l =  if k=l then 1 else (0 : F) :=by
  have neqkl {k l :n} (hk : k=i ∨ k=j) (hl : ¬ (l = i ∨ l = j)) : k ≠ l := by
    obtain hk|hk := hk
    all_goals simp [hk] at hl ⊢ ;simp [(ne_eq l j ▸ hl.right).symm, (ne_eq l i ▸ hl.left).symm]
  rcases (G2ij_mem hij M.1).mp M.2 with ⟨M',hM'⟩
  simp [hM', M2toMn]
  by_cases hk : k=i ∨ k=j
  · simp at neqkl hkl
    simp [hk, hkl hk, e2_ij, neqkl hk (hkl hk).1 (hkl hk).2]
  · simp [hk, e2_ij]
    by_cases hl : l = i ∨ l = j
    · simp [hl, (neqkl hl hk).symm]
    · simp [hl,one_apply]

noncomputable
def GL2toG2ij : GL (Fin 2) F ≃* (G2ij hij : Subgroup (GL n F)) :=  MulEquiv.ofBijective (GL2toGLn hij).rangeRestrict (GL2toG2ij_bij hij)

lemma GL2toG2ij_coe (M : GL (Fin 2) F) : ↑(↑(GL2toG2ij hij M) : GL n F) =
    M2toMn hij M.val:=by
    have  : @Subtype.val (GL n F) (fun x ↦ x ∈ ↑(G2ij hij)) ((Units.map (M2toMn hij)).rangeRestrict M)
        = M2toMn hij M.val := by
      simp
    simp [GL2toG2ij, GL2toGLn]
    rw [← this]
    rfl


noncomputable
def invGL2toG2ij (M : (G2ij hij : Subgroup (GL n F))) : GL (Fin 2) F := Matrix.nonsingInvUnit
  (Matrix.of (fun k l => M.val (equiv2_ij hij k) (equiv2_ij hij l)))
  (by let x := (GL2toG2ij hij).symm M
      have  : M = GL2toG2ij hij x := by simp [x]
      simp [this, GL2toG2ij_coe,M2toMn, mul_apply,e2_ij, equiv2_ij, Matrix.det_fin_two, (ne_of_lt hij).symm]
      rw [ ← Matrix.det_fin_two]
      have := Matrix.isUnits_det_units x
      simp at this
      assumption)

lemma GL2toG2ij_symm_apply (M : (G2ij hij : Subgroup (GL n F))) :
    (GL2toG2ij hij).symm M = invGL2toG2ij hij M := by
  apply_fun GL2toG2ij hij
  simp
  apply Subgroup.subtype_injective
  apply Units.ext
  --rcases (G2ij_mem hij M.1).mp M.2 with ⟨M',hM⟩
  simp [GL2toG2ij_coe, invGL2toG2ij, M2toMn, e2_ij]
  ext k l
  by_cases hk : k = i
  · by_cases hl : l=i
    · simp [hk,hl, nonsingInvUnit]
    · by_cases hl' : l =j
      · simp [hk, hl', nonsingInvUnit]
      · simp [hk, hl,hl']
        rw [not_ij_or_diag_of_mem_G2ij]
        · simp [(ne_eq l i ▸ hl).symm]
        · simp [hl, hl']
  · by_cases hk' : k = j
    · by_cases hl : l=i
      · simp [hk',hl, nonsingInvUnit]
      · by_cases hl' : l =j
        · simp [hk', hl', nonsingInvUnit]
        · simp [hk', hl,hl']
          rw [not_ij_or_diag_of_mem_G2ij]
          · simp [(ne_eq l j ▸ hl').symm]
          · simp [hl, hl']
    · simp [hk, hk']
      rw [not_ij_or_diag_of_mem_G2ij]
      by_cases hl : l = i ∨  l = j
      · simp [hl]
        obtain h'|h':= hl
        · simp [← h'] at hk ; exact hk
        · simp [← h'] at hk'; exact hk'
      ·  simp [hl, one_apply]
      simp [hk, hk']




lemma G2ij_Triangular_mul_apply {P T : GL n F} (hP : P ∈ G2ij hij) (hT : T ∈ TriangularGroup) :
    P * T = Matrix.of fun k l =>
      if k = i then P i i * T i l + P i j * T j l
        else if k = j then P j j * T j l + P j i * T i l
          else (T k l : F)
            :=by
  simp [G2ij, GL2toGLn, M2toMn] at hP
  rcases hP with ⟨M,hP⟩
  apply_fun fun x => x.val at hP
  simp at hP
  ext k l
  by_cases hi : k = i
  · simp [hi,mul_apply]
    have (m:n):P i m * T m l = if m = i then P i i * T i l else if m =j then P i j * T j l else 0 := by
      simp [← hP]
      by_cases h : m=i
      · simp [h]
      · by_cases h' : m = j
        · simp [h',(ne_of_lt hij).symm]
        · simp [h,h', e2_ij]
    have : ∑m : n, P i m * T m l =
      ∑ m : n, if m = i then P i i * T i l else if m =j then P i j * T j l else 0 := by
      simp [← this]
    rw [this]

    have : (∑ m : n, if m = i then P i i * T i l else if m =j then P i j * T j l else 0 )
      =  P i i * T i l + ∑ m ∈  { m | m ≠ i},P i j * T j l * if j = m then 1 else 0 := by
        sorry
    rw [this, Finset.sum_mul_boole]
    simp [(ne_of_lt hij).symm]
  · by_cases hj : k = j
    · sorry
    · simp [hi, hj, mul_apply]
      have (m : n): P k m = if m = k then 1 else 0  :=by
        simp [← hP, hi, hj, e2_ij]
        · by_cases h : m = k
          · simp [h,hi,hj]
          · simp [h,hi,hj]
            by_cases m =i ∨ m =j
            · simp [*]
            · simp [*, one_apply,(ne_eq m k▸ h).symm]
      simp [this]

lemma Triangular_G2ij_mul_apply {P T : GL n F} (hP : P ∈ G2ij hij) (hT : T ∈ TriangularGroup) :
    T * P = Matrix.of fun k l =>
      if l = i then P i i * T k i + P j i * T k j
        else if l = j then P j j * T k j + P i j * T k i
          else (T k l : F)
            :=by
 sorry

lemma Gij_comm_B : (G2ij hij : Subgroup (GL n F)).carrier * TriangularGroup.carrier ⊆
    TriangularGroup.carrier * (G2ij hij).carrier:= by
  intro M ⟨P,PinG2ij, T, TinTriangularGroup, M_eq_PT⟩

  sorry


def S₀ : Matrix (Fin 2) (Fin 2) F := Matrix.of fun k l => if k = l then 0 else 1

lemma self_inverse_S₀ : S₀ * S₀ = (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext k l
    simp [S₀,one_apply, mul_apply]
    match k,l with
    |0,0 => simp
    |0,1 => simp
    |1,0 => simp
    |1,1 => simp

def  S : GL (Fin 2) F := ⟨S₀,S₀, self_inverse_S₀, self_inverse_S₀⟩

@[simp]
lemma self_inverse_S : S * S = (1 : GL (Fin 2) F):= by
  apply Units.ext ; simp [S, self_inverse_S₀]

lemma self_inverse_S' : S = (S⁻¹ : GL (Fin 2) F):= by
  apply Units.ext ; simp [S, self_inverse_S₀]

lemma SwapMatrixij_mapsto_S :
    (PermMatrix_Hom (swap i j) : GL n F) = GL2toGLn hij S:=by
  apply Units.ext
  simp [GL2toGLn, M2toMn, PermMatrix_Hom, _PermMatrix_Hom, PermMatrix]
  ext k l
  simp [e2_ij, equiv2_ij, S₀, S]
  by_cases hk : k = i ∨ k = j
  · by_cases hl : l = i ∨ l = j
    · simp [hk,hl,(ne_of_lt hij).symm]
      obtain hk|hk := hk <;> obtain hl|hl := hl <;> simp [hk, (ne_of_lt hij).symm, hl, ne_of_lt hij]
    · simp [hk, hl]
      intro h
      apply hl
      obtain hk|hk := hk
      on_goal 1 => right
      on_goal 2 => left
      all_goals  simp [hk] at h; apply_fun swap i j ; simp [← h]
  · push_neg at hk
    simp [hk]
    · by_cases hl : l = i ∨ l =j
      · simp [hl]
        intro h
        obtain hl|hl := hl
        · simp [hl] at h ; exact hk.2 h
        . simp [hl] at h ; exact hk.1 h
      · push_neg at hl
        simp [hk,hl, one_apply, swap_apply_def]

lemma SwapMatrixij_mem_Gij :
    (PermMatrix_Hom (swap i j) : GL n F) ∈ G2ij hij :=by
  simp [G2ij]
  use S
  apply (SwapMatrixij_mapsto_S hij).symm

lemma GijTriangular_map_GL2Triangular_aux (M : G2ij hij) (coe_f : sij i j → n)
    (hcoe_f : coe_f = fun x => x.val):
      (M.val.val.submatrix (coe_f ∘ ⇑(equiv2_ij hij)) (coe_f ∘ ⇑(equiv2_ij hij))).fromBlocks 0 0 1
         (Sum.map (⇑(equiv2_ij hij).symm) id ((sumCompl fun x ↦ x = i ∨ x = j).symm k))
            (Sum.map (⇑(equiv2_ij hij).symm) id ((sumCompl fun x ↦ x = i ∨ x = j).symm l)) =
              (M.val.val k l : F)
              := by
    have neqkl {k l :n} (hk : k=i ∨ k=j) (hl : ¬ (l = i ∨ l = j)) : k ≠ l := by
        obtain hk|hk := hk
        all_goals simp [hk] at hl ⊢ ;simp [(ne_eq l j ▸ hl.right).symm, (ne_eq l i ▸ hl.left).symm]
    simp [hcoe_f]
    by_cases hk : k=i ∨ k=j
    · by_cases hl : l=i ∨ l=j
      · simp [hk,hl,fromBlocks_apply₁₁]
      · simp [hk,hl,not_ij_or_diag_of_mem_G2ij, neqkl hk hl]
    · by_cases hl : l=i ∨ l=j
      · simp [hk,hl,fromBlocks_apply₁₁, not_ij_or_diag_of_mem_G2ij, (neqkl hl hk).symm]
      · simp [hk,hl,one_apply, not_ij_or_diag_of_mem_G2ij]



lemma GijTriangular_map_GL2Triangular :
    TriangularGroup.subgroupOf (G2ij hij) =
      (TriangularGroup : Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom  :=by
  ext M
  constructor
  · intro h
    simp [Subgroup.mem_subgroupOf  ]  at h
    let coe_f : sij i j -> n := fun x => x.val
    let M₀: Matrix (Fin 2) (Fin 2) F :=
      M.val.val.submatrix (coe_f ∘ equiv2_ij hij) (coe_f ∘ equiv2_ij hij)
    have : M₀ 1 0 = 0 :=by simp [M₀, equiv2_ij,h hij]
    have : IsUnit M₀.det := by
      simp [det_fin_two, this]
      let Mdiag_ne_zero:= fun x => isUnit_iff_ne_zero.mp (diag_invertible_of_triangularGroup M.val h x)
      simp [M₀,equiv2_ij,coe_f, Mdiag_ne_zero i, Mdiag_ne_zero j]
    have : IsUnit M₀:= (isUnit_iff_isUnit_det M₀).mpr this
    rcases this with ⟨M₀' : GL (Fin 2) F,h'⟩
    use M₀'
    constructor
    · intro k l
      match k,l with
      |0,0 => simp
      |0,1 => simp
      |1,1 => simp
      |1,0 => simp [h',M₀, equiv2_ij,h hij]
    apply Subgroup.subtype_injective
    apply Units.ext
    rw [Subgroup.coeSubtype]
    simp [GL2toG2ij_coe, h', M₀]
    ext k l
    simp [Units.coe_map, M2toMn, Matrix.fromBlocks_apply₁₁,e2_ij]
    apply GijTriangular_map_GL2Triangular_aux
    rfl

  · intro ⟨M₀, M₀triangular,hM₀ ⟩
    simp [Subgroup.mem_subgroupOf, TriangularGroup, BlockTriangularGroup, ← hM₀]  at M₀triangular ⊢
    simp [GL2toG2ij_coe, BlockTriangular, M2toMn,e2_ij] at *
    intro k l hkl
    by_cases hk: k=i
    · have : ¬ (l = i ∨ l =j):= by
        by_contra h
        cases h
        · simp [*] at hkl
        · simp [*] at hkl
          exact lt_irrefl i <| lt_trans hij hkl
      simp [hk, this]
    · by_cases hk' : k=j
      · by_cases hl: l =i
        · have : (0 : Fin 2) < 1  := by simp [Fin.lt_def]
          simp [hl, hk', equiv2_ij, (ne_of_lt hij).symm, ← M₀triangular this]
        · have : ¬ (l = i ∨  l = j):= by
            intro h
            obtain h|h := h
            · exact hl h
            · simp [h,hk'] at hkl
          simp [this,hk']
      · simp [hk,hk']
        by_cases hl : l=i ∨ l= j
        · simp [hl]
        · simp [hl, one_apply, (ne_of_lt hkl).symm]


lemma GijTriangular_map_GL2Triangular' :
    (GL2toG2ij hij).symm '' (TriangularGroup.subgroupOf (G2ij hij)).carrier  =
      (TriangularGroup : Subgroup (GL (Fin 2) F)).carrier  :=by
  have h: TriangularGroup.subgroupOf (G2ij hij) =
      (TriangularGroup : Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom :=
        GijTriangular_map_GL2Triangular hij
  rw [h]
  ext
  constructor
  · intro ⟨y,hy,hy'⟩
    rcases hy with ⟨y0,y0triangular,hy0⟩
    simp [← hy', ← hy0]
    apply y0triangular
  · intro xTriangular
    simp [Subgroup.mem_carrier.mp xTriangular]

lemma ConjugatedSubgroup_map_GL2Triangular (P :PermMatrixGroup) :
    (ConjugatedSubgroup TriangularGroup P.val ).subgroupOf (G2ij hij) =
      (TriangularGroup : Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom ∨
        (ConjugatedSubgroup TriangularGroup P.val ).subgroupOf (G2ij hij) =
          (BlockTriangularGroup (·+1): Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom :=by

  rcases (PermMatrixGroup_mem_iff P.1).mp P.2  with ⟨f,hf⟩
  have permMatrix_inv : (PermMatrix f)⁻¹ = (PermMatrix f⁻¹ : Matrix n n F) := by
    rw [← PermMatrix_Homcoe, ← PermMatrix_Homcoe]
    simp [PermMatrix_Hom]
  by_cases h :  f⁻¹ i < f⁻¹  j
  · left
    rw [← GijTriangular_map_GL2Triangular]
    ext M
    simp [ConjugatedSubgroup, TriangularGroup, BlockTriangularGroup, Subgroup.mem_subgroupOf]
    simp [BlockTriangular,hf, permMatrix_inv, PermMatrix_mul,mul_PermMatrix]
    constructor
    · intro hM k l hkl
      by_cases hk : k = i
      · simp [hk] at hkl ⊢
        rw [not_ij_or_diag_of_mem_G2ij]
        simp[(ne_of_lt hkl).symm]
        push_neg
        simp [ne_of_lt hkl]
        intro leqj
        rw [leqj] at hkl
        apply not_lt_of_lt hkl hij
      · by_cases h'k : k = j
        · by_cases hl : l=i
          · simp [h'k, hl, ← hM h]
          · rw [not_ij_or_diag_of_mem_G2ij]
            simp [(ne_of_lt  hkl).symm]
            push_neg
            simp [h'k] at hkl ⊢
            simp [(ne_eq l j) ▸ ne_of_lt hkl, hl]
        · rw [not_ij_or_diag_of_mem_G2ij]
          · simp [(ne_of_lt hkl).symm]
          · simp [hk, h'k]
    intro hM k l hkl
    by_cases hfk : f k = i
    · simp [hfk] at hkl ⊢
      rw [not_ij_or_diag_of_mem_G2ij]
      simp
      · intro hfl
        simp [hfl] at hfk
        apply ne_of_lt hkl hfk.symm
      simp
      constructor
      · intro hfl; simp [← hfl] at hfk ; apply ne_of_lt hkl hfk.symm
      · intro hfl
        have :k = f⁻¹ i ∧ l = f⁻¹ j := by simp [← hfk, ← hfl]
        simp [this] at hkl
        apply lt_irrefl (f⁻¹ j) (lt_trans hkl h)
    · by_cases h'fk : f k = j
      · by_cases hfl : f l = i
        · simp [h'fk,hfl ] at hkl ⊢
          exact hM hij
        · rw [not_ij_or_diag_of_mem_G2ij]
          · simp
            intro kl
            apply (ne_of_lt hkl) kl.symm
          · simp [hfl, hfk, h'fk]
            simp [← h'fk, (ne_of_lt hkl)]
      · rw [not_ij_or_diag_of_mem_G2ij]
        · simp [(ne_of_lt hkl).symm]
        · simp [hfk, h'fk]
  · right
    simp at h
    have h : f⁻¹ j < f⁻¹ i := lt_of_le_of_ne h (by simp [(ne_of_lt hij).symm])
    ext M
    simp [ConjugatedSubgroup, TriangularGroup, Subgroup.mem_subgroupOf, BlockTriangularGroup]
    simp [BlockTriangular,hf, permMatrix_inv, PermMatrix_mul,mul_PermMatrix]
    constructor
    · intro hM
      use (GL2toG2ij hij).symm M
      simp
      intro k l hkl
      match k,l with
      |0,0 => simp at hkl
      |1,0 => simp at hkl
      |1,1 => simp at hkl
      |0,1 => have := hM h
              simp at this
              simp [GL2toG2ij_symm_apply, invGL2toG2ij, equiv2_ij, this, nonsingInvUnit]
    · intro ⟨M',M'triangular, hM'⟩ k l hkl
      by_cases hfk : f k = j
      · simp [hfk] at hkl ⊢
        rw [not_ij_or_diag_of_mem_G2ij]
        simp
        · intro hfl
          simp [hfl] at hfk
          apply ne_of_lt hkl hfk.symm
        simp
        constructor
        · intro hfl
          have :k = f⁻¹ j ∧ l = f⁻¹ i := by simp [← hfk, ← hfl]
          simp [this] at hkl
          apply lt_irrefl (f⁻¹ i) (lt_trans hkl h)
        · intro hfl; simp [← hfl] at hfk ; apply ne_of_lt hkl hfk.symm
      · by_cases h'fk : f k = i
        · by_cases hfl : f l = j
          · simp [h'fk,hfl, ← hM' ] at hkl ⊢
            simp [GL2toG2ij_coe, M2toMn, e2_ij, equiv2_ij, (ne_of_lt hij).symm]
            apply M'triangular
            simp
          · rw [not_ij_or_diag_of_mem_G2ij]
            · simp
              intro kl
              apply (ne_of_lt hkl) kl.symm
            · simp [hfl, hfk, h'fk]
              simp [← h'fk, (ne_of_lt hkl)]
        · rw [not_ij_or_diag_of_mem_G2ij]
          · simp [(ne_of_lt hkl).symm]
          · simp [hfk, h'fk]

lemma ConjugatedSubgroup_map_GL2Triangular' (M : MonomialGroup) :
    (ConjugatedSubgroup TriangularGroup M.val ).subgroupOf (G2ij hij) =
      (TriangularGroup : Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom ∨
        (ConjugatedSubgroup TriangularGroup M.val ).subgroupOf (G2ij hij) =
          (BlockTriangularGroup (·+1): Subgroup (GL (Fin 2) F)).map (GL2toG2ij hij).toMonoidHom :=by
  rcases monomial_decomposition M with ⟨P,P_PermMatrix,D,D_diag,MeqPD⟩
  let D': TriangularGroup := ⟨D,diagonalGroup_le_blockTriangularGroup id D_diag⟩
  have : M.val = P *D'  := by simp [D',MeqPD]
  rw [← conjugatedSubgroup_mul_right_eq TriangularGroup this]
  apply ConjugatedSubgroup_map_GL2Triangular hij ⟨P,P_PermMatrix⟩

lemma ConjugatedSubgroup_map_GL2Triangular'' (M : MonomialGroup):
    (GL2toG2ij hij).symm '' ((ConjugatedSubgroup TriangularGroup M.1).subgroupOf (G2ij hij)).carrier=
      (TriangularGroup : Subgroup (GL (Fin 2) F)).carrier ∨
        (GL2toG2ij hij).symm ''
          ((ConjugatedSubgroup TriangularGroup M.1).subgroupOf (G2ij hij)).carrier =
            (BlockTriangularGroup (·+1)).carrier :=by
  obtain h|h := ConjugatedSubgroup_map_GL2Triangular' hij M
  · left ; rw [h]; ext x; simp
  · right; rw [h]; ext x; simp

lemma ltFin2 {k l : Fin 2} (hkl : k < l)  : k = 0 ∧ l = 1:=by
  match k, l with
  | 0,0 => simp at hkl | 0,1 => simp| 1,0 => simp at hkl| 1,1 => simp at hkl

lemma GL2Triangular_mem_iff (M : GL (Fin 2) F) : M ∈ TriangularGroup ↔ M 1 0 = 0  := by
  simp [TriangularGroup,BlockTriangularGroup,BlockTriangular]
  constructor
  · intro h
    apply h
    simp
  · intro h i j hij
    simp [ltFin2 hij, h]

lemma GL2LowerTriangular_mem_iff (M : GL (Fin 2) F) :
    M ∈ BlockTriangularGroup (·+1) ↔ M 0 1 = 0  := by
  simp [BlockTriangularGroup,BlockTriangular]
  constructor
  · intro h
    apply h
    simp
  · intro h i j hij
    have  := ltFin2 hij
    simp at this
    have : j = 1 ∧ i = 0 := by
      simp [this]
      apply_fun fun x => x+1
      simp [this]
      exact fun a b h => by simp at h ; assumption
    simp [this, h]

lemma LowerTriangular_sub_doubleCoset_union :
    {S * (T.val : GL (Fin 2) F) * S| T : TriangularGroup} ⊆
     C TriangularGroup S ∪ C TriangularGroup (S*S)  := by
  simp [doubleCoset_one]
  intro M ⟨T,Ttriangular, hM⟩
  by_cases h : M ∈ TriangularGroup
  · simp [h]
  · simp [h]
    let U₀ : Matrix (Fin 2) (Fin 2) F := of fun i j=> match i,j with
      |0,0 => 1 |  0,1 => M 0 0/(M 1 0) | 1,0 => 0 | 1,1 => 1
    have :U₀.det = 1 := by simp [Matrix.det_fin_two, U₀ ]
    rcases (Matrix.isUnit_iff_isUnit_det U₀).mpr (this ▸ isUnit_one)  with ⟨(U: GL (Fin 2) F),hU⟩
    let V₀ : Matrix (Fin 2) (Fin 2) F := of fun i j=> match i,j with
      |0,0 => M 1 0 |  0,1 => M 1 1 | 1,0 => 0 | 1,1 => - (M 1 1) * (M 0 0) / (M 1 0)
    have M01_eq_zero: M 0 1 = 0  := by
      simp [← hM, mul_apply, S, S₀]
      apply  Ttriangular (by simp : (0 : Fin 2) < 1)
    have (k l : Fin 2) : M k l = 0 ↔ k = 0 ∧ l = 1 := by
      constructor
      swap
      · intro h
        simp [h, M01_eq_zero]
      match k,l with
      |0,0 => simp ;
              intro h
              have := M.val.det_fin_two
              simp [h, M01_eq_zero] at this
              apply IsUnit.ne_zero (Matrix.isUnits_det_units M) this
      |0,1 => simp [M01_eq_zero]
      |1,1 => simp ;
              intro h
              have := M.val.det_fin_two
              simp [h, M01_eq_zero] at this
              apply IsUnit.ne_zero (Matrix.isUnits_det_units M) this
      |1,0 => intro h'
              have : M ∈ TriangularGroup:=by
                intro i j hij
                match i, j with
                | 0, 0 => simp at hij
                | 1, 1 => simp at hij
                | 0, 1 => simp at hij
                | 1, 0 => exact h'
              simp [h this]
    have isUnit_det_V₀: IsUnit V₀.det := by simp [det_fin_two,V₀, M01_eq_zero,this]
    rcases (Matrix.isUnit_iff_isUnit_det V₀).mpr isUnit_det_V₀ with ⟨(V: GL (Fin 2) F),hV⟩
    use U, (GL2Triangular_mem_iff U).mpr (by simp [hU, U₀]),V
    use (GL2Triangular_mem_iff V).mpr (by simp [hV, V₀ ])
    apply Units.ext
    ext i j
    simp [hU,hV,S,U₀,V₀,S₀, mul_apply]
    match i,j with
    | 0, 0 => simp ; rw [div_mul_comm, div_self, one_mul] ; simp [this]
    | 0, 1 => simp [M01_eq_zero] ;
              rw [div_mul_comm,← mul_div_right_comm,← add_div, add_neg_self, zero_div]
    | 1, 0 => simp
    | 1, 1 => simp

lemma lowerTriangular_nsub_triangular :
    ¬ {S * (T.val : GL (Fin 2) F) * S| T : TriangularGroup} ⊆ TriangularGroup.carrier := by
  apply Set.not_subset.mpr
  use S*T*S
  simp [triangularT]
  simp [GL2Triangular_mem_iff, mul_apply, S,S₀, T, T₀, GeneralLinearGroup.mk'', nonsingInvUnit]

lemma univ_eq_triangular_union_triangular_S_triangular : (Set.univ : Set (GL (Fin 2) F)) =
    TriangularGroup.carrier ∪ TriangularGroup.carrier * {S} * TriangularGroup.carrier :=by
  rw [← doubleCoset_eq_doubleProd_singleton TriangularGroup S]
  let H : Subgroup (GL (Fin 2) F) := B_union_C_of_simple TriangularGroup self_inverse_S
      LowerTriangular_sub_doubleCoset_union lowerTriangular_nsub_triangular
  ext x
  simp
  suffices ⊤ ≤ H by
    have := this (Subgroup.mem_top x)
    rw [← H.mem_carrier] at this
    simp [H, B_union_C_of_simple] at this
    exact this
  have Monomial_le_H: MonomialGroup ≤ H := by
    intro M hM
    rcases monomial_decomposition ⟨M,hM⟩ with ⟨P,P_PermMatrix,D,D_diag,h⟩
    simp at h
    rw [h, ← H.mem_carrier]
    apply H.mul_mem
    · simp [PermMatrixGroup_mem_iff] at P_PermMatrix
      rcases P_PermMatrix with ⟨f,hP⟩
      rw [← hP]
      obtain h|h := @Perm.perm_fin_two f (fun f ↦  f = 1 ∨ f = Equiv.swap 0 1) rfl
      · simp [h, H.one_mem]
      · have : PermMatrix_Hom f = (S : GL (Fin 2) F) := by
          ext i j
          simp [PermMatrix_Hom, PermMatrix, _PermMatrix_Hom, S, S₀, h ]
          match i,j with
          |0,0 => simp |0,1 => simp |1,0 => simp |1,1 => simp
        rw [this]
        simp [H, B_union_C_of_simple]
        right
        use 1, TriangularGroup.one_mem, 1, TriangularGroup.one_mem
        group
    · simp [H, B_union_C_of_simple]
      left
      exact diagonalGroup_le_blockTriangularGroup id D_diag
  have :TriangularGroup ≤ H :=by
    intro T
    simp [H, B_union_C_of_simple]
    intro h
    exact Or.inl h
  apply le_trans
  swap
  · apply sup_le Monomial_le_H this
  · rw [BruhatDecomposition]



lemma LowerTriangular_conj_Triangular :
    (BlockTriangularGroup (· + 1)).carrier = {(S: GL (Fin 2) F)} * TriangularGroup.carrier * {S} :=by
  ext M
  rw [self_inverse_S']
  simp [TriangularGroup, BlockTriangularGroup, BlockTriangular]
  constructor
  · intro Mtriangular i j hij
    simp [S, S₀, mul_apply, ltFin2 hij, Mtriangular]
  · intro h i j hij
    have h := h hij
    simp [S, S₀, mul_apply, ltFin2 hij ] at h
    have := ltFin2 hij
    simp at this
    have : j = 1 ∧ i = 0 := by
      simp [this]
      apply_fun fun x => x+1
      simp [this]
      exact fun a b h => by simp at h ; assumption
    simp [this,h]

lemma univ_eq_triangular_lower_triangular_union_triangular_S_triangular' : (Set.univ : Set (GL (Fin 2) F)) =
    TriangularGroup.carrier * (BlockTriangularGroup (·+1)).carrier ∪
      TriangularGroup.carrier * {S} * (BlockTriangularGroup (· + 1)).carrier :=by
  have : (Set.univ : Set (GL (Fin 2) F)) * {S} = Set.univ := by
    ext x
    simp
    use x * S ⁻¹
    simp
  apply Set.mul_singleton_injective S
  rw [Set.union_mul, LowerTriangular_conj_Triangular, mul_assoc, mul_assoc,this]
  rw [Set.singleton_mul_singleton, self_inverse_S]
  simp_rw [mul_assoc]
  rw [Set.singleton_mul_singleton, self_inverse_S]
  simp_rw [← mul_assoc]
  nth_rw 2 [mul_assoc TriangularGroup.carrier]
  rw [Set.singleton_mul_singleton, self_inverse_S, Set.union_comm]
  simp [univ_eq_triangular_union_triangular_S_triangular, subgroup_mul]



lemma GLprop5aux_1 (B Gij B':Subgroup (GL n F)) (Pij: (MonomialGroup : Subgroup (GL n F)))
  (hGij : Gij = G2ij hij)  (hPij : PermMatrix_Hom_to_Monomial (swap i j) = Pij )
    (BTriangular : B = TriangularGroup)
      (h : ↑Gij ⊆ ↑(B ⊓ Gij) * (B' ⊓ Gij).carrier ∪ ↑(B ⊓ Gij) * {↑Pij} * ↑(B' ⊓ Gij) ) :
      {↑Pij} * B.carrier ⊆ ↑B * ↑B' ∪ ↑B * {Pij.val} * ↑B' := by
  suffices B.carrier * Gij.carrier ⊆ B*B' ∪ B*{↑Pij} * B' by
    apply subset_trans
    swap
    · exact this
    · simp [Set.singleton_mul,Set.mem_mul]
      intro x h
      simp at h
      simp [BTriangular, hGij]
      apply Gij_comm_B
      use Pij, hPij ▸ SwapMatrixij_mem_Gij hij, Pij⁻¹ * x, BTriangular ▸ h
      simp
  have:↑Gij ⊆ B.carrier * ↑B' ∪ ↑B * {↑Pij} * ↑B' →↑B * Gij.carrier ⊆ ↑B * ↑B' ∪ ↑B * {↑Pij} * ↑B':= by
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

theorem GLprop5aux_2 (B B' Gij : Subgroup (GL n F)) (P : GL n F) (P2 : Gij) (B2 B2' : Subgroup Gij)
  (hB : B2 = B.subgroupOf Gij) (hB' : B2' = B'.subgroupOf Gij) (hP : P2.val = P) (hPin : P ∈ Gij)
    (h₀ : ↑(⊤ : Subgroup Gij) = ↑B2 * B2'.carrier ∪  ↑B2 * {P2} * B2'.carrier) :
      ↑Gij ⊆ ↑(B ⊓ Gij) * (B' ⊓ Gij).carrier ∪ ↑(B ⊓ Gij) * {P} * ↑(B' ⊓ Gij):= by
  intro x h
  obtain ⟨b,binB2,b',b'inB2',h⟩| ⟨b,binB2,b',b'inB2',h⟩ := subset_of_eq h₀ (Subgroup.mem_top ⟨x,h⟩)
  · left
    simp [hB,hB', Subgroup.mem_subgroupOf] at binB2 b'inB2'
    use b.val, ⟨binB2,b.2⟩, b'.val, ⟨b'inB2',b'.2⟩
    apply_fun Subgroup.subtype Gij at h
    simp at h
    assumption
  · right
    simp [Subgroup.coe_inf, Set.mem_mul]
    simp [hP,hB,hB', Subgroup.mem_subgroupOf] at binB2 b'inB2'
    use b
    constructor
    · constructor
      · apply binB2
      · apply Gij.mul_mem b.2
        simp [hPin]
    use  b', ⟨b'inB2',b'.2⟩
    apply_fun Subgroup.subtype Gij at h
    simp at h
    assumption

theorem GLprop5 : ∀ (M Ma : MonomialGroup) (a : A), MonomialCoxeterHom A Ma = (CM A).simple a ->
    {(Ma.val * b.val * M.val : GL n F) | b : TriangularGroup} ⊆
      DoubleCoset TriangularGroup (Ma * M).val∪ DoubleCoset TriangularGroup M.val := by
  intro M Ma a
  revert Ma
  apply (prop5_iff TriangularGroup (monomialCoxeterHom_surj A) (prop3 A) M a).mpr
  rcases M_simples_are_swaps' A n a with  ⟨i,j,hij, h⟩
  let Pij : (MonomialGroup : Subgroup (GL n F)) := PermMatrix_Hom_to_Monomial (swap i j)
  use Pij, swapPerm_mapsto_simple A h

  let B : Subgroup (GL n F):= TriangularGroup
  let B': Subgroup (GL n F):= ConjugatedSubgroup B ↑M
  let Gij : Subgroup (GL n F) := G2ij hij

  apply prop5' B B' Pij M (by simp [B'])
  apply GLprop5aux_1 hij B Gij B' Pij (by simp [Gij]) (by simp[Pij]) (by simp[B])

  let B2 := B.subgroupOf Gij
  let B2' := B'.subgroupOf Gij
  let Pij' : Gij := ⟨Pij.val, SwapMatrixij_mem_Gij hij ⟩

  apply GLprop5aux_2 B B' Gij Pij'.val Pij' B2 B2' rfl rfl rfl (SwapMatrixij_mem_Gij hij)
  let GL2toGij : GL (Fin 2) F ≃* Gij := GL2toG2ij hij
  apply_fun Set.image GL2toGij.symm
  swap
  · simp [MulEquiv.injective]
  have : GL2toGij.symm '' Set.univ = (Set.univ: Set (GL (Fin 2) F)) :=
    Set.ext fun x => Iff.intro (fun _ => Set.mem_univ x)  fun _ => ⟨GL2toGij x, by simp⟩
  dsimp
  rw [this, Set.image_union]
  simp_rw [Set.mul_of_mul_image_of_MulEquiv GL2toGij.symm]
  rw [Set.image_singleton]
  dsimp [GL2toGij, B2, B]
  have : ↑(TriangularGroup.subgroupOf Gij) = (TriangularGroup.subgroupOf Gij).carrier := rfl
  rw [this, GijTriangular_map_GL2Triangular']
  have : GL2toGij.symm Pij' = S:= by
    simp [Pij', Pij, SwapMatrixij_mapsto_S hij, PermMatrix_Hom_to_Monomial, GL2toGij]
    rw [MulEquiv.symm_apply_eq]
    apply Subgroup.subtype_injective
    apply Units.ext
    simp [GL2toG2ij_coe, GL2toGLn]
  obtain h|h := ConjugatedSubgroup_map_GL2Triangular'' hij M
  · rw [h, subgroup_mul, univ_eq_triangular_union_triangular_S_triangular, this]
  · rw [h, univ_eq_triangular_lower_triangular_union_triangular_S_triangular',this]
