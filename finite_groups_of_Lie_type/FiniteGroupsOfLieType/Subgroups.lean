import FiniteGroupsOfLieType.Basic

variable {G : Type*} [Group G] {A : Type*}
variable (TS : BNMphiQuadruplet G A)

open Subgroup CoxeterSystem Function MonoidHom Set
open scoped Pointwise
section DoubleCoset
/--The bijection between the Weyl group `TS.W` of the `BNMphiQuadruplet` and the set of double Cosets.-/
noncomputable
def Weyl_doubleCosets_equiv' : TS.W  ≃  {C TS.B w | w : TS.N} :=
    f'range_eq_doubleCosets TS ▸ Weyl_doubleCosets_equiv TS

-- Bourbaki 7
theorem DoubleCoset.prodeq_iff_mul_length_lt (w : TS.W) (a : A) :
    TS.length (TS.simple a * w) > TS.length w ↔
      f' TS (TS.simple a * w) = f' TS (TS.simple a) * (f' TS w)  := by
  sorry
/-
theorem findanametoo (l : List TS.W)  (nonemptyl : l ≠ []) (hnontrivial : 1 ∉ l):
    ∀ w : TS.W, w = l.prod → TS.length w = (l.map TS.length).sum →
      f' TS w = (l.map (f' TS)).prod := by
  induction' l with u t hl
  · exfalso
    apply nonemptyl rfl
  by_cases ht : t = []
  · simp [*]
  intro w
  simp [ht] at hl ⊢
  revert hnontrivial
  rcases CoxeterSystem.exists_reduced_word TS.cs u with ⟨ls,hlength', hu⟩
  simp [hu] at *
  intro a b hw hlength
  clear hu nonemptyl a b
  induction' ls with a ts hls
  · simp
  ·
    simp [CoxeterSystem.wordProd] at hlength' ⊢
    let v := (List.map TS.cs.simple ts).prod
    have  : TS.length (TS.simple a * v) > TS.length v:= by
      simp [ ← hlength',v]
      exact lt_of_le_of_lt (CoxeterSystem.length_wordProd_le TS.cs ts) (by linarith)
    rw [(DoubleCoset.prodeq_iff_mul_length_lt TS v a).mp this]
    by_cases h: v=1
    · rw [h, f'mul_one]
      sorry
    · simp [CoxeterSystem.wordProd] at hls

      have := hls

  apply CoxeterSystem.simple_induction_left TS.cs w--CoxeterSystem.simple_induction TS.cs h
  · intro  a _ hw hlength
    let u := t.prod
    have length_w_gt_length_u : TS.length (TS.simple a * u) > TS.length u:= by
      simp [← hw, hlength,u]
      clear hl ht hlength hw
      induction' t with h' t' ht
      · simp
      · simp
        apply lt_of_le_of_lt
        · apply CoxeterSystem.length_mul_le
        · simp [← add_assoc, add_comm 1]  at ht ⊢
          rw [add_assoc]
          exact add_lt_add_of_le_of_lt (le_refl TS.length h') ht
    have : TS.length (TS.simple a * w) = TS.cs.length w - TS.length (TS.simple a):= by
      obtain h|h := CoxeterSystem.length_simple_mul TS.cs t.prod a
      · simp [hw,h]
      · simp [hw,u,← h] at length_w_gt_length_u
    have : TS.length u = (List.map TS.length t).sum := by
      calc
          TS.length u = TS.length (TS.simple a * w) := by simp [hw]
          _ = TS.length w - TS.length (TS.simple a) := by simp [this]
          _ = (List.map TS.length t).sum := by simp [hlength]
    rw [← hl ht this, ← (DoubleCoset.prodeq_iff_mul_length_lt TS t.prod a).mp length_w_gt_length_u,hw]

  · simp
  · intro w' w'' h' h'' _ hw2 hlength2
-/

end DoubleCoset
section Bsubgroup

def T : Set TS.W := {x : TS.W | ∃ a : A, IsConj x (TS.simple a)}

def Tw (w : TS.W) :Set TS.W  := sorry

-- Bourbaki 5
def BNMphiQuadruplet.simpleClosure (TS : BNMphiQuadruplet G A) (X : Set A) : Subgroup TS.W :=
    Subgroup.closure (TS.simple '' X)

noncomputable
def DoubleCoset_of_Set ( X : Set A) : Subgroup G where
  carrier := ⋃ x ∈ TS.simpleClosure X, f' TS x

  one_mem' := by
    simp
    use 1
    use (TS.simpleClosure X).one_mem
    simp [TS.B.one_mem]

  inv_mem' := by
    simp
    intro x w hw hxw
    use w⁻¹ , (TS.simpleClosure X).inv_mem hw
    simp [f'_inv, hxw]

  mul_mem' := sorry

lemma B_le_DoubleCoset_of_Set (X : Set A) : TS.B ≤ DoubleCoset_of_Set TS X :=by
  intro x h
  simp [DoubleCoset_of_Set]
  use 1, (TS.simpleClosure X).one_mem, ⟨x,h⟩, 1
  simp

noncomputable
def DoubleCoset_of_Set_bij : Set A ≃ {H :Subgroup G // TS.B ≤ H} where
  toFun := fun X => ⟨DoubleCoset_of_Set TS X, B_le_DoubleCoset_of_Set TS X⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

variable {I : Type*} (X : I → SubS TS) (hI : Nonempty I)

theorem Bourba3c :
    DoubleCoset_of_Set TS (⋂ i, X i) = ⨅  i, DoubleCoset_of_Set TS (X i) := by
  sorry

--easy
theorem Dourba3d (X Y : Set A) : X ⊆ Y ↔ DoubleCoset_of_Set TS X ≤ DoubleCoset_of_Set TS Y := by
  sorry

noncomputable
def TSX (X : Set A) {N': Subgroup G} (hN' : N' ≤ TS.N)
    (hN'X : (N'.subgroupOf TS.N).map TS.phi = (TS.simpleClosure X).map TS.cs.mulEquiv.toMonoidHom):
      BNMphiQuadruplet (DoubleCoset_of_Set TS X) A where
  B := TS.B.subgroupOf <| DoubleCoset_of_Set TS X
  N := N'.subgroupOf <| DoubleCoset_of_Set TS X
  M := sorry --Matrix.of fun i j => TS.M i j
  phi := sorry -- TS.phi.restrict (N'.subgroupOf (DoubleCoset_of_Set TS X))
  prop1 := sorry
  prop2 := sorry
  prop3 := sorry
  prop4 := sorry
  prop5 := sorry

def  prop3 {X : Set A} {g : G} (h : ConjugatedSubgroup B g ≤ (DoubleCoset_of_Set_bij TS X) ) :
    g ∈  (DoubleCoset_of_Set_bij TS X).val :=by
  sorry

end Bsubgroup

section Parabolic

def Subgroup.Parabolic (P : Subgroup G) : Prop := ∃g, ConjugatedSubgroup TS.B g ≤ P


lemma parabolic_of_ge_parabolic {P P' : Subgroup G} (hP : P.Parabolic TS) (P'_ge_P : P' ≥ P):
    P'.Parabolic TS :=
  match hP with
  | ⟨g,hP⟩ => ⟨g, le_trans hP P'_ge_P⟩

lemma parabolic_iff (P : Subgroup G) :
    P.Parabolic TS ↔ ∃ X, ∃ g, P = ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X) g :=by
  constructor
  · intro ⟨g, h⟩
    rw [ConjugatedSubgroup_le_iff] at h
    use (DoubleCoset_of_Set_bij TS).symm ⟨ConjugatedSubgroup P g⁻¹, h⟩, g
    simp [ConjugatedSubgroup_one]
  · intro ⟨X, g, h⟩
    use g
    rw [h]
    simp [ConjugatedSubgroup_le_iff]
    exact (DoubleCoset_of_Set_bij TS X).2

lemma parabolic_of_conjugated_parabolic {P : Subgroup G} (h : P.Parabolic TS) (g : G) :
    (ConjugatedSubgroup P g).Parabolic TS :=by
  rcases h with ⟨g',h'⟩
  use g*g'
  rw [← ConjugatedSubgroup_mul, ConjugatedSubgroup_le_iff, ConjugatedSubgroup_mul,
    inv_mul_self, ConjugatedSubgroup_one]
  assumption

lemma prop4b {X X' : Set A} {g g' : G} (h : P = ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X) g )
    (h' : P = ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X') g' ) : X=X' ∧ g' * g⁻¹  ∈ P :=by
  have: ConjugatedSubgroup TS.B (g⁻¹ *g') ≤
      ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X') (g⁻¹ * g'):= by
    simp [ConjugatedSubgroup_le_iff]
    group
    simp
    exact (DoubleCoset_of_Set_bij TS X').2
  nth_rw  2 [← ConjugatedSubgroup_mul] at this
  simp [← h',h, ConjugatedSubgroup_mul] at this
  have  := (DoubleCoset_of_Set_bij TS X).val.inv_mem (prop3 TS this)
  constructor
  · apply_fun DoubleCoset_of_Set_bij TS
    have yes: DoubleCoset_of_Set_bij TS X' =
        ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X) (g'⁻¹*g):= by
      rw [←ConjugatedSubgroup_mul,← h,h',ConjugatedSubgroup_mul, inv_mul_self, ConjugatedSubgroup_one]
    rw [← Subtype.val_inj, yes, ConjugatedSubgroup_mem]
    group at this ⊢
    assumption
  · have : g  * (g⁻¹ *g')  * g⁻¹   ∈ ConjugatedSubgroup (DoubleCoset_of_Set_bij TS X) g :=by
      simp [ConjugatedSubgroup]
      have := (DoubleCoset_of_Set_bij TS X).val.inv_mem this
      group at this ⊢
      assumption
    simp [← h]  at this
    assumption

theorem theorem4a {P P' : Subgroup G} (h : P.Parabolic TS) (h' : P'.Parabolic TS)
    (hinf : (P ⊓ P').Parabolic TS) {g : G} (hg : ConjugatedSubgroup P g ≤ P') : g ∈ P' ∧ P ≤ P'  := by
  sorry

theorem theorem4b {P P' : Subgroup G} (hneq : P ≠ P') (h : P.Parabolic TS) (h' : P'.Parabolic TS)
    (hinf : (P ⊓ P').Parabolic TS) : ∀g, P ≠ ConjugatedSubgroup P' g  := by
  intro g h₀
  apply hneq
  apply le_antisymm
  · rw [← inv_inv g, ← ConjugatedSubgroup_eq_iff] at h₀
    apply (theorem4a TS h h' hinf (le_of_eq h₀)).2
  · apply (theorem4a TS h' h (inf_comm P P' ▸ hinf) (le_of_eq h₀.symm)).2

theorem theorem4c {P₁ P₂ P : Subgroup G} (hP₁ : P₁.Parabolic TS) (hP₂ : P₂.Parabolic TS)
    (hle₁ : P₁ ≤ P) (hle₂ : P₂ ≤ P) {g : G} (hg : ConjugatedSubgroup P₁ g = P₂) : g ∈ P :=
  (theorem4a TS hP₁ (parabolic_of_ge_parabolic TS hP₂ hle₂) (by simp [hle₁,hP₁]) (hg ▸ hle₂)).1

theorem theorem4d {P : Subgroup G} (h : P.Parabolic TS) : P = P.normalizer := by
  apply le_antisymm le_normalizer
  intro g hn
  rw [mem_normalizer_iff] at hn
  have :ConjugatedSubgroup P g⁻¹ = P  := by
    ext h
    simp [ConjugatedSubgroup, ← mul_assoc]
    exact (hn h).symm
  apply inv_inv g ▸ (P.inv_mem <| theorem4c TS h h (le_refl P) (le_refl P) this)

theorem prop5 {P P' : Subgroup G} (h : P.Parabolic TS) (h' : P'.Parabolic TS) :
    ∃ g₀, ConjugatedSubgroup TS.T g₀ ≤ P ⊓ P' := by
  rcases h' with ⟨g',h'⟩
  rcases h with ⟨g,h⟩
  have := doubleCosetDecomp TS ▸ Subgroup.mem_top (g⁻¹ * g')
  rcases this with ⟨x,⟨b,binB,n,ninN,hx⟩,b',b'inB, hg'⟩
  simp [← hx] at hg'
  have : ConjugatedSubgroup TS.T n = TS.T := by
    ext x
    constructor
    · intro h
      simp  [ConjugatedSubgroup]  at h
      constructor
      · have : ⟨n⁻¹ * (x * n), h.2⟩ ∈ TS.T' :=  by simp [mem_subgroupOf, h]
        have := Subgroup.Normal.conj_mem TS.NormalT' ⟨n⁻¹  * (x * n) , h.2⟩ this ⟨n, ninN⟩
        simp [mem_subgroupOf]  at this
        exact this
      · have := TS.N.mul_mem (TS.N.mul_mem ninN h.2) (TS.N.inv_mem ninN)
        simp at this
        exact this
    · intro h
      simp [ConjugatedSubgroup]
      constructor
      · have : ⟨x,h.2⟩ ∈ TS.T'  := by simp [mem_subgroupOf] at h ⊢ ; exact h.1
        have  := Subgroup.Normal.conj_mem TS.NormalT' ⟨x,h.2⟩ this ⟨n,ninN⟩⁻¹
        simp [mem_subgroupOf, mul_assoc]at this
        assumption
      · have := TS.N.mul_mem (TS.N.mul_mem (TS.N.inv_mem ninN) h.2) ninN
        rw [← mul_assoc]
        exact this
  use g*b
  apply le_inf
  · apply le_trans <|(le_Conjugated_subgroup_iff_le TS.T TS.B _).mp inf_le_left
    · rw [← ConjugatedSubgroup_mul, ConjugatedSubgroup_mem TS.B binB]
      assumption
  · have : ConjugatedSubgroup TS.T (g*b)  ≤ ConjugatedSubgroup TS.B (g*b*n*b') := by
      rw [← ConjugatedSubgroup_mul _ b', ConjugatedSubgroup_mem _ b'inB, ←this,ConjugatedSubgroup_mul]
      apply (le_Conjugated_subgroup_iff_le TS.T TS.B _).mp inf_le_left
    simp_rw [mul_assoc] at this hg'
    simp [hg'] at this
    apply le_trans this h'

end Parabolic

section Simplicty
def Subgroup_mul  {B H : Subgroup G} (hH : B ≤ H.normalizer):Subgroup G where
  carrier :=B.carrier * H.carrier
  one_mem' := Set.mem_mul.mp ⟨1, B.one_mem, 1, H.one_mem, mul_one 1⟩
  mul_mem' := by
    intro x y ⟨b,binB,h,hinH,hx⟩ ⟨b',b'inB,h',h'inH, hy⟩
    use b * b', B.mul_mem binB b'inB, b'⁻¹ * h * b' * h'
    have  := ((H.mem_normalizer_iff).mp (hH (B.inv_mem b'inB)) h).mp hinH
    simp at this
    use H.mul_mem this h'inH
    simp [← hx, ← hy]
    group
  inv_mem' := by
    intro _ ⟨b,binB,h,hinH, hx⟩
    simp
    use b⁻¹, B.inv_mem binB
    have  := ((H.mem_normalizer_iff).mp (hH binB) h⁻¹).mp (H.inv_mem hinH)
    simp at this
    use b * h⁻¹ * b⁻¹, this
    simp [← hx]
    group

def Subgroup_mul' (B : Subgroup G) {H : Subgroup G} (hH : H.Normal) : Subgroup G :=
  Subgroup_mul (normalizer_eq_top.mpr hH ▸ le_top: B ≤ H.normalizer)

def mul_Subgroup {B H : Subgroup G}  (hH : B ≤ H.normalizer) : Subgroup G where
  carrier :=H.carrier * B.carrier
  one_mem' := Set.mem_mul.mp ⟨1, H.one_mem, 1, B.one_mem, mul_one 1⟩
  mul_mem' := by
    intro x y ⟨h,hinH,b,binB,hx⟩ ⟨h',h'inH,b',b'inB, hy⟩
    use  h * b * h' * b⁻¹
    have  := ((H.mem_normalizer_iff).mp (hH binB) h').mp h'inH
    simp [mul_assoc]  at this ⊢
    use H.mul_mem hinH this
    simp [← hx, ← hy]
    use b * b', B.mul_mem binB b'inB
    group
  inv_mem' := by
    intro _ ⟨h,hinH,b,binB, hx⟩
    simp
    have  := ((H.mem_normalizer_iff).mp (hH (B.inv_mem binB)) h⁻¹).mp (H.inv_mem hinH)
    simp at this
    use b⁻¹  * h⁻¹ * b, this
    use b⁻¹, B.inv_mem binB
    simp [← hx]

def mul_Subgroup'  {H : Subgroup G} (hH : H.Normal) (B : Subgroup G): Subgroup G :=
  mul_Subgroup (normalizer_eq_top.mpr hH ▸ le_top : B ≤ H.normalizer)

lemma B_le_BH' (B : Subgroup G) {H : Subgroup G} (hH : Normal H) : B ≤ Subgroup_mul' B hH  :=
  fun b hb => ⟨ b, hb, 1, H.one_mem, by simp⟩

lemma B_le_BH {B H : Subgroup G} (hH : B ≤ H.normalizer) : B ≤ Subgroup_mul hH  :=
  fun b hb => ⟨ b, hb, 1, H.one_mem, by simp⟩

lemma H_le_BH {B H : Subgroup G} (hH : B ≤  H.normalizer) : H ≤ Subgroup_mul hH :=
  fun h hh => ⟨1, B.one_mem,h,hh, by simp ; done ⟩

lemma B_le_HB {B H : Subgroup G} (hH : B ≤ H.normalizer) : B ≤ mul_Subgroup hH  :=
  fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩

lemma H_le_HB {B H : Subgroup G} (hH : B ≤  H.normalizer) : H ≤ mul_Subgroup hH :=
  fun h hh => ⟨h,hh,1, B.one_mem, by simp ; done ⟩


lemma map_le_norm { G' : Type*} [Group G'] {B H : Subgroup G} (hH : B ≤  H.normalizer)
  ( f : G →* G') :  B.map f ≤  (H.map f).normalizer :=
    le_trans (map_le_map_iff.mpr (le_trans hH le_sup_left)) (le_normalizer_map f)

@[simp]
lemma Subgroup_mul_map {G' : Type*} [Group G'] (f : G →* G') {B H : Subgroup G}
    (hH : B ≤  H.normalizer)  : (Subgroup_mul hH).map f = Subgroup_mul (map_le_norm hH f) :=by
  ext x
  constructor
  · intro ⟨_,⟨b,binB,h,hinH,hw⟩,hx⟩
    simp [← hw]  at hx
    use f b, mem_map_of_mem f binB, f h, mem_map_of_mem f hinH
  · intro ⟨_,⟨b,binB,fb⟩,_,⟨h,hinH,fh⟩,hx⟩
    simp [← fb, ← fh]  at hx
    use b*h, ⟨b,binB,h,hinH, by simp⟩
    simpa

@[simp]
lemma mul_Subgroup_map { G' : Type*} [Group G']{B H : Subgroup G} (hH : B ≤  H.normalizer)
    ( f : G →* G') : (mul_Subgroup hH).map f = mul_Subgroup (map_le_norm hH f) :=by
  ext x
  constructor
  · intro ⟨_,⟨b,binB,h,hinH,hw⟩,hx⟩
    simp [← hw]  at hx
    use f b, mem_map_of_mem f binB, f h, mem_map_of_mem f hinH
  · intro ⟨_,⟨b,binB,fb⟩,_,⟨h,hinH,fh⟩,hx⟩
    simp [← fb, ← fh]  at hx
    use b*h, ⟨b,binB,h,hinH, by simp⟩
    simpa

lemma lemma2 {H : Subgroup G} (hH : Normal H) :
    ∃ X : Set A, Subgroup_mul' TS.B hH = DoubleCoset_of_Set_bij TS X ∧
      ∀ s1 ∈ TS.simple '' X,∀ s2 ∈ TS.simple '' Xᶜ, Commute s1 s2  := by
  let BH := Subgroup_mul' TS.B hH
  let X := (DoubleCoset_of_Set_bij TS).symm ⟨BH, B_le_BH' TS.B hH⟩
  use X
  have BH_eq_GX : BH = DoubleCoset_of_Set_bij TS X := by simp [X, BH]
  use BH_eq_GX
  intro s1 s1inX s2 s2inXcomp
  simp [Commute, SemiconjBy]
  rcases QuotientGroup.mk'_surjective TS.phi.ker s1 with ⟨n1,hn1⟩
  rcases QuotientGroup.mk'_surjective TS.phi.ker s2 with ⟨n2,hn2⟩
  have : ↑n1 ∈ BH := by
    simp [BH_eq_GX, DoubleCoset_of_Set_bij, DoubleCoset_of_Set]
    use s1
    constructor
    · apply mem_closure.mpr
      intro K h
      exact h s1inX
    · rw [← hn1, f'comm_Quotientgroupmk, f]
      exact DoubleCoset.self_mem TS.B
  have : ∃b ∈ TS.B, b*↑n1 ∈ H:=
    match this with
    |⟨b,binB,h,hinH,hn1⟩ => ⟨b⁻¹ , TS.B.inv_mem binB, by simp [← hn1] ; exact hinH⟩
  rcases this with ⟨b,binB, bn1inH⟩
  let h := n2 * (b * n1) *n2⁻¹
  have hinH: h ∈ H := Normal.conj_mem hH (b * n1) bn1inH ↑n2
  have hinH_prodCs: h ∈ f' TS s2 * f' TS s1 *  f' TS s2 := by
    have :s2 = s2⁻¹ := by
      rcases s2inXcomp with ⟨a,_,ha⟩
      simp [← ha]

    nth_rw 2 [this]
    simp [← hn1, ← hn2]
    rw [← QuotientGroup.mk_inv]
    simp_rw [ f'comm_Quotientgroupmk',f]
    rw [DoubleCoset.mul_apply, Set.mem_mul]
    use 1*n2*b*n1*1, ⟨1, ⟨b,binB⟩,1,rfl⟩, n2⁻¹ , DoubleCoset.self_mem' TS.B n2⁻¹
    simp [h, mul_assoc]
  let l := TS.length (s2*s1*s2)
  have : l ≤ 3 := by match s1inX, s2inXcomp with
    |⟨a,_,h⟩, ⟨a',_,h'⟩ =>
      have := CoxeterSystem.length_wordProd_le TS.cs [a',a,a']
      simp [CoxeterSystem.wordProd, h, h', ← mul_assoc]  at this
      assumption
  by_cases hl : l = 3
  · exfalso
    have : f' TS s2 * f' TS s1 * f' TS s2 = f' TS (s2*s1*s2) := sorry

    have :  (BH.carrier ∩ f' TS (s2*s1*s2)).Nonempty := by
      simp [Set.Nonempty]
      use h
      use ⟨1,TS.B.one_mem,h,hinH, one_mul h⟩ , this ▸ hinH_prodCs
    have  :s2*s1*s2 ∈ TS.simpleClosure X  := by
      simp [BH_eq_GX, Set.Nonempty, DoubleCoset_of_Set_bij, DoubleCoset_of_Set] at this
      rcases this with ⟨x,⟨w,winX,ha⟩, h'⟩
      have : f' TS (s2*s1*s2) = f' TS w  := by
        rcases f'apply' TS (s2*s1*s2) with ⟨u,hu,hu'⟩
        rcases f'apply' TS w with ⟨v,hv,hv'⟩
        simp [hu',hv']
        by_contra h
        have := DoubleCoset.disjoint_of_neq TS.B ↑u ↑v h
        revert this
        simp [Disjoint]
        use {x}
        simp_rw [Set.singleton_subset_iff]
        simp [← hv',← hu',ha,h']
      rw [f'_inj' TS this]
      exact winX
    have : s2 ∈ TS.simple '' X := sorry
    sorry
    --exact s2inXcomp this --simple need to be bij (work in progress I think)
  · have hl :l ≤ 2 := Nat.le_of_lt_succ <| lt_of_le_of_ne this hl
    by_cases hl' : TS.length (s1*s2) = 1
    · have : s1 * s2 ∈ TS.S :=by
        simp
        match (CoxeterSystem.length_eq_one_iff TS.cs).mp hl' with
          |⟨i,h⟩ => exact ⟨i,h.symm⟩
      have : (s1*s2)^2 = 1  := match this with |⟨a,_,h⟩ => by simp [← h]
      calc
        s1*s2 = (s1*s2)^2 * (s1*s2)⁻¹ := by simp [mul_assoc, pow_two]
        _ = (s1*s2)⁻¹ := by rw [this, one_mul]
        _ = s2 * s1 := by have {s : TS.W} (h : s ∈ TS.S): s⁻¹ = s  :=
                            match h with |⟨i,_,h⟩ => by simp [← h]
                          simp
                          rw [this (Set.subset_image_iff.mpr ⟨TS.simple '' X, by simp ,rfl⟩ s1inX),
                          this (Set.subset_image_iff.mpr ⟨TS.simple '' Xᶜ,by simp,rfl⟩ s2inXcomp)]

    by_cases hl'' : TS.length (s1*s2) = 2
    · sorry
    by_cases hl''' : TS.length (s1*s2) = 0
    · exfalso
      simp [CoxeterSystem.length_eq_zero_iff TS.cs,← self_inv_of_mem_S TS s2inXcomp] at hl'''
      rw [hl'''] at s1inX
      exact s2inXcomp.2 s1inX

    · exfalso
      have : TS.length (s1*s2) ≤ 2 := by match X.2 s1inX, s2inXcomp.1 with
      |⟨a,_,h⟩, ⟨a',_,h'⟩ =>
        have := CoxeterSystem.length_wordProd_le TS.cs [a,a']
        simp [CoxeterSystem.wordProd, h, h', ← mul_assoc]  at this
        assumption
      apply not_lt_of_le this
      apply @Nat.two_lt_of_ne (TS.length (s1*s2))
      repeat {rw [ne_eq] ; simp [*, ne_eq]}

def ConjSubgroup (H : Subgroup G) : Subgroup G := ⨆ g:G, ConjugatedSubgroup H g


instance conjSubgroup_normal (H: Subgroup G) : (ConjSubgroup H).Normal where
  conj_mem := by
    intro n ninConj_H g
    simp [ConjSubgroup] at ninConj_H ⊢
    let P  := fun x => g * x * g⁻¹  ∈ ConjSubgroup H
    sorry

lemma ConjSubgroup_le (H :Subgroup G) : H ≤ ConjSubgroup H :=by
  simp [ConjSubgroup]
  have :=  le_iSup (ConjugatedSubgroup H) (1:G)
  simp at this
  assumption

abbrev BNMphiQuadruplet.Z : Subgroup G := ConjSubgroup TS.B

variable (U : Subgroup G) (hU : U ≤ TS.B) (hU' : (U.subgroupOf TS.B).Normal)
variable (hUT : ⊤ = mul_Subgroup' hU' (TS.T.subgroupOf TS.B))

lemma G1T_eq_top : ⊤ = mul_Subgroup' (conjSubgroup_normal U) TS.T :=by
  let G1T := mul_Subgroup' (conjSubgroup_normal U) TS.T
  have BleG1T: TS.B ≤ G1T := by
    intro b h
    rcases  hUT ▸ mem_top (⟨b,h ⟩: TS.B) with ⟨u,uinU,t,tinT,h'⟩
    use u.1, ConjSubgroup_le U uinU, t.1  , tinT
    apply_fun TS.B.subtype at h'
    simp at h' ⊢
    assumption
  have yes : TS.N ≤ TS.T.normalizer  := by
    intro n h
    apply mem_normalizer_iff.mpr
    sorry

  have : TS.N ≤ (ConjSubgroup U).normalizer :=
    normalizer_eq_top.mpr (conjSubgroup_normal U) ▸ le_top
  have : TS.N ≤ G1T.normalizer := by
    intro n ninN
    apply mem_normalizer_iff.mpr
    intro g
    simp [G1T, mul_Subgroup]
    constructor
    · intro ⟨u,uinCjU,t,tinT,h⟩
      use n*u*n⁻¹,(mem_normalizer_iff.mp (this ninN) u).mp uinCjU
      use n*t*n⁻¹,(mem_normalizer_iff.mp (yes ninN) t).mp tinT
      simp [← h]
    · intro ⟨u,uinCjU,t,tinT,h⟩
      have :=  (this (TS.N.inv_mem ninN) u).mp uinCjU
      simp at this ; use n⁻¹*u*n, this
      have :=  (mem_normalizer_iff.mp (yes (TS.N.inv_mem ninN)) t).mp tinT
      simp at this ;  use n⁻¹*t*n, this
      simp ;  group at h ⊢
      rw [mul_assoc, mul_assoc, ← mul_assoc u, h]
      group
  rw [← theorem4d TS ⟨1,(ConjugatedSubgroup_one TS.B).symm ▸ BleG1T⟩] at this
  apply le_antisymm
  · rw [TS.prop1]
    apply sup_le  BleG1T this
  · simp

def α : TS.N.subgroupOf (Subgroup_mul hH) →* TS.N where
  toFun := fun n => ⟨n.1, n.2⟩
  map_one' := by simp
  map_mul':= by simp

lemma G'T_eq_top {H : Subgroup G} (hH : ConjSubgroup U ≤ H.normalizer):
    Set.univ = (Subgroup_mul hH).carrier * TS.T.carrier :=by
  ext x
  simp
  rcases G1T_eq_top TS U hU' hUT ▸ mem_top x with ⟨g1,g1inG1,t,tinT, hx ⟩
  use g1, ⟨g1, g1inG1, 1, H.one_mem, by simp⟩, t, tinT

def TaKatieTaQuitte {H : Subgroup G} (hH:   (ConjSubgroup U) ≤ H.normalizer) :
    BNMphiQuadruplet (Subgroup_mul  hH) A where
  B := TS.B.subgroupOf (Subgroup_mul hH)
  N := TS.N.subgroupOf (Subgroup_mul hH)
  M := TS.M
  phi := TS.phi.comp (α TS)

  prop1 := sorry
  prop2 := sorry
  prop3 := sorry
  prop4 := sorry
  prop5 := sorry


def HnormalinG' {H U :Subgroup G} (hH:  (ConjSubgroup U) ≤ H.normalizer) :
    (H.subgroupOf (Subgroup_mul  hH)).Normal where
  conj_mem :=by
    intro h hinH g
    rcases g.2 with ⟨g',g'inG1, h',h'inH, hg⟩
    simp [mem_subgroupOf, ← hg, mul_assoc] at hinH ⊢
    have := H.mul_mem (H.mul_mem h'inH hinH) (H.inv_mem h'inH)
    have :=  ((H.mem_normalizer_iff).mp (hH g'inG1) (h'*h*h'⁻¹)).mp this
    simp [mul_assoc] at this
    exact this


def CoxeterSystem.irreducible {M : CoxeterMatrix A} (cs : CoxeterSystem M G) : Prop :=
  ∀X : Set A, (∀ a ∈ X, ∀ b ∈ Xᶜ, Commute (cs.simple a) (cs.simple b)) → X = {} ∨ X = Set.univ

def  propR (U : Subgroup G) : Prop :=
  ∀V : Subgroup G,∀ _ : (V.subgroupOf U).Normal,
    ⁅(⊤ :Subgroup  (U⧸(V.subgroupOf U))),⊤ ⁆ = (⊤ :Subgroup  (U⧸(V.subgroupOf U))) → U ≤ V

lemma theorem5_aux0 (g : G) {H: Subgroup G}  (h0: Set.univ = H.carrier * TS.B.carrier):
    ∃ h ∈ H, ConjugatedSubgroup U g = ConjugatedSubgroup U h:= by
  rcases h0 ▸ (mem_univ g) with ⟨h, hinH,b,binB, hg⟩
  use h, hinH
  simp at hg
  rw [←inv_inv g,←hg, ConjugatedSubgroup_eq_iff, ConjugatedSubgroup_mul]
  rw [inv_inv, mul_inv_rev, mul_assoc, mul_left_inv, mul_one b⁻¹]
  ext x
  constructor
  · intro xinU
    simp [ConjugatedSubgroup]
    have :  ⟨b, binB⟩ * (⟨x, hU xinU⟩ * ⟨b,binB⟩⁻¹) ∈ U.subgroupOf TS.B := by
      rw [← mul_assoc]
      apply Subgroup.Normal.conj_mem
      exact hU'
      simp [mem_subgroupOf, xinU]
    simp [mem_subgroupOf] at this
    exact this
  · intro xincU
    simp [ConjugatedSubgroup]  at xincU
    have : ⟨b,binB⟩⁻¹ * ⟨_,hU xincU⟩ * ⟨b,binB⟩⁻¹ ⁻¹ ∈ U.subgroupOf TS.B
        := by
      apply Subgroup.Normal.conj_mem
      exact hU'
      simp [mem_subgroupOf, xincU]
    simp [mem_subgroupOf] at this
    group at this
    exact this

lemma evraigros (H : Subgroup G) : map H.subtype ⊤ = H :=by
  ext x
  constructor <;> simp

theorem theorem5_aux (hH:  (ConjSubgroup U) ≤ H.normalizer) (hirred : TS.cs.irreducible)
  (RU : propR U) (perfectG1 : ⁅ (⊤ : Subgroup (ConjSubgroup U)), ⊤⁆ = (⊤: Subgroup (ConjSubgroup U)))
    (hX1 : Subgroup_mul' (TaKatieTaQuitte TS U hH).B (HnormalinG' hH) =
      (⊤ : Subgroup (Subgroup_mul  hH))) :
        ConjSubgroup U ≤ H := by
  have U_le_Hnorm : U ≤ H.normalizer := by
    apply le_trans
    swap
    · exact hH
    · nth_rw 1 [← ConjugatedSubgroup_one U]
      apply le_iSup
  have : Set.univ = H.carrier * TS.B.carrier := by
    apply_fun (·.map (Subgroup.subtype (Subgroup_mul hH))) at hX1
    simp [Subgroup_mul', Subgroup_mul_map,TaKatieTaQuitte, subgroupOf_map_subtype, evraigros] at hX1
    have HEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEERE (h0 :TS.B ⊓ Subgroup_mul hH ≤ (H ⊓ Subgroup_mul hH).normalizer) :
        Subgroup_mul h0 = mul_Subgroup h0  := by
      ext x
      constructor
      all_goals
      · intro ⟨b,hb,h,hh, hx⟩
        rw [← hx]
        first | apply (mul_Subgroup h0).mul_mem | apply (Subgroup_mul h0).mul_mem
        · use 1, Subgroup.one_mem _, b, hb
          simp
        · use h,hh, 1, Subgroup.one_mem _
          simp
    have Hprop: H ⊓ Subgroup_mul hH = H := by simp [H_le_BH]
    have : (TS.B ⊓ Subgroup_mul hH).carrier * TS.T.carrier = TS.B :=by
      ext x
      constructor
      · intro ⟨b,binBinfH,t, tinT, hx⟩
        simp [← hx]
        apply TS.B.mul_mem ((inf_le_left : TS.B ⊓ Subgroup_mul hH ≤ TS.B) binBinfH) tinT.1
      · intro h
        rcases G1T_eq_top TS U hU' hUT ▸ mem_top x with ⟨g1,g1inG1,t,tinT, hx⟩
        simp at hx
        use x*t⁻¹
        constructor
        · exact ⟨TS.B.mul_mem h (TS.B.inv_mem tinT.1), g1, g1inG1, 1, H.one_mem,by simp [← hx]⟩
        · use t,tinT
          simp
    calc
      Set.univ = (Subgroup_mul  hH).carrier * TS.T.carrier := G'T_eq_top TS U hU' hUT hH
      _ = (mul_Subgroup _).carrier * TS.T.carrier := by rw [← hX1, HEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEERE]
      _ = (H ⊓ Subgroup_mul hH).carrier * (TS.B ⊓ Subgroup_mul hH).carrier * TS.T.carrier
            := by simp [mul_Subgroup]
      _ = H.carrier * TS.B := by rw [set_mul_assoc, this, Hprop]
  have (g:G) : ConjugatedSubgroup U g ≤ mul_Subgroup U_le_Hnorm := by
    rcases theorem5_aux0 TS U hU hU' g this with ⟨h,hinH,hyp⟩
    rw [hyp]
    intro x hx
    simp [ConjugatedSubgroup] at hx
    have : h * (h⁻¹ * (x * h)) *h⁻¹ ∈ mul_Subgroup U U_le_Hnorm := (mul_Subgroup U U_le_Hnorm).mul_mem
      ((mul_Subgroup U U_le_Hnorm).mul_mem (H_le_HB U_le_Hnorm hinH) (B_le_HB U_le_Hnorm hx))
          (H_le_HB U_le_Hnorm (H.inv_mem hinH))
    group at this
    assumption
  have : ConjSubgroup U ≤ mul_Subgroup U_le_Hnorm := iSup_le this
  have : (H.subgroupOf U).Normal  := sorry
  have : (H.subgroupOf (ConjSubgroup U)).Normal  := sorry
  let f : U ⧸ (H.subgroupOf U) ≃* (ConjSubgroup U) ⧸ (H.subgroupOf (ConjSubgroup U)) := sorry
  have :  U ≤ H  := by
    apply RU
    have := perfectG1
    apply_fun (fun x => x.map <| QuotientGroup.mk' (H.subgroupOf (ConjSubgroup U))) at this
    rw [map_commutator, map_top_of_surjective] at this
    apply_fun fun x => x.map f.symm.toMonoidHom at this
    rw [map_commutator, map_top_of_surjective] at this
    simp [this]
    · exact f.symm.surjective
    · exact QuotientGroup.mk'_surjective (H.subgroupOf (ConjSubgroup U))
    · assumption

  intro x h
  let y:= f.symm (QuotientGroup.mk' (H.subgroupOf (ConjSubgroup U)) ⟨x,h⟩)
  rcases QuotientGroup.mk'_surjective (H.subgroupOf U) y with ⟨x',h'⟩
  have : y = 1:=by simp [← h',QuotientGroup.eq_one_iff, mem_subgroupOf, this x'.2]
  simp [y, mem_subgroupOf] at this
  exact this


theorem theorem5 (hH:  (ConjSubgroup U) ≤ H.normalizer) (hirred : TS.cs.irreducible):
    H ≤ ⨅ g, ConjugatedSubgroup TS.B g ∨ ConjSubgroup U ≤ H := by
  rcases lemma2 (TaKatieTaQuitte TS U hH) (HnormalinG' hH) with ⟨X,hX1,hX2⟩
  let TS' := (TaKatieTaQuitte TS U hH)
  have :(∀ a ∈ X, ∀ b ∈ Xᶜ, Commute (TS.simple a) (TS.simple b)):=by
    intro a ainX b binXc
    let s1 := TS'.cs.mulEquiv.symm (TS.cs.mulEquiv (TS.simple a))
    let s2 := TS'.cs.mulEquiv.symm (TS.cs.mulEquiv (TS.simple b))
    have s1inTSX:s1 ∈ TS'.simple '' X  := by
      use a, ainX
      simp [s1, BNMphiQuadruplet.simple,BNMphiQuadruplet.cs, CoxeterSystem.simple]
    have :s2 ∈ TS'.simple '' Xᶜ  := by
      use b, binXc
      simp [s2, BNMphiQuadruplet.simple,BNMphiQuadruplet.cs, CoxeterSystem.simple]

    have  := hX2 s1 s1inTSX s2 this
    simp [Commute, SemiconjBy]
    apply_fun TS.cs.mulEquiv
    simp
    apply_fun TS'.cs.mulEquiv.symm
    simp
    assumption

  obtain h|h :=hirred X this
  · left
    simp [h, DoubleCoset_of_Set_bij, DoubleCoset_of_Set, BNMphiQuadruplet.simpleClosure] at hX1
    simp
    intro g h hinH
    rcases G1T_eq_top TS U hU' hUT ▸ mem_top g  with ⟨g1,g1inG1,t,tinT,hg⟩
    simp at hg
    rw [←hg, ←ConjugatedSubgroup_mul,ConjugatedSubgroup_mem TS.B ((inf_le_left : TS.T ≤ TS.B) tinT), ]
    have : H.subgroupOf (Subgroup_mul (ConjSubgroup U) hH ) ≤ TS'.B := by
      intro h hinH
      have :  h ∈ Subgroup_mul' TS'.B (HnormalinG' hH):= by
        simp [Subgroup_mul', Subgroup_mul]
        rw [← one_mul h, Set.mem_mul]
        use 1, TS'.B.one_mem, h, hinH
      rw [hX1] at this
      exact this
    have : H ≤ TS.B  := fun  x h => mem_subgroupOf.mp <| this <| mem_subgroupOf.mpr
      (by simp [h]:↑(⟨x,H_le_BH hH h⟩:(Subgroup_mul (ConjSubgroup U) hH))∈ H)
    simp [ConjugatedSubgroup, ← mul_assoc]
    apply this
    have  := ((H.mem_normalizer_iff).mp (hH ((ConjSubgroup U).inv_mem g1inG1)) h).mp hinH
    rw [inv_inv] at this
    exact this
  · right

    simp [h] at hX1


end Simplicty

--#lint
/-TODO

Create BN pair and show that they are BNWphiQuadruplet
- PGLn (F)

-/
