/-TODO

Create BN pair and show that they are BNWphiQuadruplet
- PGLn (F)


-/
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.Group
import FiniteGroupsOfLieType.DoubleCosets
import Mathlib.GroupTheory.Coxeter.Length

open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] {A : Type*}

/-- A structure simpler to work on than BN pair by avoiding using quotients.-/
structure BNMphiQuadruplet (G : Type*) [Group G] (A : Type*) where
  /-- The Borel Subgroup of the BN-pair.-/
  B : Subgroup G
  /-- The N subgroup of the BN-pair-/
  N : Subgroup G
  /-- The Coxeter matrix of the group B/(B∩N)-/
  M : CoxeterMatrix A
  /--The projection from N to M.Group ≃ B/(B∩N) -/
  phi : N →* M.Group
  /-- G is generated by N and B.-/
  prop1 : ⊤ = B ⊔ N
  /-- Ensure that phi is a projection-/
  prop2 : Function.Surjective phi
  /-- Ensure that M.Group ≃ B/(B ∩ N)-/
  prop3 : phi.ker = B.subgroupOf N
  /-- For all  ni ∈ N that maps to one of the generators of the Coxeter group B/(B∩N), niBni ≠ B-/
  prop4 : ∀ (ni: N) (i : A) , phi ni = M.simple i -> {(ni :G) * (b : G) * ni | b : B} ≠ B
  /-- For all  ni ∈ N that maps to one of the generators of the Coxeter group B/(B∩N) and n∈N,
  niBn ⊆ Bn niB ∪ BnB-/
  prop5 :  ∀ (n ni : N) (i : A), phi ni = M.simple i ->
            {ni * b.val * n | b : B} ⊆  DoubleCoset B (ni * n) ∪ DoubleCoset B n

variable (TS : (BNMphiQuadruplet G A))
section

variable (B : Subgroup G) {N : Subgroup G} {M : CoxeterMatrix A} {phi : N →* M.Group}
variable (hsurj : Function.Surjective phi) (hker : phi.ker = B.subgroupOf N)
open Set
/--For `w : G` and a subgroup `B` of `G`, wBw⁻¹ si endowed with a group structure. -/
def ConjugatedSubgroup (w: G) (B : Subgroup G): Subgroup G where
  carrier := {w} * B.carrier * {w⁻¹}
  mul_mem' := by
    simp
    intro _ _ ha hb
    have := B.mul_mem ha hb
    group at this ⊢
    assumption
  inv_mem' := by
    simp
    intro _ h
    have  := B.inv_mem h
    group at this ⊢
    assumption
  one_mem' := ⟨w*1, mem_mul.mpr ⟨w, mem_singleton w,1, B.one_mem, rfl⟩,w⁻¹, mem_singleton w⁻¹, by simp⟩


lemma prop5_iff (n : N) (i : A) : (∀ (ni : N), phi ni = M.simple i ->
    {ni * b.val * n | b : B} ⊆  DoubleCoset B (ni * n) ∪ DoubleCoset B n)  ↔
      (∃ (ni : N), phi ni = M.simple i ∧
        {ni * b.val * n | b : B} ⊆  DoubleCoset B (ni * n) ∪ DoubleCoset B n ) :=
  Iff.intro (fun h => match hsurj (M.simple i) with |⟨ni,hni⟩ => ⟨ni, hni,h ni hni⟩)
    fun ⟨ni0, hni0,h0⟩ ni hni x ⟨b,hb⟩ =>
      have : ni0⁻¹ * ni  ∈ B.subgroupOf N:= by simp [← hker,phi.mem_ker, hni0,hni]
      let bi : B := ⟨ni0⁻¹ *ni, this⟩
      have : x ∈ { x | ∃ b:B, ni0.val * b.val * ↑n = x } := ⟨bi*b, by simp [← hb, bi]; group ⟩
    Or.elim (h0 this)
      (fun h => Or.inl
        (have : ni0 * ni⁻¹ ∈ B.subgroupOf N:= by simp [← hker,phi.mem_ker, hni0,hni]
        let bi2 : B := ⟨ ni0*ni⁻¹,this ⟩
        have : bi2.val * (ni * n) * 1 = ni0 * n :=by simp ; group
        by rw [← doubleCoset_quotient B bi2 1 this.symm] ; assumption))
      fun h => Or.inr h


end
section Quotient

variable {G' : Type*} [Group  G']

open Function
open MonoidHom

/-- Easier way to prove `QuotientBNMphiQuadruplet'` has a `BNMphiQuadruplet` structure.-/
def QuotientBNMphiQuadruplet
  {pi : G →* G'} (pi_surj: Surjective pi) (ker_pi_le_B : pi.ker ≤ TS.B) {pi' : TS.N →* TS.N.map pi}
  (pi'_restpi : ∀ n, pi n.val = (pi' n).val)
  {phi': TS.N.map pi →* TS.M.Group} (pi_comm_phi' : TS.phi = phi'.comp pi') :
    BNMphiQuadruplet G' A where
  B := TS.B.map pi
  N := TS.N.map pi
  M := TS.M
  phi := phi'

  prop1 := by simp [ ← map_sup TS.B TS.N pi, ← TS.prop1,
                ←range_top_of_surjective pi pi_surj,range_eq_map]

  prop2 := fun x ↦
    match TS.prop2 x with
    | ⟨a,h⟩ => ⟨ pi' a, by simp [pi_comm_phi'] at h ; assumption ⟩

  prop3 := by
    have : Surjective pi'  := by
      intro x
      rcases x.2 with ⟨y,yinN,h⟩
      use ⟨y,yinN⟩
      apply subtype_injective
      simp [← h, pi'_restpi ⟨y,yinN⟩]
    ext x
    rcases this x with ⟨a,hₐ⟩
    simp [mem_ker,mem_subgroupOf]
    constructor
    · intro h
      have :a ∈ TS.phi.ker:= by simp [mem_ker,pi_comm_phi',(hₐ.symm) ▸  h]
      rw [TS.prop3, mem_subgroupOf] at this
      use a.val
      simp [this, ← hₐ,pi'_restpi]
    intro ⟨y, yinB, ycoex⟩
    have : phi' (pi' a) = TS.phi a := by simp [pi_comm_phi']
    simp [← hₐ,this, ← mem_ker, TS.prop3, mem_subgroupOf]
    have : pi a.val = x.val := by simp [pi'_restpi, hₐ]
    rw [← this] at ycoex
    have : a.val*y⁻¹ ∈ TS.B :=by
      apply ker_pi_le_B
      simp [mem_ker, ycoex]
    have := TS.B.mul_mem this yinB
    simp at this
    assumption

  prop4 :=by
    intro ni i hi
    rcases ni.2 with ⟨ni',ni'inN,hi'⟩
    have h:= TS.prop4 ⟨ni', ni'inN⟩ i
    contrapose h
    push_neg at h ⊢
    constructor
    · simp [← hi, pi_comm_phi', pi'_restpi, ← hi']
      have : pi' ⟨ni', ni'inN⟩ =  ni :=by
        apply subtype_injective
        simp [← hi', ← pi'_restpi]
      rw [this]
    ext x
    simp
    constructor
    · intro ⟨a,ainB, ha⟩
      have :pi x ∈ {y :G' | ∃ b :TS.B.map pi, (↑ni :G') * ↑b * ↑ni = y} :=by
        simp
        use a
        simp [← ha, hi', ainB]
      rw [h] at this
      rcases this with ⟨y,yinB, hy⟩
      have : x*y⁻¹ ∈ TS.B := by apply ker_pi_le_B  ; simp [mem_ker, hy]
      have  := TS.B.mul_mem this yinB
      simp at this
      assumption
    intro xinB
    have : pi x ∈ (TS.B.map pi) := by use x ; simp [xinB]
    rw [Set.ext_iff] at h
    rcases h (pi x)|>.2 this with ⟨a,h'⟩
    rcases a.2 with ⟨a0,a0inB,ha0⟩
    let D :=ni'⁻¹*x*ni'⁻¹*a0⁻¹
    have : D ∈ ker pi:= by
      simp [mem_ker,D, ← h', hi', ha0]
      group
    use D*a0
    simp at a0inB
    simp [TS.B.mul_mem (ker_pi_le_B this) a0inB]
    simp [D]
    group

  prop5:=by
    intro n ni i hi x ⟨b,hb⟩
    rcases ni.2 with ⟨_ni',_ni'inN,hni⟩
    rcases n.2 with ⟨_n',_n'inN,hn⟩
    let n' : TS.N := ⟨_n', _n'inN⟩
    let ni' : TS.N :=⟨_ni', _ni'inN⟩
    rcases pi_surj x with ⟨x',hx⟩

    have : TS.phi ni' = TS.M.simple i  := by
      have :  (pi' ni') = ni :=by apply subtype_injective ; simp [← pi'_restpi, hni, ni']
      simp [← hi, pi_comm_phi', this]

    have hi' := TS.prop5 n' ni' i this

    have :x' ∈ {y:G | ∃ b :TS.B, ni'.val * ↑b * n'.val = y} :=by
      rcases b.2 with ⟨b',b'inB, hb'⟩
      let D :=_ni'⁻¹ * x' * _n'⁻¹ * b'⁻¹
      have :D  ∈ pi.ker:=by
        simp [mem_ker,D,hx, ← hb , hn, hni,hb' ]
        group
      simp
      use D*b'
      simp [TS.B.mul_mem (ker_pi_le_B this) b'inB]
      simp [D] ; group
    obtain h|h := hi' this
    on_goal 1 => left
    on_goal 2 => right
    all_goals {
      simp [DoubleCoset] at h ⊢
      rcases h with ⟨a1,a1inB,a2,a2inB, ha ⟩
      use a1
      simp [a1inB]
      use a2
      simp [a2inB,← hx,← hn,← hni, ← ha]
    }

variable (G' : Type*) [Group G']
variable (Z : Subgroup G) [Normal Z] (ZleB : Z ≤ TS.B)

lemma kerpi_le_B:(QuotientGroup.mk' Z).ker ≤ TS.B  :=by rw [QuotientGroup.ker_mk']; exact ZleB

/-add to mathlib ?-/
lemma map_of_restrictedrange (x : ((QuotientGroup.mk' Z).restrict TS.N).range) :
    x.val ∈ TS.N.map (QuotientGroup.mk' Z) :=
  match x.2 with | ⟨y,hy⟩=> ⟨y,by simp [← hy]⟩

/-- A group homomorphsim from pi|N (N) to pi(N).-/
def quotientshom:((QuotientGroup.mk' Z).restrict TS.N).range →* TS.N.map (QuotientGroup.mk' Z) where
  toFun := fun x => (⟨x.1, map_of_restrictedrange TS Z x⟩:TS.N.map (QuotientGroup.mk' Z))
  map_one' := by simp
  map_mul' := by simp

/--The canonical projection from TS.N to its image in G/Z.-/
def pi' : TS.N →* TS.N.map (QuotientGroup.mk' Z):=
  (quotientshom TS Z).comp ((QuotientGroup.mk' Z).restrict TS.N).rangeRestrict

lemma pi'_restpi : ∀ n, (QuotientGroup.mk' Z) n.val = (pi' TS Z n).val :=
  fun _ => by simp [pi', quotientshom]

lemma Z_le_ker_phi : (Z.subgroupOf TS.N) ≤ TS.phi.ker:=
  fun _ =>by simp [TS.prop3, mem_subgroupOf] ; apply ZleB

/--Technical definition to buil `prequotientN`.-/
def quotient_surj(x : TS.N.map (QuotientGroup.mk' Z))(y : TS.N) := x=(QuotientGroup.mk' Z) y

lemma quotient_surj' (x : TS.N.map (QuotientGroup.mk' Z)) :
     ∃ y, quotient_surj TS Z x y :=
  match x.2 with | ⟨a,ha,h'⟩ =>  ⟨⟨a,ha⟩, h'.symm⟩

/--The map that maps the preimage of x∈N/Z to one of its preimage in N.-/
noncomputable
def prequotientN (x : TS.N.map (QuotientGroup.mk' Z)) : TS.N:=
  Classical.choose (quotient_surj' TS Z x)

/--The canonical group homomorphism from the N/Z to the image of N in the quotient G/Z.-/
noncomputable
def Nquotient_of_quotientN : (TS.N.map (QuotientGroup.mk' Z)) →* TS.N ⧸ Z.subgroupOf TS.N  where
  toFun := QuotientGroup.mk' (Z.subgroupOf TS.N) ∘  (prequotientN TS Z )
  map_one' := by
    have :=Classical.choose_spec (quotient_surj' TS Z 1)
    simp [mem_subgroupOf]
    simp [quotient_surj] at this
    have : (prequotientN TS Z 1).val ∈ (QuotientGroup.mk' Z).ker := by
      rw [mem_ker, this, prequotientN] ; simp
    simp at this
    assumption

  map_mul' := by
    intro x y
    simp
    have hx := Classical.choose_spec (quotient_surj' TS Z x)
    have hy := Classical.choose_spec (quotient_surj' TS Z y)
    have hxy := Classical.choose_spec (quotient_surj' TS Z (x*y))
    simp [quotient_surj] at hx hy hxy
    suffices h :QuotientGroup.mk' (Z.subgroupOf TS.N) ( (prequotientN TS Z (x * y)) *
                  (prequotientN TS Z y)⁻¹  * (prequotientN TS Z x)⁻¹ )=1 by
      simp at h
      rw [← one_mul ((prequotientN TS Z x) : TS.N ⧸ (Z.subgroupOf TS.N)), ← h]
      simp
    rw [← mem_ker]
    simp [mem_subgroupOf]
    suffices h: QuotientGroup.mk' Z ((prequotientN TS Z (x * y)) * (prequotientN TS Z y)⁻¹  * (prequotientN TS Z x)⁻¹ ) = 1 by
      rw [← mem_ker] at h
      simp at h
      assumption
    simp [prequotientN, ← hx, ← hy, ← hxy]

lemma prequotient_prop (Z : Subgroup G) [Normal Z] (y : TS.N):
    Nquotient_of_quotientN TS Z (pi' TS Z y) = ((QuotientGroup.mk' (Z.subgroupOf TS.N)) y)  :=by
  simp [Nquotient_of_quotientN, QuotientGroup.eq, mem_subgroupOf, prequotientN]
  have this := Classical.choose_spec <| quotient_surj' TS Z <| pi' TS Z y
  simp [quotient_surj,←  pi'_restpi] at this
  symm at this
  rw [QuotientGroup.eq'] at this
  simp [this]

/--The lift of TS.phi to TS.N/Z.-/
noncomputable
def phi' : (TS.N.map (QuotientGroup.mk' Z)) →* TS.M.Group :=
  (QuotientGroup.lift (Z.subgroupOf TS.N) TS.phi (Z_le_ker_phi TS Z ZleB)).comp
    (Nquotient_of_quotientN TS Z)


lemma pi_comm_phi' : TS.phi = (phi' TS Z ZleB).comp (pi' TS Z) :=by
  ext x; simp [phi',prequotient_prop TS Z]

/-- If (B,N,M,phi) is a `BNMphiQuadruplet` over G and Z is a subgroup of `phi.ker` normal in G,
then (B/Z, N/Z, M, phi') is a `BNMphiQuadruplet` over G/Z with phi' being the map phi lifted to N/Z-/
noncomputable
def QuotientBNMphiQuadruplet' : BNMphiQuadruplet (G ⧸ Z) A :=
    QuotientBNMphiQuadruplet TS (QuotientGroup.mk'_surjective Z) (kerpi_le_B TS Z ZleB)
      (pi'_restpi TS Z) (pi_comm_phi' TS Z ZleB)

end Quotient

section DoubleCoset
open CoxeterSystem
variable (TS : (BNMphiQuadruplet G A)) {G' : Type*} [Group  G']

/--The union of all the double Cosets-/
def  BWB :Subgroup G where
  carrier := TS.B *  TS.N * TS.B

  one_mem' := mul_one (1:G) ▸ mul_one (1*1 : G) ▸
    Set.mul_mem_mul (Set.mul_mem_mul TS.B.one_mem TS.N.one_mem) TS.B.one_mem

  inv_mem' :=by
    intro x ⟨bn,⟨b,binB,n,ninN, h₀⟩,b',b'inB,h⟩
    simp [← h, ← h₀, ← mul_assoc]
    apply Set.mul_mem_mul
    apply Set.mul_mem_mul
    all_goals
      {simp [binB, ninN, b'inB] ; first | exact binB | exact ninN | exact b'inB}

  mul_mem' := sorry

/-mathlib?-/

lemma Set.subset_mul_one_mem {s t :Set G} (one_mem : 1 ∈ t) : s ⊆ s*t :=
  fun x xins ↦ Set.mem_mul.mpr ⟨x,xins,1,one_mem, mul_one x⟩

lemma Set.subset_one_mem_mul {s t :Set G} (one_mem : 1 ∈ t) : s ⊆ t*s :=
  fun x xins ↦ Set.mem_mul.mpr ⟨1,one_mem, x, xins, one_mul x⟩

theorem groupDecomp : ⊤ = BWB TS := by
  apply le_antisymm
  · rw [TS.prop1]
    apply sup_le
    · exact fun _ xinB =>
        Set.subset_mul_one_mem TS.B.one_mem <| Set.subset_mul_one_mem TS.N.one_mem xinB
    · exact fun _ h => Set.subset_mul_one_mem TS.B.one_mem <| Set.subset_one_mem_mul TS.B.one_mem h
  simp

/--The map that maps a element n ∈ TS.N to its associated double coset BnB.-/
def f (n : TS.N) : Set G := C TS.B n

lemma liftablef : ∀ m n : TS.N, QuotientGroup.con (TS.phi.ker) m n → f TS m = f TS n :=by
  intro m n h
  simp [QuotientGroup.con,QuotientGroup.leftRel_apply] at h
  simp [f]
  have : (n⁻¹ * m).val ∈ TS.B:=by
    apply mem_subgroupOf.mp
    rw [← TS.prop3]
    suffices h' : n⁻¹ *m = (m⁻¹ *n)⁻¹ by rw [ h']; exact TS.phi.ker.inv_mem h
    group
  let a' : TS.B := ⟨n⁻¹ * m, this ⟩
  have : m.val = (1 :TS.B).val * n.val * ( n⁻¹*m).val :=by simp
  apply doubleCoset_quotient TS.B (1:TS.B)  a' this

/--The quotient map that from the Weyl group N/ker phi to the Sets of G.-/
def f' : TS.N ⧸ TS.phi.ker → Set G := Quotient.lift (f TS) (liftablef TS)

lemma f'comm_Quotientgroupmk (n : TS.N) : f' TS (QuotientGroup.mk' TS.phi.ker n) = f TS n :=by
  simp [f']
  have : (QuotientGroup.mk : TS.N → TS.N ⧸ TS.phi.ker) = Quotient.mk'' :=by
    ext x
    have : (↑x : TS.N ⧸ TS.phi.ker)  = Quotient.mk'' x  := by simp
    rw [this]
  rw [this, Quotient.mk'']

lemma f'comm_Quotientgroupmk' (n : TS.N) : f' TS (↑n : TS.N ⧸ TS.phi.ker) = f TS n :=by
  rw [← f'comm_Quotientgroupmk]
  rfl

lemma f'comm_Quotientgroupmk'' (n : TS.N) : f' TS (Quotient.mk'' n) = f TS n :=by
  simp [Quotient.mk'', f']

lemma quot_surj (w : TS.N ⧸ TS.phi.ker) : ∃ u : TS.N, w = Quotient.mk'' u :=
  match QuotientGroup.mk'_surjective TS.phi.ker w with
  | ⟨u,h⟩ => ⟨u, by simp [← h]⟩

lemma quot_apply (u : TS.N) : Quotient.mk'' u = (↑u : TS.N ⧸ TS.phi.ker):=by simp

lemma f'apply (w: TS.N ⧸ TS.phi.ker) : ∃ u ∈ TS.N, f' TS w = C TS.B u :=
  match QuotientGroup.mk'_surjective TS.phi.ker w with
  |⟨u,h⟩ => ⟨u,by simp [← h, f'comm_Quotientgroupmk', f]⟩

lemma f'one : f' TS 1 = TS.B.carrier :=by
  simp [← QuotientGroup.mk_one, f'comm_Quotientgroupmk', f,← doubleCoset_one]

lemma phikerLift_isom : Function.Bijective (QuotientGroup.kerLift TS.phi):=
  And.intro
    (QuotientGroup.kerLift_injective TS.phi)
    fun y => match TS.prop2 y with |⟨u,h⟩ => ⟨QuotientGroup.mk' TS.phi.ker u, by simp [h] ⟩

/--The `CoxeterSystem` from N/ker phi to M.Group-/
noncomputable
def  cst : CoxeterSystem TS.M (TS.N ⧸ TS.phi.ker) where
  mulEquiv := MulEquiv.ofBijective (QuotientGroup.kerLift TS.phi) (phikerLift_isom TS)

lemma f'_inj_init {w w' : TS.N ⧸ TS.phi.ker} (w_neq_w' : w ≠ w') (hq :(cst TS).length w'=0):
    f' TS w ≠ f' TS w' :=by
  let cs : CoxeterSystem TS.M (TS.N ⧸ TS.phi.ker) := cst TS
  rw [(length_eq_zero_iff cs).mp hq] at w_neq_w' ⊢
  rcases quot_surj TS w with ⟨u,hu⟩
  simp [f'one, hu]
  suffices u.val ∉ TS.B.carrier by
    intro h
    apply this
    rw [← h]
    exact ⟨1, by simp⟩
  by_contra h
  apply w_neq_w'
  rwa [hu, QuotientGroup.eq_one_iff, TS.prop3, mem_subgroupOf, ←Subgroup.mem_carrier]

lemma czlihvevh {s₀ w₀ w'₀ : TS.N} (hdis:Disjoint (C TS.B (↑s₀ * ↑w'₀)) (C TS.B ↑s₀ * C TS.B ↑w₀)):
    C TS.B ↑w₀ ≠ C TS.B ↑w'₀ := by
  revert hdis
  contrapose!
  intro h
  rw [h]
  apply Set.not_disjoint_iff.mpr
  use s₀*w'₀
  apply And.intro (DoubleCoset.self_mem TS.B)
  simp [DoubleCoset.mul_apply]
  exact ⟨1, TS.B.one_mem,1, TS.B.one_mem,1, TS.B.one_mem,by simp⟩


lemma apply_left_descent {w' : TS.N ⧸ TS.phi.ker} {q : Nat} (h: (cst TS).length w' = q + 1) :
    ∃ i :A, (cst TS).length ((cst TS).simple i * w') = q  := by
  have : w'  ≠ 1 := by
    intro h'
    rw [(CoxeterSystem.length_eq_zero_iff (cst TS)).mpr h' ] at h
    contradiction
  rcases CoxeterSystem.exists_leftDescent_of_ne_one (cst TS) this with ⟨i,hi⟩
  use i
  simp [IsLeftDescent] at hi
  obtain h'|h' := CoxeterSystem.length_simple_mul (cst TS) w' i
  · rw [h'] at hi
    simp at hi
  · apply add_right_cancel
    rw [← h,h']

lemma gotαfindaname {s₀ w₀ w'₀ :TS.N} (i:A) (hs : QuotientGroup.mk' TS.phi.ker s₀ =  (cst TS).simple i)
    (h : C TS.B w₀ ≠ C TS.B (s₀  * w'₀) ∧ C TS.B (s₀ * w₀) ≠ C TS.B (s₀ * w'₀ )) :
      Disjoint (C TS.B (s₀ * w'₀)) (C TS.B s₀* (C TS.B w₀)) :=by
  apply Set.disjoint_of_subset_right
  · apply (prop4_doubleCoset_iff TS.B s₀ w₀).mp
    rw [Set.union_comm]
    apply TS.prop5 w₀ s₀ i
    have : TS.phi s₀ = (cst TS).mulEquiv (QuotientGroup.mk' TS.phi.ker s₀):= by simp [cst]
    simp [this,hs, ← CoxeterSystem.map_simple, CoxeterSystem.simple, CoxeterMatrix.simple]
  apply Set.disjoint_union_right.mpr
  constructor
  on_goal 1 =>apply (DoubleCoset.disjoint_of_neq TS.B (s₀ * w'₀) w₀)
  on_goal 2 =>apply (DoubleCoset.disjoint_of_neq TS.B (s₀ * w'₀) (s₀ *w₀))
  all_goals {symm ; simp [ne_eq] ; first |exact h.2 | exact h.1}

lemma mamamia {s w : TS.N ⧸ TS.phi.ker } {q : Nat} (i:A) (hsi : s = (cst TS).simple i)
    (hlength : (cst TS).length w ≥ q +1 ) : (cst TS).length (s*w) ≥ q :=
    let cs :=cst TS
    ge_trans (Or.elim (CoxeterSystem.length_simple_mul cs w i)
                (fun h => by simp [hsi,h]; linarith)
                  fun h => by simp [hsi,h]; linarith)
      (by rfl)

lemma f'_inj (q:Nat):
  ∀ {w w' : TS.N ⧸ TS.phi.ker},  (w_neq_w' : w ≠ w') → (hq :(cst TS).length w'=q) →
    (hlength : (cst TS).length w ≥ q) → f' TS w ≠ f' TS w':=by
  let cs : CoxeterSystem TS.M (TS.N ⧸ TS.phi.ker) := cst TS
  induction' q with q Aq
  · intro w w' w_neq_w' hq _
    exact f'_inj_init TS w_neq_w' hq

  intro w w' w_neq_w' hq hlength
  rcases apply_left_descent TS hq with ⟨i,hsw'⟩

  let s := cs.simple i

  have : cs.length w > cs.length (s*w'):= gt_of_ge_of_gt hlength (by simp [s,← hsw'])
  have wneqsw': w ≠ s*w' := fun h => by rw [h] at this ; apply ne_of_gt this; rfl
  have swneqsw': s * w ≠ s * w' := by simpa
  have : f' TS w ≠ f' TS (s*w') ∧ f' TS (s*w) ≠ f' TS (s*w'):=
    And.intro (Aq  wneqsw' hsw' (le_trans (by simp) hlength))
      (Aq  swneqsw' hsw' (mamamia TS i (by simp [s, cs]) hlength))
  rcases QuotientGroup.mk'_surjective TS.phi.ker w with ⟨w₀, hw⟩
  rcases QuotientGroup.mk'_surjective TS.phi.ker w' with ⟨w'₀, hw'⟩
  rcases QuotientGroup.mk'_surjective TS.phi.ker s with ⟨s₀, hs⟩
  simp [← hw', ← hw, ← hs, f'comm_Quotientgroupmk', f] at this ⊢
  repeat rw [← QuotientGroup.mk_mul, f'comm_Quotientgroupmk',f] at this
  exact czlihvevh TS <| gotαfindaname TS i (by simp [s,cs,hs]) this

lemma f'_inj' : Function.Injective (f' TS) := by
  intro w w' h
  let cs := cst TS
  by_contra! w_neq_w'
  exact Or.elim (Nat.le_or_le (cs.length w) (cs.length w'))
    (fun hlength => f'_inj TS (cs.length w) w_neq_w'.symm rfl hlength h.symm)
    (fun hlength => f'_inj TS (cs.length w') w_neq_w' rfl hlength h)

/--The bijection between the Weyl group of the BNMphiQuadruplet and it simage (the set of double Cosets), see `Weyl_doubleCosets_equiv'`.-/
noncomputable
def Weyl_doubleCosets_equiv : TS.N ⧸ TS.phi.ker ≃ Set.range (f' TS) :=
    Equiv.ofInjective (f' TS) (f'_inj' TS)

lemma f'range_eq_doubleCosets : Set.range (f' TS) = {C TS.B w | w : TS.N} :=by
  ext Cw
  simp [Set.mem_range]
  constructor
  · intro ⟨w, h ⟩
    rcases f'apply TS w with ⟨w₀ ,w₀inN,hw₀⟩
    use w₀
    simp [w₀inN, ← hw₀,h]
  · intro ⟨w₀, w₀inN,hw₀⟩
    use QuotientGroup.mk' TS.phi.ker ⟨w₀, w₀inN⟩
    simp [f'comm_Quotientgroupmk',f,hw₀]

/--The bijection between the Weyl group of the BNMphiQuadruplet and the set of double Cosets.-/
noncomputable
def Weyl_doubleCosets_equiv' : TS.N ⧸ TS.phi.ker ≃  {C TS.B w | w : TS.N} :=
    f'range_eq_doubleCosets TS ▸ Weyl_doubleCosets_equiv TS

end DoubleCoset

#lint
