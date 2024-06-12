/-TODO

Create BN pair and shox that they are BNWφQuadruples
- PGLn (F)


-/
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Tactic.Group
import FiniteGroupsOfLieType.DoubleCosets

open Subgroup
variable {G : Type*} [Group G] {A : Type*} 

  
structure BNMφQuadruplet (G : Type*) [Group G] (A : Type*) where
  B : Subgroup G
  N : Subgroup G

  M : CoxeterMatrix A

  φ : N →* M.Group
  prop1 : ⊤ = B ⊔ N
  prop2 : Function.Surjective φ
  prop3 : φ.ker = B.subgroupOf N
  prop4 : ∀ (ni: N) (i : A) , φ ni = M.simple i -> {(ni :G) * (b : G) * ni | b : B} ≠ B
  prop5 :  ∀ (n ni : N) (i : A), φ ni = M.simple i -> 
            {ni * b.val * n | b : B} ⊆  DoubleCoset B (n * ni) ∪ DoubleCoset B n 


section Quotient

variable (TS : (BNMφQuadruplet G A)) {G' : Type*} [Group  G']

open Function
open MonoidHom

def QuotientBNMφQuadruplet 
  {pi : G →* G'} (pi_surj: Surjective pi) (ker_pi_le_B : pi.ker ≤ TS.B) {pi' : TS.N →* TS.N.map pi} 
  (pi'_restpi : ∀ n, pi n.val = (pi' n).val) 
  {φ': TS.N.map pi →* TS.M.Group} (pi_comm_φ' : TS.φ = φ'.comp pi') : 
    BNMφQuadruplet G' A where
  B := TS.B.map pi
  N := TS.N.map pi
  M := TS.M 
  φ := φ' 

  prop1 := by simp [ ← map_sup TS.B TS.N pi, ← TS.prop1,
                ←range_top_of_surjective pi pi_surj,range_eq_map]

  prop2 := by
    intro x
    rcases TS.prop2 x with ⟨a,h⟩
    use pi' a
    simp [pi_comm_φ'] at h
    assumption

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
      have :a ∈ TS.φ.ker:= by simp [mem_ker,pi_comm_φ',(hₐ.symm) ▸  h] 
      rw [TS.prop3, mem_subgroupOf] at this 
      use a.val
      simp [this, ← hₐ,pi'_restpi]
    intro ⟨y, yinB, ycoex⟩
    have : φ' (pi' a) = TS.φ a := by simp [pi_comm_φ']
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
    · simp [← hi, pi_comm_φ', pi'_restpi, ← hi']
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
    
    have : TS.φ ni' = TS.M.simple i  := by
      have :  (pi' ni') = ni :=by apply subtype_injective ; simp [← pi'_restpi, hni, ni']
      simp [← hi, pi_comm_φ', this]
    
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
      simp at h ⊢ 
      rcases h with ⟨a1,a1inB,a2,a2inB, ha ⟩
      use a1
      simp [a1inB]
      use a2
      simp [a2inB,← hx,← hn,← hni, ← ha] 
    }

variable (G' : Type*) [Group G']
variable (Z : Subgroup G) [Normal Z] (ZleB : Z ≤ TS.B)


lemma kerpi_le_B:(QuotientGroup.mk' Z).ker ≤ TS.B  :=by rw [QuotientGroup.ker_mk']; exact ZleB

lemma map_of_restrictedrange (x : ((QuotientGroup.mk' Z).restrict TS.N).range) : 
    x.val ∈ TS.N.map (QuotientGroup.mk' Z) :=by
  rcases x.2 with ⟨y,hy⟩ 
  use y
  simp [← hy] 

def supermorphismthamakesthingswork:((QuotientGroup.mk' Z).restrict TS.N).range →* TS.N.map (QuotientGroup.mk' Z) where
  toFun := fun x => (⟨x.1, map_of_restrictedrange TS Z x⟩:TS.N.map (QuotientGroup.mk' Z))
  map_one' := by simp
  map_mul' := by simp

def pi' : TS.N →* TS.N.map (QuotientGroup.mk' Z):= 
  (supermorphismthamakesthingswork TS Z).comp ((QuotientGroup.mk' Z).restrict TS.N).rangeRestrict

lemma pi'_restpi : ∀ n, (QuotientGroup.mk' Z) n.val = (pi' TS Z n).val :=
  fun _ => by simp [pi', supermorphismthamakesthingswork] 

lemma Zlekerφ : (Z.subgroupOf TS.N) ≤ TS.φ.ker:=
  fun _ =>by simp [TS.prop3, mem_subgroupOf] ; apply ZleB

def xza   (x : TS.N.map (QuotientGroup.mk' Z))(y : TS.N) := x=(QuotientGroup.mk' Z) y 

lemma edzd (x : TS.N.map (QuotientGroup.mk' Z)) :
     ∃ y, xza TS Z x y :=by
  rcases x.2 with ⟨a,ha,h'⟩
  use ⟨a,ha⟩
  exact h'.symm 

noncomputable
def pleasework' (x : TS.N.map (QuotientGroup.mk' Z)) : TS.N:= 
  Classical.choose <| edzd TS Z x

noncomputable
def Nquotient_of_quotientN : (TS.N.map (QuotientGroup.mk' Z)) →* TS.N ⧸ Z.subgroupOf TS.N  where
  toFun := QuotientGroup.mk' (Z.subgroupOf TS.N) ∘  (pleasework' TS Z )
  map_one' := by 
    have :=Classical.choose_spec (edzd TS Z 1) 
    simp [mem_subgroupOf]
    simp [xza] at this
    have : (pleasework' TS Z 1).val ∈ (QuotientGroup.mk' Z).ker := by 
      rw [mem_ker, this, pleasework'] ; simp
    simp at this
    assumption
  map_mul' := by
    intro x y
    simp
    have hx := Classical.choose_spec (edzd TS Z x) 
    have hy := Classical.choose_spec (edzd TS Z y)
    have hxy := Classical.choose_spec (edzd TS Z (x*y))
    simp [xza] at hx hy hxy
    suffices h :
        QuotientGroup.mk' (Z.subgroupOf TS.N) ( (pleasework' TS Z (x * y)) * (pleasework' TS Z y)⁻¹  * (pleasework' TS Z x)⁻¹ )=1 by
      simp at h
      rw [← one_mul ((pleasework' TS Z x) : TS.N ⧸ (Z.subgroupOf TS.N)), ← h]
      simp
    rw [← mem_ker]
    simp [mem_subgroupOf]
    suffices h: QuotientGroup.mk' Z ((pleasework' TS Z (x * y)) * (pleasework' TS Z y)⁻¹  * (pleasework' TS Z x)⁻¹ ) = 1 by
      rw [← mem_ker] at h
      simp at h
      assumption
    simp [pleasework', ← hx, ← hy, ← hxy]

lemma pleaseworkprop (Z : Subgroup G) [Normal Z] (y : TS.N):
    Nquotient_of_quotientN TS Z (pi' TS Z y) = ((QuotientGroup.mk' (Z.subgroupOf TS.N)) y)  :=by 
  simp [Nquotient_of_quotientN]
  have h := Classical.choose_spec <| edzd TS Z <| pi' TS Z y
  simp [xza,←  pi'_restpi] at h
  symm at h
  rw [QuotientGroup.eq, mem_subgroupOf, pleasework']
  rw [QuotientGroup.eq'] at h
  simp [h]
  
noncomputable
def φ' : (TS.N.map (QuotientGroup.mk' Z)) →* TS.M.Group := (QuotientGroup.lift (Z.subgroupOf TS.N) TS.φ (Zlekerφ TS Z ZleB)).comp (Nquotient_of_quotientN TS Z)


lemma gabagool : TS.φ = (φ' TS Z ZleB).comp (pi' TS Z) :=by 
  ext x
  simp [φ',pleaseworkprop TS Z]

noncomputable
def QuotientBNMφQuadruplet' : BNMφQuadruplet (G ⧸ Z) A := 
    QuotientBNMφQuadruplet TS (QuotientGroup.mk'_surjective Z) (kerpi_le_B TS Z ZleB) (pi'_restpi TS Z) (gabagool TS Z ZleB)

end Quotient

section DoubleCoset 

variable (TS : (BNMφQuadruplet G A)) {G' : Type*} [Group  G']


def  BWB :Subgroup G where
  carrier :=set_mul TS.B (set_mul TS.N TS.B)
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

theorem groupDecomp : ⊤ = BWB TS := by 
  apply le_antisymm
  · rw [TS.prop1]
    apply sup_le
    · simp [BWB]
      intros 
      apply set_mul_le_mem_one 
      simp [set_mul]
      use 1; simp ; exact ⟨TS.N.one_mem, TS.B.one_mem⟩
    simp [BWB]
    intro x h
    simp
    apply set_mul_le_one_mem TS.B.one_mem <| set_mul_le_mem_one TS.B.one_mem h  
  simp


def f (n : TS.N) : Set G := C TS.B n 
lemma yes : ∀ m n : TS.N, QuotientGroup.con (TS.φ.ker) m n → f TS m = f TS n  :=by
  intro m n h
  simp [QuotientGroup.con,QuotientGroup.leftRel_apply]  at h
  simp [f]
  have : m.val = (1 :TS.B).val * n.val * ( n⁻¹*m).val :=by sorry
  apply doubleCoset_quotient TS.B this (1:TS.B) ((m⁻¹ *n)⁻¹) this
  


def g : TS.N ⧸ TS.φ.ker → Set G := Quotient.lift (f TS) (yes TS) 

noncomputable
def  doubleCoset_Coexter_equiv : TS.M.Group ≃ {C TS.B w | w∈ N} where
  toFun := 

  
    
      
    

  
  

end DoubleCoset


