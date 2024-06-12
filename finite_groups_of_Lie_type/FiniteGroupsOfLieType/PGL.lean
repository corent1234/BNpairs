import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.GroupTheory.QuotientGroup
import FiniteGroupsOfLieType.GLn.GLn

variable {F :Type*} [Field F] [DecidableEq F]

section PGL
variable (n : Type*)  [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]


/-- A general special linear group is the quotient of a general linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ Subgroup.center (GL n R)

end PGL

/-- `PGL(n, R)` is the projective special linear group `GL(n, R)/Z(GL(n, R))`. -/
notation "PGL"  =>ProjectiveGeneralLinearGroup

section BN
variable {n : Type*}  [Fintype n] [DecidableEq n] [LinearOrder n] {R : Type*} [CommRing R]

abbrev Z : Subgroup (GL n R) := Subgroup.center (GL n R)

/-- The (Borel) group of projective triangular matrices.-/
def B  : Subgroup (PGL n F) :=
    TriangularGroup.map (QuotientGroup.mk' Z )

/-- The group of prokective monomial matrices.-/
def N : Subgroup (PGL n F) := MonomialGroup.map (QuotientGroup.mk' Z)

/-- The torus of the projective diagonal matrices.-/
def T : Subgroup (PGL n F) := B ⊓ N

#check Subgroup.normalizer
lemma N_normalize_T : (B.subgroupOf (N: Subgroup (PGL n F))).Normal := by sorry


end BN
