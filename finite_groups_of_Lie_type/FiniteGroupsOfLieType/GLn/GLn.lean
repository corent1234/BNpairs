import FiniteGroupsOfLieType.GLn.Prop5

variable {n : Type*}  [Fintype n] [DecidableEq n] [LinearOrder n] {R : Type*}
variable {F :Type*} [Field F] [DecidableEq F]

open Matrix
open Units



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
  prop5 := GLprop5 A

/--The projective general linear group, obtained by taking the quotient `GL n F` by its center-/
abbrev ProjectiveGeneralLinearGroup  (n : Type*)  [Fintype n] [DecidableEq n]  (F :Type*) [Field F]  : 
    Type _ := GL n F ⧸ Subgroup.center (GL n F)

/-- notation for the `ProjectiveGeneralLinearGroup`-/
notation "PGL" => ProjectiveGeneralLinearGroup

lemma GLncenter_le_Triangular : 
    Subgroup.center (GL n F) ≤ TriangularGroup := by
  rw [← scalarGroup_eq_GLnCenter]
  exact le_trans scalarGroup_le_diagonalGroup (diagonalGroup_le_blockTriangularGroup id)

/--The `BNMphiQuadruplet`  structure over `PGL n F`.-/
noncomputable
def PGL' : BNMphiQuadruplet (PGL n F) A := 
  QuotientBNMphiQuadruplet' GL' (Subgroup.center (GL n F))  GLncenter_le_Triangular

#lint
