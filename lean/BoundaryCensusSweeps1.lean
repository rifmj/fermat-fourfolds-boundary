/-
  BoundaryCensusSweeps1.lean — census sweeps, batch 1: every odd level 3 ≤ m ≤ 149
  (74 levels), plus the cross-engine anchor: at the six original census levels the new
  MITM enumerator agrees with BoundaryCore's nested-loop enumerator element-for-element.
  Heavy native_decide; split into its own file so lake builds the batches in parallel.
-/
import BoundaryCensus

namespace BoundaryCensus
open BoundaryCore

theorem sweeps1 :
    (censusTable1.all fun p => levelFull p.1 p.2 (levelBases p.1)) = true := by native_decide

/-- B4 anchor: the two enumerators (nested loops of BoundaryCore, MITM of this layer)
    produce the same sorted Hodge sextuples at the six original census levels. -/
theorem rawFull_matches_core :
    (([9, 21, 27, 33, 39, 45] : List Nat).all fun m =>
      ((hodgeSextuples m).all fun s => (rawFull m).contains s) &&
      ((rawFull m).all fun s => (hodgeSextuples m).contains s) &&
      ((hodgeSextuples m).length == (rawFull m).length)) = true := by native_decide

end BoundaryCensus
