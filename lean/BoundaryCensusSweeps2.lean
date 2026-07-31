/-
  BoundaryCensusSweeps2.lean — census sweeps, batch 2: odd levels 151 ≤ m ≤ 179 (15 levels).
-/
import BoundaryCensus

namespace BoundaryCensus

theorem sweeps2 :
    (censusTable2.all fun p => levelFull p.1 p.2 (levelBases p.1)) = true := by native_decide

end BoundaryCensus
