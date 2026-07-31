/-
  BoundaryCensusSweeps3.lean — census sweeps, batch 3: odd levels 181 ≤ m ≤ 199 (10 levels).
-/
import BoundaryCensus

namespace BoundaryCensus

theorem sweeps3 :
    (censusTable3.all fun p => levelFull p.1 p.2 (levelBases p.1)) = true := by native_decide

end BoundaryCensus
