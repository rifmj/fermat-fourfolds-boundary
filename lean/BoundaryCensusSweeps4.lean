/-
  BoundaryCensusSweeps4.lean — census sweeps, batch 4: the induced-risk levels 231 and 273.
-/
import BoundaryCensus

namespace BoundaryCensus

theorem sweeps4 :
    (censusTable4.all fun p => levelFull p.1 p.2 (levelBases p.1)) = true := by native_decide

end BoundaryCensus
