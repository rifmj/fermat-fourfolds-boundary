/-
  BoundaryCensusSweeps5.lean — census sweeps, batch 5: the induced-risk level 297.
-/
import BoundaryCensus

namespace BoundaryCensus

theorem sweeps5 :
    (censusTable5.all fun p => levelFull p.1 p.2 (levelBases p.1)) = true := by native_decide

end BoundaryCensus
