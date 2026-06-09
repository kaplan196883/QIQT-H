-- Standalone verification that every declaration referenced by the blueprint
-- (blueprint/lean_decls) exists in the compiled Lean. This lives OUTSIDE the
-- QIQTH/ glob so it is not part of the library; run it with `lake env lean`.
-- It deliberately imports only the modules the blueprint references, so it does
-- not depend on unrelated work-in-progress modules.
import QIQTH.CoreNoCollapse
import QIQTH.BornTypicalityQuantum
import QIQTH.BornMeasureUniqueness
import QIQTH.NoSignalingGeneral
import QIQTH.KolmogorovFiniteFiber
import QIQTH.StateNetMeasure
import QIQTH.NormalState
import QIQTH.BHTypicalityMeasure
import QIQTH.FreeFieldTypicality

#check @QIQTH.CoreNoCollapse.exactly_one_actual
#check @QIQTH.CoreNoCollapse.qiqth_single_outcome_no_collapse
#check @QIQTH.BornTypicalityQuantum.quantum_chebyshev_freq
#check @QIQTH.BornMeasureUniqueness.product_born_measure_unique
#check @QIQTH.NoSignalingGeneral.bipartite_no_signaling
#check @QIQTH.KolmogorovFiniteFiber.exists_isLimit
#check @QIQTH.StateNetMeasure.EffectStateNet.exists_typicalityMeasure
#check @QIQTH.NormalState.diagStateHom_one
#check @QIQTH.BHTypicalityMeasure.bh_typicalityMeasure_exists
#check @QIQTH.FreeFieldTypicality.freeFieldMeasure_boost_invariant
