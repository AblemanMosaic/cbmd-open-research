import OAI.Algorithms.SubexponentialSAT.SqrtLog.AZeroNativeCollapse
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredNativeVanishing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityCoefficientClosedForm
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativeAmplitudeScalarBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativeAmplitudeCostBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterNumeratorBCM1
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BCM1CostSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutableJointBCM1
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CoordinateOrbitBCM1
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open OAI Algorithms SubexponentialSAT
open Lean Meta Elab Command

elab "audit_dependencies " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let dependencies ← Lean.collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for dependency in dependencies do
    unless allowed.contains dependency do
      throwError "{name} depends on unapproved logical primitive {dependency}"
  logInfo m!"audited {name}: {dependencies.size} approved logical dependencies"

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

#print axioms entry_eq_zero_of_A_zero_compiled
#print axioms entry_eq_zero_of_centered_compiled
#print axioms parityCoefficient_closed_form
#print axioms entry_eq_masterNumerator
#print axioms entry_eq_masterNumerator_of_scalar_bridge
#print axioms entry_eq_masterNumeratorBCM1
#print axioms masterNumeratorBCM1_eq_masterNumerator
#print axioms masterNumeratorBCM1Costed_value
#print axioms masterNumeratorBCM1Costed_counts
#print axioms masterNumeratorBCM1Costed_mul_le
#print axioms masterNumeratorBCM1Costed_div_le
#print axioms masterNumeratorBCM1Costed_add_le
#print axioms entry_eq_masterNumeratorBCM1Costed_value
#print axioms jointBCM1Total_eq_joint
#print axioms inOrbit_iff_orbitCompatible
#print axioms jointBCM1Coordinate_eq_joint

audit_dependencies entry_eq_zero_of_A_zero_compiled
audit_dependencies entry_eq_zero_of_centered_compiled
audit_dependencies parityCoefficient_closed_form
audit_dependencies entry_eq_masterNumerator
audit_dependencies entry_eq_masterNumerator_of_scalar_bridge
audit_dependencies entry_eq_masterNumeratorBCM1
audit_dependencies masterNumeratorBCM1_eq_masterNumerator
audit_dependencies masterNumeratorBCM1Costed_value
audit_dependencies masterNumeratorBCM1Costed_counts
audit_dependencies masterNumeratorBCM1Costed_mul_le
audit_dependencies masterNumeratorBCM1Costed_div_le
audit_dependencies masterNumeratorBCM1Costed_add_le
audit_dependencies entry_eq_masterNumeratorBCM1Costed_value
audit_dependencies jointBCM1Total_eq_joint
audit_dependencies inOrbit_iff_orbitCompatible
audit_dependencies jointBCM1Coordinate_eq_joint

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
