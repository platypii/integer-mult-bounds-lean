import IntegerMultBounds.Machine.NativeEndpointCharacterCopy
import IntegerMultBounds.Machine.CompactComplexEndpointRoleExchange

/-! Actual original raw-header and named endpoint ports, with arbitrary caller
suffix. These ports are shared by source character and sink phase families. -/
namespace IntegerMultBounds.Machine.NativeEndpointNamedPorts
noncomputable section
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexEndpointRoleExchange (Address Wire tapes port)
variable {s u : ℕ}

def focus (i : Fin 15) : Fin (tapes s u) :=
  Fin.castAdd u (CompactComplexNativeCodecFrame.headerSlot
    (Fin.castAdd 15 (NativeEndpointCharacterCopy.index i)))

def sourceX (b : Address) : Fin (tapes s u) := port (Sum.inl b)
def sinkY (b : Address) : Fin (tapes s u) := port (Sum.inr (Sum.inl b))

theorem sourceX_injective : Function.Injective (sourceX (s:=s) (u:=u)) := by
  intro a b h
  exact Sum.inl.inj (CompactComplexEndpointRoleExchange.port_injective h)
theorem sinkY_injective : Function.Injective (sinkY (s:=s) (u:=u)) := by
  intro a b h
  exact Sum.inl.inj (Sum.inr.inj (CompactComplexEndpointRoleExchange.port_injective h))

theorem role_focus (a : Wire) (i : Fin 15) : port (s:=s) (u:=u) a≠focus i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := (NativeEndpointCharacterCopy.index i).isLt
  simp only [port,focus,CompactComplexSpectatorTargetBank.roleSlot,
    CompactComplexNativeRoleBridge.roleSlot,CompactComplexNativeCodecFrame.headerSlot,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexControllerNativeFrame.tapes,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem sourceX_focus (b : Address) (i : Fin 15) : sourceX (s:=s) (u:=u) b≠focus i := role_focus _ _
theorem sinkY_focus (b : Address) (i : Fin 15) : sinkY (s:=s) (u:=u) b≠focus i := role_focus _ _

theorem focus_bank (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (payload : Tapes (1+roleCount) 2) (extra : Tapes u 2) (i : Fin 15) :
    let v := (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage payload).append extra
    let j := Fin.castAdd 15 (NativeEndpointCharacterCopy.index i)
    v.head (focus i)=(ActiveRepairRankHeadersCommands.bank (a:=2) stage).head j ∧
    v.tape (focus i)=(ActiveRepairRankHeadersCommands.bank (a:=2) stage).tape j := by
  dsimp only
  simp only [focus,CompactComplexNativeCodecFrame.headerSlot,CompactComplexNativeCodecFrame.bank,
    CompactComplexNativeRoleBridge.bank,CompactComplexControllerNativeFrame.bank,
    CompactComplexControllerNativeFrame.nativeSlot,CompactComplexNativeRoleBridge.native,
    Tapes.append,Fin.addCases_left,Fin.addCases_right,and_self]

end
end IntegerMultBounds.Machine.NativeEndpointNamedPorts
