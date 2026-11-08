module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCroppedRecoveryReady

/-! A fixed disjoint allocation for the existing 117-tape selector, recovery
banks, four handoff scratch ports and six batch ports. All separation is proved over role sums. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

instance : Fintype (TblR 25) := Fintype.ofList
  ((List.finRange 25).map TblR.v ++ [.wr,.wn,.acc] ++ (List.finRange 12).map TblR.z)
  (by intro i; cases i <;> simp)

instance : Fintype RecoveryControl := Fintype.ofList
  [.src,.saved,.count,.tmp,.spare,.result,.clock,.savedClock,.precision,.packet,.replicas,
   .masterWord,.masterSaved,.masterTmp,.masterQueue,.masterCarry,.cropOffset,.cropRows,.cropDst]
  (by intro i; cases i <;> simp)

noncomputable instance : Fintype RecoveryBank := Fintype.ofList
  (((Finset.univ : Finset (TblR 25)).toList.map RecoveryBank.scalar) ++
   ((List.finRange 8).map RecoveryBank.parameter) ++
   ((List.finRange 10).map RecoveryBank.master) ++
   ((List.finRange 392).map RecoveryBank.work) ++
   ((Finset.univ : Finset RecoveryControl).toList.map RecoveryBank.control))
  (by intro i; cases i <;> simp)

namespace LocalRecoveryLayout
noncomputable section

abbrev Role := Fin 117 ⊕ (RecoveryBank ⊕ Fin 10)
def tapes : ℕ := Fintype.card Role
def port : Role → Fin tapes := Fintype.equivFin Role

theorem port_injective : Function.Injective port := (Fintype.equivFin Role).injective

def geometry (i : Fin 117) : Fin tapes := port (.inl i)
def recovery (i : RecoveryBank) : Fin tapes := port (.inr (.inl i))
def scratch (i : Fin 4) : Fin tapes := port (.inr (.inr (Fin.castAdd 6 i)))
def batch (i : Fin 6) : Fin tapes := port (.inr (.inr (Fin.natAdd 4 i)))

theorem geometry_injective : Function.Injective geometry := by
  intro i j h; exact Sum.inl.inj (port_injective h)
theorem recovery_injective : Function.Injective recovery := by
  intro i j h; exact Sum.inl.inj (Sum.inr.inj (port_injective h))
theorem scratch_injective : Function.Injective scratch := by
  intro i j h
  have hh : (Fin.castAdd 6 i : Fin 10) = Fin.castAdd 6 j := Sum.inr.inj (Sum.inr.inj (port_injective h))
  exact Fin.ext (congrArg (fun x : Fin 10 => x.val) hh)
theorem geometry_ne_recovery (i : Fin 117) (j : RecoveryBank) : geometry i ≠ recovery j := by
  simp [geometry,recovery,port_injective.eq_iff]
theorem scratch_ne_recovery (i : Fin 4) (j : RecoveryBank) : scratch i ≠ recovery j := by
  simp [scratch,recovery,port_injective.eq_iff]
theorem geometry_ne_scratch (i : Fin 117) (j : Fin 4) : geometry i ≠ scratch j := by
  simp [geometry,scratch,port_injective.eq_iff]

theorem batch_injective : Function.Injective batch := by
  intro i j h; exact Fin.ext (by
    have hv := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj (port_injective h)))
    change 4+i.val = 4+j.val at hv
    omega)
theorem geometry_ne_batch (i : Fin 117) (j : Fin 6) : geometry i ≠ batch j := by
  simp [geometry,batch,port_injective.eq_iff]
theorem batch_ne_recovery (i : Fin 6) (j : RecoveryBank) : batch i ≠ recovery j := by
  simp [batch,recovery,port_injective.eq_iff]

theorem scratch_ne_batch (i : Fin 4) (j : Fin 6) : scratch i ≠ batch j := by
  intro h
  have hh : (Fin.castAdd 6 i : Fin 10) = Fin.natAdd 4 j := Sum.inr.inj (Sum.inr.inj (port_injective h))
  have hv := congrArg (fun x : Fin 10 => x.val) hh
  change i.val = 4+j.val at hv
  have hi := i.isLt
  omega

abbrev plan := RecoveryBanks.plan recovery recovery_injective
abbrev crop := RecoveryBanks.crop recovery recovery_injective

/-- The actual gather output and retained row ruler are used without relocation. -/
def source : Fin tapes := geometry 108
def rowCount : Fin tapes := geometry 116

theorem handoff_regs :
    [plan.replicas,rowCount,plan.packet,scratch 0,scratch 1,source,plan.work 124,scratch 2,scratch 3].Nodup := by
  simp [plan,RecoveryBanks.plan,rowCount,source,recovery,scratch,geometry,port_injective.eq_iff]

theorem replicas_ne_count : plan.replicas ≠ plan.count := by
  simp [plan,RecoveryBanks.plan,recovery,port_injective.eq_iff]
theorem replicas_ne_spare : plan.replicas ≠ plan.spare := by
  simp [plan,RecoveryBanks.plan,recovery,port_injective.eq_iff]

theorem cropSupport_range (k : Fin tapes) (hk : plan.cropSupport crop k) : ∃ i, recovery i = k := by
  rcases hk with h | h | h | h | h
  · obtain ⟨i,rfl⟩ := h; exact ⟨.scalar i,rfl⟩
  · obtain ⟨i,rfl⟩ := h; exact ⟨.parameter i,rfl⟩
  · obtain ⟨i,rfl⟩ := h; exact ⟨.master i,rfl⟩
  · have hp := RecoveryBanks.crop_ports recovery recovery_injective
    simp only [ComputedRecoveryPlan.cropControls] at h
    rw [hp.1,hp.2.1] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_,rfl⟩
  · obtain ⟨i,_,rfl⟩ := h; exact ⟨.work i,rfl⟩

theorem geometry_off_support (i : Fin 117) (k : Fin tapes) (hk : plan.cropSupport crop k) : geometry i ≠ k := by
  obtain ⟨j,rfl⟩ := cropSupport_range k hk
  exact geometry_ne_recovery i j

theorem source_ne_output : source ≠ crop.reg 12 := by
  rw [(RecoveryBanks.crop_ports recovery recovery_injective).2.2]
  exact geometry_ne_recovery 108 _

/-- Every selector update stays outside the ordinary recovery bank. -/
theorem ready_geometry_ovr {s A N offset rows : ℕ} [NeZero s]
    {d : InverseMasterInput s} {r : RawRecoveryJob s}
    {wl : List (Fin (A+4))} {S : Stacks tapes A}
    (h : plan.CroppedReady crop d r N offset rows wl S) (B : Stacks 117 A) :
    plan.CroppedReady crop d r N offset rows wl (embOvr geometry B.get S) := by
  apply h.of_frame
  · intro k hk
    exact (embOvr_off _ _ (fun i => geometry_off_support i k hk)).2
  · intro i
    exact (embOvr_off _ _ (fun j => geometry_ne_recovery j (.work i))).1


end
end LocalRecoveryLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
