import IntegerMultBounds.Machine.CompactNativeRoleChildBank

/-! Child row quotient/restore acts on actual exterior copied numeric43 tapes.
Every role word and retained controller/stack tape is framed without copying. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildHeadersPorts
noncomputable section
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactNativeRoleChildBank (prepare restore)
open CompactSpectatorLeafSetup (raw)
open CompactGadgetReservationShape (Shape)
variable {c t : ℕ}

def slot (t c : ℕ) : Fin 43 → Fin (callerTapes t c) := Fin.castAdd c ∘ Fin.natAdd t
theorem slot_injective (t c : ℕ) : Function.Injective (slot t c) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [slot] using hv
def placement (t c : ℕ) : Fin (43+(t+c)) ≃ Fin (callerTapes t c) :=
  InjectivePlacement.placement (slot t c) (slot_injective t c) (by unfold callerTapes; omega)

theorem active (old : Tapes t 2) (ht : 43<t) (st : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2) :
    Placement.active (placement t c) (external old ht st payload)=ActiveRepairRankHeadersCommands.bank st := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [placement,slot,external,Tapes.append,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank]

theorem extra (old : Tapes t 2) (ht : 43<t) (st su : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2) :
    Placement.extra (placement t c) (external old ht st payload)=
      Placement.extra (placement t c) (external old ht su payload) := by
  have outside (j : Fin (t+c)) (i : Fin 43) : placement t c (Fin.natAdd 43 j)≠slot t c i := by
    have he : placement t c (Fin.castAdd (t+c) i)=slot t c i := by simp [placement]
    rw [←he]
    intro h
    have hv := congrArg Fin.val ((placement t c).injective h)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals generalize hz : placement t c (Fin.natAdd 43 j)=z
  all_goals induction z using Fin.addCases (m:=t+43) (n:=c) with
  | right z => simp [external,Tapes.append]
  | left z =>
    induction z using Fin.addCases (m:=t) (n:=43) with
    | left z => simp [external,Tapes.append]
    | right z => exact False.elim (outside j z (hz.trans rfl))

def program (ops : List CompactChildHeadersArithmetic.Op) (t c : ℕ) :=
  Placement.placed (CompactChildHeadersArithmetic.compile (a:=2) ops).2 (placement t c)

private theorem framed (ops : List CompactChildHeadersArithmetic.Op)
    (old : Tapes t 2) (ht : 43<t) (st su : ActiveRepairRankHeadersCommands.State)
    (payload : Tapes (1+c) 2) (cost : ℕ)
    (h : HoareTime (CompactChildHeadersArithmetic.compile (a:=2) ops).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) cost) :
    HoareTime (program ops t c) (fun v => v=external old ht st payload)
      (fun v => v=external old ht su payload) cost := by
  have hh := Placement.hoare_at h (placement t c) (external old ht st payload) (active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra old ht st su payload,←active old ht su payload,Placement.view]

theorem prepare_runs (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (payload : Tapes (1+c) 2) (hc : 0<c) :
    HoareTime (program (prepare c) t c)
      (fun v => v=external old ht (raw s rows ell p rho left count slots right src dst) payload)
      (fun v => v=external old ht (raw s (rows/c) ell p rho left count slots right src dst) payload)
      (CompactChildHeadersArithmetic.scheduleCost (prepare c) (raw s rows ell p rho left count slots right src dst)) :=
  framed _ old ht _ _ payload _ (CompactNativeRoleChildBank.prepare_runs c s rows ell p rho left count slots right src dst hc)

theorem restore_runs (old : Tapes t 2) (ht : 43<t) (s : Shape)
    (rows ell p rho left count slots right src dst : ℕ) (payload : Tapes (1+c) 2)
    (hd : c∣rows) (hc : 0<c) (hr : 0<rows) :
    HoareTime (program (restore c) t c)
      (fun v => v=external old ht (raw s (rows/c) ell p rho left count slots right src dst) payload)
      (fun v => v=external old ht (raw s rows ell p rho left count slots right src dst) payload)
      (CompactChildHeadersArithmetic.scheduleCost (restore c) (raw s (rows/c) ell p rho left count slots right src dst)) :=
  framed _ old ht _ _ payload _ (CompactNativeRoleChildBank.restore_runs c s rows ell p rho left count slots right src dst hd hc hr)

end
end IntegerMultBounds.Machine.CompactNativeRoleChildHeadersPorts
