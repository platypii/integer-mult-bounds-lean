import IntegerMultBounds.Machine.CompactSpectatorLeafOriginal

/-! The actual leaf's native word is placed at original caller tape65, after
controller44. Its immutable ell/p ports follow all native-core workspace;
original descriptors and every exterior caller tape are framed literally. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafPlacement
noncomputable section
open CompactSpectatorLeafOriginal
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open SharedPlacementAlphabet (setTape)

abbrev source : Fin localCount := Fin.castAdd 2 (Fin.castAdd ButterflySpectatorPorts.count (Fin.natAdd 43 (0 : Fin 1)))
def ports : Fin (1+15) → Fin tapes := Fin.addCases
  (fun _ => Fin.castAdd 15 source) (Fin.natAdd localCount)
theorem ports_injective : Function.Injective ports := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact congrArg (Fin.castAdd 15) (Subsingleton.elim _ _)
    | right j =>
      have h := congrArg Fin.val he
      simp only [ports,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      unfold localCount at h
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have h := congrArg Fin.val he
      simp only [ports,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      unfold localCount at h
      omega
    | right j =>
      simp only [ports,Fin.addCases_right] at he
      exact congrArg (Fin.natAdd 1) (Fin.natAdd_injective _ _ he)

def payload (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) :=
  (CountedLoopReuseAlphabet.one f 0).append (originals vs)

theorem bank_payload (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) :
    SharedBank.payload (bank (fun _ => none) f vs) ports=payload f vs := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    simp only [ports,bank,localBank,CountedLoopHeaderClean.bank,
      CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,source,
      Fin.addCases_left,Fin.addCases_right]
    rfl
  | right i =>
    simp only [ports,bank,Tapes.append,Fin.addCases_right]

private theorem local_selected (i : Fin localCount) :
    (∃ j,ports j=Fin.castAdd 15 i) ↔ i=source := by
  constructor
  · rintro ⟨j,h⟩
    induction j using Fin.addCases with
    | left j =>
      simp only [ports,Fin.addCases_left] at h
      exact (Fin.castAdd_injective _ _ h).symm
    | right j =>
      have hh := congrArg Fin.val h
      simp only [ports,Fin.addCases_right,Fin.val_natAdd,Fin.val_castAdd] at hh
      have := i.isLt
      omega
  · rintro rfl; exact ⟨Fin.castAdd 15 (0 : Fin 1),by simp only [ports,Fin.addCases_left]⟩

private theorem original_selected (i : Fin 15) :
    ∃ j,ports j=Fin.natAdd localCount i := ⟨Fin.natAdd 1 i,by simp [ports]⟩

theorem bank_clean (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) :
    SharedBank.strip (bank (fun _ => none) f vs) ports=SharedBank.empty tapes 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | right i => simp only [original_selected,ite_true]
    | left i =>
      simp only [local_selected]
      split_ifs with hi
      · rfl
      · induction i using Fin.addCases with
        | right i => simp [bank,localBank,CountedLoopHeaderClean.bank,
            CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty]
        | left i =>
          induction i using Fin.addCases with
          | right i => simp [bank,localBank,CountedLoopHeaderClean.bank,
            CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty]
          | left i =>
            induction i using Fin.addCases with
            | left i =>
              induction i using Fin.addCases <;> simp [bank,localBank,CountedLoopHeaderClean.bank,
                CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty,
                ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller]
            | right i =>
              have hv := congrArg Fin.val (Subsingleton.elim i (0 : Fin 1))
              exact False.elim (hi (by apply Fin.ext; simp [source]))
  · funext i
    induction i using Fin.addCases with
    | right i => simp only [original_selected,ite_true]
    | left i =>
      simp only [local_selected]
      split_ifs with hi
      · rfl
      · induction i using Fin.addCases with
        | right i => simp [bank,localBank,CountedLoopHeaderClean.bank,
            CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty]
        | left i =>
          induction i using Fin.addCases with
          | right i => simp [bank,localBank,CountedLoopHeaderClean.bank,
            CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty]
          | left i =>
            induction i using Fin.addCases with
            | left i =>
              induction i using Fin.addCases <;> simp [bank,localBank,CountedLoopHeaderClean.bank,
                CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,Tapes.append,SharedBank.empty,
                ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller]
            | right i =>
              have hv := congrArg Fin.val (Subsingleton.elim i (0 : Fin 1))
              exact False.elim (hi (by apply Fin.ext; simp [source]))

abbrev callerCount (w : ℕ) := (110+w)+2
variable {w : ℕ}
def descriptor : Fin (13+2) → Fin (callerCount w) := Fin.addCases
  (fun i => Fin.castAdd 2 (Fin.castAdd w (⟨44+i.val,by omega⟩ : Fin 110)))
  (Fin.natAdd (110+w))
def common : Fin (1+15) → Fin (callerCount w) := Fin.addCases
  (fun _ => Fin.castAdd 2 (Fin.castAdd w (109 : Fin 110))) descriptor

theorem common_injective : Function.Injective (common (w:=w)) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact congrArg (Fin.castAdd 15) (Subsingleton.elim _ _)
    | right j =>
      induction j using Fin.addCases (m:=13) (n:=2) with
      | left j =>
        have hv := congrArg Fin.val h
        simp only [common,descriptor,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd] at hv
        omega
      | right j =>
        have hv := congrArg Fin.val h
        simp only [common,descriptor,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      induction i using Fin.addCases (m:=13) (n:=2) with
      | left i =>
        have hv := congrArg Fin.val h
        simp only [common,descriptor,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd] at hv
        omega
      | right i =>
        have hv := congrArg Fin.val h
        simp only [common,descriptor,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
    | right j =>
      apply congrArg (Fin.natAdd 1)
      induction i using Fin.addCases (m:=13) (n:=2) <;> induction j using Fin.addCases (m:=13) (n:=2)
      all_goals have hv := congrArg Fin.val h
      all_goals simp only [common,descriptor,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      · apply congrArg (Fin.castAdd 2); apply Fin.ext; omega
      · omega
      · omega
      · apply congrArg (Fin.natAdd 13); apply Fin.ext; omega

def program := Placement.placed CompactSpectatorLeafOriginal.program
  (CleanSubbank.placement ports (common (w:=w)) common_injective)


private theorem payload_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (hp : Function.Injective ps) (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.payload (setTape v (ps j) f p) ps=setTape (SharedBank.payload v ps) j f p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=j
  all_goals simp [SharedBank.payload,setTape,Function.update,hi,hp.eq_iff]

private theorem strip_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.strip (setTape v (ps j) f p) ps=SharedBank.strip v ps := by
  have hn (i : Fin n) (hi : ¬∃ k,ps k=i) : i≠ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j,ps j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals simp only [setTape,Function.update_of_ne (hn i hi)]

private theorem payload_replaced (f g : ℤ → Fin 6) (vs : Fin 15 → ℕ) :
    setTape (payload f vs) (Fin.castAdd 15 (0 : Fin 1)) g 0=payload g vs := by
  unfold payload
  rw [SharedPlacementAlphabet.setTape_append_left]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right sourceSlot targetSlot : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f)
    (caller : Tapes (callerCount w) 2)
    (hdata : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell p rho.val left (arity^k) slots right sourceSlot targetSlot)) :
    HoareTime (program (w:=w))
      (fun v => v=CleanSubbank.bank (s:=tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=tapes)
        (setTape caller (common (Fin.castAdd 15 (0 : Fin 1)))
          (CompactSpectatorLeafAxis.word (CompactSpectatorLeafLoop.run s rows ell p rho visit (arity^k) f)) 0))
      (CompactSpectatorLeafOriginal.cost s rows ell p rho visit slots right sourceSlot targetSlot) := by
  let vs := values s rows ell p rho.val left (arity^k) slots right sourceSlot targetSlot
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafLoop.run s rows ell p rho visit (arity^k) f)
  have hh := CompactSpectatorLeafOriginal.runs s rows ell p rho visit slots right sourceSlot targetSlot hG hA hr f hw
  change HoareTime CompactSpectatorLeafOriginal.program
    (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word f) vs)
    (fun v => v=bank (fun _ => none) g vs) _ at hh
  apply CleanSubbank.realizes CompactSpectatorLeafOriginal.program ports common ports_injective common_injective
    caller (setTape caller (common (Fin.castAdd 15 (0 : Fin 1))) g 0)
    (bank (fun _ => none) (CompactSpectatorLeafAxis.word f) vs) (bank (fun _ => none) g vs) _
    ?_ ?_ (bank_clean _ _) (bank_clean _ _) ?_ hh
  · rw [bank_payload]; exact hdata.symm
  · rw [bank_payload,payload_update _ _ common_injective,hdata,payload_replaced]
  · exact (strip_update _ _ _ _ _).symm

end
end IntegerMultBounds.Machine.CompactSpectatorLeafPlacement
