import IntegerMultBounds.Machine.CompactNativeRoleScalarProducer

/-! Fixed native role execution at the real global source43 port. Numeric
original13 storage is separate from the retained original scalar caller bank;
all other caller tapes are stationary and all appended private storage clears. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleSourcePorts
noncomputable section
open CompactNativeRoleInstall (rawCount)
open ActiveRepairRankHeadersCommands (State)
variable {c t : ℕ}

abbrev localTapes (c : ℕ) := 43+rawCount c
abbrev publicTapes (c : ℕ) := 43+(1+c)
abbrev callerTapes (t c : ℕ) := (t+43)+c

def ports (c : ℕ) : Fin (publicTapes c) → Fin (localTapes c) :=
  Fin.addCases (m:=43) (n:=1+c) (Fin.castAdd (rawCount c)) (fun i => ⟨43+i.val,by have := i.isLt; unfold localTapes rawCount CompactNativeRoleDestructive.localCount; omega⟩)

def common (t c : ℕ) (ht : 43<t) : Fin (publicTapes c) → Fin (callerTapes t c) :=
  Fin.addCases (m:=43) (n:=1+c) (fun i => ⟨t+i.val,by have := i.isLt; unfold callerTapes; omega⟩)
    (fun i => if h : i.val=0 then ⟨43,by unfold callerTapes; omega⟩
      else ⟨t+43+(i.val-1),by have := i.isLt; unfold callerTapes; omega⟩)

theorem ports_injective (c : ℕ) : Function.Injective (ports c) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  induction i using Fin.addCases (m:=43) (n:=1+c) with
  | left i =>
    induction j using Fin.addCases (m:=43) (n:=1+c) with
    | left j => simpa [ports] using hv
    | right j => have := i.isLt; simp [ports] at hv; omega
  | right i =>
    induction j using Fin.addCases (m:=43) (n:=1+c) with
    | left j => have := j.isLt; simp [ports] at hv; omega
    | right j => simp [ports] at hv ⊢; omega

theorem common_injective (t c : ℕ) (ht : 43<t) : Function.Injective (common t c ht) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  induction i using Fin.addCases (m:=43) (n:=1+c) with
  | left i =>
    induction j using Fin.addCases (m:=43) (n:=1+c) with
    | left j => simp [common] at hv ⊢; omega
    | right j =>
      have := i.isLt
      simp only [common,Fin.addCases_left,Fin.addCases_right] at hv
      split_ifs at hv <;> dsimp at hv
      all_goals simp only [Fin.val_castAdd,Fin.val_natAdd]; omega
  | right i =>
    induction j using Fin.addCases (m:=43) (n:=1+c) with
    | left j =>
      have := j.isLt
      simp only [common,Fin.addCases_left,Fin.addCases_right] at hv
      split_ifs at hv <;> dsimp at hv
      all_goals simp only [Fin.val_castAdd,Fin.val_natAdd]; omega
    | right j =>
      simp only [common,Fin.addCases_right] at hv
      split_ifs at hv <;> dsimp at hv
      all_goals simp only [Fin.val_natAdd]; omega

def source (t : ℕ) (ht : 43<t) : Fin t := ⟨43,ht⟩
def replaceSource (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) : Tapes t 2 :=
  ⟨fun i => if i=source t ht then payload.head 0 else old.head i,
   fun i => if i=source t ht then payload.tape 0 else old.tape i⟩
def roles (payload : Tapes (1+c) 2) : Tapes c 2 :=
  ⟨fun i => payload.head ⟨i.val+1,by omega⟩,fun i => payload.tape ⟨i.val+1,by omega⟩⟩
def external (old : Tapes t 2) (ht : 43<t) (st : State) (payload : Tapes (1+c) 2) :=
  ((replaceSource old ht payload).append (ActiveRepairRankHeadersCommands.bank st)).append (roles payload)

theorem ports_payload (st : State) (payload : Tapes (1+c) 2) :
    SharedBank.payload (CompactNativeRoleOriginal.bank st payload) (ports c)=
      (ActiveRepairRankHeadersCommands.bank st).append payload := by
  have point (i : Fin (publicTapes c)) :
      (SharedBank.payload (CompactNativeRoleOriginal.bank st payload) (ports c)).head i=
        ((ActiveRepairRankHeadersCommands.bank st).append payload).head i ∧
      (SharedBank.payload (CompactNativeRoleOriginal.bank st payload) (ports c)).tape i=
        ((ActiveRepairRankHeadersCommands.bank st).append payload).tape i := by
    induction i using Fin.addCases (m:=43) (n:=1+c) with
    | left i =>
      simp only [SharedBank.payload,ports,Fin.addCases_left,CompactNativeRoleOriginal.bank,Tapes.append,Fin.addCases_left]
      trivial
    | right i =>
      have he : ports c (Fin.natAdd 43 i)=
        Fin.natAdd 43 (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 i)))) := by simp only [ports,Fin.addCases_right]; exact Fin.ext rfl
      simp only [SharedBank.payload,he,CompactNativeRoleOriginal.bank,Tapes.append,
        Fin.addCases_right,CompactNativeRoleInstall.blankRaw,Fin.addCases_left]
      trivial
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

theorem common_payload (old : Tapes t 2) (ht : 43<t) (st : State) (payload : Tapes (1+c) 2) :
    SharedBank.payload (external old ht st payload) (common t c ht)=
      (ActiveRepairRankHeadersCommands.bank st).append payload := by
  have point (i : Fin (publicTapes c)) :
      (SharedBank.payload (external old ht st payload) (common t c ht)).head i=
        ((ActiveRepairRankHeadersCommands.bank st).append payload).head i ∧
      (SharedBank.payload (external old ht st payload) (common t c ht)).tape i=
        ((ActiveRepairRankHeadersCommands.bank st).append payload).tape i := by
    induction i using Fin.addCases (m:=43) (n:=1+c) with
    | left i =>
      have he : common t c ht (Fin.castAdd (1+c) i)=Fin.castAdd c (Fin.natAdd t i) := by simp only [common,Fin.addCases_left]; exact Fin.ext rfl
      simp only [SharedBank.payload,he,external,Tapes.append,Fin.addCases_left,Fin.addCases_right]
      trivial
    | right i =>
      by_cases hi : i.val=0
      · have he : common t c ht (Fin.natAdd 43 i)=
          Fin.castAdd c (Fin.castAdd 43 (source t ht)) := by simp only [common,Fin.addCases_right,dite_eq_left hi]; exact Fin.ext rfl
        have hz : i=0 := Fin.ext hi
        simp only [SharedBank.payload]
        rw [he]
        simp [hz,external,Tapes.append,replaceSource]
      · have he : common t c ht (Fin.natAdd 43 i)=
          Fin.natAdd (t+43) ⟨i.val-1,by have := i.isLt; omega⟩ := by simp only [common,Fin.addCases_right,dite_eq_right hi]; exact Fin.ext rfl
        have hz : (⟨i.val-1+1,by have := i.isLt; omega⟩ : Fin (1+c))=i := by apply Fin.ext; dsimp; omega
        simp only [SharedBank.payload,he,external,Tapes.append,Fin.addCases_right,roles,hz]
        trivial
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2


theorem port_val (c : ℕ) (i : Fin (publicTapes c)) : (ports c i).val=i.val := by
  induction i using Fin.addCases (m:=43) (n:=1+c) <;> simp [ports]

theorem has_port (c : ℕ) (i : Fin (localTapes c)) :
    (∃ j,ports c j=i) ↔ i.val<publicTapes c := by
  constructor
  · rintro ⟨j,rfl⟩
    rw [port_val]
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext (port_val c _)⟩

theorem local_private (st : State) (payload : Tapes (1+c) 2)
    (i : Fin (localTapes c)) (hi : ¬i.val<publicTapes c) :
    (CompactNativeRoleOriginal.bank st payload).head i=0 ∧
      (CompactNativeRoleOriginal.bank st payload).tape i=fun _ => blank := by
  induction i using Fin.addCases (m:=43) (n:=rawCount c) with
  | left i => have := i.isLt; simp only [Fin.val_castAdd] at hi; unfold publicTapes at hi; omega
  | right i =>
    induction i using Fin.addCases (m:=CompactNativeRoleDestructive.localCount c+1) (n:=2) with
    | right i => simp [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,Tapes.append,SharedBank.empty]
    | left i =>
      induction i using Fin.addCases (m:=CompactNativeRoleDestructive.localCount c) (n:=1) with
      | right i => simp [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,Tapes.append,SharedBank.empty]
      | left i =>
        induction i using Fin.addCases (m:=(1+c)+2) (n:=2) with
        | right i => simp [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,Tapes.append,SharedBank.empty]
        | left i =>
          induction i using Fin.addCases (m:=1+c) (n:=2) with
          | right i => simp [CompactNativeRoleOriginal.bank,CompactNativeRoleInstall.blankRaw,Tapes.append,SharedBank.empty]
          | left i =>
            have := i.isLt
            simp only [Fin.val_castAdd,Fin.val_natAdd] at hi
            unfold publicTapes at hi
            omega

theorem local_strip (st : State) (payload : Tapes (1+c) 2) :
    SharedBank.strip (CompactNativeRoleOriginal.bank st payload) (ports c)=SharedBank.empty (localTapes c) 2 := by
  have point (i : Fin (localTapes c)) :
      (SharedBank.strip (CompactNativeRoleOriginal.bank st payload) (ports c)).head i=0 ∧
      (SharedBank.strip (CompactNativeRoleOriginal.bank st payload) (ports c)).tape i=fun _ => blank := by
    by_cases hi : i.val<publicTapes c
    · simp [SharedBank.strip,(has_port c i).mpr hi]
    · simpa only [SharedBank.strip,show ¬∃ j,ports c j=i from fun h => hi ((has_port c i).mp h),ite_false]
        using local_private st payload i hi
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2


theorem external_frame (old : Tapes t 2) (ht : 43<t) (st : State)
    (before after : Tapes (1+c) 2) :
    SharedBank.strip (external old ht st before) (common t c ht)=
      SharedBank.strip (external old ht st after) (common t c ht) := by
  have point (i : Fin (callerTapes t c)) :
      (SharedBank.strip (external old ht st before) (common t c ht)).head i=
        (SharedBank.strip (external old ht st after) (common t c ht)).head i ∧
      (SharedBank.strip (external old ht st before) (common t c ht)).tape i=
        (SharedBank.strip (external old ht st after) (common t c ht)).tape i := by
    by_cases hi : ∃ j,common t c ht j=i
    · simp [SharedBank.strip,hi]
    · simp only [SharedBank.strip,hi,ite_false]
      induction i using Fin.addCases (m:=t+43) (n:=c) with
      | right i =>
        have hp : common t c ht (Fin.natAdd 43 (⟨i.val+1,by omega⟩ : Fin (1+c)))=Fin.natAdd (t+43) i := by
          simp only [common,Fin.addCases_right]
          rw [dite_eq_right (by omega)]
          apply Fin.ext
          dsimp
        exact (hi ⟨_,hp⟩).elim
      | left i =>
        induction i using Fin.addCases (m:=t) (n:=43) with
        | right i =>
          have hp : common t c ht (Fin.castAdd (1+c) i)=Fin.castAdd c (Fin.natAdd t i) := by
            simp only [common,Fin.addCases_left]
            exact Fin.ext rfl
          exact (hi ⟨_,hp⟩).elim
        | left i =>
          have hn : i≠source t ht := by
            intro hh
            subst i
            have hp : common t c ht (Fin.natAdd 43 0)=
                Fin.castAdd c (Fin.castAdd 43 (source t ht)) := by simp [common,source]
            exact hi ⟨_,hp⟩
          simp [external,Tapes.append,replaceSource,hn]
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

def placed {q : ℕ} (M : Program (localTapes c) q 2) (t : ℕ) (ht : 43<t) :=
  Placement.placed M (CleanSubbank.placement (ports c) (common t c ht) (common_injective t c ht))

theorem realizes {q : ℕ} (M : Program (localTapes c) q 2) (old : Tapes t 2) (ht : 43<t)
    (st : State) (before after : Tapes (1+c) 2) (cost : ℕ)
    (h : HoareTime M
      (fun v => v=CompactNativeRoleOriginal.bank st before)
      (fun v => v=CompactNativeRoleOriginal.bank st after) cost) :
    HoareTime (placed M t ht)
      (fun v => v=CleanSubbank.bank (s:=localTapes c) (external old ht st before))
      (fun v => v=CleanSubbank.bank (s:=localTapes c) (external old ht st after)) cost := by
  exact CleanSubbank.realizes M (ports c) (common t c ht) (ports_injective c) (common_injective t c ht)
    (external old ht st before) (external old ht st after)
    (CompactNativeRoleOriginal.bank st before) (CompactNativeRoleOriginal.bank st after) cost
    ((ports_payload st before).trans (common_payload old ht st before).symm)
    ((ports_payload st after).trans (common_payload old ht st after).symm)
    (local_strip st before) (local_strip st after) (external_frame old ht st before after) h


theorem splits (s : CompactGadgetReservationShape.Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p)
    (old : Tapes t 2) (ht : 43<t) :
    HoareTime (placed (CompactNativeRoleOriginal.splitProgram c) t ht)
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right src dst)
          (CompactNativeRoleReservedBridge.sourcePayload s rows ell f c)))
      (fun v => v=CleanSubbank.bank (s:=localTapes c)
        (external old ht (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right src dst)
          (CompactNativeRoleReservedBridge.rolePayload s rows c ell hd f)))
      (CompactNativeRoleOriginal.cost false (rows/c) c s ell p rho left count slots right src dst) := by
  exact realizes _ old ht _ _ _ _
    (CompactNativeRoleReservedBridge.splits s rows c ell p rho left count slots right src dst hc hr hd hG hA hK f hw)

end
end IntegerMultBounds.Machine.CompactNativeRoleSourcePorts
