module

public import IntegerMultBounds.MathlibTM2.M6.BitRecordChildRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open Shared50ModularControl (prime)

/-- The physical contract of a procedure call on the host's tapes. -/
def RecordChildCall {A U : Type} {N T Q H : ℕ} (c : CutoffNodeInput)
    (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T)
    (dst : Fin (142081+2) ↪ Fin N) (bank : Fin N ↪ Fin (142082+T+N))
    (place : Fin (142082+T+N) ↪ Fin H) (outer : A → Pr A H Q prime U) (entry : A) (budget : ℕ) : Prop :=
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
  ∀ (data : Fin 142080 → Fin c.cells → ZMod 2) u S,
    HelperFan ((live.trans caller).trans place) data S →
    (∀ i : Fin 6, S.R (place (caller (record (i.castAdd 28)))) = (Routines.hdr c.node i).map bitSymbol) →
    S.R (place (caller (record 6))) = binSyms c.root.width.size c.cutoff →
    LengthControl (S.R (place (caller (record 7)))) c.cells →
    (∀ i : Fin 34, 8 ≤ i.val → S.R (place (caller (record i))) = []) →
    (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N; S.L (place j) = [] ∧ S.R (place j) = []) →
    (∀ i : Fin N, let j := i.natAdd (142082+T); S.L (place j) = [] ∧ S.R (place j) = []) →
    ∃ z F t y, Exec outer (.call entry) (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t budget ∧
      HelperFan (((childReturnFan dst).trans bank).trans place) (fun r => y r.castSucc) F ∧
      packedChildOutput (c.w+1) c.cells (data ∘ Fin.lastCases 0 id) y ∧
      (∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
        (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) →
        F.L (place (caller j)) = S.L (place (caller j)) ∧ F.R (place (caller j)) = S.R (place (caller j))) ∧
      ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j

/-- Call the compiled record entry in any host that installs its procedures.
Both the caller frame and all tapes outside the installation are preserved. -/
def InstalledRecordChildExec {P U : Type} {N T Q : ℕ} (c : CutoffNodeInput)
    (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T)
    (dst : Fin (142081+2) ↪ Fin N) (bank : Fin N ↪ Fin (142082+T+N))
    (host : Empty ⊕ P → Pr (Empty ⊕ P) (142082+T+N) Q prime U)
    (program : Pr (Empty ⊕ P) (142082+T+N) Q prime U) (budget : ℕ) : Prop :=
  ∀ {A : Type} {H : ℕ} (place : Fin (142082+T+N) ↪ Fin H) (label : Empty ⊕ P → A)
    (outer : A → Pr A H Q prime U) (entry : A),
    (∀ f, outer (label f) = embProg place label (host f)) →
    outer entry = embProg place label program →
    RecordChildCall c live record dst bank place outer entry budget

theorem SplitRecordChildExec.call {P U : Type} {N T Q : ℕ} {c : CutoffNodeInput}
    {live : Fin (142080+2) ↪ Fin T} {record : Fin 34 ↪ Fin T} {dst bank}
    {host : Empty ⊕ P → Pr (Empty ⊕ P) (142082+T+N) Q prime U} {program cost budget}
    (run : SplitRecordChildExec c live record dst bank host program cost) (fits : cost+2 ≤ budget) :
    InstalledRecordChildExec c live record dst bank host program budget := by
  intro A H place label outer entry installed dispatch
  dsimp only [RecordChildCall]
  intro data u S fan fields cut length scratch bridge vacant
  obtain ⟨v,D,n,y,exec,same,paid,returned,action,frame⟩ := run data (embDn place u) (embStk place S)
    fan fields cut length scratch bridge vacant
  obtain ⟨z,F,lifted,_,user,view,off⟩ := exec_emb place.injective installed exec u rfl S rfl
  rw [← view] at paid returned frame
  have charge := CleanupBound.place place off paid
  refine ⟨z,F,n+2,y,Exec.call (dispatch ▸ lifted),user.trans same,?_,returned,action,frame,off⟩
  intro js nd
  have h := charge js nd
  omega

/-- Install a directory of compiled children on one tape machine. Each index
has a callable entry and its own procedure labels, even when banks overlap. -/
noncomputable def recordChildDirectory {I U : Type} {H Q : ℕ} {P : I → Type} {size : I → ℕ}
    (place : ∀ i, Fin (size i) ↪ Fin H)
    (body : ∀ i, P i → Pr (P i) (size i) Q prime U)
    (program : ∀ i, Pr (P i) (size i) Q prime U) :
    (I ⊕ (Σ i, P i)) → Pr (I ⊕ (Σ i, P i)) H Q prime U :=
  Sum.elim (fun i => embProg (place i) (fun f => Sum.inr ⟨i,f⟩) (program i))
    (fun p => embProg (place p.1) (fun f => Sum.inr ⟨p.1,f⟩) (body p.1 p.2))

theorem InstalledRecordChildExec.inDirectory {I U : Type} {H Q : ℕ} {P : I → Type} {N T : I → ℕ}
    (place : ∀ i, Fin (142082+T i+N i) ↪ Fin H)
    (body : ∀ i, Empty ⊕ P i → Pr (Empty ⊕ P i) (142082+T i+N i) Q prime U)
    (program : ∀ i, Pr (Empty ⊕ P i) (142082+T i+N i) Q prime U)
    (i : I) {c : CutoffNodeInput} {live record dst bank budget}
    (run : InstalledRecordChildExec (N := N i) (T := T i) c live record dst bank (body i) (program i) budget) :
    RecordChildCall c live record dst bank (place i) (recordChildDirectory place body program) (.inl i) budget :=
  run (place i) (fun f => Sum.inr ⟨i,f⟩) _ (.inl i) (fun _ => rfl) rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
