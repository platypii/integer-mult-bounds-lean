module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeRecordLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open Shared50ModularControl (prime)

private theorem suffix_ne_prefix {a b : ℕ} (i : Fin b) (j : Fin a) : i.natAdd a ≠ j.castAdd b := by
  intro eq
  have h := congrArg Fin.val eq
  change a+i.val = j.val at h
  omega

private theorem splitOwnerCharge {T n V price : ℕ} {D F : Stacks T prime}
    (paid : ∀ js : List (Fin T), js.Nodup → n+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js D+(142081*(8*V+10+2*V)+1+price)) :
    CleanupBound D F n (142081*(10*V+10)+1+price) := by
  rw [← show 8*V+10+2*V = 10*V+10 by omega]
  exact paid

/-- Execution on the physical split owners, including the frame for the caller. -/
def SplitRecordChildExec {P U : Type} {N T Q : ℕ} (c : CutoffNodeInput)
    (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T)
    (dst : Fin (142081+2) ↪ Fin N) (bank : Fin N ↪ Fin (142082+T+N))
    (host : Empty ⊕ P → Pr (Empty ⊕ P) (142082+T+N) Q prime U)
    (program : Pr (Empty ⊕ P) (142082+T+N) Q prime U) (budget : ℕ) : Prop :=
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
  ∀ (data : Fin 142080 → Fin c.cells → ZMod 2) u S,
    HelperFan (live.trans caller) data S →
    (∀ i : Fin 6, S.R (caller (record (i.castAdd 28))) = (Routines.hdr c.node i).map bitSymbol) →
    S.R (caller (record 6)) = binSyms c.root.width.size c.cutoff →
    LengthControl (S.R (caller (record 7))) c.cells →
    (∀ i : Fin 34, 8 ≤ i.val → S.R (caller (record i)) = []) →
    (∀ i : Fin 142082, let j := (i.castAdd T).castAdd N; S.L j = [] ∧ S.R j = []) →
    (∀ i : Fin N, let j := i.natAdd (142082+T); S.L j = [] ∧ S.R j = []) →
    ∃ z F t y, Exec host program (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t budget ∧
      HelperFan ((childReturnFan dst).trans bank) (fun r => y r.castSucc) F ∧
      packedChildOutput (c.w+1) c.cells (data ∘ Fin.lastCases 0 id) y ∧
      ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
        (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) →
        F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j)

/-- Only the two live control tapes can be shared with the placed child bank. -/
def ChildBankFrame {N T : ℕ} (live : Fin (142080+2) ↪ Fin T) (bank : Fin N ↪ Fin (142082+T+N)) : Prop :=
  ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) → ∀ h, bank h ≠ (j.natAdd 142082).castAdd N

/-- Initialize the child bank beside its caller, materialize the split owners,
and execute the child. The returned fan and the cleanup ledger are on the same host. -/
theorem runRecordChild {Config : Type} {N : ℕ} {input : Config → CutoffNodeInput}
    {seed : Config → Stacks N prime} (loader : LoadsNodeSeedFromRecord input seed) :
    ∃ rate : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P N Q prime U)
      (code : Pr P N Q prime U) (src dst : Fin (142081+2) ↪ Fin N)
      (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
      (∀ i j, 8 ≤ j.val → record j ≠ live i) →
      let H := 142082+T+N
      ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
        (program : Pr (Empty ⊕ P) H Q prime U),
      (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧ ChildBankFrame live bank ∧ ∀ (x : Config) (price : ℕ), let c := input x
        PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput (c.w+1) c.cells)
          body code src dst (seed x) price →
        SplitRecordChildExec c live record dst bank host program
          (rate*c.cells+(142081*(10*c.cells+10)+1+price)) := by
  obtain ⟨rate,install⟩ := loader.onLayout
  refine ⟨rate,?_⟩
  intro P U T Q body code src dst live record scratchOff H
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
  obtain ⟨bank,host,program,installed,frame,execute⟩ := runSplitOwnerFamily (body := body) code src dst live
  obtain ⟨setup,load⟩ := install host (Fin.natAddEmb (142082+T)) (record.trans caller)
    (fun i j => suffix_ne_prefix i _)
  refine ⟨bank,host,setup.seq program,installed,frame,?_⟩
  intro x price c child
  dsimp only [SplitRecordChildExec]
  intro data u S fan fields cut length scratch bridge vacant
  obtain ⟨v,D,n,start,same,paid,ready,off⟩ := load x u S fields cut length scratch vacant
  have kept j (safe : ∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) :=
    off (caller j) (fun i => suffix_ne_prefix i _) (fun i h => caller.injective.ne (safe i h))
  have fresh (i : Fin 142082) := off ((i.castAdd T).castAdd N) (fun j => suffix_ne_prefix j _)
    (fun j _ => (Fin.castAddEmb N).injective.ne (suffix_ne_prefix (record j) i))
  obtain ⟨z,F,m,y,finish,charge,user,_,acts,returned,keptFrame⟩ := execute (seed x) cleanupWeight (2*c.cells)
    (packedChildOutput (c.w+1) c.cells) (fun word len => by simp [cleanupWeight,len,Nat.add_comm]) child data v D
    (helperFan_of_agree fan (fun i => kept (live i) (fun j h => scratchOff i j h)))
    (fun i => ⟨(fresh i).1.trans (bridge i).1,(fresh i).2.trans (bridge i).2⟩) ready
  refine ⟨z,F,_,y,start.seq finish,user.trans same,?_,returned,acts,?_⟩
  · exact paid.seq (splitOwnerCharge (V := c.cells) charge)
  · intro j outside safe
    exact ⟨(keptFrame j outside).1.trans (kept j safe).1,(keptFrame j outside).2.trans (kept j safe).2⟩

/-- A single entry program works for every runtime configuration of this child. -/
def SplitRecordChildFamily {P U Config : Type} {N Q : ℕ} (input : Config → CutoffNodeInput)
    (body : P → Pr P N Q prime U) (dst : Fin (142081+2) ↪ Fin N) (price : Config → ℕ) : Prop :=
  ∃ rate : ℕ, ∀ {T : ℕ} (live : Fin (142080+2) ↪ Fin T) (record : Fin 34 ↪ Fin T),
    (∀ i j, 8 ≤ j.val → record j ≠ live i) →
    let H := 142082+T+N
    ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U), (∀ f, host (.inr f) = embProg bank Sum.inr (body f)) ∧ ChildBankFrame live bank ∧ ∀ x, let c := input x
        SplitRecordChildExec c live record dst bank host program
          (rate*c.cells+(142081*(10*c.cells+10)+1+price x))

theorem splitRecordChildFamily {P U Config : Type} {N Q : ℕ} {input : Config → CutoffNodeInput}
    {seed : Config → Stacks N prime} (loader : LoadsNodeSeedFromRecord input seed)
    {body : P → Pr P N Q prime U} {code src dst} {price : Config → ℕ}
    (child : ∀ x, let c := input x
      PackedPieceHandoffWithCharge cleanupWeight c.cells (packedChildOutput (c.w+1) c.cells)
        body code src dst (seed x) (price x)) :
    SplitRecordChildFamily (P := P) (U := U) (Q := Q) input body dst price := by
  obtain ⟨rate,build⟩ := runRecordChild loader
  refine ⟨rate,?_⟩
  intro T live record apart H
  obtain ⟨bank,host,program,installed,frame,execute⟩ := build body code src dst live record apart
  exact ⟨bank,host,program,installed,frame,fun x => execute x (price x) (child x)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
