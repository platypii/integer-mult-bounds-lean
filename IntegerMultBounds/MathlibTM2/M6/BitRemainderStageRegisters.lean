module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScheduledRoundTrip
public import IntegerMultBounds.MathlibTM2.M6.BitNineStageHandoff

/-! Identify the four binary words on the allocated stage with their ordinary handoff inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The scheduled scanner supplies the modulus and precision clock even
after the five return tapes have been appended to its entry bank. -/
theorem ordinaryEntryDimensions {w : ℕ} (extra W beforeRows rows beforeH : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4))) :
    let entry := ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes
    let words : Fin ((66+extra)+5) → List (Fin (prime+4)) := Fin.addCases (fun i : Fin (66+extra) => entry i.val) (fun _ : Fin 5 => [])
    ∃ modulus precision, words modulus = binSyms (prime^(w+1)).size (prime^(w+1)) ∧
      (words precision).length = w := by
  intro entry words
  let modulus : Fin (66+extra) := ⟨2,by omega⟩
  let precision : Fin (66+extra) := ⟨45,by omega⟩
  refine ⟨modulus.castAdd 5,precision.castAdd 5,?_,?_⟩
  · simp only [words,Fin.addCases_left]; rfl
  · simp only [words,Fin.addCases_left]
    exact List.length_replicate

open IntegerMultBounds.Networks Cover M8.RevMachine Cover.Fallback IntegerMultBounds.MathlibTM2.Fast.Main
open RecursiveInterchangeLayout (role)

/-- Run the actual scheduled scanner inside the one-owner round trip. -/
theorem scheduledOwnerRoundTrip_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ extra : ℕ, ∃ rate : ℝ, ∀ (w B W : ℕ), 0 < B → 0 < W →
      let layout := stagedScannerLayout w B W
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        (root = true → ∀ i, parent i = 1) → ∀ (prefixWidth : ℕ) (prefixes : ℕ → List (Fin (prime+4))),
        (∀ i < B, (prefixes i).length = prefixWidth) → prefixWidth ≤ prime^layout.width →
        ∀ (c : Certificates.PR589.Nine.PortCertificate) (checked : c.Checked),
    let M := prime^(w+1)
    let size := (66+(common+24+31+(work+extra)+1))+5
    let entryWords := ordinaryEntryWords (layout.between*layout.afterD) layout.beforeRows 1 layout.beforeH root parent prefixWidth
      ((List.range (layout.beforeRows*1*B)).flatMap prefixes)
    ∃ stage back : SharedBankStage.Stage _ 1 prime (phaseOwners (N := LabelMask.records (role layout 142080)*(M^128*(layout.between*layout.afterD)))),
      (∃ seed, ChartPrivateReady stage seed) ∧
      let Q := max (max stage.states columnCapacity) back.states
      let words : Fin size → List (Fin (prime+4)) := Fin.addCases
        (fun i : Fin (66+(common+24+31+(work+extra)+1)) => entryWords i.val) (fun _ : Fin 5 => [])
      ∃ body : Unit → Pr Unit ((size+stage.tapes+back.tapes)+99) Q prime U,
        OwnerRoundTrip (stage := stage) (words := words) (interval := interval) (parent := parent)
          (c := c) (checked := checked) (B := B) (W := W) body rate := by
  obtain ⟨extra,rate,scanner⟩ := scheduledReturn_exec (U := U) interval member space pool room fits pairRoom
  refine ⟨extra,rate,?_⟩
  intro w B W hb hw layout root parent units atRoot prefixWidth prefixes lengths small c checked M size entryWords
  obtain ⟨stage,back,seed,body,scan,scheduled⟩ := scanner w B W hb hw root parent units atRoot prefixWidth prefixes lengths small c checked
  obtain ⟨modulus,precision,modulusWord,precisionWord⟩ := ordinaryEntryDimensions
    (common+24+31+(work+extra)+1) (layout.between*layout.afterD) layout.beforeRows 1 layout.beforeH root parent
    prefixWidth ((List.range (layout.beforeRows*1*B)).flatMap prefixes)
  have capacity : 235 ≤ columnCapacity := (by decide : 235 ≤ 11192).trans remainderStates_fit
  exact ⟨stage,back,seed,body,scheduled.roundTrip modulus modulusWord precision precisionWord hb hw
    (capacity.trans ((le_max_right ..).trans (le_max_left ..)))⟩

/-- Stage registers 0, 1, 2 and 12 hold the tail width, row count, staging
block count and inherited block count, respectively. -/
def stageWordPorts : Fin 4 ↪ Fin 14 := ⟨![0,1,2,12],by decide⟩

/-- At the boundary between programs, the four retained inputs can be the
stage's actual registers. Every other scanner tape stays in its own bank. -/
theorem stageRegisterPlacement {T m : ℕ} (reg : Fin 14 ↪ Fin m) (payload : Fin m) (owner : Fin T)
    (apart : ∀ i, reg (stageWordPorts i) ≠ payload) :
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)),
      bank (aroundScanner owner 0) = payload.castAdd (T+99) ∧
      (∀ j, aroundScanner owner 0 ≠ j → (∀ i, retainedStagePorts T i ≠ j) → bank j = j.natAdd m) ∧
      ∀ {B N D K} (F : Stacks m prime) (S : Stacks (m+(T+99)) prime),
      embStk (Fin.castAdd (T+99)) S = F →
      StageDimensionWords (fun i => reg (i.castAdd 11)) K N D F →
      F.R (reg 12) = binSyms B.size B →
      ∀ i, let n := (![K,N,D,B] : Fin 4 → ℕ) i
        S.R (bank (retainedStagePorts T i)) = binSyms n.size n := by
  let single {t : ℕ} (j : Fin t) : Fin 1 ↪ Fin t := ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩
  have single_apply {t : ℕ} (j : Fin t) (i : Fin 1) : single j i = j := rfl
  let out := appendPorts (stageWordPorts.trans reg) (single payload) (fun i _ => apart i)
  have disjoint (i : Fin 4) : retainedStagePorts T i ≠ aroundScanner owner 0 :=
    retainedPort_private owner _ 0
  let input := appendPorts (retainedStagePorts T) (single (aroundScanner owner 0)) (fun i _ => disjoint i)
  obtain ⟨bank,share,privateTape⟩ := adjacentStagePlacement out input
  refine ⟨bank,?_,?_,?_⟩
  · simpa only [input,out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right,single_apply] using share ((0 : Fin 1).natAdd 4)
  · intro j ownerOff wordOff
    apply privateTape
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [input,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] using wordOff i
    | right i => simpa only [input,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_right,single_apply] using ownerOff
  intro B N D K F S view dims block i
  have placed := share (i.castAdd 1)
  simp only [input,out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] at placed
  rw [placed]
  have atPort := congrArg (fun C => C.R ((stageWordPorts.trans reg) i)) view
  apply atPort.trans
  fin_cases i
  · exact (dims 0).2
  · exact (dims 1).2
  · exact (dims 2).2
  · exact block

/-- The preceding stage can only affect the payload and its four retained
words. In particular all scanner entry words, scratch tapes and the three
header destinations read directly from the private bank. -/
private theorem stageScannerPrivate {T : ℕ} (owner : Fin T) (keep : Fin (T+99) → Prop)
    (privateTape : ∀ j, aroundScanner owner 0 ≠ j → (∀ i, retainedStagePorts T i ≠ j) → keep j) :
    (∀ j : Fin T, keep (j.castAdd 99)) ∧
    (∀ j : Fin 93, j ≠ 0 → keep (aroundScanner owner j)) ∧
    ∀ j : Fin 7, j = 0 ∨ j = 2 ∨ j = 4 → keep (retainedPort T j) := by
  let idx : Fin 4 ↪ Fin 7 := ⟨![6,1,5,3],by decide⟩
  have port (i : Fin 4) : retainedStagePorts T i = retainedPort T (idx i) := rfl
  refine ⟨?_,?_,?_⟩
  · intro j
    apply privateTape _ (aroundScanner_private owner 0 (by decide) j).symm
    intro i eq
    rw [port] at eq
    have h := congrArg Fin.val eq
    simp [retainedPort] at h
    omega
  · intro j hj
    exact privateTape _ ((aroundScanner owner).injective.ne hj.symm)
      (fun i => port i ▸ retainedPort_private owner (idx i) j)
  · intro j hj
    apply privateTape _ (retainedPort_private owner j 0).symm
    intro i eq
    rw [port] at eq
    have h := congrArg Fin.val eq
    have same : idx i = j := Fin.ext (by simpa [retainedPort] using h)
    have distinct : ∀ i, idx i ≠ 0 ∧ idx i ≠ 2 ∧ idx i ≠ 4 := by decide
    obtain ⟨a,b,c⟩ := distinct i
    rcases hj with h|h|h <;> subst j <;> contradiction

/-- The private scanner bank supplies all readiness and scratch conditions
after the stage writes its owner payload and retained dimensions. -/
theorem scannerReadyAfterStage {V size back : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} :
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    let old := Fin.castAddEmb 99 (n := T)
    ∀ (R₀ S : Stacks (T+99) prime), ScannerReady stage size back words (embStk old R₀) →
      (∀ j, j ≠ 0 → R₀.L (slots j) = [] ∧ R₀.R (slots j) = []) →
      (∀ j, j = 0 ∨ j = 2 ∨ j = 4 → R₀.R (retainedPort T j) = []) →
      (∀ j, slots 0 ≠ j → (∀ i, retainedStagePorts T i ≠ j) → S.L j = R₀.L j ∧ S.R j = R₀.R j) →
      ScannerReady stage size back words (embStk old S) ∧
      (∀ j, j ≠ 0 → S.L (slots j) = [] ∧ S.R (slots j) = []) ∧
      ∀ j, j = 0 ∨ j = 2 ∨ j = 4 → S.R (retainedPort T j) = [] := by
  intro T slots old R₀ S ready free blanks frame
  obtain ⟨entry,scratch,headers⟩ := stageScannerPrivate _ _ frame
  refine ⟨ready.of_owner_change (fun j _ => entry j),?_,?_⟩
  · intro j hj
    exact ⟨(scratch j hj).1.trans (free j hj).1,(scratch j hj).2.trans (free j hj).2⟩
  · intro j hj
    exact (headers j hj).2.trans (blanks j hj)

/-- Sequence a stage and a scanner on the same host, sharing the owner and
its four dimensions. All private scanner tapes start from their entry bank. -/
theorem runStageScanner {P U : Type} {m T q : ℕ} (reg : Fin 14 ↪ Fin m)
    (payload : Fin m) (owner : Fin T) (apart : ∀ i, reg (stageWordPorts i) ≠ payload) :
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)),
    bank (aroundScanner owner 0) = payload.castAdd (T+99) ∧
    ∀ (left : P → Pr P m q prime U) (right : Unit → Pr Unit (T+99) q prime U) a b,
    let leftBank := Fin.castAdd (T+99) (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g))
      (fun g => embProg bank Sum.inr (right g))
    ∀ u L (R₀ : Stacks (T+99) prime) v F t budget (tail N D B : ℕ) (post : U → Stacks (T+99) prime → Prop),
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      StageDimensionWords (fun i => reg (i.castAdd 11)) tail N D F →
      F.R (reg 12) = binSyms B.size B →
      (∀ (w : HS (T+99) q prime U) (S : Stacks (T+99) prime), w.user = v.user →
        (∀ i, let n := (![tail,N,D,B] : Fin 4 → ℕ) i
          S.R (retainedStagePorts T i) = binSyms n.size n) →
        S.L (aroundScanner owner 0) = F.L payload → S.R (aroundScanner owner 0) = F.R payload →
        (∀ j, aroundScanner owner 0 ≠ j → (∀ i, retainedStagePorts T i ≠ j) →
          S.L j = R₀.L j ∧ S.R j = R₀.R j) →
        ∃ z C s, Exec right b (mk w S) s (mk z C) ∧ s ≤ budget ∧ post z.user C) →
      ∃ z C steps, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks L R₀)) steps (mk z C) ∧ steps ≤ t+budget ∧ post z.user (embStk bank C) ∧
        ∀ j, j ≠ payload → (∀ i, reg (stageWordPorts i) ≠ j) →
          C.L (leftBank j) = F.L j ∧ C.R (leftBank j) = F.R j := by
  let single {k : ℕ} (j : Fin k) : Fin 1 ↪ Fin k := ⟨fun _ => j,fun _ _ _ => Subsingleton.elim _ _⟩
  let out := appendPorts (stageWordPorts.trans reg) (single payload) (fun i _ => apart i)
  let input := appendPorts (retainedStagePorts T) (single (aroundScanner owner 0))
    (fun _ _ => retainedPort_private owner _ 0)
  obtain ⟨bank,sharedPorts,_,compose⟩ := runAdjacentStages (P := P) (R := Unit) (U := U) (q := q) (A := prime) out input
  refine ⟨bank,sharedPorts ((0 : Fin 1).natAdd 4),?_⟩
  intro left right a b leftBank body u L R₀ v F t budget tail N D B post exec dims block next
  obtain ⟨z,C,s,run,cost,result,keep⟩ := compose left right a b u L R₀ v F t budget post exec (by
    intro w S user shared privateTape
    have ownerWord := shared ((0 : Fin 1).natAdd 4)
    refine next w S user ?_ ownerWord.1 ownerWord.2 ?_
    · intro i
      have word := (shared (i.castAdd 1)).2
      simp only [input,out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] at word
      apply word.trans
      fin_cases i
      · exact (dims 0).2
      · exact (dims 1).2
      · exact (dims 2).2
      · exact block
    · intro j h hs
      apply privateTape
      intro i
      induction i using Fin.addCases with
      | left i => simpa only [input,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left] using hs i
      | right i => fin_cases i; exact h)
  refine ⟨z,C,s,run,cost,result,?_⟩
  intro j hp hd
  apply keep
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [out,appendPorts,Function.Embedding.coeFn_mk,Fin.addCases_left,Function.Embedding.trans_apply] using hd i
  | right i => fin_cases i; exact hp.symm

open IntegerMultBounds.Swap.Modular Matrix
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Follow a completed stage by the scheduled owner scan in one execution. -/
theorem OwnerRoundTrip.afterStage [M8.Machine.Net] {P U : Type} {m V size back Q w B W : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))} {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {right : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {rate : ℝ}
    (trip : OwnerRoundTrip (stage := stage) (words := words) (interval := interval) (parent := parent)
      (c := c) (checked := checked) (B := B) (W := W) right rate)
    (reg : Fin 14 ↪ Fin m) (payload : Fin m) (apart : ∀ i, reg (stageWordPorts i) ≠ payload) :
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    let leftBank := Fin.castAdd (T+99) (n := m)
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)), ∃ scan : Pr Unit (T+99) Q prime U,
    bank (slots 0) = leftBank payload ∧
    ∀ (left : P → Pr P m Q prime U) a u L R₀ v F t
      (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) i,
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      StageDimensionWords (fun j => reg (j.castAdd 11)) tail (M^(64*64)) (A*B) F →
      F.R (reg 12) = binSyms B.size B →
      WordAtZero (singleLabelBank (firstRowLabel (w+1)) x i) (F.L payload) (F.R payload) →
      ScannerReady stage size back words (embStk (Fin.castAddEmb 99) R₀) →
      (∀ j, j ≠ 0 → R₀.L (slots j) = [] ∧ R₀.R (slots j) = []) →
      (∀ j, j = 0 ∨ j = 2 ∨ j = 4 → R₀.R (retainedPort T j) = []) →
      let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g))
      ∃ z C steps, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr scan))
        (mk u (adjacentStageStacks L R₀)) steps (mk z C) ∧
        steps ≤ t+⌊ownerRoundTripTime w B W rate c checked⌋₊ ∧
        (∀ j, j ≠ payload → (∀ h, reg (stageWordPorts h) ≠ j) →
          C.L (leftBank j) = F.L j ∧ C.R (leftBank j) = F.R j) ∧ z.user = v.user ∧
        ∃ staged, WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0)
          (C.L (bank (slots 0))) (C.R (bank (slots 0))) ∧
          let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
          let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
          let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
            ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
          ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k) := by
  intro T slots leftBank M A tail
  obtain ⟨scan,run⟩ := trip
  obtain ⟨bank,placedOwner,compose⟩ := runStageScanner (P := P) (U := U) (q := Q) reg payload (((stage.slots 0).natAdd size).castAdd back) apart
  refine ⟨bank,scan,placedOwner,?_⟩
  intro left a u L R₀ v F t x i exec dims block live ready fresh empty body
  obtain ⟨z,C,s,ran,paid,result,keep⟩ := compose left right a scan u L R₀ v F t ⌊ownerRoundTripTime w B W rate c checked⌋₊ tail _ _ B
    (fun user C => user = v.user ∧ ∃ staged : Fin (A*(B*tail)) → ZMod 2, WordAtZero (singleLabelBank (firstRowLabel (w+1)) (fun _ => staged) 0)
      (C.L (slots 0)) (C.R (slots 0)) ∧
          let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
          let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
          let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
            ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
          ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = x i (addr b y k)) exec dims block (by
    intro y S user headers hl hr frame
    obtain ⟨entry,scratch,blank⟩ := scannerReadyAfterStage R₀ S ready fresh empty frame
    obtain ⟨z,C,s,staged,ran,paid,zu,word,cells⟩ := run x i y S entry (blank 0 (by decide))
      (blank 2 (by decide)) (blank 4 (by decide)) headers (hl ▸ hr ▸ live) scratch
    exact ⟨z,C,s,ran,Nat.le_floor paid,zu.trans user,staged,word,cells⟩)
  exact ⟨z,C,s,ran,paid,keep,result⟩

/-- Read the selected ordinary owner from the allocated stage's final fan.
The stage trace and its original budget accompany the scanner inputs. -/
theorem stageHandoffOwner_exec {P U : Type} {m q : ℕ} {n : Fin 9} {w B W : ℕ}
    {left : P → Pr P m q prime U} {code : Pr P m q prime U}
    {src dst : Fin (142081+2) ↪ Fin m} {prepared : Stacks m prime} {budget : ℕ}
    (reg : Fin 14 ↪ Fin m) :
    let M := prime^(w+1)
    let tail := M^112*W
    let entry := singleLabelBank (B := B) (K := tail) (firstRowLabel (w+1))
    StageHandoffExec n (w+1) B W left code src dst prepared budget
      (fun F => StageDimensionWords (fun j => reg (j.castAdd 11)) tail (prime^(64*((w+1)*64))) (M^16*B) F ∧
        F.R (reg 12) = binSyms B.size B) →
    ∀ x u S, HelperFan src (entry x) S →
      (∀ j, (∀ h, src h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ v F t packed out, Exec left code (mk u S) t (mk v F) ∧ t ≤ budget ∧ v.user = u.user ∧
        StageTrace n (w+1) B W (entry x) packed out ∧
        StageDimensionWords (fun j => reg (j.castAdd 11)) tail (M^(64*64)) (M^16*B) F ∧
        F.R (reg 12) = binSyms B.size B ∧
        StageControls dst (M^16*(B*prime^(64*((w+1)*64))*tail)) F ∧
        ∀ i, let word := entry (Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0)) i
          WordAtZero word (F.L (dst (i.castAdd 2))) (F.R (dst (i.castAdd 2))) := by
  intro M tail entry run x u S live frame
  obtain ⟨v,F,t,p,y,exec,time,user,fan,trace,dims,block⟩ := run x u S live frame
  have rows : M^(64*64) = prime^(64*((w+1)*64)) := by
    dsimp [M]
    rw [← pow_mul]
    congr 1
    omega
  refine ⟨v,F,t,p,y,exec,time,user,trace,rows ▸ dims,block,?_,?_⟩
  · intro j z
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply] using fan (j.natAdd 142081) z
  intro i word z
  have cell := fanPayload fan i z
  rw [encodedOwnerCell] at cell
  simpa only [sub_zero,word,entry] using cell

/-- Run an allocated stage handoff and scan one of its output owners. -/
theorem OwnerRoundTrip.afterAllocatedStage [M8.Machine.Net] {P U : Type} {total V size back Q w B W : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))} {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {right : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {rate : ℝ}
    (trip : OwnerRoundTrip (stage := stage) (words := words) (interval := interval) (parent := parent)
      (c := c) (checked := checked) (B := B) (W := W) right rate)
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin total) (i : Fin 142081) :
    let m := total+14+142081*7+142081+10
    let reg := (((Fin.natAddEmb total (m := 14)).trans (Fin.castAddEmb (142081*7))).trans
      (Fin.castAddEmb 142081)).trans (Fin.castAddEmb 10)
    let dst := stageOutputFan n (fan.trans (Fin.castAddEmb 14))
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    let leftBank := Fin.castAdd (T+99) (n := m)
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)), ∃ scan : Pr Unit (T+99) Q prime U,
    ∀ (left : P → Pr P m Q prime U) a src prepared budget,
      StageHandoffExec n (w+1) B W left a src dst prepared budget
        (fun F => StageDimensionWords (fun j => reg (j.castAdd 11)) tail (prime^(64*((w+1)*64))) (A*B) F ∧
          F.R (reg 12) = binSyms B.size B) →
      ∀ (x : Fin 142081 → Fin (A*(B*tail)) → ZMod 2) u L R₀, HelperFan src (singleLabelBank (firstRowLabel (w+1)) x) L →
      (∀ j, (∀ h, src h ≠ j) → L.L j = prepared.L j ∧ L.R j = prepared.R j) →
      ScannerReady stage size back words (embStk (Fin.castAddEmb 99) R₀) →
      (∀ j, j ≠ 0 → R₀.L (slots j) = [] ∧ R₀.R (slots j) = []) →
      (∀ j, j = 0 ∨ j = 2 ∨ j = 4 → R₀.R (retainedPort T j) = []) →
      let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g))
      ∃ z C steps, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr scan))
        (mk u (adjacentStageStacks L R₀)) steps (mk z C) ∧
        steps ≤ budget+⌊ownerRoundTripTime w B W rate c checked⌋₊ ∧ z.user = u.user ∧
        ∃ packed out staged, StageTrace n (w+1) B W (singleLabelBank (firstRowLabel (w+1)) x) packed out ∧
          HelperFan (dst.trans (Fin.castAddEmb (T+99)))
            (singleLabelBank (firstRowLabel (w+1))
              (Function.update (Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0)) i staged)) C ∧
          let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
          let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
          let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
            ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
          ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0) i (addr b y k) := by
  intro m reg dst T slots leftBank M A tail
  have apart (h : Fin (142081+2)) (j : Fin 4) : reg (stageWordPorts j) ≠ dst h := by
    apply Ne.symm
    apply stageOutputFan_off_original
    intro k eq
    have h := congrArg Fin.val eq
    simp at h
    omega
  obtain ⟨bank,scan,placedOwner,compose⟩ := trip.afterStage (P := P) reg (dst (i.castAdd 2)) (apart (i.castAdd 2))
  refine ⟨bank,scan,?_⟩
  intro left a src prepared budget stageRun x u L R₀ represented frame ready fresh empty body
  obtain ⟨v,F,t,packed,out,exec,time,user,trace,dims,block,controls,words⟩ :=
    stageHandoffOwner_exec reg stageRun x (embDn leftBank u) L represented frame
  obtain ⟨z,C,s,ran,paid,keep,preserved,staged,word,cells⟩ := compose left a u L R₀ v F t _ i
    exec dims block (words i) ready fresh empty
  refine ⟨z,C,s,ran,paid.trans (Nat.add_le_add_right time _),preserved.trans user,
    packed,out,staged,trace,?_,cells⟩
  intro h
  refine Fin.addCases (fun j p => ?_) (fun j p => ?_) h
  · simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,sub_zero]
    change putWord _ 0 (List.ofFn fun l => SparseRoleCircuit.encode _) p = _
    by_cases same : j = i
    · subst j
      rw [placedOwner] at word
      simpa only [singleLabelBank,Function.update_self,Function.Embedding.trans_apply,Fin.castAddEmb_apply]
        using (word p).symm
    · have distinct := dst.injective.ne ((Fin.castAddEmb 2).injective.ne same)
      obtain ⟨hl,hr⟩ := keep (dst (j.castAdd 2)) distinct (apart (j.castAdd 2))
      simpa only [singleLabelBank,Function.update_of_ne same,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
        ← hl,← hr] using (words j p).symm
  · have distinct : j.natAdd 142081 ≠ i.castAdd 2 := by
      intro eq
      have h := congrArg Fin.val eq
      simp at h
      omega
    obtain ⟨hl,hr⟩ := keep _ (dst.injective.ne distinct) (apart (j.natAdd 142081))
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
      ite_self,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.castAddEmb_apply,← hl,← hr]
      using controls j p

/-- Package the stage followed by one owner pass in the node schedule interface. -/
theorem OwnerRoundTrip.allocatedPiece [M8.Machine.Net] {P U : Type} {total V size back Q w B W : ℕ}
    {stage : SharedBankStage.Stage _ 1 prime (phaseOwners (N := V))}
    {words : Fin size → List (Fin (prime+4))} {interval : ℕ × ℕ}
    {parent : Fin 64 → ZMod (prime^(w+1))} {c : Certificates.PR589.Nine.PortCertificate} {checked : c.Checked}
    {right : Unit → Pr Unit ((size+stage.tapes+back)+99) Q prime U} {rate : ℝ}
    (trip : OwnerRoundTrip (stage := stage) (words := words) (interval := interval) (parent := parent)
      (c := c) (checked := checked) (B := B) (W := W) right rate)
    (n : Fin 9) (fan : Fin (142081+2) ↪ Fin total) (i : Fin 142081) :
    let m := total+14+142081*7+142081+10
    let reg := (((Fin.natAddEmb total (m := 14)).trans (Fin.castAddEmb (142081*7))).trans
      (Fin.castAddEmb 142081)).trans (Fin.castAddEmb 10)
    let dst := stageOutputFan n (fan.trans (Fin.castAddEmb 14))
    let T := size+stage.tapes+back
    let slots := aroundScanner (((stage.slots 0).natAdd size).castAdd back)
    let leftBank := Fin.castAddEmb (T+99) (n := m)
    let M := prime^(w+1)
    let A := M^16
    let tail := M^112*W
    ∃ bank : Fin (T+99) ↪ Fin (m+(T+99)), ∃ scan : Pr Unit (T+99) Q prime U,
    ∀ (left : P → Pr P m Q prime U) a src prepared budget,
      StageHandoffExec n (w+1) B W left a src dst prepared budget
        (fun F => StageDimensionWords (fun j => reg (j.castAdd 11)) tail (prime^(64*((w+1)*64))) (A*B) F ∧
          F.R (reg 12) = binSyms B.size B) →
      ∀ R₀, ScannerReady stage size back words (embStk (Fin.castAddEmb 99) R₀) →
      (∀ j, j ≠ 0 → R₀.L (slots j) = [] ∧ R₀.R (slots j) = []) →
      (∀ j, j = 0 ∨ j = 2 ∨ j = 4 → R₀.R (retainedPort T j) = []) →
      let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g))
      PieceHandoff (w+1) B W (fun x y => ∃ packed out staged,
        StageTrace n (w+1) B W (singleLabelBank (firstRowLabel (w+1)) x) packed out ∧
        let carry := Function.update (collapseLabelBank out) (Fin.last 142080) (fun _ => 0)
        y = Function.update carry i staged ∧
        let proj := IntegerMultBounds.Swap.Modular.reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
        let frame := Matrix.fromBlocks (Matrix.diagonal parent) 0 0 (M8.ReversedExchange.rev 64)
        let addr := fun b y (k : Fin W) => stagedOwnerIndex b (FlatCoordinateLayout.index
          ((frame.mulVec y) ∘ (finSumFinEquiv : (Fin 64 ⊕ Fin 64) ≃ Fin 128).symm) k)
        ∀ b y k, staged (addr b ((Matrix.fromBlocks (1-proj) proj proj (1-proj)).mulVec y) k) = carry i (addr b y k))
        body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr scan)) (src.trans leftBank)
        (dst.trans leftBank) (adjacentStageStacks prepared R₀) (budget+⌊ownerRoundTripTime w B W rate c checked⌋₊) := by
  intro m reg dst T slots leftBank M A tail
  obtain ⟨bank,scan,run⟩ := trip.afterAllocatedStage (P := P) n fan i
  refine ⟨bank,scan,?_⟩
  intro left a src prepared budget stageRun R₀ ready fresh empty body x u S rep frame
  let R := embStk (Fin.natAdd m) S
  have privateRead (j : Fin (T+99)) : R.L j = R₀.L j ∧ R.R j = R₀.R j := by
    have h := frame (j.natAdd m) (by
      intro k eq
      have e := congrArg Fin.val eq
      change (src k).val = m+j.val at e
      omega)
    simpa only [adjacentStageStacks,Fin.addCases_right,R,embStk,Function.comp_apply] using h
  obtain ⟨z,C,t,exec,paid,user,p,out,y,trace,updated,cells⟩ := run left a src prepared budget stageRun
    x u (embStk leftBank S) R rep (by
      intro j hj
      have h := frame (leftBank j) (fun k eq => hj k (leftBank.injective eq))
      simpa [adjacentStageStacks,leftBank,embStk] using h)
    (ready.of_owner_change (fun j _ => privateRead _))
    (fun j hj => ⟨(privateRead _).1.trans (fresh j hj).1,(privateRead _).2.trans (fresh j hj).2⟩)
    (fun j hj => (privateRead _).2.trans (empty j hj))
  rw [show adjacentStageStacks (embStk leftBank S) R = S from splitStacks S] at exec
  exact ⟨z,C,t,_,exec,paid,user,updated,p,out,y,trace,rfl,cells⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
