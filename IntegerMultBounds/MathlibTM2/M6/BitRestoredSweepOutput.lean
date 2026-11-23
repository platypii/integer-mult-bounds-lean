module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedSweepCharge

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

private theorem scannedPayload {V T : ℕ} (word : Fin V → ZMod 2) (S : Stacks T prime) (port : Fin T)
    (read : WordAtZero word (S.L port) (S.R port)) : RecordPayload port (fun _ => blank) 0 word S := by
  intro j
  rw [encodedOwnerCell,sub_zero]
  exact read j

private theorem scanTotal {t s f r h A B N K : ℕ}
    (bill : t+f ≤ s+r*((A*B)*(N*K))+h*(A*(B*N*K))) :
    t+f ≤ s+(r+h)*((A*B)*(N*K)) := by
  simpa only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using bill

private theorem scanFan_projection {k T R V : ℕ} (fan : Fin (k+2) ↪ Fin T) (ext : Fin T ↪ Fin R)
    (out : Fin k → Fin V → ZMod 2) (S : Stacks R prime) :
    HelperFan (fan.trans ext) out S ↔ HelperFan fan out (embStk ext S) := Iff.rfl

private theorem projectedScanUser {T R Q A : ℕ} {U : Type} (e : Fin T ↪ Fin R)
    (u : HS R Q A U) : (embDn e u).user = u.user := rfl

/-- Read the restored targets and return the collapsed parent words on one fixed program. -/
theorem restoredSweepOutputWithCharge (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let inner := (Fin.castAddEmb 14 (n := T)).trans (Fin.castAddEmb (142081*7))
    let placedFan := fan.trans (Fin.castAddEmb 14)
    let bank := fun k : I => targetScanBank placedFan (targetOwner n k)
    let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb T (m := 14)).trans (Fin.castAddEmb (142081*7)))
    let ext := (Fin.castAddEmb 142081 (n := (T+14)+142081*7)).trans (Fin.castAddEmb 10)
    ∀ (body : P → Pr P ((T+14)+142081*7) Q prime U), ∃ code, ∃ rate : ℕ,
    ∀ (w B W : ℕ) (x),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    let label := firstRowLabel w
    0 < K → 0 < B → ∀ u S y out, HelperFan ((fan.trans inner).trans ext) out S →
    (∀ j, (T+14)+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    (∀ i : Fin 3, S.L (ext (reg (i.castAdd 7))) = [separator] ∧
      S.R (ext (reg (i.castAdd 7))) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (ext (reg (i.natAdd 3))) = []) →
    (∀ k (j : Fin 7), S.L (ext (bank k j.succ)) = [] ∧ S.R (ext (bank k j.succ)) = []) →
    ∃ z F steps, Exec (fun g => embProg ext id (body g)) code (mk u S) steps (mk z F) ∧
      (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*(D*(N*K))) ∧
      z.user = u.user ∧ HelperFan (stageOutputFan n placedFan)
        (singleLabelBank label (Function.update (collapseLabelBank (B := B) (K := K) out)
          (Fin.last 142080) (fun _ => 0))) F := by
  intro I
  obtain ⟨states,build⟩ := scanRestoredTargetsWithCharge n
  refine ⟨max states 215,?_⟩
  intro T Q P U fan fits inner placedFan bank reg ext body
  obtain ⟨scan,scanRate,scanRun⟩ := build fan ((le_max_left _ _).trans fits) body
  let src : Fin 3 → Fin (T+14) := fun i : Fin 3 => (((i.castAdd 7).castAdd 4).natAdd T : Fin (T+14))
  have apart (i j) : placedFan i ≠ src j := by
    intro eq
    have h := congrArg Fin.val eq
    change (fan i).val = T+j.val at h
    exact (fan i).isLt.not_ge (h ▸ Nat.le_add_right T j.val)
  obtain ⟨combined,rate,run⟩ := scannedStageWithHandoffCharge (T := T+14) n placedFan ((le_max_right _ _).trans fits)
    src apart body scan
  refine ⟨combined,scanRate+rate,?_⟩
  intro w B W x K N D label hk hb u S y out restored fresh trace labels dims free scratch
  obtain ⟨v,A,m,ran,paid,user,words,controls,headers,_,retained⟩ :=
    scanRun w B W label x hk hb (embDn ext u) (embStk ext S) y out ((scanFan_projection _ ext out S).mp restored) trace labels dims free scratch
  have targets (k : I) := scannedPayload _ A _ (words k)
  obtain ⟨z,F,t,exec,cost,same,ready,_,_⟩ :=
    run w B W hb hk x y out u S v A m (scanRate*(D*(N*K)))
      ran paid (user.trans (projectedScanUser ext u)) fresh headers controls retained targets trace labels
  exact ⟨z,F,t,exec,fun js unique => scanTotal (cost js unique),same,ready⟩

private theorem placeSweep {T R Q : ℕ} {P U : Type} (e : Fin T ↪ Fin R)
    (body : P → Pr P T Q prime U) (p : Pr P T Q prime U) (u : HS R Q prime U) (S : Stacks R prime)
    {v C t price} (exec : Exec body p (mk (embDn e u) (embStk e S)) t (mk v C))
    (bill : ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js C ≤ tapeCharge cleanupWeight js (embStk e S)+price) :
    ∃ z F, Exec (fun g => embProg e id (body g)) (embProg e id p) (mk u S) t (mk z F) ∧
      (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price) ∧
      z.user = v.user ∧ embStk e F = C ∧
      ∀ j, (∀ i, e i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨z,F,ran,_,same,view,off⟩ := exec_emb (ι := id) (body' := fun g => embProg e id (body g))
    e.injective (fun _ => rfl) exec u rfl S rfl
  rw [← view] at bill
  exact ⟨z,F,ran,placedCleanup_cost_le e S F cleanupWeight t price off bill,same,view,off⟩

private theorem outsideSweep {T a b : ℕ} (j : Fin (T+a+b)) (h : T ≤ j.val) (i : Fin T) :
    (i.castAdd a).castAdd b ≠ j := fun eq => i.isLt.not_ge ((congrArg Fin.val eq) ▸ h)

private theorem joinedBill {m t s c f p r : ℕ} (a : m+c ≤ s+p) (b : t+f ≤ c+r) :
    m+t+f ≤ s+p+r := by omega

/-- Place the sweep below its private scan workspace and charge its execution once. -/
theorem sweepAndParentOutputWithCharge (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let inner := (Fin.castAddEmb 14 (n := T)).trans (Fin.castAddEmb (142081*7))
    let placedFan := fan.trans (Fin.castAddEmb 14)
    let bank := fun k : I => targetScanBank placedFan (targetOwner n k)
    let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb T (m := 14)).trans (Fin.castAddEmb (142081*7)))
    let ext := (Fin.castAddEmb 142081 (n := (T+14)+142081*7)).trans (Fin.castAddEmb 10)
    ∀ (body : P → Pr P T Q prime U) (sweep : Pr P T Q prime U), ∃ code, ∃ rate : ℕ,
    ∀ (w B W : ℕ) (x),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    let label := firstRowLabel w
    0 < K → 0 < B → ∀ u S v C m price y out,
    Exec body sweep (mk (embDn inner (embDn ext u)) (embStk inner (embStk ext S))) m (mk v C) →
    (∀ js : List _, js.Nodup → m+tapeCharge cleanupWeight js C ≤
      tapeCharge cleanupWeight js (embStk inner (embStk ext S))+price) →
    v.user = u.user → HelperFan fan out C →
    (∀ j, (T+14)+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    (∀ i : Fin 3, S.L (ext (reg (i.castAdd 7))) = [separator] ∧
      S.R (ext (reg (i.castAdd 7))) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (ext (reg (i.natAdd 3))) = []) →
    (∀ k (j : Fin 7), S.L (ext (bank k j.succ)) = [] ∧ S.R (ext (bank k j.succ)) = []) →
    ∃ z F steps, Exec (fun g => embProg ext id (embProg inner id (body g))) code (mk u S) steps (mk z F) ∧
      (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+rate*(D*(N*K))) ∧
      z.user = u.user ∧ HelperFan (stageOutputFan n placedFan)
        (singleLabelBank label (Function.update (collapseLabelBank (B := B) (K := K) out)
          (Fin.last 142080) (fun _ => 0))) F := by
  intro I
  obtain ⟨states,build⟩ := restoredSweepOutputWithCharge n
  refine ⟨states,?_⟩
  intro T Q P U fan fits inner placedFan bank reg ext body sweep
  let table := fun g => embProg inner id (body g)
  obtain ⟨output,rate,finish⟩ := build fan fits table
  refine ⟨.seq (embProg ext id (embProg inner id sweep)) output,rate,?_⟩
  intro w B W x K N D label hk hb u S v C m price y out ran bill user live fresh trace restore dims free scratch
  obtain ⟨v₁,C₁,r₁,b₁,u₁,h₁,off₁⟩ := placeSweep inner body sweep (embDn ext u) (embStk ext S) ran bill
  obtain ⟨v₂,C₂,r₂,b₂,u₂,h₂,off₂⟩ := placeSweep ext table (embProg inner id sweep) u S r₁ b₁
  have keep (j) (high : T ≤ j.val) : C₂.L (ext j) = S.L (ext j) ∧ C₂.R (ext j) = S.R (ext j) := by
    have h := off₁ j (outsideSweep j high)
    rw [← h₂] at h
    exact h
  have regs (i : Fin 10) := keep (reg i) (Nat.le_add_right T i.val)
  have privateTapes (k : I) (j : Fin 7) := keep (bank k j.succ)
    (show T ≤ (T+14)+(finProdFinEquiv (targetOwner n k,j)).val from
      (Nat.le_add_right T 14).trans (Nat.le_add_right _ _))
  rw [← h₁,← h₂] at live
  obtain ⟨z,F,t,done,paid,same,ready⟩ := finish w B W x hk hb v₂ C₂ y out ((scanFan_projection _ ext out C₂).mpr ((scanFan_projection fan inner out _).mpr live))
    (fun j high => by
      obtain ⟨l,r⟩ := off₂ j (outsideSweep j high)
      exact ⟨l.trans (fresh j high).1,r.trans (fresh j high).2⟩)
    trace restore
    (fun i => ⟨(regs _).1.trans (dims i).1,(regs _).2.trans (dims i).2⟩)
    (fun i => (regs _).2.trans (free i))
    (fun k j => ⟨(privateTapes k j).1.trans (scratch k j).1,(privateTapes k j).2.trans (scratch k j).2⟩)
  exact ⟨z,F,m+t,Exec.seq r₂ done,fun js hj => joinedBill (b₂ js hj) (paid js hj),
    same.trans (u₂.trans (u₁.trans user)),ready⟩

/-- Append the three binary scan dimensions and leave the remaining workspace blank. -/
private noncomputable def scanSeed {t : ℕ} (T : ℕ) (S : Stacks t prime) (dims : Fin 3 → ℕ) : Stacks T prime :=
  let cells (old : Fin t → List (Fin (prime+4))) (header : Fin 3 → List (Fin (prime+4))) (j : Fin T) :=
    if h : j.val < t then old ⟨j.val,h⟩ else
    if h : j.val-t < 3 then header ⟨j.val-t,h⟩ else []
  ⟨S.inp,S.out,cells S.L (fun _ => [separator]),cells S.R (fun i => binSyms (dims i).size (dims i))⟩

private theorem scanPlacement_val {t a b c d : ℕ} (j : Fin t) :
    ((((j.castAdd a).castAdd b).castAdd c).castAdd d).val = j.val := rfl

private theorem scanSeed_view {t T : ℕ} (e : Fin t ↪ Fin T) (val : ∀ i, (e i).val = i.val)
    (S : Stacks t prime) (dims : Fin 3 → ℕ) : embStk e (scanSeed T S dims) = S := by
  cases S
  simp [embStk,scanSeed,Function.comp_def,val]

private theorem scanSeed_shared {k t m T : ℕ} (fan : Fin k ↪ Fin t) (inner : Fin t ↪ Fin m)
    (ext : Fin m ↪ Fin T) (S : Stacks T prime) {base shared}
    (seed : embStk (inner.trans ext) S = base) (view : embStk fan base = shared) :
    embStk ((fan.trans inner).trans ext) S = shared :=
  (congrArg (embStk fan) seed).trans view

private theorem scanSeed_frame {t T k : ℕ} (e : Fin t ↪ Fin T) (val : ∀ i, (e i).val = i.val)
    (fan : Fin k ↪ Fin t) (S : Stacks t prime) (dims : Fin 3 → ℕ) (F : Stacks T prime)
    (frame : ∀ j, (∀ i, e (fan i) ≠ j) →
      F.L j = (scanSeed T S dims).L j ∧ F.R j = (scanSeed T S dims).R j) :
    (∀ j, (∀ i, fan i ≠ j) → F.L (e j) = S.L j ∧ F.R (e j) = S.R j) ∧
    (∀ (i : Fin 3) j, j.val = t+i.val → F.L j = [separator] ∧ F.R j = binSyms (dims i).size (dims i)) ∧
    ∀ j, t+3 ≤ j.val → F.L j = [] ∧ F.R j = [] := by
  have high j (h : t ≤ j.val) := frame j (fun i eq => by
    have v := congrArg Fin.val eq
    rw [val] at v
    exact (fan i).isLt.not_ge (v ▸ h))
  refine ⟨fun j hj => ?_,fun i j hj => ?_,fun j hj => ?_⟩
  · simpa [scanSeed,val] using frame (e j) (fun i eq => hj i (e.injective eq))
  · simpa [scanSeed,hj] using high j (hj ▸ Nat.le_add_right t i.val)
  · simpa [scanSeed,show ¬ j.val < t by omega,show ¬ j.val-t < 3 by omega] using high j (by omega)

/-- Run every packed invocation, restore the helper labels and return the parent owner bank. -/
theorem packedSweepAndParentOutput [M8.Machine.Net] (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (states T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U)
      (_ : states ≤ Q),
    let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb LeafCore.small)
    let stageBank := (Fin.castAddEmb 41 (n := T)).trans caller
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let outer := fun f => embProg stageBank id (table f)
    let inner := (Fin.castAddEmb 14 (n := T+41+273+LeafCore.small)).trans (Fin.castAddEmb (142081*7))
    let placedFan := (fan.trans stageBank).trans (Fin.castAddEmb 14)
    let ext := (Fin.castAddEmb 142081 (n := ((T+41+273+LeafCore.small)+14)+142081*7)).trans (Fin.castAddEmb 10)
    ∃ program, ∃ C : ℝ, ∃ rate : ℕ, ∀ (w B W : ℕ) (row : Descriptor), row.Positive →
      row.beforeH = B*prime^(64*((w+1)*64)) → row.beforeRows*row.rows*row.between*row.afterD = W →
      ∀ (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^(w+1))^16*(B*prime^(64*((w+1)*64))*((prime^(w+1))^112*W))
    let children := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
    (∀ i (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports i) x S →
      (∀ j, (∀ h, ports i h ≠ j) → S.L j = (initial i).L j ∧ S.R j = (initial i).R j) →
      ∃ z F t y, Exec (body i) (code i) (mk u S) t (mk z F) ∧ (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(localCost i + children i)) ∧
        z.user = u.user ∧ HelperFan (ports i) y F ∧ packedStageEffect n i (w+1) B W x y) →
    let K := (prime^(w+1))^112*W
    let N := prime^(64*((w+1)*64))
    let D := (prime^(w+1))^16*B
    let entry := singleLabelBank (B := B) (K := K) (firstRowLabel (w+1))
    let src := (((fan.trans stageBank).trans inner).trans ext)
    ∃ prepared, embStk src prepared = shared ∧
    ∀ x u S, HelperFan src (entry x) S →
    (∀ j, (∀ i, src i ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F t next, Exec (fun f => embProg ext id (embProg inner id (outer f))) program (mk u S) t (mk z F) ∧
      (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
        ((stageRuns.map localCost).sum+((List.range' (stageChildStart n)
        (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1+
        ⌈C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊)+rate*(D*(N*K))) ∧
      z.user = u.user ∧ HelperFan (stageOutputFan n placedFan) (entry next) F ∧
      sweepEffect n (w+1) B W x next := by
  obtain ⟨states,output⟩ := sweepAndParentOutputWithCharge n
  obtain ⟨T,fan,bank,portsAgree,stages⟩ := restoredStageRunsWithCharge n tapes ports
  refine ⟨max states columnCapacity,T,fan,bank,portsAgree,?_⟩
  intro P U Q body code fits caller stageBank table outer inner placedFan ext
  let bank' := fun k : (Fin 32 × Fin 5) × Fin 111 => targetScanBank placedFan (targetOwner n k)
  let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb (T+41+273+LeafCore.small) (m := 14)).trans (Fin.castAddEmb (142081*7)))
  obtain ⟨sweep,C,run⟩ := stages body code (restoreSlotChanges (stageFinalSlot n)) ((le_max_right _ _).trans fits)
  obtain ⟨program,rate,finish⟩ := output (fan.trans stageBank) ((le_max_left _ _).trans fits) outer sweep
  refine ⟨program,C,rate,?_⟩
  intro w B W row positive height width localCost childTime initial shared V children workers
  obtain ⟨prepared,view,execute⟩ := run w B W row positive height width localCost childTime initial shared workers
  intro K N D entry src
  have hb : 0 < B := Nat.pos_of_mul_pos_right (height ▸ positive.2.2.1)
  have hw : 0 < W := width ▸ Nat.mul_pos (Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1)
    positive.2.2.2.1) positive.2.2.2.2
  have hk : 0 < K := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hw
  let e := inner.trans ext
  let seed := scanSeed (T+41+273+LeafCore.small+14+142081*7+142081+10) prepared ![K,N,D]
  have placeVal (i : Fin (T+41+273+LeafCore.small)) : (e i).val = i.val :=
    scanPlacement_val (a := 14) (b := 142081*7) (c := 142081) (d := 10) i
  have seedView := scanSeed_view e placeVal prepared ![K,N,D]
  refine ⟨seed,?_,?_⟩
  · exact scanSeed_shared (fan.trans stageBank) inner ext seed seedView view
  intro x u S full frame
  let small := embStk inner (embStk ext S)
  have live := (scanFan_projection (fan.trans stageBank) inner (entry x) (embStk ext S)).mp
    ((scanFan_projection ((fan.trans stageBank).trans inner) ext (entry x) S).mp full)
  obtain ⟨workerFrame,headers,blank⟩ := scanSeed_frame e placeVal (fan.trans stageBank)
    prepared ![K,N,D] S frame
  have dims (i : Fin 3) := headers i (ext (reg (i.castAdd 7))) rfl
  have free (i : Fin 7) := (blank (ext (reg (i.natAdd 3))) (Nat.add_le_add_left (Nat.le_add_right 3 i.val) _)).2
  have scratch (k) (j : Fin 7) := blank (ext (bank' k j.succ))
    (show _+3 ≤ _+14+(finProdFinEquiv (targetOwner n k,j)).val from
      (Nat.add_le_add_left (by decide : 3 ≤ 14) _).trans (Nat.le_add_right _ _))
  have fresh (j) (hj : (T+41+273+LeafCore.small+14)+142081*7 ≤ j.val) := blank j
    (((Nat.add_le_add_left (by decide : 3 ≤ 14) _).trans (Nat.le_add_right _ _)).trans hj)
  obtain ⟨v,A,m,y,out,ran,bill,same,ready,trace,labels⟩ :=
    execute (entry x) (embDn inner (embDn ext u)) small live workerFrame
  rw [height] at labels
  obtain ⟨z,F,t,exec,paid,user,returned⟩ := finish (w+1) B W x hk hb u S v A m _ y out ran
    (fun js hj => by simpa only [Nat.add_assoc] using bill js hj)
    (same.trans ((projectedScanUser inner _).trans (projectedScanUser ext u))) ready fresh trace labels dims free scratch
  exact ⟨z,F,t,_,exec,(fun js hj => by simpa only [Nat.add_assoc] using paid js hj),user,returned,y,out,⟨trace,labels⟩,rfl⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
