module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyRecordSetup
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryWidth
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryLeaf
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedScan
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Run a parent chart and the recursive directory stage on their shared owner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Insert the four mask work tapes and six replay tapes immediately before
the five owner registers, so register zero still shares the chart payload. -/
def directoryChartPlacement (T : ℕ) : Fin (T+5) ↪ Fin ((T+10)+5) where
  toFun i := ⟨if i.val < T then i.val else i.val+10, by split <;> omega⟩
  inj' := by
    intro i j eqn
    have h := congrArg Fin.val eqn
    change (if i.val < T then i.val else i.val+10) = (if j.val < T then j.val else j.val+10) at h
    apply Fin.ext
    split at h <;> split at h <;> omega

def directoryChartWork (T : ℕ) : Fin 10 ↪ Fin ((T+10)+5) :=
  (Fin.natAddEmb T).trans (Fin.castAddEmb 5)

def directoryChartReplay (T : ℕ) : Fin 6 ↪ Fin ((T+10)+5) :=
  (Fin.natAddEmb 4).trans (directoryChartWork T)

def directoryChartMasks {T : ℕ} (live bad : Fin T) (apart : live ≠ bad) : Fin 6 ↪ Fin ((T+10)+5) :=
  let work := directoryChartWork T
  let place := directoryChartPlacement T
  ⟨![place (live.castAdd 5),place (bad.castAdd 5),work 0,work 1,work 2,work 3],by
    intro i j eqn
    have small (s : Fin T) (k : Fin 10) : place (s.castAdd 5) ≠ work k := by
      intro h
      have eq := congrArg Fin.val h
      simp [place,directoryChartPlacement,work,directoryChartWork,s.isLt] at eq
      omega
    have diff : place (live.castAdd 5) ≠ place (bad.castAdd 5) :=
      place.injective.ne ((Fin.castAddEmb 5).injective.ne apart)
    fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact False.elim (diff eqn)
    | exact False.elim (diff eqn.symm)
    | exact False.elim (small _ _ eqn)
    | exact False.elim (small _ _ eqn.symm)
    | exact False.elim (work.injective.ne (by decide) eqn)⟩

theorem directoryChartPlacement_local {T : ℕ} (i : Fin T) :
    directoryChartPlacement T (i.castAdd 5) = (i.castAdd 10).castAdd 5 := Fin.ext (if_pos i.isLt)

theorem directoryChartPlacement_owner {T : ℕ} (j : Fin 5) :
    directoryChartPlacement T (j.natAdd T) = j.natAdd (T+10) := by
  apply Fin.ext
  change (if T+j.val < T then _ else _) = _
  rw [ite_eq_right (by omega)]
  simp
  omega

theorem directoryChartPlacement_ne_work {T : ℕ} (i : Fin (T+5)) (j : Fin 10) :
    directoryChartPlacement T i ≠ directoryChartWork T j := by
  intro eqn
  have h := congrArg Fin.val eqn
  change (if i.val < T then i.val else i.val+10) = T+j.val at h
  split at h <;> omega

theorem directoryChartPlacement_ne_mask {T : ℕ} (live bad : Fin T) (apart : live ≠ bad)
    (j : Fin 6) (high : 2 ≤ j) (i : Fin (T+5)) :
    directoryChartPlacement T i ≠ directoryChartMasks live bad apart j := by
  fin_cases j <;> first | contradiction | exact directoryChartPlacement_ne_work i _

/-- The child reads the saved directory and both masks at their original
local indices. Its other metadata and scratch stay on the scanner tapes. -/
noncomputable def directoryChartReplayBank [M8.Machine.Net] {K : ℕ}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1) :=
  let T := 66+(K+1)
  let place := directoryChartPlacement T
  let saved := (Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay T)
  replayPlacement (((directoryOrdinaryBank room).trans (Fin.castAddEmb 5)).trans place)
    (replaySlots.trans (Fin.castAddEmb K)) saved (fun i j => directoryChartPlacement_ne_work _ _)

noncomputable def directoryChartChildBank [M8.Machine.Net] {K : ℕ}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1) :=
  let T := 66+(K+1)
  let owner := (Fin.castLEEmb (by decide : 1 ≤ 5)).trans (Fin.natAddEmb (T+10))
  Fin.Embedding.append (x := directoryChartReplayBank room) (y := owner) (Set.disjoint_range_iff.mpr (by
    intro i j
    have sep := directoryReplay_owner_ne (directoryOrdinaryBank room) (directoryChartPlacement T)
      (replaySlots.trans (Fin.castAddEmb K)) ((Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay T))
      (fun _ _ => directoryChartPlacement_ne_work _ _) i ((Fin.castLEEmb (by decide : 1 ≤ 5)) j)
    rw [directoryChartPlacement_owner] at sep
    exact sep))

/-- Call table for a scheduled directory stage on the chart's actual tapes. -/
noncomputable def directoryChartHost [M8.Machine.Net] {K : ℕ} {P C U : Type}
    (archiveRoom : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (localBody : P → Pr P (66+K) columnCapacity prime U)
    (child : C → Pr C ((66+K)+1) columnCapacity prime U) :=
  let T := 66+(K+1)
  directoryStageHost (directoryOrdinaryBank archiveRoom) (directoryChartPlacement T)
    (replaySlots.trans (Fin.castAddEmb K))
    ((Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay T))
    (fun i j => directoryChartPlacement_ne_work i _) localBody
    (directoryChartChildBank archiveRoom) child

/-- Form the child prefix clock in fresh workspace. The three source
lengths are the inherited prefix width, the precision minus one, and one. -/
def directoryChildPrefixClock {T Q A : ℕ} {P U : Type} (m : ℕ) (r : Fin 5 ↪ Fin T) : Pr P T Q A U :=
  ((Node.ucopy (r 0) (r 3) (r 4)).seq (Node.umul (m*m) (r 1) (r 3) (r 4))).seq
    (Node.umul (m*m) (r 2) (r 3) (r 4))

private theorem directoryChildPrefixClock_exec {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (m w : ℕ) (r : Fin 5 ↪ Fin T)
    (u : HS T Q prime U) (S : Stacks T prime) (precision : (S.R (r 1)).length = w)
    (unit : (S.R (r 2)).length = 1) (empty : S.R (r 3) = []) (tmp : S.R (r 4) = []) :
    let width := (S.R (r 0)).length
    ∃ z, z.user = u.user ∧ Exec body (directoryChildPrefixClock m r) (mk u S) (4*width+4*w+16)
      (mk z {S with R := Function.update S.R (r 3) (List.replicate (width+(w+1)*(m*m)) Node.tick)}) := by
  intro width
  obtain ⟨b,bu,copy⟩ := Node.ucopy_exec (body := body) (a := r 0) (b := r 3) (t := r 4)
    (by simp) (by simp) (by simp) u S tmp
  rw [empty,List.append_nil] at copy
  let B := {S with R := Function.update S.R (r 3) (List.replicate width Node.tick)}
  obtain ⟨c,cb,mul⟩ := Node.umul_exec (body := body) (m*m) (a := r 1) (b := r 3) (t := r 4)
    (by simp) (by simp) (by simp) b B (by simpa [B] using tmp)
  let C := {S with R := Function.update S.R (r 3) (List.replicate (m*m*w+width) Node.tick)}
  simp [B,precision,List.replicate_append_replicate] at mul
  obtain ⟨z,zc,one⟩ := Node.umul_exec (body := body) (m*m) (a := r 2) (b := r 3) (t := r 4)
    (by simp) (by simp) (by simp) c C (by simpa [C] using tmp)
  simp [C,unit,List.replicate_append_replicate] at one
  rw [show m*m+(m*m*w+width) = width+(w+1)*(m*m) by ring] at one
  exact ⟨z,zc.trans (cb.trans bu),by
    convert Exec.seq (Exec.seq copy mul) one using 1 <;> first | rfl | (dsimp [width]; omega)⟩

def childPrefixPorts : Fin 5 ↪ Fin 66 := ⟨![47,45,28,58,59],by decide⟩

/-- The replay queue already holds each complete child prefix. Build its
unary width on tape 58 and carry the directory size estimate into recursion. -/
theorem replayChildPrefix_exec {T K Q w W H J : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (replay : Fin (66+K) ↪ Fin T) (owner : Fin T)
    (separate : ∀ i, replay i ≠ owner) (v : RecursiveInterchangeLayout.Descriptor)
    (proj : Matrix (Fin 64) (Fin 64) ℚ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (rs : List ℕ) (u : HS T Q prime U)
    (S : Stacks T prime) (A : Stacks (66+K) prime)
    (entry : DirectoryReady v proj w W H J weights prefixes [] (fun _ => []) A rs)
    (publicWords : ∀ i : Fin 66, S.R (replay (i.castAdd K)) = A.R (i.castAdd K)) :
    let r := (childPrefixPorts.trans (Fin.castAddEmb K)).trans replay
    let width := (S.R (r 0)).length
    let next := width+(w+1)*(64*64)
    let D := {S with R := Function.update S.R (r 3) (List.replicate next Node.tick)}
    ∃ z, z.user = u.user ∧ Exec body (directoryChildPrefixClock 64 r) (mk u S) (4*width+4*w+16) (mk z D) ∧
      D.R (replay ((46 : Fin 66).castAdd K)) = rs.flatMap (LabelDirectory.entry prefixes 64 (w+1)) ∧
      (∀ j ∈ rs, (LabelDirectory.entry prefixes 64 (w+1) j).length = (D.R (r 3)).length) ∧
      (∀ rank ≤ 42, 11*next + 2048*((w+1)*rank) ≤ 11*width + 2048*(64*(w+1))) ∧
      ∀ {N : ℕ} (core : Pr P T Q prime U) (word : Fin N → ZMod 2)
        (b : HS T Q prime U) (B : Stacks T prime) (k : ℕ),
        b.user = z.user → Exec body core (mk z D) k (mk b B) →
        RecordPayload owner (fun _ => blank) 0 word B →
        (∀ i, i ≠ owner → B.L i = D.L i ∧ B.R i = D.R i) →
        ∃ y F, y.user = u.user ∧ Exec body (((directoryChildPrefixClock 64 r).seq core).seq (Fast.clearR (r 3)))
          (mk u S) (4*width+4*w+16+k+(2*next+2)) (mk y F) ∧
          RecordPayload owner (fun _ => blank) 0 word F ∧
          ∀ i, i ≠ owner → F.L i = S.L i ∧ F.R i = S.R i := by
  intro r width next D
  obtain ⟨queue,widths,free,_,_,_,unit,_,_,_,precision,_⟩ := entry
  have tmp : S.R (r 4) = [] := (publicWords 59).trans ((free ((59 : Fin 66).castAdd K) (by change 58 ≤ 59; decide)).2)
  have dst : S.R (r 3) = [] := (publicWords 58).trans ((free ((58 : Fin 66).castAdd K) (by rfl)).2)
  have clock := (congrArg List.length (publicWords 45)).trans precision
  have one := (congrArg List.length ((publicWords 28).trans unit)).trans (length_binSyms ..)
  obtain ⟨z,user,run⟩ := directoryChildPrefixClock_exec body 64 w r u S clock one dst tmp
  refine ⟨z,user,run,?_,?_,?_,?_⟩
  · have away : replay ((46 : Fin 66).castAdd K) ≠ r 3 :=
      replay.injective.ne ((Fin.castAddEmb K).injective.ne (by decide : (46 : Fin 66) ≠ 58))
    exact ((Function.update_of_ne away (List.replicate next Node.tick) S.R).trans ((publicWords 46).trans queue)).trans (List.append_nil _)
  · intro j hj
    rw [LabelDirectory.entry_length]
    have len : width = (prefixes j).length := (congrArg List.length (publicWords 47)).trans (widths j hj)
    simp [D,next,len]
  · intro rank bound
    have smaller := Nat.mul_le_mul_left (w+1) bound
    dsimp only [next]
    omega

  · intro N core word b B k bz coreRun payload frame
    have apart : r 3 ≠ owner := separate _
    obtain ⟨y,yb,clear⟩ := Fast.clearR_exec body (r 3) b B
    have length : (B.R (r 3)).length = next := by rw [(frame _ apart).2]; simp [D]
    rw [length] at clear
    refine ⟨y,_,yb.trans (bz.trans user),Exec.seq (Exec.seq run coreRun) clear,?_,?_⟩
    · intro j
      simpa only [Function.update_of_ne apart.symm] using payload j
    · intro i hi
      refine ⟨(frame i hi).1,?_⟩
      change Function.update B.R (r 3) [] i = S.R i
      by_cases clock : i = r 3
      · subst i
        rw [Function.update_self]
        exact dst.symm
      · rw [Function.update_of_ne clock,(frame i hi).2]
        exact Function.update_of_ne clock ..

noncomputable def withReplayPrefix {T Q : ℕ} {P U : Type} (r : Fin 5 ↪ Fin T) (core : Pr P T Q prime U) :=
  ((directoryChildPrefixClock 64 r).seq core).seq (Fast.clearR (r 3))

/-- Prepare the active child's archive width, run its body, and release the
clock. The caller pays at most 28 steps per child payload symbol for the clock. -/
theorem withReplayPrefix_exec {T K Q w W H J V : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (replay : Fin (66+K) ↪ Fin T) (owner : Fin T)
    (separate : ∀ i, replay i ≠ owner) (v : RecursiveInterchangeLayout.Descriptor)
    (proj : Matrix (Fin 64) (Fin 64) ℚ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (rs : List ℕ) (u : HS T Q prime U)
    (S : Stacks T prime) (A : Stacks (66+K) prime)
    (entry : DirectoryReady v proj w W H J weights prefixes [] (fun _ => []) A rs)
    (publicWords : ∀ i : Fin 66, S.R (replay (i.castAdd K)) = A.R (i.castAdd K))
    (core : Pr P T Q prime U) (budget : ℕ) (input output : Fin V → ZMod 2)
    (payload : RecordPayload owner (fun _ => blank) 0 input S) :
    let r := (childPrefixPorts.trans (Fin.castAddEmb K)).trans replay
    let next := (S.R (r 0)).length+(w+1)*(64*64)
    let D := {S with R := Function.update S.R (r 3) (List.replicate next Node.tick)}
    next ≤ V →
    (∀ z : HS T Q prime U,
      D.R (replay ((46 : Fin 66).castAdd K)) = rs.flatMap (LabelDirectory.entry prefixes 64 (w+1)) →
      (∀ j ∈ rs, (LabelDirectory.entry prefixes 64 (w+1) j).length = (D.R (r 3)).length) →
      RecordPayload owner (fun _ => blank) 0 input D →
      ∃ b B k, b.user = z.user ∧ k ≤ budget ∧ Exec body core (mk z D) k (mk b B) ∧
        RecordPayload owner (fun _ => blank) 0 output B ∧ ∀ i, i ≠ owner → B.L i = D.L i ∧ B.R i = D.R i) →
    ∃ y F k, y.user = u.user ∧ k ≤ budget+28*V ∧ Exec body (withReplayPrefix r core) (mk u S) k (mk y F) ∧
      RecordPayload owner (fun _ => blank) 0 output F ∧ ∀ i, i ≠ owner → F.L i = S.L i ∧ F.R i = S.R i := by
  intro r next D fits run
  obtain ⟨z,_,_,archive,widths,_,release⟩ :=
    replayChildPrefix_exec body replay owner separate v proj weights prefixes rs u S A entry publicWords
  have ownerOff : owner ≠ r 3 := (separate _).symm
  obtain ⟨b,B,k,user,paid,execution,out,frame⟩ := run z archive widths (fun i => by
    simpa only [D,Function.update_of_ne ownerOff] using payload i)
  obtain ⟨y,F,same,complete,result,restored⟩ := release core output b B k user execution out frame
  exact ⟨y,F,_,same,by dsimp only [next,r] at fits; omega,complete,result,restored⟩

/-- Read unary dimensions on 29–31 and borrow scratch 58–63. Only the
three binary results live beyond the scanner's bank. -/
def directoryOuterHeaderBank (K : ℕ) : Fin 12 ↪ Fin ((66+K)+3) where
  toFun i := ⟨if i.val < 3 then 29+i.val else if i.val < 6 then 66+K+(i.val-3) else 58+(i.val-6),
    by split <;> first | omega | split <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    repeat' split at h
    all_goals omega

/-- Save the three outer dimensions and reuse the three rank-dependent
headers already written by the record scanner. The combined six words
describe the whole recursive batch. -/
theorem directoryBatchHeaders_exec {K Q : ℕ} {P U : Type} (body : P → Pr P ((66+K)+3) Q prime U)
    (parent : RecursiveInterchangeLayout.Descriptor)
    (positive : parent.Positive) (lo hi w : ℕ) (u : HS ((66+K)+3) Q prime U) (S : Stacks ((66+K)+3) prime) :
    let bank := directoryOuterHeaderBank K
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let outer := ((Fin.natAddEmb (m := 3) 3).trans (Fin.castAddEmb 6)).trans bank
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let batch := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    (∀ i : Fin 3, (S.R (bank (i.castAdd 9))).length = values i) →
    (∀ i : Fin 12, 3 ≤ i.val → S.R (bank i) = []) →
    ∃ z D n, z.user = u.user ∧ n ≤ 63*LabelMask.records parent+31 ∧
      Exec body (IntervalDescriptor.directoryOuterHeaders bank) (mk u S) n (mk z D) ∧ D.L = S.L ∧
      (∀ k, (∀ i, k ≠ outer i) → D.R k = S.R k) ∧
      (∀ (i : Fin (66+K)) (j : Fin 3), i.castAdd 3 ≠ outer j) ∧
      ∀ (F : Stacks ((66+K)+3) prime) (inner : Fin 3 → Fin ((66+K)+3)),
        (∀ i, F.R (outer i) = D.R (outer i)) →
        (∀ i, F.R (inner i) = (Routines.hdr row (i.natAdd 3)).map bitSymbol) →
        ∀ i : Fin 6, F.R (Fin.append outer inner i) = (Routines.hdr batch i).map bitSymbol := by
  intro bank values outer row batch src empty
  obtain ⟨z,D,n,user,paid,run,left,words,frame⟩ :=
    IntervalDescriptor.directoryOuterHeaders_exec body bank values u S src empty
  let R := LabelMask.records parent
  have pair := Nat.mul_pos positive.1 positive.2.1
  have first : parent.beforeRows ≤ R := (Nat.le_mul_of_pos_right _ positive.2.1).trans
    (Nat.le_mul_of_pos_right _ positive.2.2.1)
  have rows : parent.rows ≤ R := (Nat.le_mul_of_pos_left _ positive.1).trans
    (Nat.le_mul_of_pos_right _ positive.2.2.1)
  have last : parent.beforeH ≤ R := Nat.le_mul_of_pos_left _ pair
  change n ≤ 21*(parent.beforeRows+parent.rows+parent.beforeH)+31 at paid
  refine ⟨z,D,n,user,by change n ≤ 63*R+31; omega,run,left,frame,?_,?_⟩
  · intro i j eq
    have h := congrArg Fin.val eq
    change i.val = (if 3+j.val < 3 then _ else if 3+j.val < 6 then _ else _) at h
    simp only [if_neg (by omega : ¬ 3+j.val < 3),if_pos (by omega : 3+j.val < 6)] at h
    omega
  intro F inner kept tail i
  induction i using Fin.addCases (m := 3) (n := 3) with
  | left j =>
    rw [Fin.append_left,kept,words,← canonicalBits_symbols]
    fin_cases j <;> rfl
  | right j =>
    rw [Fin.append_right,tail]
    fin_cases j <;> simp [Routines.hdr,RecursiveDimensionBank.values,row,batch,
      remainderRecordChild,ordinaryDirectoryChild,ordinaryChildDescriptor,Nat.mul_comm,two_mul]

/-- Chart-local placement of the six header readers, the owner, and the leaf's
private tapes. The scanner's last three descriptor fields occupy 36–38. -/
def stoppedChartBank (K T : ℕ) : Fin (7+T) ↪ Fin ((66+(K+3+T))+1) where
  toFun i := ⟨if i.val < 3 then 66+K+i.val else if i.val < 6 then 33+i.val
    else if i.val = 6 then 66+(K+3+T) else 66+K+3+(i.val-7), by split_ifs <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    split_ifs at h <;> omega

theorem stoppedChartBank_owner (K T : ℕ) :
    stoppedChartBank K T ((Fin.last 6).castAdd T) = (0 : Fin 1).natAdd (66+(K+3+T)) := Fin.ext rfl

def stoppedChartHeader (K T : ℕ) (j : Fin 6) : Fin (66+(K+3+T)) :=
  ⟨if j.val < 3 then 66+K+j.val else 33+j.val, by split <;> omega⟩

def stoppedChartPrivate (K T : ℕ) (j : Fin T) : Fin (66+(K+3+T)) :=
  ⟨66+K+3+j.val,by omega⟩

theorem stoppedChartBank_header (K T : ℕ) (j : Fin 6) :
    stoppedChartBank K T (j.castSucc.castAdd T) = (stoppedChartHeader K T j).castSucc := by
  apply Fin.ext
  simp only [stoppedChartBank,stoppedChartHeader,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_castSucc]
  split_ifs <;> omega

theorem stoppedChartBank_private (K T : ℕ) (j : Fin T) :
    stoppedChartBank K T (j.natAdd 7) = (stoppedChartPrivate K T j).castSucc := by
  apply Fin.ext
  simp only [stoppedChartBank,stoppedChartPrivate,Function.Embedding.coeFn_mk,Fin.val_natAdd,Fin.val_castSucc]
  split_ifs <;> omega

noncomputable def stoppedChartChild [M8.Machine.Net] (K : ℕ) {U : Type} (_ : Unit) :
    Pr Unit ((66+(K+3+LeafCore.small))+1) columnCapacity prime U :=
  embProg (stoppedChartBank K LeafCore.small) Empty.elim
    (hostedStoppedDirectory (le_refl columnCapacity) Fin.castSucc (Fin.last 6))

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
theorem stoppedChartChild_exec [M8.Machine.Net] (K : ℕ) {U : Type}
    (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ) (aligned : node.width = 64*(w+1))
    (rows : 142080 ∣ node.rows) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let scheduled := scheduledChild prime node i
    let e := (scheduledDirectoryCoordinates node i w aligned rows).choose
    let T := LeafCore.small
    let bank := stoppedChartBank K T
    let port := (0 : Fin 1).natAdd (66+(K+3+T))
    ∀ (word : Fin (volume prime scheduled) → ZMod 2) (v : HS ((66+(K+3+T))+1) columnCapacity prime U)
      (S : Stacks ((66+(K+3+T))+1) prime), 0 < volume prime node →
      (∀ j : Fin 6, S.R (bank (j.castSucc.castAdd T)) = (Routines.hdr batch j).map bitSymbol) →
      (∀ j : Fin T, S.L (bank (j.natAdd 7)) = [] ∧ S.R (bank (j.natAdd 7)) = []) →
      RecordPayload port (fun _ => blank) 0 (word ∘ e) S →
      ∃ y B k, y.user = v.user ∧ Exec (stoppedChartChild K) (stoppedChartChild K ()) (mk v S) k (mk y B) ∧
        (k : ℝ) ≤ descriptorHeaderCost batch +
          ((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|))*
          ((volume prime scheduled : ℝ)*((max 1 scheduled.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        RecordPayload port (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd scheduled.rows) word ∘ e) B ∧
        ∀ j, j ≠ port → B.L j = S.L j ∧ B.R j = S.R j := by
  intro r batch scheduled e T bank port word v S positive words free payload
  have owner : bank ((Fin.last 6).castAdd T) = port := stoppedChartBank_owner K T
  have input : RecordPayload (bank ((Fin.last 6).castAdd T)) (fun _ => blank) 0 (word ∘ e) S := owner.symm ▸ payload
  obtain ⟨z,D,k,user,run,paid,out,frame,clean⟩ := hostedStoppedDirectory_exec
    (n := 7) (le_refl columnCapacity) (P := Empty) Empty.elim Fin.castSucc (Fin.last 6)
    node i w aligned rows word (embDn bank v) (embStk bank S) positive words input free
  obtain ⟨y,B,installed,_,same,view,off⟩ := exec_emb (body' := stoppedChartChild K) (ι := Empty.elim)
    bank.injective (fun f => nomatch f) run v rfl S rfl
  simp only [embDn] at user
  refine ⟨y,B,k,same.trans user,installed,paid,?_,?_⟩
  · rw [← view] at out
    rw [← owner]
    exact out
  · intro j ne
    rw [← owner] at ne
    by_cases inside : ∃ l, bank l = j
    · obtain ⟨l,rfl⟩ := inside
      induction l using Fin.addCases with
      | left l =>
        rw [← view] at frame
        exact frame l (fun eq => ne (congrArg (fun t : Fin 7 => bank (t.castAdd T)) eq))
      | right l =>
        rw [← view] at clean
        exact ⟨(clean l).1.trans (free l).1.symm,(clean l).2.trans (free l).2.symm⟩
    · exact off j (fun l eq => inside ⟨l,eq⟩)

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Install the scheduled recursive transpose in directory tape order. It
returns the batch transpose with the same cost and preserves every other tape. -/
theorem directoryChartHost_child_exec [M8.Machine.Net] {K : ℕ} {P C U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (localBody : P → Pr P (66+K) columnCapacity prime U)
    (child : C → Pr C ((66+K)+1) columnCapacity prime U) (f : C)
    (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) (budget : ℕ) (entry : Stacks (66+K) prime → Prop) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let scheduled := scheduledChild prime node i
    let e := (scheduledDirectoryCoordinates node i w aligned rows).choose
    let T := 66+(K+1)
    let bank := directoryChartChildBank room
    let port := (0 : Fin 1).natAdd (66+K)
    let owner := (0 : Fin 5).natAdd (T+10)
    let host := directoryChartHost room localBody child
    ∀ (a : HS ((T+10)+5) columnCapacity prime U) (A : Stacks ((T+10)+5) prime)
      (x : Fin (RecursiveInterchangeLayout.volume prime batch) → ZMod 2),
    entry (embStk (directoryChartReplayBank room) A) →
    RecordPayload owner (fun _ => blank) 0 x A →
    (∀ (u : HS ((66+K)+1) columnCapacity prime U) (S : Stacks ((66+K)+1) prime), entry (embStk (Fin.castAdd 1) S) →
      ∀ word : Fin (volume prime scheduled) → ZMod 2,
      RecordPayload port (fun _ => blank) 0 (word ∘ e) S →
      ∃ y B k, y.user = u.user ∧ k ≤ budget ∧ Exec child (child f) (mk u S) k (mk y B) ∧
        RecordPayload port (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd scheduled.rows) word ∘ e) B ∧
        ∀ i, i ≠ port → B.L i = S.L i ∧ B.R i = S.R i) →
    ∃ y B k, y.user = a.user ∧ k ≤ budget ∧ Exec host (host (.inr (.inr f))) (mk a A) k (mk y B) ∧
      RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
      ∀ i, i ≠ owner → B.L i = A.L i ∧ B.R i = A.R i := by
  intro r batch scheduled e T bank port owner host a A x free input recursive
  have slot : bank port = owner := by simp [bank,port,owner,T,directoryChartChildBank]
  rw [← slot] at input ⊢
  apply directoryStageHost_child_exec _ _ _ _ _ localBody bank child f port batch budget a A x input
  have view : embStk (Fin.castAdd 1) (embStk bank A) =
      embStk (directoryChartReplayBank room) A := by
    apply Stacks.ext <;> first | rfl | (funext i; simp [bank,directoryChartChildBank,embStk,Function.comp_def])
  intro payload
  let word := x ∘ e.symm
  have physical : word ∘ e = x := funext fun k => congrArg x (e.symm_apply_apply k)
  obtain ⟨y,B,k,user,paid,run,returned,frame⟩ :=
    recursive _ _ (view.symm ▸ free) word (physical.symm ▸ payload)
  have action := (scheduledDirectoryCoordinates node i w aligned rows).choose_spec.2 word
  change Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) (word ∘ e) =
    Shared50RecursiveNodeRows.transpose (one_dvd scheduled.rows) word ∘ e at action
  rw [physical] at action
  exact ⟨y,B,k,user,paid,run,action.symm ▸ returned,frame⟩

-- The pre-setup chart projection is available at bfe0b0b4.
/-- The stopped call needs only the six saved words and its own blank tapes
in the replay bank. The payload is supplied separately on the chart owner. -/
def StoppedChartReady (K T : ℕ) (batch : RecursiveInterchangeLayout.Descriptor)
    (S : Stacks (66+(K+3+T)) prime) : Prop :=
  (∀ j, S.R (stoppedChartHeader K T j) = (Routines.hdr batch j).map bitSymbol) ∧
    ∀ j, S.L (stoppedChartPrivate K T j) = [] ∧ S.R (stoppedChartPrivate K T j) = []

/-- Save the outer headers beside the scanner's bank, preserving the three
inner headers at 36–38 and the unused suffix for the leaf. -/
theorem prepareStoppedChart_exec {K T Q : ℕ} {P U : Type}
    (body : P → Pr P (66+(K+3+T)) Q prime U) (parent : RecursiveInterchangeLayout.Descriptor)
    (positive : parent.Positive) (lo hi w : ℕ) (u : HS (66+(K+3+T)) Q prime U)
    (S : Stacks (66+(K+3+T)) prime) :
    let place := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+T) by omega)
    let bank := directoryOuterHeaderBank K
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let batch := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    (∀ j : Fin 3, (S.R (place (bank (j.castAdd 9)))).length = values j) →
    (∀ j : Fin 12, 3 ≤ j.val → S.R (place (bank j)) = []) →
    (∀ j : Fin 3, S.R (stoppedChartHeader K T (j.natAdd 3)) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
    (∀ j, S.L (stoppedChartPrivate K T j) = [] ∧ S.R (stoppedChartPrivate K T j) = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ 63*LabelMask.records parent+31 ∧
      Exec body (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank)) (mk u S) n (mk z F) ∧
      F.L = S.L ∧ StoppedChartReady K T batch F ∧
      ∀ j, (∀ i : Fin 3, j ≠ stoppedChartHeader K T (i.castAdd 3)) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro place bank values row batch src empty tail free
  let outer := ((Fin.natAddEmb (m := 3) 3).trans (Fin.castAddEmb 6)).trans bank
  let inner (j : Fin 3) : Fin ((66+K)+3) := ⟨36+j.val,by omega⟩
  have first (j : Fin 3) : place (outer j) = stoppedChartHeader K T (j.castAdd 3) := by
    apply Fin.ext
    change (if 3+j.val < 3 then 29+(3+j.val) else if 3+j.val < 6 then 66+K+(3+j.val-3)
      else 58+(3+j.val-6)) = (if j.val < 3 then 66+K+j.val else 33+j.val)
    split_ifs <;> omega
  have last (j : Fin 3) : place (inner j) = stoppedChartHeader K T (j.natAdd 3) := by
    apply Fin.ext
    change 36+j.val = (if 3+j.val < 3 then 66+K+(3+j.val) else 33+(3+j.val))
    split_ifs <;> omega
  obtain ⟨y,D,n,user,paid,run,left,keep,_,headers⟩ := directoryBatchHeaders_exec (P := Empty)
    Empty.elim parent positive lo hi w (embDn place u) (embStk place S) src empty
  obtain ⟨z,F,installed,_,same,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim)
    place.injective (fun f => nomatch f) run u rfl S rfl
  have stable (j) (outside : ∀ i : Fin 3, j ≠ stoppedChartHeader K T (i.castAdd 3)) :
      F.L j = S.L j ∧ F.R j = S.R j := by
    by_cases inside : ∃ l, place l = j
    · obtain ⟨l,rfl⟩ := inside
      rw [← view] at left keep
      exact ⟨congrFun left l,keep l (fun i eq => outside i ((congrArg place eq).trans (first i)))⟩
    · exact off j (fun l eq => inside ⟨l,eq⟩)
  have tailWords (j) : D.R (inner j) = (Routines.hdr row (j.natAdd 3)).map bitSymbol := by
    rw [keep]
    · change S.R (place (inner j)) = _
      rw [last,tail]
    · intro i eq
      have h := congrArg Fin.val ((last j).symm.trans ((congrArg place eq).trans (first i)))
      change (if 3+j.val < 3 then _ else _) = (if i.val < 3 then _ else _) at h
      split_ifs at h <;> omega
  have allWords := headers D inner (fun _ => rfl) tailWords
  refine ⟨z,F,n,same.trans user,paid,installed,?_,⟨?_,?_⟩,stable⟩
  · funext j
    by_cases inside : ∃ l, place l = j
    · obtain ⟨l,rfl⟩ := inside
      rw [← view] at left
      exact congrFun left l
    · exact (off j (fun l eq => inside ⟨l,eq⟩)).1
  · intro j
    rw [← view] at allWords
    induction j using Fin.addCases (m := 3) (n := 3) with
    | left j =>
      rw [← first]
      exact (Fin.append_left outer inner j) ▸ allWords (j.castAdd 3)
    | right j => simpa only [Fin.append_right,embStk,Function.comp_apply,last] using allWords (j.natAdd 3)
  · intro j
    have kept := stable (stoppedChartPrivate K T j) (by
      intro i eq
      have h := congrArg Fin.val eq
      change 66+K+3+j.val = (if i.val < 3 then _ else _) at h
      simp only [Fin.val_castAdd] at h
      split_ifs at h <;> omega)
    exact ⟨kept.1.trans (free j).1,kept.2.trans (free j).2⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
theorem directoryChartHost_stopped_exec [M8.Machine.Net] (K : ℕ) {P U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (K+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+(K+3+LeafCore.small)) columnCapacity prime U)
    (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ) (aligned : node.width = 64*(w+1))
    (rows : 142080 ∣ node.rows) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let scheduled := scheduledChild prime node i
    let T := LeafCore.small
    let tapes := 66+((K+3+T)+1)
    let owner := (0 : Fin 5).natAdd (tapes+10)
    let host := directoryChartHost room localBody (stoppedChartChild K)
    let price := (descriptorHeaderCost batch : ℝ) +
      ((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|))*
      ((volume prime scheduled : ℝ)*((max 1 scheduled.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    ∀ (a : HS ((tapes+10)+5) columnCapacity prime U) (A : Stacks ((tapes+10)+5) prime)
      (x : Fin (volume prime batch) → ZMod 2), 0 < volume prime node →
      StoppedChartReady K T batch (embStk (directoryChartReplayBank room) A) →
      RecordPayload owner (fun _ => blank) 0 x A →
      ∃ y B k, y.user = a.user ∧ k ≤ ⌊price⌋₊ ∧ Exec host (host (.inr (.inr ()))) (mk a A) k (mk y B) ∧
        RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j := by
  intro r batch scheduled T tapes owner host price a A x positive ready payload
  apply directoryChartHost_child_exec room localBody (stoppedChartChild K) () node i w aligned rows
    ⌊price⌋₊ (StoppedChartReady K T batch) a A x ready payload
  intro u S prepared word input
  obtain ⟨y,B,k,user,run,paid,out,frame⟩ := stoppedChartChild_exec K node i w aligned rows word u S
    positive (fun j => stoppedChartBank_header K T j ▸ prepared.1 j)
    (fun j => stoppedChartBank_private K T j ▸ prepared.2 j) input
  exact ⟨y,B,k,user,Nat.le_floor paid,run,out,frame⟩

private theorem retireChartHeaders_exec {T Q N : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (owner : Fin T) (saved : Fin 3 → Fin T) (inject : Function.Injective saved)
    (apart : ∀ j, saved j ≠ owner) (headers : Fin 3 → List Bool) (word : Fin N → ZMod 2)
    (v : HS T Q prime U) (S B : Stacks T prime)
    (initial : ∀ j, S.R (saved j) = []) (words : ∀ j, B.R (saved j) = (headers j).map bitSymbol)
    (left : ∀ j, j ≠ owner → B.L j = S.L j)
    (right : ∀ j, j ≠ owner → (∀ l, j ≠ saved l) → B.R j = S.R j)
    (out : RecordPayload owner (fun _ => blank) 0 word B) :
    let scratch := (List.finRange 3).map saved
    let charge := ((List.finRange 3).map fun j => 2*(headers j).length+2).sum+1
    ∃ last G, last.user = v.user ∧ Exec body (Prog.seqList (scratch.map WordCmd.dropR)) (mk v B) charge (mk last G) ∧
      RecordPayload owner (fun _ => blank) 0 word G ∧ ∀ j, j ≠ owner → G.L j = S.L j ∧ G.R j = S.R j := by
  intro scratch charge
  obtain ⟨last,G,same,erase,keepLeft,keepRight⟩ := retire_exec body scratch ((List.nodup_finRange _).map inject) v B
  have time : (scratch.map fun j => 2*(B.R j).length+2).sum+1 = charge := by
    simp only [scratch,charge,List.map_map,Function.comp_def,words,List.length_map]
  have outside : owner ∉ scratch := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    exact apart j eq
  refine ⟨last,G,same,time ▸ erase,?_,?_⟩
  · intro t
    change readAt blank (G.L owner) (G.R owner) (t-0) = _
    rw [keepLeft,keepRight,if_neg outside]
    exact out t
  · intro j ne
    refine ⟨(congrFun keepLeft j).trans (left j ne),?_⟩
    rw [keepRight]
    split_ifs with mem
    · obtain ⟨l,_,rfl⟩ := List.mem_map.mp mem
      exact (initial l).symm
    · exact right j ne (fun l eq => mem (List.mem_map.mpr ⟨l,List.mem_finRange l,eq.symm⟩))

private theorem leafRate_nonneg (tapes : ℕ) (rate : ℝ) :
    0 ≤ (tapes+5 : ℕ)*|rate|+8+tapes*(16+8*|rate|) := by positivity

private theorem stoppedDispatchCost_le {records erase header V b : ℕ} {C τ : ℝ}
    (vol : 0 < V) (active : 0 < b) (count : records ≤ V) (cleanup : erase ≤ 19*V)
    (copy : header ≤ 110*V) (rate : 0 ≤ C) (exponent : τ ≤ 1) :
    (((63*records+31)+⌊(header : ℝ)+C*((V : ℝ)*((max 1 b : ℕ) : ℝ)^τ)⌋₊+erase : ℕ) : ℝ) ≤
      ((223+C)*b)*V := by
  have one : (1 : ℝ) ≤ b := by exact_mod_cast active
  have power : (b : ℝ)^τ ≤ b := by simpa using Real.rpow_le_rpow_of_exponent_le one exponent
  rw [max_eq_right active]
  have floor := Nat.floor_le (show 0 ≤ (header : ℝ)+C*(V*(b : ℝ)^τ) by positivity)
  have initial : ((63*records+31 : ℕ) : ℝ) ≤ 94*(V : ℝ) := by exact_mod_cast (by omega : 63*records+31 ≤ 94*V)
  have headers : (header : ℝ) ≤ 110*(V : ℝ) := by exact_mod_cast copy
  have finalCost : (erase : ℝ) ≤ 19*(V : ℝ) := by exact_mod_cast cleanup
  have machine := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left power (Nat.cast_nonneg V)) rate
  have overhead := mul_le_mul_of_nonneg_left one (show 0 ≤ 223*(V : ℝ) by positivity)
  push_cast at initial ⊢
  linarith only [initial,headers,finalCost,floor,machine,overhead]

open RecursiveInterchangeLayout in
theorem directoryHeaderCosts (parent : Descriptor) (r g w : ℕ) :
    let batch := ordinaryDirectoryChild parent r g w
    let V := volume prime batch
    0 < V → LabelMask.records parent ≤ V ∧
      ((List.finRange 3).map fun j => 2*(Routines.hdr batch (j.castAdd 3)).length+2).sum+1 ≤ 19*V := by
  intro batch V pos
  have split := ordinaryDirectoryChild_volume parent r g w
  change LabelMask.records parent * volume prime (ordinaryChildDescriptor r g w (parent.between*parent.afterD)) = V at split
  have length (j : Fin 3) : 2*(Routines.hdr batch (j.castAdd 3)).length+2 ≤ 4*V+2 := by
    have h := RecursiveRowsNode.header_length batch (LeafCore.positive_of_volume pos) _ (Routines.hdr_headers batch) (j.castAdd 3)
    omega
  have sum := List.sum_le_sum (l := List.finRange 3) (fun j _ => length j)
  simp only [List.map_const',List.sum_replicate_nat,List.length_finRange] at sum
  exact ⟨(Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left (split.symm ▸ pos))).trans_eq split,by omega⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
private theorem stoppedDispatch_linear [M8.Machine.Net] (node : Descriptor) (i : Fin nodeChildren5.length)
    (lo hi w : ℕ) (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows)
    (rank : hi-lo = nodeChildren5[i.val]) (positive : 0 < volume prime node) :
    let parent := role node 142080
    let batch := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    let child := scheduledChild prime node i
    let V := volume prime child
    let C := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
    let erase := ((List.finRange 3).map fun j => 2*(Routines.hdr batch (j.castAdd 3)).length+2).sum+1
    (((63*LabelMask.records parent+31)+⌊(descriptorHeaderCost batch : ℝ)+C*((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌋₊+erase : ℕ) : ℝ) ≤
      ((223+C)*child.width)*V := by
  intro parent batch child V C erase
  have shape := (scheduledDirectoryTranspose node i w aligned rows).1
  rw [← rank] at shape
  have size : volume prime batch = V := shape.volume
  have weight := (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2
  have pos : 0 < V := Nat.pos_of_mul_pos_right (weight.symm ▸ positive)
  have batchPos := LeafCore.positive_of_volume (size.symm ▸ pos)
  obtain ⟨count,cleanup⟩ := directoryHeaderCosts parent (hi-lo) (64-(hi-lo)) w (size.symm ▸ pos)
  change LabelMask.records parent ≤ volume prime batch at count
  change erase ≤ 19*volume prime batch at cleanup
  rw [size] at count cleanup
  have nonzero := (nodeChildren5_bounds i).1
  have active : 0 < child.width := by
    rw [← shape.width]
    exact Nat.mul_pos (Nat.succ_pos _) (rank.symm ▸ nonzero)
  apply stoppedDispatchCost_le pos active count cleanup _ _ M8.Machine.BudgetBound.exponent_range.2.le
  · rw [← size]
    exact descriptorHeaderCost_le batch batchPos
  · exact leafRate_nonneg LeafCore.small LeafCore.C

open RecursiveInterchangeLayout in
/-- The large and stopped branches borrow the same outer-header tapes. The
continuation reads the physical batch descriptor and retains the rest of the caller. -/
theorem withDirectoryHeaders_exec {K T N Q : ℕ} {P U : Type}
    (host : P → Pr P N Q prime U) (replay : Fin (66+(K+3+T)) ↪ Fin N)
    (owner : Fin N) (apart : ∀ j, replay j ≠ owner) (core : Pr P N Q prime U)
    (parent : Descriptor) (hp : parent.Positive) (lo hi w : ℕ) (budget : ℕ) :
    let batch := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let place := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+T) by omega)
    let bank := directoryOuterHeaderBank K
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let saved := fun j : Fin 3 => replay (stoppedChartHeader K T (j.castAdd 3))
    let scratch := (List.finRange 3).map saved
    let eraseCost := ((List.finRange 3).map fun j => 2*(Routines.hdr batch (j.castAdd 3)).length+2).sum+1
    ∀ (a : HS N Q prime U) (A : Stacks N prime) (x : Fin (volume prime batch) → ZMod 2),
      (∀ j : Fin 3, (A.R (replay (place (bank (j.castAdd 9))))).length = values j) →
      (∀ j : Fin 12, 3 ≤ j.val → A.R (replay (place (bank j))) = []) →
      (∀ j : Fin 3, A.R (replay (stoppedChartHeader K T (j.natAdd 3))) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
      (∀ j, A.L (replay (stoppedChartPrivate K T j)) = [] ∧ A.R (replay (stoppedChartPrivate K T j)) = []) →
      RecordPayload owner (fun _ => blank) 0 x A →
      (∀ z F, StoppedChartReady K T batch (embStk replay F) →
        (∀ j, (∀ l : Fin 3, j ≠ saved l) → F.L j = A.L j ∧ F.R j = A.R j) →
        RecordPayload owner (fun _ => blank) 0 x F →
        ∃ y B k, y.user = z.user ∧ k ≤ budget ∧ Exec host core (mk z F) k (mk y B) ∧
          RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
          ∀ j, j ≠ owner → B.L j = F.L j ∧ B.R j = F.R j) →
      ∃ y B k, y.user = a.user ∧ k ≤ (63*LabelMask.records parent+31)+budget+eraseCost ∧
        Exec host (((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
          core).seq (Prog.seqList (scratch.map WordCmd.dropR))) (mk a A) k (mk y B) ∧
        RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j := by
  intro batch row place bank values saved scratch eraseCost a A x src empty tail free payload child
  obtain ⟨v,D,n,user,paid,prep,left,ready,stable⟩ := prepareStoppedChart_exec (K := K) (T := T)
    (P := Empty) Empty.elim parent hp lo hi w (embDn replay a) (embStk replay A) src empty tail free
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (body' := host) (ι := Empty.elim)
    replay.injective (fun f => nomatch f) prep a rfl A rfl
  have ownerKept := off owner apart
  have input : RecordPayload owner (fun _ => blank) 0 x F := by
    intro t
    change readAt blank (F.L owner) (F.R owner) (t-0) = _
    rw [ownerKept.1,ownerKept.2]
    exact payload t
  rw [← view] at left ready stable
  have keep (j) (untouched : ∀ l : Fin 3, j ≠ saved l) : F.L j = A.L j ∧ F.R j = A.R j := by
    by_cases inside : ∃ l, replay l = j
    · obtain ⟨l,rfl⟩ := inside
      exact stable l (fun l' eq => untouched l' (congrArg replay eq))
    · exact off j (fun l eq => inside ⟨l,eq⟩)
  obtain ⟨y,B,k,finish,time,run,out,frame⟩ := child z F ready keep input
  simp only [embDn] at user
  have inject : Function.Injective saved := by
    intro l j eq
    have h := congrArg Fin.val (replay.injective eq)
    change (if l.val < 3 then 66+K+l.val else 33+l.val) =
      (if j.val < 3 then 66+K+j.val else 33+j.val) at h
    apply Fin.ext
    split_ifs at h <;> omega
  have initial (j : Fin 3) : A.R (saved j) = [] := by
    have eq : stoppedChartHeader K T (j.castAdd 3) = place (bank ((j.natAdd 3).castAdd 6)) := by
      apply Fin.ext
      change (if j.val < 3 then 66+K+j.val else 33+j.val) =
        (if 3+j.val < 3 then 29+(3+j.val) else if 3+j.val < 6 then 66+K+(3+j.val-3) else 58+(3+j.val-6))
      split_ifs <;> omega
    change A.R (replay (stoppedChartHeader K T (j.castAdd 3))) = []
    rw [eq]
    exact empty _ (by change 3 ≤ 3+j.val; omega)
  have words (j : Fin 3) : B.R (saved j) = (Routines.hdr batch (j.castAdd 3)).map bitSymbol :=
    (frame (saved j) (apart (stoppedChartHeader K T (j.castAdd 3)))).2.trans (ready.1 (j.castAdd 3))
  obtain ⟨last,G,finalUser,erase,output,restored⟩ := retireChartHeaders_exec host owner saved inject
    (fun j => apart (stoppedChartHeader K T (j.castAdd 3))) (fun j => Routines.hdr batch (j.castAdd 3))
    (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) y A B initial words (by
      intro j ne
      apply (frame j ne).1.trans
      by_cases inside : ∃ l, replay l = j
      · obtain ⟨l,rfl⟩ := inside
        exact congrFun left l
      · exact (off j (fun l eq => inside ⟨l,eq⟩)).1) (by
      intro j ne outer
      exact (frame j ne).2.trans (keep j outer).2) out
  exact ⟨last,G,(n+k)+eraseCost,finalUser.trans (finish.trans (same.trans user)),
    Nat.add_le_add_right (Nat.add_le_add paid time) _,Exec.seq (Exec.seq placed run) erase,output,restored⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Prepare the stopped branch in the replay bank and dispatch the chart child
on the shared owner, then retire the three saved outer words. -/
theorem dispatchStoppedChart_exec [M8.Machine.Net] (K : ℕ) {P U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (K+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+(K+3+LeafCore.small)) columnCapacity prime U)
    (node : Descriptor) (i : Fin nodeChildren5.length) (lo hi w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) (rank : hi-lo = nodeChildren5[i.val]) :
    let parent := role node 142080
    let batch := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let scheduled := scheduledChild prime node i
    let T := LeafCore.small
    let tapes := 66+((K+3+T)+1)
    let owner := (0 : Fin 5).natAdd (tapes+10)
    let host := directoryChartHost room localBody (stoppedChartChild K)
    let replay := directoryChartReplayBank room
    let place := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+T) by omega)
    let bank := directoryOuterHeaderBank K
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let saved := fun j : Fin 3 => replay (stoppedChartHeader K T (j.castAdd 3))
    let scratch := (List.finRange 3).map saved
    ∀ (a : HS ((tapes+10)+5) columnCapacity prime U) (A : Stacks ((tapes+10)+5) prime)
      (x : Fin (volume prime batch) → ZMod 2), 0 < volume prime node →
      (∀ j : Fin 3, (A.R (replay (place (bank (j.castAdd 9))))).length = values j) →
      (∀ j : Fin 12, 3 ≤ j.val → A.R (replay (place (bank j))) = []) →
      (∀ j : Fin 3, A.R (replay (stoppedChartHeader K T (j.natAdd 3))) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
      (∀ j, A.L (replay (stoppedChartPrivate K T j)) = [] ∧ A.R (replay (stoppedChartPrivate K T j)) = []) →
      RecordPayload owner (fun _ => blank) 0 x A →
      ∃ y B, ∃ k : ℕ, y.user = a.user ∧ (k : ℝ) ≤ ((223+((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|)))*scheduled.width)*volume prime scheduled ∧
        Exec host (((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
          (host (.inr (.inr ())))).seq (Prog.seqList (scratch.map WordCmd.dropR))) (mk a A) k (mk y B) ∧
        RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j := by
  intro parent batch row scheduled T tapes owner host replay place bank values saved scratch a A x positive src empty tail free payload
  let eraseCost := ((List.finRange 3).map fun j => 2*(Routines.hdr batch (j.castAdd 3)).length+2).sum+1
  let price := (descriptorHeaderCost batch : ℝ) +
      ((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|))*
      ((volume prime scheduled : ℝ)*((max 1 scheduled.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
  have hp := RecursiveRowsNodeLayout.role_positive 142080 node (by decide)
    (LeafCore.positive_of_volume positive) rows
  have apart (j) : replay j ≠ owner := by
    have sep := directoryReplay_owner_ne (directoryOrdinaryBank room) (directoryChartPlacement tapes)
      (replaySlots.trans (Fin.castAddEmb (K+3+T))) ((Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay tapes))
      (fun i j => directoryChartPlacement_ne_work i _) j (0 : Fin 5)
    rw [directoryChartPlacement_owner] at sep
    exact sep
  obtain ⟨y,B,k,user,time,run,out,frame⟩ := withDirectoryHeaders_exec host replay owner apart
    (host (.inr (.inr ()))) parent hp lo hi w ⌊price⌋₊ a A x src empty tail free payload (by
      intro z F ready _ input
      have call := directoryChartHost_stopped_exec K room localBody node i w aligned rows z F
      rw [← rank] at call
      exact call x positive ready input)
  exact ⟨y,B,k,user,((Nat.cast_le (α := ℝ)).mpr time).trans
    (stoppedDispatch_linear node i lo hi w aligned rows rank positive),run,out,frame⟩

/-- The initialized directory leaves the four mask work tapes and six replay
tapes free. Only the two selector ports overlap the scanner's own bank. -/
theorem directoryChart_workspace {T : ℕ} (room : 58 ≤ T) (live bad : Fin T) (apart : live ≠ bad)
    (A : Stacks ((T+10)+5) prime) (free : ∀ i : Fin (T+10), 58 ≤ i.val → A.R (i.castAdd 5) = []) :
    let place := directoryChartPlacement T
    let masks := directoryChartMasks live bad apart
    let replay := directoryChartReplay T
    masks 0 = place (live.castAdd 5) ∧ masks 1 = place (bad.castAdd 5) ∧
      (∀ j, 2 ≤ j → ∀ i, place i ≠ masks j) ∧ (∀ j, 2 ≤ j → A.R (masks j) = []) ∧
      (∀ i j, place i ≠ replay j) ∧ (∀ i j, masks i ≠ replay j) ∧ ∀ j, A.R (replay j) = [] := by
  intro place masks replay
  let work := directoryChartWork T
  have sep := directoryChartPlacement_ne_work (T := T)
  have blankWork (j : Fin 10) : A.R (work j) = [] :=
    free (j.natAdd T) (by change 58 ≤ T+j.val; omega)
  refine ⟨rfl,rfl,?_,?_,fun i j => sep i (j.natAdd 4),?_,fun j => blankWork (j.natAdd 4)⟩
  · exact directoryChartPlacement_ne_mask live bad apart
  · intro j hj
    fin_cases j <;> first | contradiction | exact blankWork _
  · intro i j
    have low (k : Fin 10) (hk : k.val < 4) : work k ≠ replay j := by
      apply work.injective.ne
      intro eqn
      have h := congrArg Fin.val eqn
      change k.val = 4+j.val at h
      omega
    fin_cases i <;> first | exact sep _ _ | exact low _ (by decide)

/-- A chart specifies the selected owner's tape contents extensionally. Normalize
its two physical stacks to the exact queue consumed by the recursive stage. -/
theorem directoryChartOwner_exec {T Q N : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (slot : Fin T) (word : Fin N → ZMod 2) (a : HS T Q prime U) (A : Stacks T prime)
    (read : RecordPayload slot (fun _ => blank) 0 word A) :
    let bits := payloadWord (SparseRoleCircuit.encode ∘ word)
    ∃ z n, z.user = a.user ∧ n ≤ 6*((A.L slot).length+(A.R slot).length)+6 ∧
      Exec body (normTape slot) (mk a A) n
        (mk z {A with L := Function.update A.L slot [], R := Function.update A.R slot bits}) := by
  intro bits
  have nonblank : blank ∉ bits := by
    intro h
    obtain ⟨i,eqn⟩ := List.mem_ofFn.mp (by simpa only [bits,payloadWord,List.map_ofFn] using h)
    by_cases one : word i = 1 <;>
      simp [Function.comp_def,SparseRoleCircuit.encode,one,bitSymbol,blank,RadixToBinary.binaryEncoding] at eqn
  have tape (j : ℤ) : wordTape bits j = readAt blank (A.L slot) (A.R slot) (j-0) := by
    rw [← readAt_nil_left]
    exact (payload_reads (SparseRoleCircuit.encode ∘ word) j).symm.trans (by
      simpa [M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using (read j).symm)
  obtain ⟨z,n,user,price,run⟩ := normTape_exec body slot a A
  exact ⟨z,n,user,price,by simpa only [sweep,filter_window _ _ 0 bits nonblank tape] using run⟩

/-- Borrow the first seven chart work tapes before the scan. The two binary
inputs are the ordinary metadata registers and the result is owner register two. -/
def directoryChartClock {T : ℕ} (room : 53 < T) : Fin 10 ↪ Fin ((T+10)+5) where
  toFun i := ⟨if i.val = 0 then 2 else if i.val = 1 then 53 else if i.val < 9 then T+(i.val-2) else T+12,
    by split <;> first | omega | split <;> first | omega | split <;> omega⟩
  inj' := by
    intro i j eqn
    apply Fin.ext
    have h := congrArg Fin.val eqn
    dsimp only at h
    repeat' split at h
    all_goals omega

/-- The chart carries its padded stopping threshold in the scanner's cutoff register. -/
noncomputable def directoryChartWords {w : ℕ} (cutoffWord : List (Fin (prime+4)))
    (W beforeRows rows beforeH : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (i : ℕ) :=
  if i = 40 then cutoffWord else ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes i

/-- Load a fresh chart bank from the parent's physical words, including the
saved cutoff. Only the ten destination registers change. -/
private theorem directoryChartWords_exec {T Q s w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (source : Fin 9 → Fin T) (bank : Fin s ↪ Fin T) (room : 59 ≤ s) (cut tmp aux : Fin T)
    (W a b h : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (queue : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let words := ordinaryEntryWords W a b h root parent width queue
    let dst := (ordinaryMetadataPorts.trans (Fin.castLEEmb room)).trans bank
    let saved := bank ((40 : Fin 59).castLE room)
    (∀ i, S.R (source i) = words (ordinaryMetadataPorts i).val) →
    (∀ i j, source i ≠ dst j) → (∀ i, [source i,dst i,tmp,aux].Nodup) →
    (∀ i, cut ≠ dst i) → [cut,saved,tmp,aux].Nodup →
    S.R tmp = [] → S.R aux = [] → (∀ i, S.R (bank i) = []) →
    ∃ z F, z.user = u.user ∧ Exec body
      ((Record.copyLeafHeaders source dst tmp aux (List.finRange 9)).seq (bcopy cut saved tmp aux))
      (mk u S) ((6*((prime^(w+1)).size+a+b+h+w+width+W.size+(if root then 0 else 64*(prime^(w+1)).size)+queue.length)+55) +
        (6*(S.R cut).length+6)) (mk z F) ∧ F.L = S.L ∧
      (∀ i, F.R (bank i) = directoryChartWords (S.R cut) W a b h root parent width queue i.val) ∧
      ∀ j, j ≠ saved → (∀ i, dst i ≠ j) → F.R j = S.R j := by
  intro words dst saved sources apart ports cutOff cutoffPorts tmpFree auxFree fresh
  obtain ⟨v,D,user,load,left,loaded,off⟩ := ordinaryMetadata_exec body source bank room tmp aux
    W a b h root parent width queue u S sources apart ports tmpFree auxFree fresh
  have scratch (i : Fin 9) : dst i ≠ tmp ∧ dst i ≠ aux := by
    have distinct := ports i
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at distinct
    exact distinct.2.1
  obtain ⟨z,same,copy⟩ := bcopy_exec body cutoffPorts v D
    ((off tmp (fun i => (scratch i).1)).trans tmpFree) ((off aux (fun i => (scratch i).2)).trans auxFree)
  have cutoff := off cut (fun i => (cutOff i).symm)
  have empty : D.R saved = [] := (loaded _).trans rfl
  rw [cutoff,empty,List.append_nil] at copy
  refine ⟨z,_,same.trans user,Exec.seq load copy,left,?_,fun j away rest => (Function.update_of_ne away ..).trans (off j rest)⟩
  intro i
  by_cases h : i.val = 40
  · have eq : i = (40 : Fin 59).castLE room := Fin.ext h
    subst i
    exact Function.update_self ..
  · have away : bank i ≠ saved := bank.injective.ne (fun eq => h (congrArg Fin.val eq))
    exact (Function.update_of_ne away ..).trans ((loaded i).trans (ite_eq_right h).symm)

/-- Load the scanner registers alongside a live forward chart. The source
registers may belong to the parent outside the entire round-trip bank. -/
theorem directoryChartEntry_exec {T Q s k back w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (place : Fin (((s+5)+k)+back) ↪ Fin T) (room : 59 ≤ s)
    (source : Fin 9 → Fin T) (cut tmp aux : Fin T) (W a b h : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (queue : List (Fin (prime+4)))
    (u : HS T Q prime U) (S : Stacks T prime) :
    let localBank := ((Fin.castAddEmb (n := s) 5).trans (Fin.castAddEmb k)).trans (Fin.castAddEmb back)
    let bank := localBank.trans place
    let chart := (Fin.natAddEmb (s+5) (m := k)).trans (Fin.castAddEmb back)
    let dst := (ordinaryMetadataPorts.trans (Fin.castLEEmb room)).trans bank
    let saved := bank ((40 : Fin 59).castLE room)
    let words := directoryChartWords (S.R cut) W a b h root parent width queue
    (∀ i, S.R (source i) = ordinaryEntryWords W a b h root parent width queue (ordinaryMetadataPorts i).val) →
    (∀ i j, source i ≠ dst j) → (∀ i, [source i,dst i,tmp,aux].Nodup) →
    (∀ i, cut ≠ dst i) → [cut,saved,tmp,aux].Nodup → S.R tmp = [] → S.R aux = [] →
    (∀ j : Fin (s+5), let i := place ((j.castAdd k).castAdd back)
      S.L i = [] ∧ S.R i = []) →
    (∀ j : Fin back, let i := place (j.natAdd ((s+5)+k))
      S.L i = [] ∧ S.R i = []) →
    ∃ z F, z.user = u.user ∧ Exec body
      ((Record.copyLeafHeaders source dst tmp aux (List.finRange 9)).seq (bcopy cut saved tmp aux))
      (mk u S) (6*((prime^(w+1)).size+a+b+h+w+width+W.size+(if root then 0 else 64*(prime^(w+1)).size)+queue.length)+55 +
        (6*(S.R cut).length+6)) (mk z F) ∧
      ordinaryParentEntry (T := s) back words (embStk (chart.trans place) F) =
        embStk place F ∧ F.L = S.L ∧ ∀ j, (∀ i, j ≠ bank i) → F.R j = S.R j := by
  intro localBank bank chart dst saved words sources apart ports cutOff cutoffPorts tmpFree auxFree empty suffix
  obtain ⟨z,F,user,run,left,loaded,off⟩ := directoryChartWords_exec body source bank room cut tmp aux
    W a b h root parent width queue u S sources apart ports cutOff cutoffPorts tmpFree auxFree
    (fun i => (empty (i.castAdd 5)).2)
  have kept (j) (outside : ∀ i, j ≠ bank i) := off j (outside _) (fun i => (outside _).symm)
  refine ⟨z,F,user,run,?_,left,kept⟩
  have outside (j : Fin (((s+5)+k)+back)) (high : s ≤ j.val) : F.R (place j) = S.R (place j) := by
    apply kept
    intro i eq
    have h := congrArg Fin.val (place.injective eq)
    change j.val = i.val at h
    omega
  apply ordinaryParentEntry_recover words (embStk place F)
  · intro j
    refine ⟨(congrFun left _).trans (empty j).1,?_⟩
    induction j using Fin.addCases with
    | left i => rw [Fin.addCases_left]; exact loaded i
    | right i =>
      rw [Fin.addCases_right]
      exact (outside _ (by change s ≤ s+i.val; omega)).trans (empty (i.natAdd s)).2
  · intro j
    exact ⟨(congrFun left _).trans (suffix j).1,(outside _ (by change s ≤ (s+5)+k+j.val; omega)).trans (suffix j).2⟩

private theorem directoryChartWords_high {w : ℕ} (cutoffWord : List (Fin (prime+4)))
    (W beforeRows rows beforeH : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (i : ℕ) (high : 58 < i) :
    directoryChartWords cutoffWord W beforeRows rows beforeH root parent width prefixes i = [] := by
  unfold directoryChartWords
  rw [ite_eq_right (show i ≠ 40 by omega)]
  unfold ordinaryEntryWords
  split <;> first | rfl | omega

private theorem directoryChartWords_parameters {w : ℕ} (cutoffWord : List (Fin (prime+4)))
    (W beforeRows rows beforeH : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (units : root = true → ∀ i, parent i = 1) :
    ParentParameters root W (prime^(w+1)).size W.size parent
      (fun i => directoryChartWords cutoffWord W beforeRows rows beforeH root parent width prefixes i.val) := by
  cases root
  · exact ⟨rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩
  · exact ⟨units rfl,rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩

/-- Prepare the interval directory on the chart host after the row clock is
installed. All five owner registers retain their physical stacks. -/
theorem directoryChartSetup_exec {T Q w : ℕ} {P U : Type} (room : 72 ≤ T)
    (body : P → Pr P (T+5) Q prime U) (layout : RecursiveInterchangeLayout.Descriptor)
    (rows B : ℕ) (positive : layout.Positive) (digits : layout.width = 64*(w+1))
    (split : layout.rows = 142080*rows) (shape : layout.beforeH = B*prime^(64*((w+1)*64)))
    (lo hi : ℕ) (ordered : lo ≤ hi) (upper : hi ≤ 64) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, parent i = 1)
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) (fits : width ≤ prime^layout.width)
    (u : HS (T+5) Q prime U) (S : Stacks (T+5) prime) (cutoffWord : List (Fin (prime+4)) := []) :
    let W := layout.between*layout.afterD
    let M := prime^(w+1)
    let parents := layout.beforeRows*rows*B
    let directory := RecursiveInterchangeLayout.role layout 142080
    let child := remainderRecordChild lo hi (w+1) W
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let metadata := directoryChartWords cutoffWord W layout.beforeRows rows layout.beforeH root parent width ((List.range parents).flatMap prefixes)
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    (∀ j < parents, (prefixes j).length = width) →
    (∀ i : Fin T, S.L (i.castAdd 5) = [] ∧ S.R (i.castAdd 5) = metadata i.val) →
    ∃ z D n, z.user = u.user ∧ n ≤ (366+16*64*64+19*64+344)*RecursiveInterchangeLayout.volume prime directory ∧
      Exec body (remainderOwnerSetup root lo hi bank) (mk u S) n (mk z D) ∧
      DirectoryScanInput child proj w W M.size W.size parent (fun j => prefixes (j/M^(64*64))) []
        (List.range (LabelMask.records directory)) (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin T, 58 ≤ i.val → D.R (i.castAdd 5) = []) ∧
      D.R (bank 48) = matrixWords prime M.size (reduce M proj) ∧
      (∀ i : Fin 58, i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) →
        D.R (bank (i.castLE (by decide))) = metadata i.val) ∧
      (∀ i : Fin T, D.L (i.castAdd 5) = []) ∧
      ∀ i : Fin 5, D.R (i.natAdd T) = S.R (i.natAdd T) ∧ D.L (i.natAdd T) = S.L (i.natAdd T) := by
  intro W M parents directory child proj metadata bank widths cells
  have R (i : Fin 72) : S.R (bank i) = metadata i.val := (cells (i.castLE room)).2
  have L (i : Fin T) : S.L (i.castAdd 5) = [] := (cells i).1
  have params := directoryChartWords_parameters cutoffWord W layout.beforeRows rows layout.beforeH root parent width
    ((List.range parents).flatMap prefixes) units
  obtain ⟨z,D,n,user,time,run,input,free,matrix,right,_,left,regs⟩ := remainderDirectory_prepareOwner room body
    layout child w rows B W M.size W.size positive digits split shape lo hi rfl rfl rfl ordered upper
    (by intro i; fin_cases i <;> rfl) root parent prefixes [] u S
    (by rw [R]; exact List.length_replicate) (by rw [R]; exact List.length_replicate)
    (by rw [R]; exact List.length_replicate) (by
      intro i hi
      rw [(cells i).2]
      apply directoryChartWords_high <;> omega)
    (by rw [R,List.append_nil]; rfl)
    (fun i hi => (widths i hi).trans (by rw [R]; exact List.length_replicate.symm))
    (by rw [R]; simpa [metadata,directoryChartWords,ordinaryEntryWords] using fits)
    (by rw [R]; rfl) (by rw [R]; rfl) (by rw [R]; rfl) (by
      change ParentParameters _ _ _ _ _ (fun i => S.R (bank (i.castLE _)))
      simpa only [R,M,metadata,Fin.val_castLE] using params)
  have archive : S.R (bank 46) = [] := (R 46).trans rfl
  have tail : S.R (bank 48) = [] := (R 48).trans rfl
  refine ⟨z,D,n,user,?_,run,archive ▸ input,free,by change D.R (bank 48) = matrixWords prime M.size (reduce M proj) ++ S.R (bank 48) at matrix; simpa only [tail,List.append_nil] using matrix,
    fun i hi => (right i hi).trans (R _),?_,regs⟩
  · apply le_trans _ (ordinaryParentSetup_volume_le layout rows split)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide))).mpr
    simpa [remainderDirectoryPorts,bank,L,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using time
  · intro i
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero ((left _).trans (by rw [(cells i).1]; rfl)))

def directoryChartPrefix (replayRole : Option (Fin 142080)) (H box : ℕ) (archive : ℕ → List (Fin (prime+4))) (k : ℕ) :=
  match replayRole with
  | none => archive (k/box)
  | some j => archive (directoryRoleRecord H j k)

private theorem directoryChartPrefix_all (role : Option (Fin 142080)) {H box groups parents records : ℕ}
    (byGroup : records = groups*H) (byParent : records = parents*box) (positive : 0 < box)
    (archive : ℕ → List (Fin (prime+4))) (property : List (Fin (prime+4)) → Prop)
    (valid : ∀ j < (if role.isSome then groups*142080*H else parents), property (archive j)) :
    ∀ j ∈ List.range records, property (directoryChartPrefix role H box archive j) := by
  intro j mem
  have inside := List.mem_range.mp mem
  cases role with
  | none => exact valid _ ((Nat.div_lt_iff_lt_mul positive).mpr (byParent ▸ inside))
  | some role => exact valid _ (directoryRoleRecord_lt role (byGroup ▸ inside))

def directoryChartQueue (replayRole : Option (Fin 142080)) (H parents records : ℕ) (archive : ℕ → List (Fin (prime+4))) :=
  match replayRole with
  | none => (List.range parents).flatMap archive
  | some j => (List.range records).flatMap fun k => archive (directoryRoleRecord H j k)

/-- Appending the next label to a blank-free prefix preserves the queue
encoding used when materializing a role tape. -/
theorem directoryEntry_nonblank (ancestor : ℕ → List (Fin (prime+4))) (m w i : ℕ)
    (clean : blank ∉ ancestor i) : blank ∉ LabelDirectory.entry ancestor m w i := by
  rw [LabelDirectory.entry,List.mem_append]
  intro h
  rcases h with h | h
  · exact clean h
  · obtain ⟨d,_,eq⟩ := List.mem_map.mp h
    have bad := congrArg Fin.val eq
    change d.val+4 = 0 at bad
    omega

private theorem chartRoleSplit_cost (groups H width N : ℕ) (positive : 0 < groups) (labels : 0 < H)
    (row : 0 < N) (fits : width ≤ N) :
    let bs := FlatCoordinateSchedule.bits (H*width)
    let gs := FlatCoordinateSchedule.bits groups
    CyclicRowNormalized.cost 142080 groups (H*width) bs gs ≤ 149*(groups*(142080*(H*N))) := by
  intro bs gs
  have hn := Nat.mul_pos labels row
  have hw := Nat.mul_le_mul_left H fits
  have hb : bs.length ≤ 2*(H*N) := FlatCoordinateDimensions.bits_length_le_twice hw hn
  have hg : gs.length ≤ 2*groups := FlatCoordinateDimensions.bits_length_le_twice le_rfl positive
  have loop : 7*(142080*(H*width))+142080*(7*bs.length+17) ≤ 38*(142080*(H*N)) := by omega
  have total := Nat.mul_le_mul_left groups loop
  have work : groups ≤ groups*(142080*(H*N)) := Nat.le_mul_of_pos_right _ (by positivity)
  rw [show groups*(38*(142080*(H*N))) = 38*(groups*(142080*(H*N))) by ring] at total
  have bill (n V k g : ℕ) (p : 0 < n) (nv : n ≤ V) (time : k ≤ 38*V) (digits : g ≤ 2*n) :
      2*(k+6*n+7*g+16)+1 ≤ 149*V := by omega
  exact bill groups _ _ _ positive work total hg

/-- The inner two controls count row symbols. The outer pair counts groups. -/
def roleSplitControls (c : ℕ) : Fin 4 ↪ Fin (((1+c)+2)+2) :=
  ⟨fun i => ⟨1+c+i.val,by omega⟩,fun i j eq => Fin.ext (by have := congrArg Fin.val eq; dsimp only at this; omega)⟩

private theorem splitCounter_read (bits : List Bool) (z : ℤ) :
    CountedLoopReuseAlphabet.binary bits z =
      readAt (blank : Fin (prime+4)) [separator] (bits.map bitSymbol) (z-1) := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  change RadixZeroFill.encodedBinary _ z = _
  rw [encodedBinary_eq,readAt_single]

/-- Install the four left separators on a split bank containing the literal
archive and the two computed binary words. All heads start at the positions
expected by the cyclic splitter. -/
theorem prepareRoleSplit_exec {c Q : ℕ} {P U : Type}
    (body : P → Pr P (((1+c)+2)+2) Q prime U) (u : HS (((1+c)+2)+2) Q prime U)
    (S : Stacks (((1+c)+2)+2) prime) (archive : List (Fin (prime+4))) (symbols groups : ℕ)
    (left : ∀ i, S.L i = []) (source : S.R (((0 : Fin (1+c)).castAdd 2).castAdd 2) = archive)
    (roles : ∀ j : Fin c, S.R (((j.natAdd 1).castAdd 2).castAdd 2) = [])
    (headers : ∀ i : Fin 4, S.R (roleSplitControls c i) =
      ![[],binSyms symbols.size symbols,[],binSyms groups.size groups] i) :
    let fields := (List.finRange 4).map (roleSplitControls c)
    let B := {S with L := fun i => if i ∈ fields then separator :: S.L i else S.L i}
    let bs := FlatCoordinateSchedule.bits symbols
    let gs := FlatCoordinateSchedule.bits groups
    let initial := CyclicRowSplit.bank (CyclicRowCopy.bank (putWord (fun _ => blank) 0 archive)
      (fun _ _ => blank) 0 (fun _ => 0) bs) gs
    Exec body (Prog.act (pushMarkers fields)) (mk u S) 1 (mk u B) ∧ RepT initial B.L B.R := by
  intro fields B bs gs initial
  have mark := Exec.act (body := body) (pushMarkers fields) (mk u S)
  rw [pushMarkers_run _ ((List.nodup_finRange 4).map (roleSplitControls c).injective)] at mark
  refine ⟨mark,?_⟩
  have low (j : Fin (1+c)) : B.L ((j.castAdd 2).castAdd 2) = [] := by
    have off : (j.castAdd 2).castAdd 2 ∉ fields := by
      intro mem
      obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
      have h := congrArg Fin.val eq
      change 1+c+i.val = j.val at h
      omega
    simp [B,off,left]
  have high (j : Fin 4) : B.L (roleSplitControls c j) = [separator] := by
    have mem : roleSplitControls c j ∈ fields := List.mem_map_of_mem (List.mem_finRange j)
    simp [B,mem,left]
  intro i z
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        have eq : i = 0 := Subsingleton.elim _ _
        subst i
        simp only [initial,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
          CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,sub_zero,low,putWord_blank_zero]
        change wordTape archive z = readAt blank [] (S.R (((0 : Fin (1+c)).castAdd 2).castAdd 2)) z
        rw [source,readAt_nil_left]
      | right j =>
        simp only [initial,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
          CyclicRowCopy.payload,Tapes.append,Fin.addCases_left,Fin.addCases_right,sub_zero,low]
        rw [show B.R (((j.natAdd 1).castAdd 2).castAdd 2) = [] from roles j,readAt_nil_left,wordTape_nil]
    | right j =>
      simp only [initial,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
        Tapes.append,Fin.addCases_left,Fin.addCases_right,CountedLoopReuseAlphabet.controls]
      fin_cases j
      · change CountedLoopReuseAlphabet.binary [] z = readAt blank (B.L (roleSplitControls c 0)) (S.R (roleSplitControls c 0)) (z-1)
        rw [high,headers]; exact splitCounter_read [] z
      · change CountedLoopReuseAlphabet.binary bs z = readAt blank (B.L (roleSplitControls c 1)) (S.R (roleSplitControls c 1)) (z-1)
        rw [high,headers]; change CountedLoopReuseAlphabet.binary bs z = readAt blank [separator] (binSyms symbols.size symbols) (z-1); simpa only [bs,canonicalBits_symbols] using splitCounter_read bs z
  | right j =>
    simp only [initial,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_right,CountedLoopReuseAlphabet.controls]
    fin_cases j
    · change CountedLoopReuseAlphabet.binary [] z = readAt blank (B.L (roleSplitControls c 2)) (S.R (roleSplitControls c 2)) (z-1)
      rw [high,headers]; exact splitCounter_read [] z
    · change CountedLoopReuseAlphabet.binary gs z = readAt blank (B.L (roleSplitControls c 3)) (S.R (roleSplitControls c 3)) (z-1)
      rw [high,headers]; change CountedLoopReuseAlphabet.binary gs z = readAt blank [separator] (binSyms groups.size groups) (z-1); simpa only [gs,canonicalBits_symbols] using splitCounter_read gs z

/-- Split one full archive into the queues read by the role charts. The
counters hold a row's symbol count and the number of complete role groups. -/
theorem directoryChartRoleSplit_exec {Q : ℕ} {P U : Type}
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (groups H width N : ℕ) (positive : 0 < groups) (labels : 0 < H) (row : 0 < N) (fits : width ≤ N)
    (archive : ℕ → List (Fin (prime+4))) (widths : ∀ k < groups*142080*H, (archive k).length = width)
    (clean : ∀ k < groups*142080*H, blank ∉ archive k) :
    let T := ((1+142080)+2)+2
    let bs := FlatCoordinateSchedule.bits (H*width)
    let gs := FlatCoordinateSchedule.bits groups
    let input := (List.range (groups*142080*H)).flatMap archive
    let src := putWord (fun _ => blank) 0 input
    let fields := (List.finRange 4).map (roleSplitControls 142080)
    let finish := CyclicRowSplit.bank (CyclicRowCopy.bank src
      (fun j => putWord (fun _ => blank) 0 (directoryChartQueue (some j) H 0 (groups*H) archive))
      0 (fun _ => 0) bs) gs
    ∀ (body : P → Pr P T Q prime U) (u : HS T Q prime U) (S : Stacks T prime),
      (∀ i, S.L i = []) → S.R (((0 : Fin (1+142080)).castAdd 2).castAdd 2) = input →
      (∀ j : Fin 142080, S.R (((j.natAdd 1).castAdd 2).castAdd 2) = []) →
      (∀ i : Fin 4, S.R (roleSplitControls 142080 i) =
        ![[],binSyms (H*width).size (H*width),[],binSyms groups.size groups] i) →
      ∃ z F t, z.user = u.user ∧ t ≤ 149*(T+5)*(groups*142080*H*N)+7 ∧
        Exec body ((Prog.act (pushMarkers fields)).seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))) (mk u S) t (mk z F) ∧
        RepT finish F.L F.R ∧
        ∀ j : Fin 142080, let port := ((j.natAdd 1).castAdd 2).castAdd 2
          let queue := directoryChartQueue (some j) H 0 (groups*H) archive
          ∃ y k, y.user = z.user ∧
            k ≤ 1788*(groups*142080*H*N)+6 ∧
            Exec body (normTape port) (mk z F) k
              (mk y {F with L := Function.update F.L port [], R := Function.update F.R port queue}) := by
  intro T bs gs input src fields finish body u S left source roles headers
  obtain ⟨mark,ready⟩ := prepareRoleSplit_exec body u S input (H*width) groups left source roles headers
  have split := directoryRoleSplit_hoare groups H width archive widths (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0) bs gs
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
  obtain ⟨z,F,_,rfl,rep,user,_,_,stock,t,paid,run⟩ := foreign_exec (body := body)
    (liftQ _ capacity) (HoareTime.liftQ capacity split) u _ _ rfl ready
  have bound := chartRoleSplit_cost groups H width N positive labels row fits
  change CyclicRowNormalized.cost 142080 groups (H*width) bs gs ≤ _ at bound
  rw [show groups*(142080*(H*N)) = groups*142080*H*N by ring] at bound
  refine ⟨z,F,1+t,user,?_,Exec.seq mark run,rep,?_⟩
  · have scale : CyclicRowNormalized.cost 142080 groups (H*width) bs gs*(T+5) ≤
        149*(T+5)*(groups*142080*H*N) := calc
      _ ≤ (149*(groups*142080*H*N))*(T+5) := Nat.mul_le_mul_right _ bound
      _ = _ := by ring
    omega
  · intro j port queue
    have nonblank : blank ∉ queue := by
      intro h
      obtain ⟨k,hk,hit⟩ := List.mem_flatMap.mp h
      exact clean _ (directoryRoleRecord_lt (groups := groups) j (List.mem_range.mp hk)) hit
    have tape (i : ℤ) : wordTape queue i = readAt blank (F.L port) (F.R port) (i-0) := by
      have cell := rep port i
      simpa only [CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,CyclicRowCopy.payload,
        Tapes.append,port,queue,directoryChartQueue,Fin.addCases_left,Fin.addCases_right,putWord_blank_zero] using cell
    obtain ⟨y,k,user',cost,clean⟩ := normTape_exec body port z F
    refine ⟨y,k,user',?_,?_⟩
    · have size := stock port
      have twice := Nat.mul_le_mul_left 2 bound
      rw [← Nat.mul_assoc] at twice
      have apart : port ∉ fields := by
        intro h
        obtain ⟨i,_,eq⟩ := List.mem_map.mp h
        have bad := congrArg Fin.val eq
        change 1+142080+i.val = 1+j.val at bad
        omega
      change (F.L port).length+(F.R port).length ≤ (if port ∈ fields then separator :: S.L port else S.L port).length+
        (S.R port).length+2*CyclicRowNormalized.cost 142080 groups (H*width) bs gs at size
      simp only [ite_eq_right apart] at size
      rw [left port,show S.R port = [] from roles j] at size
      simp only [List.length_nil,zero_add] at size
      have charge := Nat.mul_le_mul_left 6 (size.trans twice)
      rw [← Nat.mul_assoc] at charge
      exact cost.trans (Nat.add_le_add_right charge 6)
    · simpa only [sweep,filter_window _ _ 0 queue nonblank tape] using clean

/-- Both chart entry paths copy at most one prefix per record. The saved
cutoff is charged once in addition to the ordinary metadata. -/
theorem directoryChartEntry_volume_le {w W a b h width parents : ℕ} (root : Bool)
    (role : Option (Fin 142080)) (prefixes : ℕ → List (Fin (prime+4))) (cutoffWord : List (Fin (prime+4)))
    (widths : ∀ j < (if role.isSome then a*b*142080*h else parents), (prefixes j).length = width)
    (blocks : parents ≤ a*b*h) (positive : 0 < W) (outer : 0 < a) (rows : 0 < b) (labels : 0 < h) :
    let M := prime^(w+1)
    let N := M^128*W
    let V := a*b*h*N
    let queue := directoryChartQueue role h parents (a*b*h) prefixes
    width ≤ N → cutoffWord.length ≤ V →
    6*(M.size+a+b+h+w+width+W.size+(if root then 0 else 64*M.size)+queue.length)+55+
      (6*cutoffWord.length+6) ≤ 499*V := by
  intro M N V queue fits cut
  have volumePos : 0 < V := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos outer rows) labels)
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive)
  have metadata : 6*(M.size+a+b+h+w+width+W.size+(if root then 0 else 64*M.size)+queue.length)+55 ≤ 487*V := by
    cases role with
    | none => exact ordinaryMetadata_volume_le root prefixes widths blocks positive outer rows labels fits
    | some j =>
      exact ordinaryMetadata_volume_le root (fun i => prefixes (directoryRoleRecord h j i))
        (fun i hi => widths _ (directoryRoleRecord_lt (groups := a*b) j hi)) le_rfl positive outer rows labels fits
  omega

noncomputable def directoryChartOwnerSetup {T Q : ℕ} {P U : Type} (replayRole : Option (Fin 142080))
    (root : Bool) (lo hi : ℕ) (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  match replayRole with
  | none => remainderOwnerSetup root lo hi bank
  | some _ => replayOwnerSetup root lo hi bank

def directoryChartSetupRate : Option (Fin 142080) → ℕ
  | none => 366+16*64*64+19*64+344
  | some _ => 1327

private theorem directoryChartOwnerSetup_exec {T Q w : ℕ} {P U : Type} (replayRole : Option (Fin 142080)) (room : 72 ≤ T)
    (body : P → Pr P (T+5) Q prime U) (layout : RecursiveInterchangeLayout.Descriptor)
    (rows B : ℕ) (positive : layout.Positive) (digits : layout.width = 64*(w+1))
    (split : layout.rows = 142080*rows) (shape : layout.beforeH = B*prime^(64*((w+1)*64)))
    (lo hi : ℕ) (ordered : lo ≤ hi) (upper : hi ≤ 64) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, parent i = 1)
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) (fits : width ≤ prime^layout.width)
    (u : HS (T+5) Q prime U) (S : Stacks (T+5) prime) (cutoffWord : List (Fin (prime+4)) := []) :
    let W := layout.between*layout.afterD
    let M := prime^(w+1)
    let parents := layout.beforeRows*rows*B
    let directory := RecursiveInterchangeLayout.role layout 142080
    let child := remainderRecordChild lo hi (w+1) W
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
    let metadata := directoryChartWords cutoffWord W layout.beforeRows rows layout.beforeH root parent width (directoryChartQueue replayRole layout.beforeH parents (LabelMask.records directory) prefixes)
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    (∀ j < (if replayRole.isSome then layout.beforeRows*rows*142080*layout.beforeH else parents), (prefixes j).length = width) →
    (∀ i : Fin T, S.L (i.castAdd 5) = [] ∧ S.R (i.castAdd 5) = metadata i.val) →
    ∃ z D n, z.user = u.user ∧ n ≤ directoryChartSetupRate replayRole *RecursiveInterchangeLayout.volume prime directory ∧
      Exec body (directoryChartOwnerSetup replayRole root lo hi bank) (mk u S) n (mk z D) ∧
      DirectoryScanInput child proj w W M.size W.size parent (directoryChartPrefix replayRole layout.beforeH (M^(64*64)) prefixes) []
        (List.range (LabelMask.records directory)) (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin T, 58 ≤ i.val → D.R (i.castAdd 5) = []) ∧
      D.R (bank 48) = matrixWords prime M.size (reduce M proj) ∧
      (∀ i : Fin 58, i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) →
        D.R (bank (i.castLE (by decide))) = metadata i.val) ∧
      (∀ i : Fin T, D.L (i.castAdd 5) = []) ∧
      ∀ i : Fin 5, D.R (i.natAdd T) = S.R (i.natAdd T) ∧ D.L (i.natAdd T) = S.L (i.natAdd T) := by
  cases replayRole with
  | none => exact directoryChartSetup_exec room body layout rows B positive digits split shape lo hi ordered upper root parent units width prefixes fits u S cutoffWord
  | some j =>
    intro W M parents directory child proj metadata bank widths cells
    have R (i : Fin 72) : S.R (bank i) = metadata i.val := (cells (i.castLE room)).2
    let queue := directoryChartQueue (some j) layout.beforeH parents (LabelMask.records directory) prefixes
    have params := directoryChartWords_parameters cutoffWord W layout.beforeRows rows layout.beforeH root parent width queue units
    have shape' : layout.beforeH = B*prime^(64*layout.width) := by rw [digits,Nat.mul_comm 64 (w+1)]; exact shape
    obtain ⟨z,D,n,user,time,run,input,matrix,right,free,left,off⟩ := prepareReplayOwner_exec body bank layout child
      w rows B W M.size W.size lo hi positive digits split shape' rfl rfl rfl ordered upper
      (by intro i; fin_cases i <;> rfl) root parent j prefixes u S
      (by rw [R]; exact List.length_replicate) (by rw [R]; exact List.length_replicate)
      (by rw [R]; exact List.length_replicate) (by rw [R]; rfl)
      (fun i hi => (widths i hi).trans (by rw [R]; exact List.length_replicate.symm))
      (by rw [R]; simpa [metadata,directoryChartWords,ordinaryEntryWords] using fits)
      (by rw [R]; rfl) (by rw [R]; rfl) (by rw [R]; rfl) (by
        intro i hi
        rw [R]; apply directoryChartWords_high <;> omega) (by simpa only [R,metadata,M,queue,Fin.val_castLE] using params)
    have empty : S.R (bank 46) = [] := (R 46).trans rfl
    have tail : S.R (bank 48) = [] := (R 48).trans rfl
    refine ⟨z,D,n,user,?_,run,empty ▸ input,?_,?_,fun i h => (right i h).trans (R _),
      fun i => (congrFun left _).trans (cells i).1,?_⟩
    · have size : RecursiveInterchangeLayout.volume prime directory*142080 = RecursiveInterchangeLayout.volume prime layout := by
        have vr : directory.rows = rows := by simp [directory,RecursiveInterchangeLayout.role,split]
        unfold RecursiveInterchangeLayout.volume
        rw [vr,split]; dsimp only [directory,RecursiveInterchangeLayout.role]; ring
      have smaller := Nat.le_mul_of_pos_left n (pow_pos Shared50ModularControl.prime_prime.pos layout.width)
      rw [← size,← Nat.mul_assoc] at time
      exact smaller.trans (Nat.le_of_mul_le_mul_right time (by decide : 0 < 142080))
    · intro i hi
      by_cases small : i.val < 72
      · exact free ⟨i.val,small⟩ hi
      · have away (l : Fin 72) : i.castAdd 5 ≠ bank l := by
          intro eq
          have h := congrArg Fin.val eq
          change i.val = l.val at h
          omega
        rw [off _ away,(cells i).2]; apply directoryChartWords_high <;> omega
    · simpa only [tail,List.append_nil] using matrix
    · intro i
      exact ⟨off _ (fun l eq => by
        have h := congrArg Fin.val eq
        change T+i.val = l.val at h
        omega),congrFun left _⟩

/-- Present the same physical queue to the rank-split scanner. Reindexing its
modular weights and row words changes neither the directory nor any tape. -/
private theorem intervalInput_cast [M8.Machine.Net] {K d m n w W R : ℕ} (dim : m = n)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1) (v directory : RecursiveInterchangeLayout.Descriptor)
    (interval : ℕ × ℕ) (weights : Fin n → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (S : Stacks ((66+(K+1))+5) prime) :
    let M := prime^(w+1)
    let width : M^(m+m)*W = M^(n+n)*W := by rw [dim]
    let proj (a : ℕ) : Matrix (Fin a) (Fin a) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    ∀ word : Fin (R*(M^(n+n)*W)) → ZMod 2,
    GeneratedDirectoryInput (W := W) room v directory (proj n) M.size W.size weights prefixes [] []
      (List.range R) (ownerRow (R := R) rfl word) S →
    GeneratedDirectoryInput (W := W) room v directory (proj m) M.size W.size (weights ∘ Fin.cast dim) prefixes [] []
      (List.range R) (fun j i => ownerRow (R := R) rfl word j (i.cast width)) S := by
  subst n
  exact fun _ input => input

private theorem intervalReady_cast {m n w W K : ℕ} (dim : m = n)
    (interval : ℕ × ℕ) (weights : Fin n → ZMod (prime^(w+1))) (child : RecursiveInterchangeLayout.Descriptor)
    (archive : ℕ → List (Fin (prime+4))) (rs : List ℕ) (S : Stacks (66+K) prime) :
    let proj (k : ℕ) : Matrix (Fin k) (Fin k) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    DirectoryReady child (proj m) w W (prime^(w+1)).size W.size (weights ∘ Fin.cast dim) archive [] (fun _ => []) S rs →
      DirectoryReady child (proj n) w W (prime^(w+1)).size W.size weights archive [] (fun _ => []) S rs := by
  subst n
  exact id

/-- Transport the scanner's projected row action back to the chart dimensions.
The owner port and the physical execution stay on the same tapes. -/
private theorem intervalStage_cast [M8.Machine.Net] {T R m n w W : ℕ} {P U : Type}
    (dim : m = n) (interval : ℕ × ℕ) (weights : Fin n → ZMod (prime^(w+1)))
    (host : P → Pr P T columnCapacity prime U) (program : Pr P T columnCapacity prime U)
    (a : HS T columnCapacity prime U) (A : Stacks T prime) (prior bound : ℕ)
    (port : Fin T) (tail : List (Fin (prime+4))) (finished : Stacks T prime → Prop) :
    let M := prime^(w+1)
    let size : M^(m+m)*W = M^(n+n)*W := by rw [dim]
    let e := finSumFinEquiv.trans (finCongr (show m+m = n+n by rw [dim]))
    let proj (k : ℕ) : Matrix (Fin k) (Fin k) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let parent := weights ∘ Fin.cast dim
    ∀ routed : Fin (R*(M^(n+n)*W)) → ZMod 2,
    DirectoryStageResult (R := R) host program a A prior bound port tail
      (fun j word => if LabelStock.live m (w+1) 1 j then ∀ x (h : Fin W),
        word ((index ((projectorResidual e (reduce M (proj m)) parent (fun i => Ring.inverse (parent i))
          (physicalLabel m (w+1) j)).mulVec x) h).cast size.symm) = ownerRow rfl routed j (index x h)
        else (fun i => ownerRow rfl routed j (i.cast size)) = word) finished →
    DirectoryStageResult (R := R) host program a A prior bound port tail
      (fun j word => if LabelStock.live n (w+1) 1 j then ∀ x (h : Fin W),
        word (index ((projectorResidual finSumFinEquiv (reduce M (proj n)) weights (fun i => Ring.inverse (weights i))
          (physicalLabel n (w+1) j)).mulVec x) h) = ownerRow rfl routed j (index x h)
        else ownerRow rfl routed j = word) finished := by
  subst n
  exact fun _ stage => stage

private theorem outerWords_of_headers {K a b h : ℕ} (S : Stacks (66+K) prime)
    (outer : S.R ((29 : Fin 66).castAdd K) = List.replicate a Node.tick)
    (rows : S.R ((30 : Fin 66).castAdd K) = List.replicate b Node.tick)
    (labels : S.R ((31 : Fin 66).castAdd K) = List.replicate h Node.tick) :
    ∀ j : Fin 3, directoryOuterWords S j = List.replicate (![a,b,h] j) Node.tick := by
  intro j
  fin_cases j <;> first | exact outer | exact rows | exact labels

/-- The two scanner procedures and the framed child transpose installed on a chart. -/
def DirectoryChartCall [M8.Machine.Net] {K w : ℕ} {L P U : Type}
    (archiveRoom : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (localBody : L → Pr L (66+K) columnCapacity prime U)
    (body : P → Pr P ((66+(K+1)+10)+5) columnCapacity prime U)
    (incoming outgoing : L → P) (childLabel : P)
    (directory child batch : RecursiveInterchangeLayout.Descriptor) (W H J width childBudget : ℕ)
    (proj : Matrix (Fin 64) (Fin 64) ℚ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (entryPrefix : ℕ → List (Fin (prime+4))) (cutoffWord : List (Fin (prime+4))) : Prop :=
    let T := 66+(K+1)
    let slot := (0 : Fin 5).natAdd (T+10)
    let replayBank := directoryChartReplayBank archiveRoom
    let saved := (Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay T)
    let outgoingBank := directoryOutgoingPlacement (directoryOrdinaryBank archiveRoom) (directoryChartPlacement T)
      (replaySlots.trans (Fin.castAddEmb K)) saved (fun _ _ => directoryChartPlacement_ne_work _ _)
    (∀ f, body (incoming f) = embProg (directoryChartPlacement T) incoming
      (embProg (Fin.castAdd 5) id (embProg (directoryOrdinaryBank archiveRoom) id (localBody f)))) ∧
    (∀ f, body (outgoing f) = embProg outgoingBank outgoing (embProg (Fin.castAdd 5) id (localBody f))) ∧
    (∀ (b : HS ((T+10)+5) columnCapacity prime U) (D : Stacks ((T+10)+5) prime)
      (x : Fin (RecursiveInterchangeLayout.volume prime batch) → ZMod 2),
      (entryPrefix 0).length = width → (∀ j ∈ List.range (LabelMask.records directory), blank ∉ entryPrefix j) →
      DirectoryReady child proj w W H J weights entryPrefix [] (fun _ => [])
        (embStk replayBank D) (List.range (LabelMask.records directory)) →
      D.R (replayBank ((40 : Fin 66).castAdd K)) = cutoffWord →
      (∀ j : Fin 3, directoryOuterWords (embStk replayBank D) j =
        List.replicate (![directory.beforeRows,directory.rows,directory.beforeH] j) Node.tick) →
      RecordPayload slot (fun _ => blank) 0 x D →
      ∃ y B k, y.user = b.user ∧ k ≤ childBudget ∧ Exec body (body childLabel) (mk b D) k (mk y B) ∧
        RecordPayload slot (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ i, i ≠ slot → B.L i = D.L i ∧ B.R i = D.R i)

/-- Only nine entry words and the cutoff occupy the initial scanner prefix. -/
private theorem chartMetadataLength {w t : ℕ} (room : 59 ≤ t) (cut : List (Fin (prime+4)))
    (W a b h : ℕ) (root : Bool) (weights : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (queue : List (Fin (prime+4))) :
    let M := prime^(w+1)
    let words := directoryChartWords cut W a b h root weights width queue
    ((List.finRange t).map (fun j => (words j.val).length)).sum =
      cut.length+(M.size+a+b+h+w+width+W.size+(if root then 0 else 64*M.size)+queue.length) := by
  intro M words
  classical
  let ports := ordinaryMetadataPorts.trans (Fin.castLEEmb room)
  let cutoff : Fin t := (40 : Fin 59).castLE room
  let value (j : Fin t) := (words j.val).length
  have off (j : Fin 9) : (ports j).val ≠ 40 := by
    change (ordinaryMetadataPorts j).val ≠ 40
    exact (by decide : ∀ i, (ordinaryMetadataPorts i).val ≠ 40) j
  have separate : cutoff ∉ Finset.univ.map ports := by
    intro hj
    obtain ⟨i,_,eq⟩ := Finset.mem_map.mp hj
    exact off i (congrArg Fin.val eq)
  have support : ∑ j, value j = ∑ j ∈ insert cutoff (Finset.univ.map ports), value j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ unused
    have ne : j.val ≠ 40 := fun eq => unused (Finset.mem_insert.mpr (Or.inl (Fin.ext eq)))
    have absent (i : Fin 9) : (ordinaryMetadataPorts i).val ≠ j.val := fun eq =>
      unused (Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,Fin.ext eq⟩)))
    simp only [value,words,directoryChartWords,ite_eq_right ne,ordinaryEntryWords_unused _ _ _ _ _ _ _ _ _ absent,List.length_nil]
  have packed := ordinaryMetadata_time W a b h root weights width queue
  let ordinary := ordinaryEntryWords W a b h root weights width queue
  change (((List.finRange 9).map (fun i => 6*(ordinary (ordinaryMetadataPorts i).val).length+6)).sum+1) = _ at packed
  simp only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate_nat,List.length_finRange] at packed
  have mapped (i : Fin 9) : value (ports i) = (ordinary (ordinaryMetadataPorts i).val).length := by
    simp only [value,words,directoryChartWords,ite_eq_right (off i)]
    rfl
  have all (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by ext; simp
  rw [← List.sum_toFinset value (List.nodup_finRange t),all,support,Finset.sum_insert separate,Finset.sum_map]
  simp only [mapped]
  rw [← List.sum_toFinset _ (List.nodup_finRange 9),all] at packed
  change cut.length+_ = _
  dsimp only [M]
  omega

/-- Erase both private banks around the child owners, including the final halt. -/
def chartReturnCost {front owners back : ℕ} (D : Stacks ((front+owners)+back) prime) : ℕ :=
  let cost (i) := 4*(D.L i).length+2*(D.R i).length+4
  ((List.finRange front).map (fun j => cost ((j.castAdd owners).castAdd back))).sum+
    ((List.finRange back).map (fun j => cost (j.natAdd (front+owners)))).sum+1

private theorem chartCleanupCost {t n : ℕ} (place : Fin t ↪ Fin n) (D : Stacks n prime)
    (metadata : ℕ → List (Fin (prime+4))) (width growth : ℕ)
    (stock : ∀ j, (D.L (place j)).length ≤ growth ∧
      (D.R (place j)).length ≤ (metadata j.val).length+width+growth) :
    ((List.finRange t).map (fun j => 4*(D.L (place j)).length+2*(D.R (place j)).length+4)).sum ≤
      2*((List.finRange t).map (fun j => (metadata j.val).length)).sum + t*(6*growth+2*width+4) := by
  have bound := List.sum_le_sum (l := List.finRange t)
    (f := fun j => 4*(D.L (place j)).length+2*(D.R (place j)).length+4)
    (g := fun j => 2*(metadata j.val).length+(6*growth+2*width+4))
    (fun j _ => by obtain ⟨l,r⟩ := stock j; omega)
  simpa only [List.sum_map_add,List.sum_map_mul_left,List.map_const',List.sum_replicate_nat,List.length_finRange] using bound

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
/-- Run both certified charts around the scanner from the current owner words
and the private stacks reserved for this scheduled occurrence. -/
theorem chartDirectory_exec [M8.Machine.Net] {common aux w : ℕ} {L P U : Type}
    (window : Fin 9) (job : Fin idleCopies.length)
    (layout : RecursiveInterchangeLayout.Descriptor) (rows B : ℕ) (positiveLayout : layout.Positive)
    (digits : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (weights : Fin 64 → ZMod (prime^(w+1))) (units : root = true → ∀ i, weights i = 1) (invertible : ∀ i, IsUnit (weights i))
    (width : ℕ) (prefixes : ℕ → List (Fin (prime+4))) (widthFits : width ≤ prime^layout.width) (inherited : Bool := false) (cutoffWord : List (Fin (prime+4)) := []) :
    let k := 142081
    let copy := idleCopies[job.val]
    let interval := idleInterval window copy.2
    let member := idleInterval_mem window copy.2
    let role := idleRole window copy
    let replayRole := if inherited then some (idleRoleIndex window copy) else none
    let r := interval.2-interval.1
    let m := r+(64-r)
    let dim : m = 64 := by have := (BitHosting.remainder_counts interval member).2.1; dsimp only [m,r]; omega
    let K := common+24+31+aux
    let T := 66+(K+1)
    let W := layout.between*layout.afterD
    let M := prime^(w+1)
    let N := M^128*W
    let directory := RecursiveInterchangeLayout.role layout 142080
    let R := LabelMask.records directory
    let parents := layout.beforeRows*rows*B
    let data : ScanData m 127 w W := {
      records := R, H := M.size, J := W.size, table := fun _ => 0, matrix := fun _ => 0, input := fun _ _ => 0,
      signed := [], matrixTail := [], pivotTail := [], inputTail := [], outputTail := []}
    let child := remainderRecordChild interval.1 interval.2 (w+1) W
    let metadata := directoryChartWords cutoffWord W layout.beforeRows rows layout.beforeH root weights width (directoryChartQueue replayRole layout.beforeH parents R prefixes)
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let src := idleTape window copy
    let cert := port role.port.val
    let checked := port_checked _ role.port.isLt
    ∃ stage back : SharedBankStage.Stage _ k prime (phaseOwners (N := R*N)),
    ∃ forward : RemainderChartFrame (packedRemainderChart_stage src cert checked false).choose_spec.choose directory (w+1) stage,
    ∃ reverse : RemainderChartFrame (packedRemainderChart_stage src cert checked true).choose_spec.choose directory (w+1) back,
    ∀ words : Fin k → Fin (R*N) → ZMod 2,
    let routed := stage.transform words src
    ∀ (pool : (RingFormula.conjugationDepth m+1)*13 ≤ aux) (rowRoom : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (archiveRoom : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
      (queueRoom : (36+2*m+1+(RingFormula.conjugationDepth m+1)*13)+3 ≤ K+1)
      (pairRoom : m*m+m*m ≤ K) (localBody : L → Pr L (66+K) columnCapacity prime U) (localPush placedPush : ℕ)
      (bounded : ∀ f, Fast.Main.mnProgPush (localBody f) ≤ localPush)
      (placed : ∀ f, Fast.Main.mnProgPush (embProg (directoryOrdinaryBank archiveRoom) id (localBody f)) ≤ placedPush)
      (widths : ∀ i < (if replayRole.isSome then layout.beforeRows*rows*142080*layout.beforeH else parents), (prefixes i).length = width)
      (clean : ∀ i < (if replayRole.isSome then layout.beforeRows*rows*142080*layout.beforeH else parents), blank ∉ prefixes i),
    let bank := (Fin.castLEEmb (by omega : 72 ≤ T+10)).trans (Fin.castAddEmb 5)
    let setup := directoryChartOwnerSetup (P := P) (U := U) (Q := columnCapacity) replayRole root interval.1 interval.2 bank
    let setupCost := directoryChartSetupRate replayRole *RecursiveInterchangeLayout.volume prime directory
    let clock := directoryChartClock (by omega : 53 < T)
    let slot := (0 : Fin 5).natAdd (T+10)
    let placement := payloadPlacement slot (stage.slots src)
    let chart : Fin stage.tapes ↪ Fin (((T+10)+5)+stage.tapes) := Fin.natAddEmb ((T+10)+5)
    let baseBank := Fin.castAddEmb (n := ((T+10)+5)+stage.tapes) back.tapes
    let headers := (Fin.castLEEmb forward.fits).trans chart
    let ret := returnChartBank (Fin.castLEEmb reverse.fits) headers
    ∀ (body : P → Pr P ((T+10)+5) columnCapacity prime U) (incoming outgoing : L → P) (childLabel : P),
    let live := (57 : Fin 66).castAdd (K+1)
    let bad := (56 : Fin 66).castAdd (K+1)
    let apart := (Fin.castAddEmb (K+1)).injective.ne (by decide : (57 : Fin 66) ≠ 56)
    let masks := directoryChartMasks live bad apart
    let intervalProj : Matrix (Fin m) (Fin m) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let program := directoryScanProgram (common := common) r (64-r) (by change m+m = 127+1; omega) intervalProj
      (LabelRing.res prime (w+1) (by omega) ∘ weights ∘ Fin.cast dim) pool rowRoom archiveRoom queueRoom
      remainderAnchorFits localBody pairRoom (directoryChartPlacement T) masks (directoryChartReplay T)
      (directoryChartPlacement_ne_mask live bad apart) (fun i _ => directoryChartPlacement_ne_work i _) incoming outgoing childLabel
    let batch := ordinaryDirectoryChild directory r (64-r) w
    let entryPrefix := directoryChartPrefix replayRole layout.beforeH (M^(64*64)) prefixes
    let finished := fun D : Stacks ((T+10)+5) prime =>
      D.R ((1 : Fin 5).natAdd (T+10)) = [] ∧ (D.R ((2 : Fin 5).natAdd (T+10))).length = N ∧
      D.R ((3 : Fin 5).natAdd (T+10)) = [] ∧ D.R ((4 : Fin 5).natAdd (T+10)) = [] ∧
      (∀ j, D.R (directoryChartReplay T j) = []) ∧ (∀ j : Fin 6, 2 ≤ j → D.R (masks j) = [] ∧ D.L (masks j) = []) ∧
      ∀ i : Fin (66+K), 58 ≤ i.val →
        let port := directoryChartPlacement T ((directoryOrdinaryBank archiveRoom i).castAdd 5)
        D.L port = [] ∧ D.R port = []
    ∀ (childBudget capacity : ℕ) (chartFits : stage.states ≤ capacity) (fits : columnCapacity ≤ capacity)
      (backFits : back.states ≤ capacity) (seed : Stacks stage.tapes prime)
      (A : Stacks ((((T+10)+5)+stage.tapes)+back.tapes) prime),
    let ownerSlots := fun j => baseBank (chart (stage.slots j))
    let S := embStk (chart.trans baseBank) A
    let p := max placedPush (Fast.Main.mnProgPush (directoryQueueInitProgram (P := L) (U := U) (Q := columnCapacity) archiveRoom queueRoom))
    let scanRate := (directoryScanCharge_clean (P := L) (U := U) (common := common) r (64-r) 127 dim rfl pool rowRoom
      archiveRoom remainderAnchorFits localPush placedPush p).choose
    let budget := ⌊(childBudget : ℝ)+scanRate*(((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((R : ℝ)*N))⌋₊
    let scanOverhead := ⌊scanRate*(((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((R : ℝ)*N))⌋₊
    ChartPrivateReady stage seed →
    RepT (phaseOwners words) (embStk ownerSlots A).L (embStk ownerSlots A).R →
    (∀ j, (∀ l, ownerSlots l ≠ j) → let entry := ordinaryParentEntry (T := T+10) back.tapes metadata seed
      A.L j = entry.L j ∧ A.R j = entry.R j) →
    DirectoryChartCall archiveRoom localBody body incoming outgoing childLabel directory child batch W M.size W.size
      width childBudget proj weights entryPrefix cutoffWord →
    let positive : 0 < columnCapacity := columnCapacity_pos
    let outer := fun f => statePlacedPr placement fits positive id (body f)
    let enter := (embProg chart (Empty.elim : Empty → P) (foreign (liftQ stage.program chartFits))).seq
      (statePlacedNormalized placement fits positive id ((((normTape slot).seq (directoryRowClock clock)).seq setup).seq program))
    let leave : Pr P ((((T+10)+5)+stage.tapes)+back.tapes) capacity prime U :=
      embProg ret (Empty.elim : Empty → P) (foreign (liftQ back.program backFits))
    let stock := (S.L (stage.slots src)).length+(S.R (stage.slots src)).length
    ∀ u, ∃ z D, ∃ n : ℕ, ∃ final, (n : ℝ) ≤ (13*packedChartRate src cert checked false layout.width +
      packedChartRate src cert checked true layout.width)*(R*N : ℕ) + ((6*stock+directoryRowClockRate*N+setupCost+budget+91 : ℕ) : ℝ) ∧
      Exec (fun f => embProg baseBank id (outer f)) ((embProg baseBank id enter).seq leave) (mk u A) n (mk z D) ∧
      z.user = u.user ∧
      ChartPrivateReady back (embStk ret D) ∧
      (∀ push, Fast.Main.mnProgPush setup ≤ push → Fast.Main.mnProgPush program ≤ push →
        (∀ f, Fast.Main.mnProgPush (body f) ≤ push) →
        let growth := push*(setupCost+scanOverhead)
        chartReturnCost D ≤
          2*cutoffWord.length+167*(R*N)+
            ((T+10)+5)*(6*growth+2*N+4)+back.tapes*(12*(back.cost*(back.tapes+5)+6)+4)+1) ∧
      let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
      (privateTapes.map (fun i => let port := directoryChartPlacement T ((directoryOrdinaryBank archiveRoom i).castAdd 5)
        let tape := baseBank (port.castAdd stage.tapes)
        4*(D.L tape).length+2*(D.R tape).length+4)).sum = 4*privateTapes.length ∧
      (∀ j : Fin 10, D.R (baseBank ((directoryChartWork T j).castAdd stage.tapes)) = []) ∧
      (∀ j : Fin 4, D.L (baseBank ((directoryChartWork T (j.castAdd 6)).castAdd stage.tapes)) = []) ∧
      ((List.finRange 5).map (fun j => let i := baseBank ((j.natAdd (T+10)).castAdd stage.tapes)
        (D.R i).length)).sum = N ∧
      RepT (stage.input final) (embStk (chart.trans baseBank) D).L (embStk (chart.trans baseBank) D).R ∧
      RepT (phaseOwners final) (embStk (fun i => baseBank (chart (stage.slots i))) D).L
        (embStk (fun i => baseBank (chart (stage.slots i))) D).R ∧
      (∀ i, i ≠ src → final i = words i) ∧ OriginalPortReads R W parents interval weights cert (words src) (final src) ∧
      ∃ F, finished (embStk placement F) ∧ ∀ j, (∀ i, headers i ≠ j) →
        D.L (baseBank j) = F.L j ∧ D.R (baseBank j) = F.R j := by
  intro k copy interval member role replayRole r m dim K T W M N directory R parents data child metadata proj src cert checked
  obtain ⟨stage,forward,forwardCost,forwardRun⟩ := (packedRemainderChart_stage src cert checked false).choose_spec.choose_spec
    layout w rows B positiveLayout digits split shape
  obtain ⟨back,reverse,reverseCost,reverseRun⟩ := (packedRemainderChart_stage src cert checked true).choose_spec.choose_spec
    layout w rows B positiveLayout digits split shape
  refine ⟨stage,back,forward,reverse,?_⟩
  intro words routed pool rowRoom archiveRoom queueRoom pairRoom localBody localPush placedPush bounded placed widths clean bank setup setupCost clock slot placement chart baseBank headers ret body incoming outgoing childLabel livePort badPort portsApart maskBank intervalMatrix program batch entryPrefix finished childBudget capacity chartFits fits backFits seedBank initial ownerSlots S p scanRate budget scanOverhead seedReady ownerInput fresh calls positive outer enter leave stock u
  obtain ⟨inCalls,outCalls,childRun⟩ := calls
  obtain ⟨entryEq,input⟩ := ordinaryParentEntry_after_passes (T := T+10) (back := back.tapes) stage metadata seedBank seedReady words initial ownerInput fresh
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts interval member
  have room : 53 < T := by omega
  have base : metadata 2 = binSyms M.size M := rfl
  have seed : metadata 53 = binSyms W.size W := rfl
  have spectators : 0 < W := Nat.mul_pos positiveLayout.2.2.2.1 positiveLayout.2.2.2.2
  have records : R = parents*M^(64*64) := remainderDirectoryCount layout w rows B split shape
  let post := fun (out : Fin (R*N) → ZMod 2) (D : Stacks ((T+10)+5) prime) =>
    (∀ push, Fast.Main.mnProgPush setup ≤ push → Fast.Main.mnProgPush program ≤ push →
      (∀ f, Fast.Main.mnProgPush (body f) ≤ push) → ∀ j, j ≠ slot →
        let growth := push*(setupCost+scanOverhead)
        (D.L j).length ≤ growth ∧ (D.R j).length ≤ (metadata j.val).length+N+growth) ∧
    finished D ∧ PortReads R W parents interval weights routed out ∧
      ∀ j : Fin R, LabelStock.live 64 (w+1) 1 j = false → ownerRow rfl out j = ownerRow rfl routed j
  obtain ⟨z,D,n,out,⟨projectedStock,done,reads,inactive⟩,time,run,user,ready,unusedSlot,owners⟩ :=
    chartOwner_scan stage src metadata words forward.restored positive body ((((normTape slot).seq (directoryRowClock clock)).seq setup).seq program) (6*chartOwnerStock stage src S+6+directoryRowClockRate*N+setupCost+budget) post capacity chartFits fits (embDn baseBank u) S input (by
      intro a F represented stock
      let A := embStk placement (ordinaryOwnerBank metadata F)
      have read : RecordPayload slot (fun _ => blank) 0 routed A := by
        intro j
        have cell := (represented src j).symm
        rw [encodedOwnerCell]
        simpa [A,placement,slot,ordinaryOwnerBank_project,phaseOwners,embStk,routed,encodedOwnerCell] using cell
      have extent : (A.L slot).length+(A.R slot).length ≤ chartOwnerStock stage src S := by
        simpa [A,slot,placement,ordinaryOwnerBank_project] using stock
      obtain ⟨v,normSteps,hu,cost,normalize⟩ := directoryChartOwner_exec body slot routed a A read
      let normalized := {A with L := Function.update A.L slot [], R := Function.update A.R slot (payloadWord (SparseRoleCircuit.encode ∘ routed))}
      have privateTapes := ordinaryOwnerBank_private (T := T+10) metadata F (stage.slots src)
      have privateWord (i : Fin (T+10)) : normalized.R (i.castAdd 5) = metadata i.val := by
        have off : i.castAdd 5 ≠ slot := by
          intro eqn
          have h := congrArg Fin.val eqn
          change i.val = (T+10)+0 at h
          omega
        exact (Function.update_of_ne off ..).trans (privateTapes.1 i).2
      have low (i : Fin T) : normalized.R ((i.castAdd 10).castAdd 5) = metadata i.val :=
        privateWord (i.castAdd 10)
      have work (i : Fin 10) : normalized.R ((i.natAdd T).castAdd 5) = [] :=
        (privateWord (i.natAdd T)).trans (by
          change metadata (T+i.val) = []
          apply directoryChartWords_high <;> omega)
      have dst : clock 9 = (2 : Fin 5).natAdd (T+10) := by
        apply Fin.ext
        change T+12 = (T+10)+2
        omega
      have empty : normalized.R (clock 9) = [] := by
        rw [dst]
        exact (Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne (by decide : (2 : Fin 5) ≠ 0)) ..).trans
          (privateTapes.2 2 (by decide)).2
      obtain ⟨b,l,bu,clockTime,init⟩ := directoryRowClock_exec body clock M W v normalized
        ((low ⟨2,by omega⟩).trans base) ((low ⟨53,room⟩).trans seed) (by
          intro i hi
          by_cases last : i = 9
          · exact last ▸ empty
          have lt : i.val < 9 := by
            have : i.val ≠ 9 := fun h => last (Fin.ext h)
            omega
          let j : Fin 10 := ⟨i.val-2,by omega⟩
          have pos : 2 ≤ i.val := hi
          have eqn : clock i = (j.natAdd T).castAdd 5 := by
            apply Fin.ext
            change (if i.val = 0 then 2 else if i.val = 1 then 53 else if i.val < 9 then T+(i.val-2) else T+12) = T+(i.val-2)
            rw [if_neg (by omega),if_neg (by omega),if_pos lt]
          exact eqn ▸ work j)
      rw [dst] at init
      have clockBound : l ≤ directoryRowClockRate*N :=
        clockTime.trans (directoryRowClockTime_linear (pow_pos Shared50ModularControl.prime_prime.pos _) spectators)
      let C := {normalized with R := Function.update normalized.R ((2 : Fin 5).natAdd (T+10)) (List.replicate N Node.tick)}
      have privateOff (i : Fin (T+10)) (j : Fin 5) : i.castAdd 5 ≠ j.natAdd (T+10) := by
        intro eqn
        have h := congrArg Fin.val eqn
        change i.val = (T+10)+j.val at h
        omega
      have cells (i : Fin (T+10)) : C.L (i.castAdd 5) = [] ∧ C.R (i.castAdd 5) = metadata i.val :=
        ⟨(Function.update_of_ne (privateOff i 0) ..).trans (privateTapes.1 i).1,
          (Function.update_of_ne (privateOff i 2) ..).trans (privateWord i)⟩
      obtain ⟨c,D,s,cu,setupTime,prepare,dir,free,matrix,headers,left,regs⟩ := directoryChartOwnerSetup_exec replayRole
        (by omega : 72 ≤ T+10) body layout rows B positiveLayout digits split shape interval.1 interval.2
        ordered (by omega) root weights units width prefixes widthFits b C cutoffWord widths cells
      have source : C.R slot = payloadWord (SparseRoleCircuit.encode ∘ routed) := by
        simp [C,normalized,slot]
      let place := directoryChartPlacement T
      let localState := embStk place D
      let start := embStk (Fin.castAddEmb (n := T) 5) localState
      let raw := embStk (directoryOrdinaryBank archiveRoom) start
      have shared (i : Fin 58) : raw.R ((i.castAdd 8).castAdd K) = D.R (bank (i.castLE (by decide))) := by
        change D.R (place (((directoryOrdinaryBank archiveRoom) ((i.castAdd 8).castAdd K)).castAdd 5)) = _
        rw [directoryOrdinaryBank_caller,directoryChartPlacement_local]
        rfl
      have localL (i : Fin T) : start.L i = [] := by
        change D.L (place (i.castAdd 5)) = []
        rw [directoryChartPlacement_local]
        exact left _
      have localR (i : Fin T) (hi : 58 ≤ i.val) : start.R i = [] := by
        change D.R (place (i.castAdd 5)) = []
        rw [directoryChartPlacement_local]
        exact free _ hi
      have cleared := (directoryOrdinaryBank_clear_iff archiveRoom start).mpr
        (fun i hi _ => ⟨localL i,localR i hi⟩)
      have hreg (i : Fin 5) : localState.R (i.natAdd T) = C.R (i.natAdd (T+10)) := by
        change D.R (place (i.natAdd T)) = _
        rw [directoryChartPlacement_owner]
        exact (regs i).1
      have blankReg (i : Fin 5) (h₀ : i ≠ 0) (h₂ : i ≠ 2) : localState.R (i.natAdd T) = [] :=
        (hreg i).trans ((Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne h₂) ..).trans
          ((Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne h₀) ..).trans (privateTapes.2 i h₀).2))
      have header (i : Fin 58) (hi : i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58))) :=
        (shared i).trans (headers i hi)
      have entry : GeneratedDirectoryInput (W := W) archiveRoom child directory proj M.size W.size weights
          (directoryChartPrefix replayRole layout.beforeH (M^(64*64)) prefixes) [] [] (List.range R) (ownerRow (R := R) (N := N) rfl routed) localState := by
        refine ⟨localR _ (by have := directoryMatrixTape_private archiveRoom; omega),fun i hi => (cleared i hi).2,
          ?_,?_,?_,?_,header 50 (by decide),header 57 (by decide),header 56 (by decide),header 54 (by decide),
          ?_,blankReg 1 (by decide) (by decide),?_,blankReg 3 (by decide) (by decide),blankReg 4 (by decide) (by decide),?_⟩
        · change DirectoryScanInput _ _ _ _ _ _ _ _ _ _ (fun i => raw.R ((i.castAdd 8).castAdd K))
          rw [funext shared]
          exact dir
        · exact (congrArg List.length (header 29 (by decide))).trans List.length_replicate
        · have eq : directory.rows = rows := by simp [directory,RecursiveInterchangeLayout.role,split]
          exact (congrArg List.length (header 30 (by decide))).trans (List.length_replicate.trans eq.symm)
        · exact (congrArg List.length (header 31 (by decide))).trans List.length_replicate
        · rw [List.append_nil]
          exact ((hreg 0).trans source).trans (ownerRow_queue rfl routed)
        · exact (congrArg List.length (hreg 2)).trans (by simp [C])
        · intro j
          have cell := header 24 (by decide)
          change start.R (directoryOrdinaryBank archiveRoom ((24 : Fin 66).castAdd K)) = [] at cell
          rw [directoryOrdinaryBank_caller] at cell
          change readAt blank (start.L _) (start.R _) j = blank
          rw [localL,cell,readAt_nil_left,wordTape_nil]
      obtain ⟨liveEq,badEq,outside,maskFree,separate,disjoint,replayFree⟩ := directoryChart_workspace (by omega : 58 ≤ T)
        ((57 : Fin 66).castAdd (K+1)) ((56 : Fin 66).castAdd (K+1)) ((Fin.castAddEmb (K+1)).injective.ne (by decide)) D free
      have prepared := intervalInput_cast dim archiveRoom child directory interval weights _ localState routed entry
      have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positiveLayout ⟨rows,split⟩
      have generated := @scheduledIntervalDirectory_exec _ L U w common aux interval member directory weights invertible
        B rolePositive shape pool rowRoom archiveRoom queueRoom pairRoom localBody localPush placedPush bounded placed
        (directoryChartPrefix replayRole layout.beforeH (M^(64*64)) prefixes) _ (embDn place c) localState prepared
      have ownerLeft : localState.L ((0 : Fin 5).natAdd T) = [] := by
        change D.L (place ((0 : Fin 5).natAdd T)) = []
        rw [directoryChartPlacement_owner,(regs 0).2]
        simp [C,normalized,slot]
      have controls := outerWords_of_headers raw (header 29 (by decide)) (header 30 (by decide)) (header 31 (by decide))
      have ownerPort : directoryReturnPorts place maskBank outside 0 = slot :=
        directoryChartPlacement_owner (0 : Fin 5)
      have recordsPos : 0 < R := Nat.mul_pos (Nat.mul_pos rolePositive.1 rolePositive.2.1) rolePositive.2.2.1
      have actualWidth : (entryPrefix 0).length = width :=
        (dir.widths 0 (List.mem_range.mpr recordsPos)).symm.trans
          ((congrArg List.length (headers 47 (by decide))).trans List.length_replicate)
      have groups : R = layout.beforeRows*rows*layout.beforeH := by
        simp only [R,LabelMask.records,directory,RecursiveInterchangeLayout.role,split,Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
      have cleanRows := directoryChartPrefix_all replayRole groups records (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
        prefixes (fun word => blank ∉ word) clean
      have dirRows : directory.rows = rows := by simp [directory,RecursiveInterchangeLayout.role,split]
      obtain ⟨prior,bound,outsideSteps,tail,head,paid,exec⟩ := generated place maskBank incoming body inCalls c D rfl rfl
        liveEq badEq outside maskFree (directoryChartReplay T) separate disjoint replayFree ownerLeft rfl childLabel childBudget
        (by
          intro b D x ready cut dims _ read
          rw [ownerPort] at read ⊢
          exact childRun b D x actualWidth cleanRows (intervalReady_cast dim interval weights child entryPrefix _ _ ready.1) (cut.trans (header 40 (by decide))) (fun j => by
            apply (congrFun dims j).trans
            rw [dirRows]
            exact controls j) read)
        dim outgoing outCalls
      have wordFits : width ≤ N := by
        apply widthFits.trans
        change _ ≤ (prime^(w+1))^128*W
        rw [digits,← pow_mul]
        exact (Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos (by omega)).trans (Nat.le_mul_of_pos_right _ spectators)
      have rowWidth : M^(m+m)*W = N := by rw [dim]
      have cost := paid (show (entryPrefix 0).length ≤ M^(m+m)*W by rw [rowWidth,actualWidth]; exact wordFits)
        p (le_max_right ..) (fun f => (placed f).trans (le_max_left ..))
      have noLeft (i : Fin (66+K)) : raw.L i = [] := localL _
      have matrixSize : (raw.R ((48 : Fin 66).castAdd K)).length = m*m*M.size := by
        have word : raw.R ((48 : Fin 66).castAdd K) = _ := (shared 48).trans matrix
        rw [word,length_matrixWords,dim]
      have zeroStock : (((List.finRange (66+K)).filter fun i => 58 ≤ i.val).map fun i => 4*(raw.L i).length).sum = 0 := by simp [noLeft]
      change ((max (prior+bound) (outsideSteps+childBudget) : ℕ) : ℝ) ≤ directoryScanCharge (P := L) (U := U) (common := common) r (64-r) 127 dim rfl pool rowRoom archiveRoom remainderAnchorFits localPush placedPush p w R (M^(m+m)*W)
        (entryPrefix 0).length (((List.finRange (66+K)).filter fun i => 58 ≤ i.val).map fun i => 4*(raw.L i).length).sum
        0 ((raw.R ((48 : Fin 66).castAdd K)).drop (m*m*M.size)).length childBudget at cost
      simp only [rowWidth,actualWidth,zeroStock,List.length_drop,matrixSize,Nat.sub_self] at cost
      have weighted := (directoryScanCharge_clean (P := L) (U := U) (common := common) r (64-r) 127 dim rfl
        pool rowRoom archiveRoom remainderAnchorFits localPush placedPush p).choose_spec w R N width childBudget
        recordsPos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) spectators) wordFits
      have price : prior+bound ≤ budget := (Nat.le_max_left _ _).trans (Nat.le_floor (cost.trans weighted))
      rw [ownerPort] at exec
      have chartStage := intervalStage_cast (W := W) dim interval weights body program c D prior bound slot tail _ routed exec
      obtain ⟨y,B,t,out,user,time,run,reads,inactive,_,done⟩ := chartStage.portReads interval weights routed records upper
      have regEq (j : Fin 5) : ((Fin.natAddEmb T).trans place) j = j.natAdd (T+10) := directoryChartPlacement_owner j
      have cleaned : finished B := by
        obtain ⟨_,acc,widthReg,save,tmp,replayFree,maskFree,privateFree,_⟩ := done
        refine ⟨(regEq 1) ▸ acc,(regEq 2) ▸ widthReg.trans rowWidth,(regEq 3) ▸ save,(regEq 4) ▸ tmp,replayFree,?_,privateFree⟩
        intro j hj
        refine ⟨(maskFree j hj).1,(maskFree j hj).2.trans ?_⟩
        fin_cases j <;> first | (norm_num at hj; done) | exact left _
      have spectatorStock (push : ℕ) (setupPush : Fast.Main.mnProgPush setup ≤ push)
          (scanPush : Fast.Main.mnProgPush program ≤ push) (bodyPush : ∀ f, Fast.Main.mnProgPush (body f) ≤ push)
          (j : Fin ((T+10)+5)) (ne : j ≠ slot) :
          let growth := push*(setupCost+scanOverhead)
          (B.L j).length ≤ growth ∧ (B.R j).length ≤ (metadata j.val).length+N+growth := by
        have initial : C.L j = [] ∧ (C.R j).length ≤ (metadata j.val).length+N := by
          induction j using Fin.addCases with
          | left i => exact ⟨(cells i).1,((congrArg List.length (cells i).2).le.trans (Nat.le_add_right ..))⟩
          | right i =>
            have nz : i ≠ 0 := fun eq => ne (eq ▸ rfl)
            have old := privateTapes.2 i nz
            have off := (Fin.natAddEmb (T+10)).injective.ne nz
            refine ⟨(Function.update_of_ne off ..).trans old.1,?_⟩
            by_cases eqn : i = 2
            · subst i; simp [C]
            · have empty : C.R (i.natAdd (T+10)) = [] :=
                (Function.update_of_ne ((Fin.natAddEmb (T+10)).injective.ne eqn) ..).trans
                  ((Function.update_of_ne off ..).trans old.2)
              rw [empty]
              exact Nat.zero_le _
        have l₁ := exec_stack_length prepare setupPush bodyPush (.lt j)
        have r₁ := exec_stack_length prepare setupPush bodyPush (.rt j)
        change (D.L j).length ≤ (C.L j).length+push*s at l₁
        change (D.R j).length ≤ (C.R j).length+push*s at r₁
        rw [initial.1,List.length_nil,zero_add] at l₁
        obtain ⟨l₂,r₂⟩ := done.2.2.2.2.2.2.2.2.1 push scanPush bodyPush j ne
        have setupBound := Nat.mul_le_mul_left push (show s ≤ setupCost from setupTime)
        have overhead : outsideSteps ≤ scanOverhead := by
          apply Nat.le_floor
          have paid := (Nat.cast_le (α := ℝ)).mpr (Nat.le_max_right (prior+bound) (outsideSteps+childBudget))
          have h := paid.trans (cost.trans weighted)
          rw [Nat.cast_add] at h
          linarith only [h]
        have scanBound := Nat.mul_le_mul_left push overhead
        have startRight := initial.2
        dsimp only
        rw [Nat.mul_add]
        constructor <;> omega
      exact ⟨y,B,((normSteps+l)+s)+(prior+t),out,by change s ≤ setupCost at setupTime; omega,⟨spectatorStock,cleaned,reads,inactive⟩,user.trans (cu.trans (bu.trans hu)),⟨Exec.seq (Exec.seq (Exec.seq normalize init) prepare) run.run,run.reads⟩⟩)
  let updated := Function.update (stage.transform words) src out
  have chartInput : RepT (stage.input updated) (embStk chart D).L (embStk chart D).R := by
    apply chartOwner_input stage _ (embStk chart D) _ ready _ (fun _ _ => ⟨rfl,rfl⟩)
    intro i j
    simpa [phaseOwners,updated,embStk,chart] using (owners i j).symm
  obtain ⟨y,F,t,price,exec,finish,privateReady,final,suffixStock,frame⟩ := ownerRun_returnChart forward reverse backFits chart outer
    enter updated (ordinaryOwnerBank metadata S) D u z n run chartInput
  change Exec _ _ (mk u (ordinaryParentEntry (T := T+10) back.tapes metadata S)) _ _ at exec
  rw [entryEq] at exec
  refine ⟨y,F,n+t,back.transform updated,?_,exec,finish.trans user,?_⟩
  · let localCost := 6*stock+directoryRowClockRate*N+setupCost+budget+91
    have actual : n+t ≤ 13*(stage.cost*(stage.tapes+5))+back.cost*(back.tapes+5)+localCost := by
      dsimp only [chartOwnerStock] at time
      dsimp only [localCost,stock]
      omega
    have runtime : ((n+t : ℕ) : ℝ) ≤ 13*(stage.cost*(stage.tapes+5) : ℕ)+(back.cost*(back.tapes+5) : ℕ)+localCost := by
      exact_mod_cast actual
    have widthBound : (w+1)*64 ≤ layout.width := by omega
    have firstCost := forwardCost layout.width widthBound
    have lastCost := reverseCost layout.width widthBound
    change _ ≤ (((_ : ℝ)+_)*((R*N : ℕ) : ℝ))*_ at firstCost lastCost
    change _ ≤ ((_ : ℝ)+_)*((R*N : ℕ) : ℝ)+(localCost : ℝ)
    unfold packedChartRate
    dsimp only
    linarith only [runtime,firstCost,lastCost]
  have prefixFrame (j : Fin ((T+10)+5)) := frame (j.castAdd stage.tapes) (fun i eq => by
    have h := congrArg Fin.val eq
    change (T+10)+5+i.val = j.val at h
    omega)
  have prefixPort (j : Fin ((T+10)+5)) (ne : j ≠ slot) : placement j = j.castAdd stage.tapes := by
    have apart : j.castAdd stage.tapes ≠ (stage.slots src).natAdd ((T+10)+5) := by
      intro eq
      have h := congrArg Fin.val eq
      change j.val = (T+10)+5+(stage.slots src).val at h
      omega
    exact Equiv.swap_apply_of_ne_of_ne ((Fin.castAddEmb stage.tapes).injective.ne ne) apart
  have maskPos (l : Fin 4) : maskBank (l.natAdd 2) = directoryChartWork T (l.castAdd 6) := by
    fin_cases l <;> rfl
  have metaBound : 2*((List.finRange ((T+10)+5)).map (fun j => (metadata j.val).length)).sum ≤
      2*cutoffWord.length+167*(R*N) := by
    have groups : R = layout.beforeRows*rows*layout.beforeH := by
      simp only [R,LabelMask.records,directory,RecursiveInterchangeLayout.role,split,Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
    have blocks : parents ≤ layout.beforeRows*rows*layout.beforeH := by
      rw [← groups,records]
      exact Nat.le_mul_of_pos_right _ (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    have fit : width ≤ N := by
      apply widthFits.trans
      change _ ≤ (prime^(w+1))^128*W
      rw [digits,← pow_mul]
      exact (Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos (by omega)).trans (Nat.le_mul_of_pos_right _ spectators)
    have rowPos : 0 < rows := by have := positiveLayout.2.1; omega
    have bound := directoryChartEntry_volume_le (w := w) root replayRole prefixes [] widths blocks
      spectators positiveLayout.1 rowPos positiveLayout.2.2.1 fit (Nat.zero_le _)
    have measure := chartMetadataLength (t := (T+10)+5) (by omega) cutoffWord W layout.beforeRows rows layout.beforeH root
      weights width (directoryChartQueue replayRole layout.beforeH parents R prefixes)
    change ((List.finRange ((T+10)+5)).map (fun j => (metadata j.val).length)).sum = _ at measure
    rw [measure,groups]
    change 6*(_+(_ : List (Fin (prime+4))).length)+55+(6*0+6) ≤ 499*(layout.beforeRows*rows*layout.beforeH*N) at bound
    omega
  have suffixCost : ((List.finRange back.tapes).map (fun j => let i := j.natAdd (((T+10)+5)+stage.tapes)
      4*(F.L i).length+2*(F.R i).length+4)).sum ≤ back.tapes*(12*(back.cost*(back.tapes+5)+6)+4) := by
    have total := List.sum_le_sum (l := List.finRange back.tapes) (g := fun _ => 12*(back.cost*(back.tapes+5)+6)+4)
        (f := fun j => let i := j.natAdd (((T+10)+5)+stage.tapes)
          4*(F.L i).length+2*(F.R i).length+4) (fun j _ => by
            obtain ⟨left,right⟩ := suffixStock j
            dsimp only
            omega)
    simpa only [List.map_const',List.sum_replicate_nat,List.length_finRange] using total
  refine ⟨privateReady,?_,?_,?_,?_,?_,final,?_,?_,?_,D,done,frame⟩
  · intro push setupPush scanPush bodyPush
    apply Nat.add_le_add_right (Nat.add_le_add ?_ suffixCost) 1
    apply le_trans _ (Nat.add_le_add_right metaBound _)
    apply chartCleanupCost ((Fin.castAddEmb stage.tapes).trans baseBank)
    intro j
    change (F.L (baseBank (j.castAdd stage.tapes))).length ≤ _ ∧ (F.R (baseBank (j.castAdd stage.tapes))).length ≤ _
    rw [(prefixFrame j).1,(prefixFrame j).2]
    by_cases eq : j = slot
    · subst j; rw [unusedSlot.1,unusedSlot.2]; exact ⟨Nat.zero_le _,Nat.zero_le _⟩
    · have h := projectedStock push setupPush scanPush bodyPush j eq
      change (D.L (placement j)).length ≤ _ ∧ (D.R (placement j)).length ≤ _ at h
      rwa [prefixPort j eq] at h
  · let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    have charge (i) (hi : i ∈ privateTapes) := done.2.2.2.2.2.2 i (List.mem_filter.mp hi |>.2 |> of_decide_eq_true)
    let physical := fun i : Fin (66+K) => directoryChartPlacement T ((directoryOrdinaryBank archiveRoom i).castAdd 5)
    have off (i) : physical i ≠ slot := by
      intro eq
      have h := congrArg Fin.val eq
      change (if (directoryOrdinaryBank archiveRoom i).val < T then _ else _) = (T+10)+0 at h
      rw [ite_eq_left (directoryOrdinaryBank archiveRoom i).isLt] at h
      have bound := (directoryOrdinaryBank archiveRoom i).isLt
      omega
    have four (i) (hi : i ∈ privateTapes) :
        let j := baseBank ((physical i).castAdd stage.tapes)
        4*(F.L j).length+2*(F.R j).length+4 = 4 := by
      obtain ⟨left,right⟩ := charge i hi
      change D.L (placement (physical i)) = [] at left
      change D.R (placement (physical i)) = [] at right
      rw [prefixPort _ (off i)] at left right
      dsimp only
      rw [(prefixFrame _).1,(prefixFrame _).2,left,right]
      rfl
    change (privateTapes.map _).sum = _
    rw [List.map_congr_left four,List.map_const',List.sum_replicate_nat,Nat.mul_comm]
  · intro j
    have off : directoryChartWork T j ≠ slot := by
      intro eq
      have h := congrArg Fin.val eq
      change T+j.val = (T+10)+0 at h
      omega
    rw [(prefixFrame _).2,← prefixPort _ off]
    change (embStk placement D).R (directoryChartWork T j) = []
    by_cases mask : j.val < 4
    · let l : Fin 4 := ⟨j.val,mask⟩
      have atMask := done.2.2.2.2.2.1 (l.natAdd 2) (by change 2 ≤ 2+l.val; omega)
      rw [maskPos l] at atMask
      exact atMask.1
    · let l : Fin 6 := ⟨j.val-4,by omega⟩
      have pos : directoryChartReplay T l = directoryChartWork T j := by
        apply congrArg (directoryChartWork T)
        apply Fin.ext
        change 4+(j.val-4) = j.val
        omega
      exact pos ▸ done.2.2.2.2.1 l
  · intro j
    have off : directoryChartWork T (j.castAdd 6) ≠ slot := by
      intro eq
      have h := congrArg Fin.val eq
      change T+j.val = (T+10)+0 at h
      omega
    rw [(prefixFrame _).1,← prefixPort _ off,← maskPos]
    exact (done.2.2.2.2.2.1 (j.natAdd 2) (by change 2 ≤ 2+j.val; omega)).2
  · have kept (j : Fin 5) := prefixFrame (j.natAdd (T+10))
    have regs (j : Fin 5) (ne : j ≠ 0) := prefixPort (j.natAdd (T+10)) ((Fin.natAddEmb (T+10)).injective.ne ne)
    obtain ⟨acc,widthReg,save,tmp,_⟩ := done
    change D.R (placement _) = [] at acc save tmp
    change (D.R (placement _)).length = N at widthReg
    rw [regs 1 (by decide)] at acc
    rw [regs 2 (by decide)] at widthReg
    rw [regs 3 (by decide)] at save
    rw [regs 4 (by decide)] at tmp
    simp [List.finRange_succ]
    dsimp only [baseBank]
    simp only [(kept 0).2,(kept 1).2,(kept 2).2,(kept 3).2,(kept 4).2,unusedSlot.2,acc,widthReg,save,tmp,List.length_nil,Nat.zero_add,Nat.add_zero]
  · rw [← stage.input_payload]
    exact fun i h => final (stage.slots i) h
  · intro i hi
    exact ((reverseRun updated).1 i hi).trans ((Function.update_of_ne hi ..).trans ((forwardRun words).1 i hi))
  · have undo := (reverseRun updated).2
    simp only [ite_true] at undo
    have rowCount : directory.rows = rows := by simp [directory,RecursiveInterchangeLayout.role,split]
    have transport := PortReads.roundTrip directory digits shape interval weights cert checked (words src) routed out
      (back.transform updated src) (by simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,M] using records)
      (forwardRun words).2 (by simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,W] using reads)
      inactive (by rw [show updated src = out from Function.update_self ..] at undo; exact undo)
    simpa only [directory,RecursiveInterchangeLayout.role,show layout.rows/142080 = rows from rowCount,parents,W] using transport

end IntegerMultBounds.MathlibTM2.M6.BitNode
