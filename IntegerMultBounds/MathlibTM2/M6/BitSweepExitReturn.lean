module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitPlacement

/-! Execute the physical stage exit and its return to parent addresses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback RingFormula Node
open Shared50ModularControl (prime)

structure ReturnHeaders (w H : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (W B : ℕ)
    (R : Fin tapes → List (Fin (prime+4))) : Prop where
  exponent : (R (p 10)).length = w+1
  bits : (R (p 18)).length = H
  unit : (R (p 29)).length = 1
  archiveSize : (R (p 37)).length = (prime^(w+1)).size
  archive : ∃ tail, R (p 38) = (List.ofFn fun i => binSyms (prime^(w+1)).size (parent i).val).flatten ++ tail
  blank : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), R (p i) = []
  matrixFree : ∀ j, R (pool j) = []
  rankFree : ∀ j, R (rankPool j) = []
  coordFree : ∀ j, R (coordPool j) = []
  maskFree : ∀ j, j ≠ .width → R (rg j) = []
  recordWidth : (R (g 3)).length = W
  empty : R (g 0) = []
  gatherFree : ∀ i : Fin 10, 5 ≤ i → R (g i) = []
  scanFree : ∀ i : Fin 5, i ≠ 0 → R (s i) = []
  transpose : ∃ record row : List (Fin (prime+4)), record.length = (prime^(w+1))^112*W ∧
    row.length = B*((prime^(w+1))^112*W) ∧ ∀ r i, i ≠ (6 : Fin 8) →
      R (bank r i) = (transposeStacks (⟨[],[],fun _ => [],fun _ => []⟩ : Stacks 8 prime) [] [] [] record row).R i

/-- Return exact owner words to node order. A producer may fill the owners
while the return headers stay on the other registers. -/
theorem placedWordReturn_exec {P U : Type} {Q : ℕ} (n : Fin 9) :
    ∃ C : ℕ, ∀ {T : ℕ} (body : P → Pr P T Q prime U) (sw : Fin tapes ↪ Fin T), ∃ back, ∀ (w H B W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W →
    ∀ (x : OwnerArray (w+1) B W) (v : HS T Q prime U) (S D : Stacks T prime),
    ReturnHeaders w H parent W B (embStk sw S).R →
    (∀ j, (∀ i, owners i ≠ j) → (embStk sw D).R j = (embStk sw S).R j) →
    (∀ r, D.R (sw (owners (sweepRoleTape r))) = List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x (sweepRoleTape r) i)) →
    ∃ z G l, Exec body back (mk v D) l (mk z G) ∧
      l ≤ 142080*(C*(M^16*(B*prime^(64*((w+1)*64))*(M^112*W)))+8)+1 ∧ z.user = v.user ∧
      ∀ r, G.R (sw (owners (sweepRoleTape r))) = List.ofFn fun i =>
        SparseRoleCircuit.encode (nodeArray parent units n x (sweepRoleTape r) i) := by
  obtain ⟨back,C,restore⟩ := sweepAllocatedReturn_exec (P := Empty) (U := U) (Q := Q) Empty.elim n
  refine ⟨C,?_⟩
  intro T body sw
  refine ⟨embProg sw Empty.elim back,?_⟩
  intro w H B W parent units M hw bound hb hwid x v S D headers frame written
  let F := embStk sw D
  have keep (j) (apart : ∀ i, owners i ≠ j) : F.R j = (embStk sw S).R j := frame j apart
  have workKept i := keep (work i) (by intro h eqn; cases (Fintype.equivFin File).injective eqn)
  have matrixKept i := keep (pool i) (by intro h eqn; cases (Fintype.equivFin File).injective eqn)
  have rankKept i := keep (rankPool i) (by intro h eqn; cases (Fintype.equivFin File).injective eqn)
  have coordKept i := keep (coordPool i) (by intro h eqn; cases (Fintype.equivFin File).injective eqn)
  obtain ⟨tail,archive⟩ := headers.archive
  obtain ⟨record,row,len,rowLen,prepared⟩ := headers.transpose
  have atP i : F.R (p i) = (embStk sw S).R (p i) := workKept _
  obtain ⟨a,R,l,same,bill,ret,done,_⟩ := restore w H W B parent units tail hw bound hwid hb
    x (embDn sw v) F (by rw [atP]; exact headers.exponent) (by rw [atP]; exact headers.bits)
    (by rw [atP]; exact headers.unit) (by rw [atP]; exact headers.archiveSize) ((atP _).trans archive)
    (fun i hi => (atP _).trans (headers.blank i hi)) (fun i => (matrixKept i).trans (headers.matrixFree i))
    (fun i => (rankKept i).trans (headers.rankFree i)) (fun i => (coordKept i).trans (headers.coordFree i))
    (fun i hi => (workKept _).trans (headers.maskFree i hi)) (by rw [show F.R (g 3) = _ from workKept (gatherSlot 3)]; exact headers.recordWidth)
    ((workKept _).trans headers.empty) (fun i hi => (workKept _).trans (headers.gatherFree i hi))
    (fun i hi => (workKept _).trans (headers.scanFree i hi)) record row len rowLen (by
      intro r
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases h : i = 6
      · subst i; exact written r
      have eqn : bank r i = work (transposeSlot i) := by simp [bank,work,address,transReg,h]; rfl
      change F.R (bank r i) = _
      rw [show F.R (bank r i) = (embStk sw S).R (bank r i) by rw [eqn]; exact workKept _]
      exact (prepared r i h).trans (by fin_cases i <;> first | contradiction | rfl))
  obtain ⟨z,G,placed,_,hz,view,_⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    sw.injective (fun e => nomatch e) ret v rfl D rfl
  refine ⟨z,G,l,placed,bill,hz.trans same,?_⟩
  intro r
  exact (congrArg (fun E : Stacks tapes prime => E.R (owners (sweepRoleTape r))) view).trans (done r)

theorem stageExitReturn_exec {P U : Type} {Q t : ℕ} (n : Fin 9) (fan : Fin (142081+2) ↪ Fin t)
    (fits : 215 ≤ Q) :
    ∃ C : ℕ, ∀ (w H B W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let K := M^112*W
    let A := M^16
    let N := prime^(64*((w+1)*64))
    M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W →
    ∀ (leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K)))),
    leave.states ≤ Q → ∀ body : P → Pr P (size t leave.tapes) Q prime U,
    let crop := port fan leave.slots
    let sw := sweep t leave.tapes
    let dest := owners.trans sw
    let scratch := tmp t leave.tapes
    ∃ code, ∀ x u S, HelperFan (fan.trans (recursive t leave.tapes)) (singleLabelBank (firstRowLabel (w+1)) x) S →
      ChartPrivateReady leave (embStk (chart t leave.tapes) S) → CropCounters (crop 0) (A*B) N K S →
      (∀ i z, readAt blank (S.L (crop i 1)) (S.R (crop i 1)) z = blank) →
      S.L scratch = [] → S.R scratch = [] → (∀ i, S.R (dest i) = []) →
      ReturnHeaders w H parent W B (embStk sw S).R →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧
        l ≤ 142081*(7021*(A*B)*(N*K)+6)+1 + (leave.cost*(leave.tapes+5)+6) +
          (142081*(8*(A*(B*K))+10)+1) + (142080*(C*(A*(B*N*K))+8)+1) ∧
        z.user = u.user ∧ ∀ r, F.R (dest (sweepRoleTape r)) = List.ofFn fun i =>
          SparseRoleCircuit.encode (nodeArray parent units n (leave.transform x) (sweepRoleTape r) i) := by
  obtain ⟨C,restore⟩ := placedWordReturn_exec (P := P) (U := U) (Q := Q) n
  refine ⟨C,?_⟩
  intro w H B W parent units M K A N hw bound hb hwid leave room body crop sw dest scratch
  obtain ⟨code,run⟩ := placedStageExit_exec (w := w+1) fan fits hb
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hwid) leave room body
  obtain ⟨back,finish⟩ := restore body sw
  refine ⟨code.seq back,?_⟩
  intro x u S live privateReady counters empty left right fresh headers
  obtain ⟨v,D,k,exitRun,paid,user,words,frame⟩ := run x u S live privateReady counters empty left right fresh
  obtain ⟨z,G,l,placed,bill,same,done⟩ := finish w H B W parent units hw bound hb hwid
    (leave.transform x) v S D headers (fun j apart => (frame j apart).2) (fun r => words (sweepRoleTape r))
  exact ⟨z,G,k+l,Exec.seq exitRun placed,Nat.add_le_add paid bill,same.trans user,done⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
