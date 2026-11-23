module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
public import IntegerMultBounds.MathlibTM2.Host.TapeCharge
public import IntegerMultBounds.MathlibTM2.Host.ForeignStock
public import IntegerMultBounds.MathlibTM2.M6.BitOwnerRead
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalSetup
public import IntegerMultBounds.MathlibTM2.M6.BitHelperFanRun

/-! The recursive owner tapes and their two loop controls inside a split COPY bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

def intervalOwners (c : ℕ) : Fin (c+2) ↪ Fin (((1+c)+2)+2) where
  toFun := Fin.addCases (fun j => ((j.natAdd 1).castAdd 2).castAdd 2) (fun j => j.natAdd ((1+c)+2))
  inj' := by
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [Fin.addCases_left,Fin.addCases_right] <;> intro h <;>
      have eq := congrArg Fin.val h <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at eq
    all_goals first | congr 1; exact Fin.ext (by omega) | omega

/-- Reattach the original target and two inner counters to the child output
owners and their two volume counters. This placement requires no tape moves. -/
def returnedMergeBank {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) : Fin (((1+c)+2)+2) ↪ Fin T where
  toFun := Fin.addCases (Fin.addCases (Fin.addCases (fun _ => saved 0)
    (fun r => fan (r.castAdd 2))) (fun j => saved j.succ)) (fun j => fan (j.natAdd c))
  inj' := by
    have split (P : Fin (((1+c)+2)+2) → Prop)
        (src : ∀ i : Fin 1, P (((i.castAdd c).castAdd 2).castAdd 2))
        (owner : ∀ r : Fin c, P (((r.natAdd 1).castAdd 2).castAdd 2))
        (inner : ∀ j : Fin 2, P ((j.natAdd (1+c)).castAdd 2))
        (outer : ∀ j : Fin 2, P (j.natAdd ((1+c)+2))) : ∀ i, P i :=
      Fin.addCases (Fin.addCases (Fin.addCases src owner) inner) outer
    intro i j
    revert j i
    apply split <;> intro i <;> apply split <;> intro j
    all_goals simp only [Fin.addCases_left,Fin.addCases_right]
    all_goals intro eq
    all_goals first
      | apply Fin.ext; simp only [Fin.val_castAdd]; omega
      | exact False.elim (apart _ _ eq)
      | exact False.elim (apart _ _ eq.symm)
      | apply Fin.ext
        first | have h := congrArg Fin.val (saved.injective eq)
              | have h := congrArg Fin.val (fan.injective eq)
        simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_succ,Fin.val_zero] at *
        omega

theorem returnedMergeBank_owners {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) :
    (intervalOwners c).trans (returnedMergeBank saved fan apart) = fan := by
  ext i
  induction i using Fin.addCases <;> simp [returnedMergeBank,intervalOwners]

theorem returnedMergeBank_target {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) : returnedMergeBank saved fan apart 0 = saved 0 := by
  change returnedMergeBank saved fan apart ((((0 : Fin 1).castAdd c).castAdd 2).castAdd 2) = _
  simp [returnedMergeBank]

theorem returnedMergeBank_inner {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (j : Fin 2) :
    returnedMergeBank saved fan apart ((j.natAdd (1+c)).castAdd 2) = saved j.succ := by
  simp [returnedMergeBank]

noncomputable def intervalOwnerBank {m c : ℕ} (src : ℤ → Fin (prime+4)) (data : Fin c → Fin m → ZMod 2) :=
  CyclicRowSplit.bank (CyclicRowCopy.bank src
    (fun j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded data j)))
    0 (fun _ => 0) (FlatCoordinateSchedule.bits 1)) (FlatCoordinateSchedule.bits m)

/-- The split roles and the outer loop header already represent the owner bank. -/
theorem intervalOwners_ready {m c : ℕ} (src : ℤ → Fin (prime+4)) (data : Fin c → Fin m → ZMod 2)
    (S : Stacks (((1+c)+2)+2) prime) (ready : RepT (intervalOwnerBank src data) S.L S.R) :
    HelperFan (intervalOwners c) data S := by
  intro i z
  induction i using Fin.addCases with
  | left j =>
    simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
      CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
      embStk,Function.comp_apply,intervalOwners,Function.Embedding.coeFn_mk] using
      ready (((j.natAdd 1).castAdd 2).castAdd 2) z
  | right j =>
    simpa only [intervalOwnerBank,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,
      Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,intervalOwners,Function.Embedding.coeFn_mk] using
      ready (j.natAdd ((1+c)+2)) z

/-- Returning the owner fan suffices for merge. Only the source and the inner
loop's two controls lie outside the fan. -/
theorem intervalOwners_return {m c : ℕ} (src : ℤ → Fin (prime+4))
    (x y : Fin c → Fin m → ZMod 2) (S F : Stacks (((1+c)+2)+2) prime)
    (ready : RepT (intervalOwnerBank src x) S.L S.R) (out : HelperFan (intervalOwners c) y F)
    (source : F.L 0 = S.L 0 ∧ F.R 0 = S.R 0)
    (inner : ∀ j : Fin 2, let k := (j.natAdd (1+c)).castAdd 2
      F.L k = S.L k ∧ F.R k = S.R k) :
    RepT (intervalOwnerBank src y) F.L F.R := by
  intro i z
  induction i using Fin.addCases with
  | right j => simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
        CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        embStk,Function.comp_apply,intervalOwners,Function.Embedding.coeFn_mk] using out (j.natAdd c) z
  | left i =>
    induction i using Fin.addCases with
    | right j =>
      rw [(inner j).1,(inner j).2]
      simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
        CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        embStk,Function.comp_apply,intervalOwners,Function.Embedding.coeFn_mk] using ready ((j.natAdd (1+c)).castAdd 2) z
    | left i =>
      induction i using Fin.addCases with
      | right j => simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
        CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
        embStk,Function.comp_apply,intervalOwners,Function.Embedding.coeFn_mk] using out (j.castAdd 2) z
      | left j =>
        have eq : j = 0 := Subsingleton.elim _ _
        subst j
        change _ = readAt blank (F.L 0) (F.R 0) _
        rw [source.1,source.2]
        exact ready (((0 : Fin (1+c)).castAdd 2).castAdd 2) z

/-- Merge the returned rows into a single interleaved word while retaining
the owner tapes. The entry bank may contain either the original or an empty
destination, as specified by its tape function. -/
theorem mergeReturnedOwners_exec {P U : Type} {Q m : ℕ}
    (body : P → Pr P intervalSplitTapes Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (dst : ℤ → Fin (prime+4)) (data : Fin 142080 → Fin m → ZMod 2)
    (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (ready : RepT (intervalOwnerBank dst data) S.L S.R) :
    let word := fun k : Fin (m*142080) => let p := finProdFinEquiv.symm k
                                         SparseRoleCircuit.encode (a := prime) (data p.2 p.1)
    ∃ z F t, Exec body (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))
      (mk u S) t (mk z F) ∧ t ≤ 149*(m*142080)*(intervalSplitTapes+5)+6 ∧ z.user = u.user ∧
      RepT (intervalOwnerBank (putWord dst 0 (List.ofFn word)) data) F.L F.R ∧
      ∀ j, (F.L j).length+(F.R j).length ≤ (S.L j).length+(S.R j).length+298*(m*142080) := by
  intro word
  let rows := fun (i : Fin m) (r : Fin 142080) => [word (finProdFinEquiv (i,r))]
  let bs := FlatCoordinateSchedule.bits 1
  let gs := FlatCoordinateSchedule.bits m
  have hm := CyclicRowNormalized.merge_hoare dst (fun _ _ => blank) 0 (fun _ => 0) rows 1
    (fun _ _ => rfl) bs gs (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
  obtain ⟨src,parts⟩ := singletonRows word
  change CyclicRowSplit.sourceWord rows = _ at src
  change ∀ j, CyclicRowSplit.roleWord rows j = _ at parts
  have lanes (j : Fin 142080) : CyclicRowSplit.roleWord rows j =
      List.ofFn (SparseRoleCircuit.encoded (a := prime) data j) := by
    change _ = List.ofFn (fun i => SparseRoleCircuit.encode (data j i))
    simpa only [word,Equiv.symm_apply_apply] using parts j
  simp only [src,lanes] at hm
  obtain ⟨z,F,_,rfl,rep,user,_,_,growth,t,paid,run⟩ := foreign_exec (body := body)
    (liftQ _ capacity) (HoareTime.liftQ capacity hm) u _ _ rfl ready
  have bound := CyclicRowNormalized.cost_linear 1 bs gs (by decide : 0 < 142080) positive (by decide)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  rw [Nat.mul_one] at bound
  refine ⟨z,F,t,run,paid.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ bound) _),user,rep,?_⟩
  intro j
  have h := growth j
  omega

/-- Execute the merger on the returned fan and the three retained splitter
tapes, leaving the surrounding record workspaces untouched. -/
theorem placedMergeReturnedOwners_exec {P U : Type} {T Q m : ℕ}
    (body : P → Pr P T Q prime U) (place : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (dst : ℤ → Fin (prime+4)) (original data : Fin 142080 → Fin m → ZMod 2)
    (before : Stacks intervalSplitTapes prime) (u : HS T Q prime U) (S : Stacks T prime)
    (split : RepT (intervalOwnerBank dst original) before.L before.R)
    (rows : HelperFan ((intervalOwners 142080).trans place) data S)
    (source : S.L (place 0) = before.L 0 ∧ S.R (place 0) = before.R 0)
    (inner : ∀ j : Fin 2, let k := (j.natAdd (1+142080)).castAdd 2
      S.L (place k) = before.L k ∧ S.R (place k) = before.R k) :
    let word := fun k : Fin (m*142080) => let p := finProdFinEquiv.symm k
                                         SparseRoleCircuit.encode (a := prime) (data p.2 p.1)
    ∃ z F n, Exec body (embProg place Empty.elim (foreign (liftQ
      (CyclicRowNormalized.mergeProgram 142080 prime) capacity))) (mk u S) n (mk z F) ∧
      n ≤ 149*(m*142080)*(intervalSplitTapes+5)+6 ∧ z.user = u.user ∧
      RepT (intervalOwnerBank (putWord dst 0 (List.ofFn word)) data) (embStk place F).L (embStk place F).R ∧
      (∀ j, (F.L (place j)).length+(F.R (place j)).length ≤
        (S.L (place j)).length+(S.R (place j)).length+298*(m*142080)) ∧
      (∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ js : List (Fin T), js.Nodup →
        (js.map fun j => 4*(F.L j).length+2*(F.R j).length+4).sum ≤
        (js.map fun j => 4*(S.L j).length+2*(S.R j).length+4).sum+12*n := by
  intro word
  have ready := intervalOwners_return dst original data before (embStk place S) split rows source inner
  obtain ⟨v,D,n,run,paid,user,result,growth⟩ := mergeReturnedOwners_exec (P := Empty) Empty.elim
    capacity positive dst data (embDn place u) (embStk place S) ready
  obtain ⟨z,F,exec,_,same,view,keep⟩ := exec_emb (body' := body) (ι := Empty.elim)
    place.injective (fun e => nomatch e) run u rfl S rfl
  rw [← view] at growth result
  refine ⟨z,F,n,exec,paid,same.trans user,result,growth,keep,?_⟩
  intro js distinct
  have push {K P σ : Type} {Γ : K → Type} {p : Prog P Γ σ} {c : ℕ}
      (bound : Fast.Main.mnNativePushBound c p) : Fast.Main.mnProgPush p ≤ c := by
    induction p with
    | act => exact bound
    | seq _ _ ih₁ ih₂ | cond _ _ _ ih₁ ih₂ => exact max_le (ih₁ bound.1) (ih₂ bound.2)
    | loop _ _ ih => exact ih bound
    | call => exact bound.elim
  have bill := placedCleanup_cost_le place S F (fun l r => 4*l.length+2*r.length+4) 0 (12*n) keep (by
    intro is separate
    have charge := Cover.Fallback.recordCleanup_cost_le is separate run (push (foreign_native _)) (fun e => nomatch e)
    rw [← view] at charge
    simp only [embStk,Function.comp_apply] at charge
    simp only [tapeCharge,embStk,Function.comp_apply,Nat.zero_add]
    omega) js distinct
  simpa only [Nat.zero_add,tapeCharge] using bill

/-- Insert one private helper before the physical bank. In the logical owner
order it follows the data and precedes both controls. -/
def withHelperPort {c T : ℕ} (fan : Fin (c+2) ↪ Fin T) : Fin ((c+1)+2) ↪ Fin (T+1) where
  toFun := Fin.addCases (Fin.lastCases 0 (fun j => (fan (j.castAdd 2)).succ))
    (fun j => (fan (j.natAdd c)).succ)
  inj' := by
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases
    case left.left a b =>
      induction a using Fin.lastCases <;> induction b using Fin.lastCases <;> simp [fan.injective.eq_iff] <;> intro h <;> have eq := congrArg Fin.val h <;> simp only [Fin.val_zero,Fin.val_succ,Fin.val_castAdd,Fin.val_natAdd] at eq <;> omega
    case left.right a b =>
      induction a using Fin.lastCases <;> simp [fan.injective.eq_iff] <;> intro h <;> have eq := congrArg Fin.val h <;> simp only [Fin.val_zero,Fin.val_succ,Fin.val_castAdd,Fin.val_natAdd] at eq <;> omega
    case right.left a b =>
      induction b using Fin.lastCases <;> simp [fan.injective.eq_iff] <;> intro h <;> have eq := congrArg Fin.val h <;> simp only [Fin.val_zero,Fin.val_succ,Fin.val_castAdd,Fin.val_natAdd] at eq <;> omega
    case right.right => simp [fan.injective.eq_iff]

theorem withHelperPort_ready {c T m : ℕ} (fan : Fin (c+2) ↪ Fin T)
    (x : Fin c → Fin m → ZMod 2) (S : Stacks (T+1) prime)
    (owners : HelperFan fan x (embStk Fin.succ S)) (left : S.L 0 = [])
    (helper : S.R 0 = List.replicate m (bitSymbol false)) :
    HelperFan (withHelperPort fan) (Fin.lastCases (fun _ => 0) x) S := by
  have encoded {n} (data : Fin n → Fin m → ZMod 2) (j : Fin n) :
      SparseRoleCircuit.encoded (a := prime) data j = fun i => SparseRoleCircuit.encode (data j i) := rfl
  intro i z
  induction i using Fin.addCases with
  | left j =>
    induction j using Fin.lastCases with
    | cast j =>
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.lastCases_castSucc,
        encoded,embStk,Function.comp_apply,withHelperPort,Function.Embedding.coeFn_mk] using owners (j.castAdd 2) z
    | last =>
      simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.lastCases_last,
        encoded,embStk,Function.comp_apply,withHelperPort,Function.Embedding.coeFn_mk,
        left,helper,sub_zero,putWord_blank_zero,readAt_nil_left]
      simp [SparseRoleCircuit.encode]
  | right j =>
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,
      withHelperPort,Function.Embedding.coeFn_mk] using owners (j.natAdd c) z

/-- Project the returned data and both controls back to the merge bank,
independently of the helper's final value. -/
theorem withHelperPort_return {c T m : ℕ} (fan : Fin (c+2) ↪ Fin T)
    (y : Fin (c+1) → Fin m → ZMod 2) (F : Stacks (T+1) prime)
    (out : HelperFan (withHelperPort fan) y F) :
    HelperFan fan (fun j => y j.castSucc) (embStk Fin.succ F) := by
  have encoded {n} (data : Fin n → Fin m → ZMod 2) (j : Fin n) :
      SparseRoleCircuit.encoded (a := prime) data j = fun i => SparseRoleCircuit.encode (data j i) := rfl
  intro i z
  induction i using Fin.addCases with
  | left j =>
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.lastCases_castSucc,
      encoded,embStk,Function.comp_apply,withHelperPort,Function.Embedding.coeFn_mk] using out (j.castSucc.castAdd 2) z
  | right j =>
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,
      withHelperPort,Function.Embedding.coeFn_mk] using out (j.natAdd (c+1)) z

/-- A single encoded input and empty work tapes supply the packed node's full
owner fan, including its zero helper and both restored loop controls. -/
theorem intervalPackedInput_exec {P U : Type} {Q m : ℕ}
    (body : P → Pr P (intervalSplitTapes+1) Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (x : Fin (m*142080) → ZMod 2) (u : HS (intervalSplitTapes+1) Q prime U)
    (S : Stacks (intervalSplitTapes+1) prime)
    (source : S.R (Fin.succ 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)))
    (left : ∀ i, S.L i = []) (empty : ∀ i, i ≠ Fin.succ 0 → S.R i = []) :
    let r := intervalCounterPorts.trans (Fin.succEmb _)
    let init := (intervalHeaders r).seq (moveR (r 1) 0 (fun _ => bitSymbol false))
    let prepare := init.seq (embProg Fin.succ (Empty.elim : Empty → P) intervalMarkers)
    let split := embProg Fin.succ (Empty.elim : Empty → P)
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    let data := fun (j : Fin 142080) (i : Fin m) => x (finProdFinEquiv (i,j))
    ∃ z F t, z.user = u.user ∧ t ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+24 ∧
      Exec body (prepare.seq split) (mk u S) t (mk z F) ∧
      RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (S.R (Fin.succ 0))) data)
        (embStk Fin.succ F).L (embStk Fin.succ F).R ∧
      HelperFan (withHelperPort (intervalOwners 142080)) (Fin.lastCases (fun _ => 0) data) F := by
  intro r init prepare split data
  obtain ⟨v,D,k,user,time,prep,hl,hr,ready⟩ := intervalPrepareHelper_exec (m := m) body u S (by rw [source,List.length_ofFn]) left empty
  let word := fun i => SparseRoleCircuit.encode (a := prime) (x i)
  let rows := fun (i : Fin m) (j : Fin 142080) => [word (finProdFinEquiv (i,j))]
  let bs := FlatCoordinateSchedule.bits 1
  let gs := FlatCoordinateSchedule.bits m
  have divide := CyclicRowNormalized.split_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    rows 1 (fun _ _ => rfl) bs gs (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
  obtain ⟨sx,px⟩ := singletonRows word
  change CyclicRowSplit.sourceWord rows = _ at sx
  change ∀ j, CyclicRowSplit.roleWord rows j = _ at px
  simp only [sx,px] at divide
  rw [source] at ready
  obtain ⟨w,E,_,rfl,rep,same,_,_,_,t,paid,run⟩ := foreign_exec (P := Empty) (body := Empty.elim)
    (liftQ _ capacity) (HoareTime.liftQ capacity divide) (embDn Fin.succ v) _ _ rfl ready
  obtain ⟨z,F,placed,_,zu,view,off⟩ := exec_emb (body' := body) (ι := Empty.elim) (Fin.succ_injective _)
    (fun f => f.elim) run v rfl D rfl
  have keep := off 0 (fun i => Fin.succ_ne_zero i)
  have owners : RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (S.R (Fin.succ 0))) data)
      (embStk Fin.succ F).L (embStk Fin.succ F).R := by rw [view,source]; exact rep
  refine ⟨z,F,_,zu.trans (same.trans user),?_,Exec.seq prep placed,owners,
    withHelperPort_ready _ _ _ (intervalOwners_ready _ _ _ owners) (keep.1.trans hl) (keep.2.trans hr)⟩
  have bound := CyclicRowNormalized.cost_linear 1 bs gs (by decide : 0 < 142080) positive (by decide)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  rw [Nat.mul_one] at bound
  have scale := Nat.mul_le_mul_right (intervalSplitTapes+5) bound
  change t ≤ CyclicRowNormalized.cost 142080 m 1 bs gs*(intervalSplitTapes+5)+6 at paid
  dsimp only [intervalSplitTapes] at *
  omega

/-- Split the serialized payload directly into the live fan consumed by the
child owner copy. The source index is the packed position followed by its owner. -/
theorem splitChildInput_exec {P U : Type} {Q V : ℕ}
    (body : P → Pr P (intervalSplitTapes+1) Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < V) (x : Fin (V*142080) → ZMod 2)
    (u : HS (intervalSplitTapes+1) Q prime U) (S : Stacks (intervalSplitTapes+1) prime)
    (source : S.R (Fin.succ 0) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)))
    (left : ∀ i, S.L i = []) (empty : ∀ i, i ≠ Fin.succ 0 → S.R i = []) :
    let fan := (intervalOwners 142080).trans (Fin.succEmb _)
    let r := intervalCounterPorts.trans (Fin.succEmb _)
    let init := (intervalHeaders r).seq (moveR (r 1) 0 (fun _ => bitSymbol false))
    let prepare := init.seq (embProg Fin.succ (Empty.elim : Empty → P) intervalMarkers)
    let split := embProg Fin.succ (Empty.elim : Empty → P)
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∃ z F t, z.user = u.user ∧ t ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 ∧
      Exec body (prepare.seq split) (mk u S) t (mk z F) ∧
      HelperFan fan (fun row position => x (finProdFinEquiv (position,row))) F := by
  intro fan r init prepare split
  obtain ⟨z,F,t,user,cost,run,owners,_⟩ := intervalPackedInput_exec body capacity positive x u S source left empty
  exact ⟨z,F,t,user,cost,run,intervalOwners_ready _ _ _ owners⟩


/-- Lay out the splitter on the parent's row and counter ports. The extra
helper stays at port zero on both sides. Only the source and the two inner
counters come from the three saved ports. -/
def ownerSplitBank {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) : Fin ((((1+c)+2)+2)+1) ↪ Fin (T+1) where
  toFun := Fin.cases 0 (fun j => (returnedMergeBank saved fan apart j).succ)
  inj' := by
    intro i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [Fin.succ_inj,(returnedMergeBank saved fan apart).injective.eq_iff] <;>
      intro h <;> exact False.elim (Fin.succ_ne_zero _ h.symm)

theorem ownerSplitBank_succ {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (k : Fin (((1+c)+2)+2)) :
    ownerSplitBank saved fan apart k.succ = (returnedMergeBank saved fan apart k).succ := rfl

theorem ownerSplitBank_fan {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) :
    (withHelperPort (intervalOwners c)).trans (ownerSplitBank saved fan apart) = withHelperPort fan := by
  have rows (i) := DFunLike.congr_fun (returnedMergeBank_owners saved fan apart) i
  apply Function.Embedding.ext
  intro i
  induction i using Fin.addCases with
  | left j =>
    induction j using Fin.lastCases with
    | last => simp [withHelperPort,ownerSplitBank]
    | cast j => simp only [Function.Embedding.trans_apply,withHelperPort,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.lastCases_castSucc]; exact congrArg Fin.succ (rows (j.castAdd 2))
  | right j => simp only [Function.Embedding.trans_apply,withHelperPort,Function.Embedding.coeFn_mk,Fin.addCases_right]; exact congrArg Fin.succ (rows (j.natAdd c))

theorem ownerSplitBank_source {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) :
    ownerSplitBank saved fan apart (Fin.succ 0) = (saved 0).succ := by
  exact congrArg Fin.succ (returnedMergeBank_target saved fan apart)

/-- Split the source directly on the caller's chosen owner tapes. The child
starts with all rows, its zero helper, and its two volume controls. Tapes
outside the placement, including a parked parent archive, are preserved. -/
theorem placedChildInput_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ program : Pr P T Q prime U, ∀ (m : ℕ), 0 < m → ∀ (x : Fin (m*142080) → ZMod 2)
      (u : HS T Q prime U) (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      ∃ z F t, Exec body program (mk u S) t (mk z F) ∧ z.user = u.user ∧
        t ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+24 ∧
        RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (x i)))
          (fun row i => x (finProdFinEquiv (i,row))))
          (embStk Fin.succ (embStk bank F)).L (embStk Fin.succ (embStk bank F)).R ∧
        HelperFan ((withHelperPort (intervalOwners 142080)).trans bank)
          (Fin.lastCases (fun _ => 0) (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let r := intervalCounterPorts.trans (Fin.succEmb _)
  let init : Pr Empty _ Q prime U := (intervalHeaders r).seq (moveR (r 1) 0 (fun _ => bitSymbol false))
  let prepare := init.seq (embProg Fin.succ (Empty.elim : Empty → Empty) intervalMarkers)
  let split : Pr Empty _ Q prime U := embProg Fin.succ (Empty.elim : Empty → Empty)
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
  refine ⟨embProg bank Empty.elim (prepare.seq split),?_⟩
  intro m positive x u S source left empty
  obtain ⟨z,F,t,user,paid,run,splitRows,rows⟩ := intervalPackedInput_exec (P := Empty) Empty.elim capacity
    positive x (embDn bank u) (embStk bank S) source left empty
  obtain ⟨v,D,placed,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun f => nomatch f) run u rfl S rfl
  rw [← view] at rows splitRows
  change RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (S.R (bank (Fin.succ 0)))) _) _ _ at splitRows
  rw [source] at splitRows
  exact ⟨v,D,t,placed,same.trans user,paid,splitRows,rows,frame⟩

/-- Execute the split on the parked row bank and hand the represented child
directly to that same fan, preserving every off-bank stack. -/
theorem parkedChildInput_exec {P U : Type} {T Q : ℕ} (body : P → Pr P (T+1) Q prime U)
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let bank := ownerSplitBank saved fan apart
    ∃ program : Pr P (T+1) Q prime U, ∀ (m : ℕ), 0 < m → ∀ (x : Fin (m*142080) → ZMod 2)
      (u : HS (T+1) Q prime U) (S : Stacks (T+1) prime),
      S.R (saved 0).succ = List.ofFn (fun i => SparseRoleCircuit.encode (x i)) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      ∃ z F t, Exec body program (mk u S) t (mk z F) ∧ z.user = u.user ∧
        t ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+24 ∧
        RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (x i)))
          (fun row i => x (finProdFinEquiv (i,row))))
          (embStk Fin.succ (embStk bank F)).L (embStk Fin.succ (embStk bank F)).R ∧
        HelperFan (withHelperPort fan) (Fin.lastCases (fun _ => 0)
          (fun row i => x (finProdFinEquiv (i,row)))) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  simpa only [ownerSplitBank_source,ownerSplitBank_fan] using
    placedChildInput_exec body (ownerSplitBank saved fan apart) capacity

/-- Forget the child's temporary helper and read its output on the merge
ports in place. This works for any owner count. -/
theorem parkedMergeRows {c T m : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (y : Fin (c+1) → Fin m → ZMod 2)
    (F : Stacks (T+1) prime) (out : HelperFan (withHelperPort fan) y F) :
    let merge := (returnedMergeBank saved fan apart).trans (Fin.succEmb T)
    HelperFan ((intervalOwners c).trans merge) (fun j => y j.castSucc) F := by
  intro merge
  change HelperFan (((intervalOwners c).trans (returnedMergeBank saved fan apart)).trans (Fin.succEmb T)) _ F
  rw [returnedMergeBank_owners]
  exact withHelperPort_return fan y F out

private theorem mergeOutside {c T : ℕ} (saved : Fin 3 ↪ Fin T) (fan : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ fan j) (j : Fin (T+1))
    (off : ∀ k, ownerSplitBank saved fan apart k ≠ j) :
    ∀ k, ((returnedMergeBank saved fan apart).trans (Fin.succEmb T)) k ≠ j := by
  intro k
  exact off k.succ

/-- Merge on the parent's reused ports after the child restores the source
and the two inner counters. The merge program is fixed across row lengths. -/
theorem parkedChildMerge_exec {P U : Type} {T Q : ℕ} (body : P → Pr P (T+1) Q prime U)
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let bank := ownerSplitBank saved fan apart
    let merge := (returnedMergeBank saved fan apart).trans (Fin.succEmb T)
    ∃ program : Pr P (T+1) Q prime U, ∀ (m : ℕ), 0 < m →
    ∀ (dst : ℤ → Fin (prime+4)) (data : Fin 142080 → Fin m → ZMod 2)
      (y : Fin (142080+1) → Fin m → ZMod 2) (D E : Stacks (T+1) prime) (u : HS (T+1) Q prime U),
      let before := embStk Fin.succ (embStk bank D)
      let word := fun k : Fin (m*142080) => let p := finProdFinEquiv.symm k
                                           SparseRoleCircuit.encode (a := prime) (y p.2.castSucc p.1)
      RepT (intervalOwnerBank dst data) before.L before.R →
      HelperFan (withHelperPort fan) y E →
      (∀ j, E.L (saved j).succ = D.L (saved j).succ ∧ E.R (saved j).succ = D.R (saved j).succ) →
      ∃ z F n, Exec body program (mk u E) n (mk z F) ∧ n ≤ 149*(m*142080)*(intervalSplitTapes+5)+6 ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord dst 0 (List.ofFn word)) (fun j => y j.castSucc))
          (embStk merge F).L (embStk merge F).R ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = E.L j ∧ F.R j = E.R j := by
  intro bank merge
  refine ⟨embProg merge Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity)),?_⟩
  intro m pos dst data y D E u before word repr returned preserved
  have keep (k : Fin intervalSplitTapes) (j : Fin 3) (eq : returnedMergeBank saved fan apart k = saved j) :
      E.L (merge k) = before.L k ∧ E.R (merge k) = before.R k := by
    change E.L ((returnedMergeBank saved fan apart k).succ) = D.L ((returnedMergeBank saved fan apart k).succ) ∧
      E.R ((returnedMergeBank saved fan apart k).succ) = D.R ((returnedMergeBank saved fan apart k).succ)
    rw [eq]
    exact preserved j
  obtain ⟨z,F,n,run,cost,user,out,_,frame,_⟩ := placedMergeReturnedOwners_exec body merge capacity pos dst data
    (fun j => y j.castSucc) before u E repr (parkedMergeRows saved fan apart y E returned)
    (keep 0 0 (returnedMergeBank_target saved fan apart))
    (fun j => keep _ j.succ (returnedMergeBank_inner saved fan apart j))
  refine ⟨z,F,n,run,cost,user,out,?_⟩
  intro j off
  exact frame j (mergeOutside saved fan apart j off)

private theorem withHelperPort_avoids {c T : ℕ} (fan : Fin (c+2) ↪ Fin T) (j : Fin T)
    (away : ∀ i, fan i ≠ j) (k : Fin ((c+1)+2)) : withHelperPort fan k ≠ j.succ := by
  induction k using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last => simpa [withHelperPort] using (Fin.succ_ne_zero j).symm
    | cast i => simpa [withHelperPort] using away (i.castAdd 2)
  | right i => simpa [withHelperPort] using away (i.natAdd c)

/-- A child on the owner fan cannot touch the saved split source or counters.
Embedding its actual call also supplies the caller's off-bank frame. -/
theorem runOnParkedFan {c T Q m : ℕ} {P U : Type} (saved : Fin 3 ↪ Fin T)
    (fan : Fin (c+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (body : P → Pr P ((c+1)+2) Q prime U) (call : Pr P ((c+1)+2) Q prime U)
    (x y : Fin (c+1) → Fin m → ZMod 2) (price : ℕ)
    (run : ∀ u S, HelperFan (Function.Embedding.refl _) x S →
      ∃ z F t, Exec body call (mk u S) t (mk z F) ∧ t ≤ price ∧ z.user = u.user ∧
        HelperFan (Function.Embedding.refl _) y F) :
    let ports := withHelperPort fan
    ∀ v D, HelperFan ports x D →
      ∃ z F t, Exec (fun f => embProg ports id (body f)) (embProg ports id call) (mk v D) t (mk z F) ∧
        t ≤ price ∧ z.user = v.user ∧ HelperFan ports y F ∧
        (∀ j, F.L (saved j).succ = D.L (saved j).succ ∧ F.R (saved j).succ = D.R (saved j).succ) ∧
        ∀ j, (∀ k, ownerSplitBank saved fan apart k ≠ j) → F.L j = D.L j ∧ F.R j = D.R j := by
  intro ports v D rep
  obtain ⟨u,E,t,exec,paid,user,out⟩ := run (embDn ports v) (embStk ports D) rep
  obtain ⟨z,F,placed,_,same,view,frame⟩ := exec_emb (ι := id) (body' := fun f => embProg ports id (body f))
    ports.injective (fun _ => rfl) exec v rfl D rfl
  rw [← view] at out
  refine ⟨z,F,t,placed,paid,same.trans user,out,fun j => frame _ (withHelperPort_avoids fan _ (fun i => (apart j i).symm)),?_⟩
  intro j off
  apply frame
  intro k
  have eq := DFunLike.congr_fun (ownerSplitBank_fan saved fan apart) k
  exact eq ▸ off (withHelperPort (intervalOwners c) k)

private theorem roundTripCost (a b c m t price : ℕ)
    (split : a ≤ (149*t+5)*m+24) (child : b ≤ price) (merge : c ≤ 149*m*t+6) :
    a+(b+c) ≤ price+(298*t+5)*m+30 := by
  calc
    _ ≤ _ := Nat.add_le_add split (Nat.add_le_add child merge)
    _ = _ := by ring

/-- The parked split and merge surround a child on the same owner fan. Only
three saved tapes must survive the child, in addition to the caller's frame. -/
theorem parkedChildRoundTrip {P U : Type} {T Q : ℕ} (body : P → Pr P (T+1) Q prime U)
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let bank := ownerSplitBank saved fan apart
    let merge := (returnedMergeBank saved fan apart).trans (Fin.succEmb T)
    ∃ wrap : Pr P (T+1) Q prime U → Pr P (T+1) Q prime U,
    ∀ (call : Pr P (T+1) Q prime U) (price m : ℕ), 0 < m →
    ∀ (x : Fin (m*142080) → ZMod 2) (y : Fin (142080+1) → Fin m → ZMod 2)
      (u : HS (T+1) Q prime U) (S : Stacks (T+1) prime),
      let src := List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)
      let dst := putWord (fun _ => blank) 0 src
      let data := fun (row : Fin 142080) (i : Fin m) => x (finProdFinEquiv (i,row))
      let word := fun k : Fin (m*142080) => let p := finProdFinEquiv.symm k
                                           SparseRoleCircuit.encode (a := prime) (y p.2.castSucc p.1)
      S.R (saved 0).succ = src → (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (∀ v D, HelperFan (withHelperPort fan) (Fin.lastCases (fun _ => 0) data) D →
        (∀ j, (∀ k, bank k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F t, Exec body call (mk v D) t (mk z F) ∧ t ≤ price ∧ z.user = v.user ∧
          HelperFan (withHelperPort fan) y F ∧
          (∀ j, F.L (saved j).succ = D.L (saved j).succ ∧ F.R (saved j).succ = D.R (saved j).succ) ∧
          ∀ j, (∀ k, bank k ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) →
      ∃ z F t, Exec body (wrap call) (mk u S) t (mk z F) ∧
        t ≤ price+(298*(intervalSplitTapes+5)+5)*(m*142080)+30 ∧ z.user = u.user ∧
        RepT (intervalOwnerBank (putWord dst 0 (List.ofFn word)) (fun j => y j.castSucc))
          (embStk merge F).L (embStk merge F).R ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank merge
  obtain ⟨split,run⟩ := parkedChildInput_exec body saved fan apart capacity
  obtain ⟨finish,back⟩ := parkedChildMerge_exec body saved fan apart capacity
  refine ⟨fun call => split.seq (call.seq finish),?_⟩
  intro call price m pos x y u S src dst data word source left empty child
  obtain ⟨v,D,a,splitRun,vu,aCost,repr,owners,frame⟩ := run m pos x u S source left empty
  obtain ⟨w,E,b,childRun,bCost,wv,returned,preserved,childFrame⟩ := child v D owners frame
  obtain ⟨z,F,c,mergeRun,cCost,zw,out,mergeFrame⟩ := back m pos dst data y D E w repr returned preserved
  refine ⟨z,F,_,splitRun.seq (childRun.seq mergeRun),roundTripCost _ _ _ _ _ _ aCost bCost cCost,
    zw.trans (wv.trans vu),out,?_⟩
  intro j off
  exact ⟨(mergeFrame j off).1.trans ((childFrame j off).1.trans (frame j off).1),
    (mergeFrame j off).2.trans ((childFrame j off).2.trans (frame j off).2)⟩

theorem intervalOwnerPayload {T c m V : ℕ} (bank : Fin (((1+c)+2)+2) ↪ Fin T)
    (S : Stacks T prime) (word : Fin V → ZMod 2) (data : Fin c → Fin m → ZMod 2)
    (ready : RepT (intervalOwnerBank (putWord (fun _ => blank) 0
      (List.ofFn fun k => SparseRoleCircuit.encode (word k))) data) (embStk bank S).L (embStk bank S).R) :
    Cover.Fallback.RecordPayload (bank 0) (fun _ => blank) 0 word S := by
  intro z
  rw [encodedOwnerCell]
  have zero : ((((0 : Fin 1).castAdd c).castAdd 2).castAdd 2) = 0 := Fin.ext rfl
  rw [← zero]
  simpa only [intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
    CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply] using
    (ready ((((0 : Fin 1).castAdd c).castAdd 2).castAdd 2) z).symm

theorem castPayload {T m n : ℕ} (size : m = n) (port : Fin T) (S : Stacks T prime)
    (word : Fin n → ZMod 2) :
    Cover.Fallback.RecordPayload port (fun _ => blank) 0 (fun i => word (i.cast size)) S →
      Cover.Fallback.RecordPayload port (fun _ => blank) 0 word S := by
  subst n
  exact id

open RecursiveInterchangeLayout in
/-- A row transpose on the parked child ports executes the full wide transpose
on the serialized source tape. The helper and the archive are outside the output word. -/
theorem parkedMoveTranspose {P U : Type} {T Q : ℕ} (body : P → Pr P (T+1) Q prime U)
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let bank := ownerSplitBank saved fan apart
    let merge := (returnedMergeBank saved fan apart).trans (Fin.succEmb T)
    ∃ wrap : P → Pr P (T+1) Q prime U,
    ∀ (entry : P) (price : ℕ) (lane : Descriptor),
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (helper : Fin m → ZMod 2),
      let src := List.ofFn fun i : Fin (m*142080) => SparseRoleCircuit.encode (a := prime) (x (i.cast size))
      let data := fun (r : Fin 142080) (i : Fin m) => x ((finProdFinEquiv (i,r)).cast size)
      let rows := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let output := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x
      ∀ (u : HS (T+1) Q prime U) (S : Stacks (T+1) prime), 0 < m →
      S.R (saved 0).succ = src → (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (∀ v D, HelperFan (withHelperPort fan) (Fin.lastCases (fun _ => 0) data) D →
        (∀ j, (∀ k, bank k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F n, Exec body (body entry) (mk v D) n (mk z F) ∧ n ≤ price ∧ z.user = v.user ∧
          HelperFan (withHelperPort fan) (Fin.lastCases helper rows) F ∧
          (∀ j, F.L (saved j).succ = D.L (saved j).succ ∧ F.R (saved j).succ = D.R (saved j).succ) ∧
          ∀ j, (∀ k, bank k ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) →
      ∃ z F t, Exec body (wrap entry) (mk u S) t (mk z F) ∧
        t ≤ price+(298*(intervalSplitTapes+5)+37)*volume prime wide ∧ z.user = u.user ∧
        Cover.Fallback.RecordPayload (saved 0).succ (fun _ => blank) 0 output F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank merge
  obtain ⟨wrap,run⟩ := parkedChildRoundTrip body saved fan apart capacity
  refine ⟨fun entry => wrap (.call entry),?_⟩
  intro entry price lane m wide size x helper src data rows output u S positive source left empty child
  let y : Fin (142080+1) → Fin m → ZMod 2 := Fin.lastCases helper rows
  obtain ⟨z,F,t,exec,paid,user,rep,frame⟩ := run (.call entry) (price+2) m positive (fun i => x (i.cast size)) y u S source left empty (by
      intro v D owners off
      obtain ⟨z,F,n,exec,paid,user,out,keep,frame⟩ := child v D owners off
      exact ⟨z,F,n+2,Exec.call exec,Nat.add_le_add_right paid 2,user,out,keep,frame⟩)
  refine ⟨z,F,t,exec,?_,user,?_,frame⟩
  · rw [← size]
    have live : 0 < m*142080 := Nat.mul_pos positive (by decide)
    apply paid.trans
    have absorb (a n : ℕ) (pos : 0 < n) :
        price+2+(a+5)*n+30 ≤ price+(a+37)*n := by
      simp only [Nat.add_mul]
      omega
    exact absorb _ _ live
  · have read (k : Fin (m*142080)) : rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 = output (k.cast size) := by
      obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
      simpa only [Equiv.symm_apply_apply] using (transpose_trailingRows lane 142080 x i j).symm
    simp only [y,Fin.lastCases_castSucc,read] at rep
    rw [FlatControlledShiftArray.overwrite _ _ _ _ (by simp)] at rep
    have payload := castPayload size (merge 0) F output (intervalOwnerPayload merge F _ _ rep)
    change Cover.Fallback.RecordPayload (returnedMergeBank saved fan apart 0).succ _ _ _ _ at payload
    rwa [returnedMergeBank_target] at payload

end IntegerMultBounds.MathlibTM2.M6.BitNode
