module

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

end IntegerMultBounds.MathlibTM2.M6.BitNode
