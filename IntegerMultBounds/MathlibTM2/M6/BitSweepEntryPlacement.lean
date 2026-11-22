module

public import IntegerMultBounds.MathlibTM2.M6.BitCorrectedNodeStage
public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitPlacement

/-! Pad compact chart outputs directly into the recursive worker's input bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)

/-- The forward conversion writes its owners directly to the entry chart's
payload slots. Its work registers stay in the private sweep register file. -/
noncomputable def forwardBank {t c : ℕ} (slots : Fin 142081 ↪ Fin c) : Fin tapes ↪ Fin (size t c) :=
  let e := Fintype.equivFin File
  let f : File → Register t c := fun j => match j with
    | .owner i => .chart (slots i)
    | j => .sweep (e j)
  e.symm.toEmbedding.trans (place f (by
    intro i j h
    cases i <;> cases j <;> simp_all [f,slots.injective.eq_iff]))

theorem forwardBank_owner {t c : ℕ} (slots : Fin 142081 ↪ Fin c) (i : Fin 142081) :
    forwardBank (t := t) slots (owners i) = chart t c (slots i) := by
  let e := Fintype.equivFin File
  change (Fintype.equivFin (Register t c)) (match e.symm (e (SweepFile.Register.owner i)) with
    | .owner j => .chart (slots j)
    | j => .sweep (e j)) = _
  rw [e.symm_apply_apply]
  rfl

def padReg {t c : ℕ} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (i : Fin 142081) (j : Fin 12) : Register t c :=
  if j = 0 then .chart (slots i) else if j = 1 then .recursive (fan (i.castAdd 2)) else .crop j

noncomputable def padPort {t c : ℕ} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (i : Fin 142081) := place (padReg fan slots i) (by
  intro j k h
  unfold padReg at h
  split_ifs at h <;> simp_all)

private theorem padReg_apart {t c} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (inj : Function.Injective slots) (i k : Fin 142081) (ne : i ≠ k) (j : Fin 12) :
    padReg fan slots i j ≠ padReg fan slots k 0 ∧ padReg fan slots i j ≠ padReg fan slots k 1 := by
  simp [padReg]
  split_ifs <;> simp [fan.injective.eq_iff,inj.eq_iff,ne]
  exact (Fin.castAddEmb 2).injective.ne ne

theorem placedEntryPad_exec {P U : Type} {w B K t c Q : ℕ} (fan : Fin (142081+2) ↪ Fin t)
    (slots : Fin 142081 ↪ Fin c) (body : P → Pr P (size t c) Q prime U)
    (fits : 215 ≤ Q) (hb : 0 < B) (hk : 0 < K) :
    let pad := padPort fan slots
    let dst := fan.trans (recursive t c)
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    ∃ code, ∀ x u S, StageControls dst (A*(B*N*K)) S → CropCounters (pad 0) (A*B) N K S →
      RepT (phaseOwners x) (embStk (slots.trans (chart t c)) S).L (embStk (slots.trans (chart t c)) S).R →
      (∀ (i : Fin 142081) z, readAt blank (S.L (dst (i.castAdd 2))) (S.R (dst (i.castAdd 2))) z = blank) →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧ l ≤ 142081*(7021*(A*B)*(N*K)+6)+1 ∧
        z.user = u.user ∧ HelperFan dst (singleLabelBank (B := B) (K := K) (firstRowLabel w) x) F ∧
        ∀ j, (∀ i : Fin 142081, fan (i.castAdd 2) ≠ j) →
          F.L (recursive t c j) = S.L (recursive t c j) ∧ F.R (recursive t c j) = S.R (recursive t c j) := by
  intro pad dst A N
  let e := Fintype.equivFin (Register t c)
  have addr i j : pad i j = e (padReg fan slots i j) := rfl
  have off (i j h) (ne : fan (i.castAdd 2) ≠ j) : pad i h ≠ recursive t c j := by
    apply e.injective.ne
    change padReg _ _ _ _ ≠ .recursive _
    unfold padReg; split_ifs <;> simp [ne]
  obtain ⟨code,run⟩ := padPlacedCorrection_exec (w := w) pad (by
    intro i k j h d; simp only [addr,padReg,h,d,ite_false]) (by
    intro i k ne j
    simp only [addr,ne_eq,e.injective.eq_iff]
    exact padReg_apart fan slots slots.injective i k ne j) fits body hb hk
  refine ⟨code,?_⟩
  intro x u S ctrl counters words blank
  obtain ⟨z,F,l,exec,paid,user,live,frame⟩ := run dst x u S (fun _ => rfl) (by
    intro j i h
    apply off
    exact fan.injective.ne (by intro eqn; have hv := congrArg Fin.val eqn; simp at hv; omega))
    ctrl counters words blank
  exact ⟨z,F,l,exec,paid,user,live,fun j hj => frame _ (fun i h => off i j h (hj i))⟩

/-- Execute the entry chart and pad its represented output directly into the
recursive fan. All recursive workspace outside the input words is preserved. -/
theorem placedEntryCorrection_exec {P U : Type} {w B W t Q : ℕ} (n : Fin 9)
    (parent : Fin 64 → ZMod (prime^w)) (units : ∀ i, IsUnit (parent i))
    (fan : Fin (142081+2) ↪ Fin t) (hb : 0 < B) (hw : 0 < W) (fits : 215 ≤ Q) :
    let M := prime^w
    let K := M^112*W
    let A := M^16
    let N := prime^(64*(w*64))
    ∀ (enter : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K)))),
    enter.states ≤ Q → ∀ body : P → Pr P (size t enter.tapes) Q prime U,
    let dst := fan.trans (recursive t enter.tapes)
    let src := (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes).trans (chart t enter.tapes)
    let pad := padPort fan enter.slots
    ∃ code, ∀ x u S, ChartPrivateReady enter (embStk (chart t enter.tapes) S) →
      (∀ r, S.L (src (sweepRoleTape r)) = []) →
      (∀ r, S.R (src (sweepRoleTape r)) = List.ofFn fun i =>
        SparseRoleCircuit.encode (sweepArray parent units n x (sweepRoleTape r) i)) →
      WordAtZero (x (Fin.last 142080)) (S.L (src (Fin.last 142080))) (S.R (src (Fin.last 142080))) →
      StageControls dst (A*(B*N*K)) S → CropCounters (pad 0) (A*B) N K S →
      (∀ (i : Fin 142081) z, readAt blank (S.L (dst (i.castAdd 2))) (S.R (dst (i.castAdd 2))) z = blank) →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧
        l ≤ enter.cost*(enter.tapes+5)+6 + (142081*(7021*(A*B)*(N*K)+6)+1) ∧
        z.user = u.user ∧ HelperFan dst (singleLabelBank (B := B) (K := K) (firstRowLabel w) (enter.transform (sweepArray parent units n x))) F ∧
        ∀ j, (∀ i : Fin 142081, fan (i.castAdd 2) ≠ j) →
          F.L (recursive t enter.tapes j) = S.L (recursive t enter.tapes j) ∧
          F.R (recursive t enter.tapes j) = S.R (recursive t enter.tapes j) := by
  intro M K A N enter room body dst src pad
  let slots := (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes)
  obtain ⟨pack,run⟩ := placedEntryPad_exec (w := w) fan slots body fits hb (Nat.mul_pos
    (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hw)
  refine ⟨.seq (embProg (chart t enter.tapes) Empty.elim (foreign (liftQ enter.program room))) pack,?_⟩
  intro x u S ready left words extra controls counters empty
  obtain ⟨v,D,k,exec,paid,user,compact,off⟩ := correctionAfterSweep_exec parent units n enter
    (chart t enter.tapes) src (fun _ => rfl) room body x u S ready left words extra
  let e := Fintype.equivFin (Register t enter.tapes)
  have kept j := off (recursive t enter.tapes j) (fun i => e.injective.ne
    (show Register.chart i ≠ .recursive j by intro h; cases h))
  obtain ⟨z,F,l,packExec,bill,same,live,frame⟩ := run _ v D (by
    intro j h
    change _ = readAt blank (D.L (recursive t enter.tapes _)) (D.R (recursive t enter.tapes _)) _
    rw [(kept _).1,(kept _).2]; exact controls j h) (by
    intro j h d z
    have addr : pad 0 j = e (.crop j) := by
      change e (padReg _ _ _ _) = _; simp [padReg,h,d]
    have cell := off (pad 0 j) (fun i => by
      rw [addr]
      exact e.injective.ne (show Register.chart i ≠ .crop j by intro eqn; cases eqn))
    change _ = readAt blank (D.L (pad 0 j)) (D.R (pad 0 j)) _
    rw [cell.1,cell.2]; exact counters j h d z) compact (by
    intro i z
    change readAt blank (D.L (recursive t enter.tapes _)) (D.R (recursive t enter.tapes _)) _ = _
    rw [(kept _).1,(kept _).2]; exact empty i z)
  exact ⟨z,F,k+l,Exec.seq exec packExec,Nat.add_le_add paid bill,same.trans user,live,
    fun j h => ⟨((frame j h).1).trans (kept j).1,((frame j h).2).trans (kept j).2⟩⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
