module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStage
public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

private theorem scheduledBanksWithCharge {I : Type} [Fintype I] {k : ℕ}
    (tapes : I → ℕ) (ports : ∀ i, Fin k ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin k ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {X P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U) (code : ∀ i, Pr P (tapes i) Q prime U)
      (weight : List (Fin (prime+4)) → List (Fin (prime+4)) → ℕ)
      (represented : X → Stacks k prime → Prop) (effect : I → X → X → Prop)
      (cost : I → ℕ) (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks k prime),
    (∀ i x u S, represented x (embStk (ports i) S) →
      (∀ l, (∀ j, ports i j ≠ l) → S.L l = (initial i).L l ∧ S.R l = (initial i).R l) →
      ∃ v D t y, Exec (body i) (code i) (mk u S) t (mk v D) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge weight js D ≤ tapeCharge weight js S+cost i) ∧ v.user = u.user ∧
        represented y (embStk (ports i) D) ∧ effect i x y) →
    let table := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ (order : List I), order.Nodup → ∀ x u S, represented x (embStk fan S) →
      (∀ l, (∀ j, fan j ≠ l) → S.L l = prepared.L l ∧ S.R l = prepared.R l) →
      ∃ v D t y, Exec table (Prog.seqList (order.map placed)) (mk u S) t (mk v D) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge weight js D ≤ tapeCharge weight js S+(order.map cost).sum+1) ∧ v.user = u.user ∧ represented y (embStk fan D) ∧
        order.foldr (fun i next a => ∃ b, effect i a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,prepare,off⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro X P U Q body code weight represented effect cost initial shared run table placed
  obtain ⟨prepared,owners,stock⟩ := prepare shared initial
  refine ⟨prepared,owners,?_⟩
  let fresh := fun i (S : Stacks T prime) => ∀ l, (∀ j, ports i j ≠ l) →
    S.L (bank i l) = (initial i).L l ∧ S.R (bank i l) = (initial i).R l
  have project (i) (S : Stacks T prime) : embStk (ports i) (embStk (bank i) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,selected]
  intro order unique x u S ready saved
  have frames : ∀ i ∈ order, fresh i S := by
    intro i _ l privateSlot
    obtain ⟨a,b⟩ := saved _ (off i l privateSlot).1
    obtain ⟨c,d⟩ := stock i l privateSlot
    exact ⟨a.trans c,b.trans d⟩
  clear saved
  induction order generalizing x S u with
  | nil => exact ⟨u,S,1,x,Exec.act .done _,by intro js _; simp; omega,rfl,ready,rfl⟩
  | cons i rest ih =>
    obtain ⟨v,D,t,y,exec,time,user,mid,act⟩ := run i x (embDn (bank i) u) (embStk (bank i) S)
      ((project i S) ▸ ready) (frames i List.mem_cons_self)
    obtain ⟨z,F,first,_,same,view,untouched⟩ := exec_emb (ι := Prod.mk i) (body' := table)
      (bank i).injective (fun _ => rfl) exec u rfl S rfl
    rw [← view,project] at mid
    obtain ⟨v',D',t',y',last,bill,final,out,acts⟩ := ih (List.nodup_cons.mp unique).2 y z F mid (by
      intro j member l privateSlot
      have ne : i ≠ j := fun eq => (List.nodup_cons.mp unique).1 (eq ▸ member)
      obtain ⟨a,b⟩ := untouched _ ((off j l privateSlot).2 i ne)
      obtain ⟨c,d⟩ := frames j (List.mem_cons_of_mem _ member) l privateSlot
      exact ⟨a.trans c,b.trans d⟩)
    refine ⟨v',D',_,y',Exec.seq first last,?_,final.trans (same.trans user),out,y,act,acts⟩
    intro js unique
    rw [← view] at time
    have head := placedCleanup_cost_le (bank i) S F weight t (cost i) untouched time js unique
    have tail := bill js unique
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Execute all 160 invocations on a shared owner bank. The change in cleanup
cost telescopes across runs and the child budgets form one directory interval. -/
theorem packedStageRunsWithCharge [M8.Machine.Net] (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q w B W : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U)
      (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*W))
    let children := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
    (∀ i (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports i) x S →
      (∀ j, (∀ h, ports i h ≠ j) → S.L j = (initial i).L j ∧ S.R j = (initial i).R j) →
      ∃ z F t y, Exec (body i) (code i) (mk u S) t (mk z F) ∧ (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(localCost i + children i)) ∧
        z.user = u.user ∧ HelperFan (ports i) y F ∧ packedStageEffect n i w B W x y) →
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
      ∃ z F t y, Exec table (Prog.seqList (stageRuns.map placed)) (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(stageRuns.map localCost).sum +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1) ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        stageRuns.foldr (fun i next a => ∃ b, packedStageEffect n i w B W a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,build⟩ := scheduledBanksWithCharge tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro P U Q w B W body code localCost childTime initial shared V children run table placed
  let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (s : Stacks (142081+2) prime) =>
    RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) s.L s.R
  obtain ⟨prepared,owners,stage⟩ := build body code cleanupWeight ready (fun i => packedStageEffect n i w B W)
    (fun i => localCost i + children i) initial shared run
  refine ⟨prepared,owners,?_⟩
  intro x u S rep fresh
  obtain ⟨z,F,t,y,exec,paid,user,done,acts⟩ := stage stageRuns stageRuns_nodup x u S rep fresh
  refine ⟨z,F,t,y,exec,?_,user,done,acts⟩
  have sum (ls : List (Fin 32 × Fin 5)) :
      (ls.map (fun i => localCost i + children i)).sum = (ls.map localCost).sum + (ls.map children).sum := by
    induction ls with
    | nil => rfl
    | cons i ls ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  intro js unique
  have bill := paid js unique
  rw [sum,show (stageRuns.map children).sum = _ from scheduledChildBill (fun _ => Geometry.Moves.localPaid)
    childTime stageRuns stageRuns_nodup (stageChildStart n)] at bill
  simpa only [Nat.add_assoc] using bill

/-- The fixed helper restoration program pays for its own tape growth,
independently of the procedures used for recursive sweep calls. -/
theorem parentSlotChangesWithCharge [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (changes : List (Fin 142081 × Option (Fin 56) × Option (Fin 56)))
    (fan : Fin (142081+2) ↪ Fin T) (hdr : Fin 6 → Fin T) (regs : Fin 35 ↪ Fin T)
    (capacity : columnCapacity ≤ Q) (body : P → Pr P ((T+273)+LeafCore.small) Q prime U) :
    let bank := Fin.castAddEmb LeafCore.small (n := T+273)
    let caller := (Fin.castAddEmb 273 (n := T)).trans bank
    ∃ code, ∃ C : ℝ, ∀ (row : Descriptor) (w V : ℕ), row.Positive →
      let W := row.beforeRows*row.rows*row.between*row.afterD
      let M := prime^(w+1)
      V = M^16*(row.beforeH*(M^112*W)) →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      S.R (caller (regs 2)) = binSyms M.size M → S.R (caller (regs 28)) = binSyms 1 1 →
      (S.R (caller (regs 33))).length = w →
      (∀ i, S.R (caller (hdr i)) = (Routines.hdr row i).map bitSymbol) →
      (∀ j : Fin 273, S.L (bank (j.natAdd T)) = [] ∧ S.R (bank (j.natAdd T)) = []) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd (T+273)) = [] ∧ S.R (j.natAdd (T+273)) = []) →
      HelperFan (fan.trans caller) data S →
      ∃ z F t a, z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+⌈C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊) ∧
        HelperFan (fan.trans caller) a F ∧ HelperLabelTrace (w+1) row.beforeH W changes data a ∧
        ∀ j : Fin T, (∀ o : Fin 142081, j ≠ fan (o.castAdd 2)) →
          F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j) := by
  intro bank caller
  obtain ⟨code,C,run⟩ := parentSlotChanges_exec changes fan hdr regs capacity (P := Empty) (U := U) Empty.elim
  let push := Fast.Main.mnProgPush code
  let factor := 1+6*push
  refine ⟨embProg id Empty.elim code,(factor : ℝ)*C,?_⟩
  intro row w V pos W M size data u S base unit clock headers free scratch owners
  obtain ⟨z,F,t,a,user,exec,paid,out,trace,keep⟩ := run row w V pos size data u S base unit clock headers free scratch owners
  have project (v : HS ((T+273)+LeafCore.small) Q prime U) : embDn id v = v := by
    cases v with
    | mk flag sym st scan nxt user => cases nxt <;> rfl
  obtain ⟨y,D,placed,state,_,view,_⟩ := exec_emb (e := id) (ι := Empty.elim) (body' := body)
    Function.injective_id (fun f => nomatch f) exec u (project u) S rfl
  rw [project] at state
  change D = F at view
  subst y D
  refine ⟨z,F,t,a,user,placed,?_,out,trace,keep⟩
  intro js unique
  have growth := recordCleanup_cost_le js unique exec (c := push) le_rfl (fun f => nomatch f)
  change tapeCharge cleanupWeight js F+1 ≤ tapeCharge cleanupWeight js S+1+6*(push*t) at growth
  have scaled := mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg (α := ℝ) factor)
  have bill : factor*t ≤ ⌈(factor : ℝ)*C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ := by
    apply_mod_cast (show ((factor*t : ℕ) : ℝ) ≤ (⌈(factor : ℝ)*C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ : ℝ) from
      (by simpa only [Nat.cast_mul,mul_assoc] using scaled.trans (Nat.le_ceil _)))
  have expand : factor*t = t+6*(push*t) := by simp only [factor,Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  rw [expand] at bill
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
