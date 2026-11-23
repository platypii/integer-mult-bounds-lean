module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedInvocation
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

/-- A closed local program can run in any procedure table. Its fixed push bound
pays for the cleanup of any selected tapes in addition to elapsed time. -/
private theorem placeClosedWithCharge {P U : Type} {T Q : ℕ}
    (body : P → Pr P T Q prime U) (code : Pr Empty T Q prime U)
    {u z : HS T Q prime U} {S F : Stacks T prime} {t : ℕ}
    (exec : Exec Empty.elim code (mk u S) t (mk z F)) :
    Exec body (embProg id Empty.elim code) (mk u S) t (mk z F) ∧
    ∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤
      tapeCharge cleanupWeight js S+(1+6*Fast.Main.mnProgPush code)*t := by
  have project (v : HS T Q prime U) : embDn id v = v := by
    cases v with
    | mk flag sym st scan nxt user => cases nxt <;> rfl
  obtain ⟨y,D,placed,state,_,view,_⟩ := exec_emb (e := id) (ι := Empty.elim) (body' := body)
    Function.injective_id (fun f => nomatch f) exec u (project u) S rfl
  rw [project] at state
  change D = F at view
  subst y D
  refine ⟨placed,?_⟩
  intro js unique
  have growth := recordCleanup_cost_le js unique exec (c := Fast.Main.mnProgPush code) le_rfl (fun f => nomatch f)
  change tapeCharge cleanupWeight js F+1 ≤ tapeCharge cleanupWeight js S+1+6*(Fast.Main.mnProgPush code*t) at growth
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
  omega

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
  obtain ⟨placed,charge⟩ := placeClosedWithCharge body code exec
  refine ⟨z,F,t,a,user,placed,?_,out,trace,keep⟩
  intro js unique
  have scaled := mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg (α := ℝ) factor)
  have bill : factor*t ≤ ⌈(factor : ℝ)*C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ := by
    apply_mod_cast (show ((factor*t : ℕ) : ℝ) ≤ (⌈(factor : ℝ)*C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊ : ℝ) from
      (by simpa only [Nat.cast_mul,mul_assoc] using scaled.trans (Nat.le_ceil _)))
  exact (charge js unique).trans (Nat.add_le_add_left bill _)

open SweepFile in
/-- Transfer the returned owner words to the next program while charging cleanup once across both banks. -/
theorem runAfterPackedStageWithCharge {T N Q V D : ℕ} {P R U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (input : Fin (142081+2) ↪ Fin N) :
    let m := Exit.size 0 T
    ∃ bank : Fin N ↪ Fin (m+N), ∀ (left : P → Pr P m Q prime U) (right : R → Pr R N Q prime U) a b,
    let leftBank := Fin.castAdd N (n := m)
    let body := Sum.elim (fun g => embProg leftBank Sum.inl (left g)) (fun g => embProg bank Sum.inr (right g))
    ∀ u L seed v F t setup budget (x : Fin 142081 → Fin D → ZMod 2) (post : U → Stacks N prime → Prop),
      Exec left a (mk (embDn leftBank u) L) t (mk v F) →
      (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js L+setup) →
      ParentStageWords (fun i => Exit.sweep 0 T (owners i)) (fan.trans (Exit.chart 0 T)) V x F →
      (∀ w S, w.user = v.user → ParentStageWords (fun i => input (i.castAdd 2)) input V x S →
        (∀ j, (∀ i, input i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
        ∃ z G k, Exec right b (mk w S) k (mk z G) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+budget) ∧ post z.user G) →
      ∃ z G k, Exec body ((embProg leftBank Sum.inl a).seq (embProg bank Sum.inr b))
        (mk u (adjacentStageStacks L seed)) k (mk z G) ∧ (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js (adjacentStageStacks L seed)+(setup+budget)) ∧ post z.user (embStk bank G) := by
  intro m
  obtain ⟨bank,_,_,sequence⟩ := runAdjacentStagesWithCharge (A := prime) (P := P) (R := R) (U := U) (q := Q) (returnedFan fan) input
  refine ⟨bank,?_⟩
  intro left right a b leftBank body u L seed v F t setup budget x post exec paid words next
  obtain ⟨z,G,k,ran,paid,done,_⟩ := sequence left right a b u L seed v F t setup budget cleanupWeight post exec paid (by
    intro w S user shared privateTapes
    apply next w S user _ privateTapes
    constructor
    · intro i
      rw [(shared (i.castAdd 2)).1,returnedFan_owner]; exact words.left i
    · intro i
      rw [(shared (i.castAdd 2)).2,returnedFan_owner]; exact words.right i
    · intro j z
      rw [(shared (j.natAdd 142081)).1,(shared (j.natAdd 142081)).2]
      rw [returnedFan_counter]; exact words.controls j z)
  exact ⟨z,G,k,ran,paid,done⟩

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Charge helper-slot packing before the recursive call on the same owner words. -/
theorem scheduledSlotPackWithCharge [M8.Machine.Net] {P U : Type} {t q : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (pre : List (Fin 32 × Fin 5)) (bank : Fin ((rowSwapBlock.tapes+35)+142081) ↪ Fin t) (capacity : rowSwapBlock.states ≤ q)
    (body : P → Pr P t q prime U) :
    let owners := (Fin.natAddEmb (rowSwapBlock.tapes+35) (m := 142081)).trans bank
    let before := pre.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ code, ∃ (factor : ℕ) (C : ℝ), ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (v : HS t q prime U) (S : Stacks t prime) (data : Fin 142081 → Fin V → ZMod 2),
      embStk bank S = helperPackInput w W (embStk owners S) →
      RepT (phaseOwners data) (embStk owners S).L (embStk owners S).R →
      ∃ z F, ∃ time : ℕ, ∃ result : Fin 142081 → Fin V → ZMod 2,
        Exec body code (mk v S) time (mk z F) ∧ z.user = v.user ∧
        (∀ js : List _, js.Nodup → time+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+factor*⌈1+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊) ∧
        RepT (phaseOwners result) (embStk owners F).L (embStk owners F).R ∧
        (∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → result j = data j) ∧
        ∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro owners before
  obtain ⟨code,C,run⟩ := scheduledSlotPack_placed (P := Empty) (U := U) n p pre bank capacity Empty.elim
  refine ⟨embProg id Empty.elim code,1+6*Fast.Main.mnProgPush code,C,?_⟩
  intro w W live V v S data initial represented
  obtain ⟨z,F,t,result,exec,user,paid,out,off,idle,slots⟩ := run w W live v S data initial represented
  obtain ⟨placed,charge⟩ := placeClosedWithCharge body code exec
  refine ⟨z,F,t,result,placed,user,?_,out,off,idle,slots⟩
  intro js unique
  have price := Nat.ceil_le_ceil paid
  rw [Nat.ceil_natCast] at price
  exact (charge js unique).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ price) _)

/-- Pass the packed slots and untouched private tapes to the hosted call, paying its budget once. -/
theorem packThenInvokeWithCharge [M8.Machine.Net] {P U : Type} {t q : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (pre : List (Fin 32 × Fin 5)) (bank : Fin ((rowSwapBlock.tapes+35)+142081) ↪ Fin t) (capacity : rowSwapBlock.states ≤ q)
    (body : P → Pr P t q prime U) :
    let owners := (Fin.natAddEmb (rowSwapBlock.tapes+35) (m := 142081)).trans bank
    let before := pre.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ pack, ∃ (factor : ℕ) (C : ℝ), ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (v : HS t q prime U) (S : Stacks t prime) (data : Fin 142081 → Fin V → ZMod 2),
      ∀ (call : Pr P t q prime U) (price : ℕ) (post : U → Stacks t prime → Prop),
      embStk bank S = helperPackInput w W (embStk owners S) →
      RepT (phaseOwners data) (embStk owners S).L (embStk owners S).R →
      (∀ (u : HS t q prime U) (D : Stacks t prime) (result : Fin 142081 → Fin V → ZMod 2), u.user = v.user →
        RepT (phaseOwners result) (embStk owners D).L (embStk owners D).R →
        (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → result j = data j) →
        (∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j)) →
        ∃ z F k, Exec body call (mk u D) k (mk z F) ∧
          (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+price) ∧
          post z.user F) →
      ∃ z F t, Exec body (.seq pack call) (mk v S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          factor*⌈1+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+price) ∧ post z.user F := by
  intro owners before
  obtain ⟨pack,factor,C,execute⟩ := scheduledSlotPackWithCharge n p pre bank capacity body
  refine ⟨pack,factor,C,?_⟩
  intro w W live V v S data call price post initial words invoke
  obtain ⟨u,D,m,a,packed,user,packing,ready,off,idle,slots⟩ := execute w W live v S data initial words
  obtain ⟨z,F,k,ran,paid,done⟩ := invoke u D a user ready off idle slots
  refine ⟨z,F,m+k,Exec.seq packed ran,?_,done⟩
  intro js unique
  have localBill := packing js unique
  have childBill := paid js unique
  dsimp only [V]
  omega

/-- Run the invocation on its own embedded bank after the helper slots have been packed. -/
theorem packPlacedInvocationWithCharge [M8.Machine.Net] {P U : Type} {t q k : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (pre : List (Fin 32 × Fin 5)) (bank : Fin ((rowSwapBlock.tapes+35)+142081) ↪ Fin t) (capacity : rowSwapBlock.states ≤ q)
    (caller : Fin k ↪ Fin t) (fan : Fin 142081 ↪ Fin k)
    (shared : fan.trans caller = (Fin.natAddEmb (rowSwapBlock.tapes+35)).trans bank)
    (body : P → Pr P k q prime U) :
    let outer := fun g => embProg caller id (body g)
    let owners := (Fin.natAddEmb (rowSwapBlock.tapes+35) (m := 142081)).trans bank
    let before := pre.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ pack, ∃ (factor : ℕ) (C : ℝ), ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (v : HS t q prime U) (S : Stacks t prime) (data : Fin 142081 → Fin V → ZMod 2),
      ∀ (call : Pr P k q prime U) (price : ℕ) (post : U → Stacks k prime → Prop),
      embStk bank S = helperPackInput w W (embStk owners S) →
      RepT (phaseOwners data) (embStk owners S).L (embStk owners S).R →
      (∀ (u : HS k q prime U) (D : Stacks k prime) (result : Fin 142081 → Fin V → ZMod 2), u.user = v.user →
        RepT (phaseOwners result) (embStk fan D).L (embStk fan D).R →
        (∀ j, (∀ i, bank i ≠ caller j) → D.L j = S.L (caller j) ∧ D.R j = S.R (caller j)) →
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → result j = data j) →
        (∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j)) →
        ∃ z F k, Exec body call (mk u D) k (mk z F) ∧
          (∀ js : List _, js.Nodup → k+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+price) ∧
          post z.user F) →
      ∃ z F t, Exec outer (.seq pack (embProg caller id call)) (mk v S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          factor*⌈1+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌉₊+price) ∧ post z.user (embStk caller F) := by
  intro outer owners before
  obtain ⟨pack,factor,C,run⟩ := packThenInvokeWithCharge n p pre bank capacity outer
  refine ⟨pack,factor,C,?_⟩
  intro w W live V v S data call price post initial words invoke
  apply run w W live v S data (embProg caller id call) price
    (fun user F => post user (embStk caller F)) initial words
  intro u D a user ready off idle slots
  change RepT (phaseOwners a) (embStk owners D).L (embStk owners D).R at ready
  have represented : RepT (phaseOwners a) (embStk (fan.trans caller) D).L (embStk (fan.trans caller) D).R := shared ▸ ready
  obtain ⟨z,F,m,ran,paid,done⟩ := invoke (embDn caller u) (embStk caller D) a user represented
    (fun j away => off (caller j) away) idle slots
  obtain ⟨v',G,placed,_,same,view,untouched⟩ := exec_emb (e := caller) (ι := id) (body' := outer)
    caller.injective (fun _ => rfl) ran u rfl D rfl
  rw [← view] at paid done
  exact ⟨v',G,m,placed,placedCleanup_cost_le caller D G cleanupWeight m price untouched paid,same ▸ done⟩

/-- Restore the helper charts after running a charged sweep. Its child budget
passes through the restoration with coefficient one. -/
theorem restorePackedSweep [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (fan : Fin (142081+2) ↪ Fin T) (body : P → Pr P T Q prime U) (sweep : Pr P T Q prime U)
    (changes : List (Fin 142081 × Option (Fin 56) × Option (Fin 56))) (capacity : columnCapacity ≤ Q) :
    let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb LeafCore.small)
    let bank := (Fin.castAddEmb 41 (n := T)).trans caller
    let outer := fun f => embProg bank id (body f)
    ∃ code, ∃ C : ℝ, ∀ (row : Descriptor) (w V price : ℕ), row.Positive →
      let W := row.beforeRows*row.rows*row.between*row.afterD
      let M := prime^(w+1)
      V = M^16*(row.beforeH*(M^112*W)) →
      ∀ (prepared : Stacks T prime) (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop),
      (∀ x u S, HelperFan fan x S →
        (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
        ∃ v D t y, Exec body sweep (mk u S) t (mk v D) ∧
          (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+price) ∧
          v.user = u.user ∧ HelperFan fan y D ∧ effect x y) →
      ∃ initial, embStk bank initial = prepared ∧ ∀ x u S, HelperFan (fan.trans bank) x S →
        (∀ j, (∀ h, (fan.trans bank) h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
        ∃ z F t y out, Exec outer code (mk u S) t (mk z F) ∧
          (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
            price+⌈C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊) ∧
          z.user = u.user ∧ HelperFan (fan.trans bank) out F ∧ effect x y ∧
          HelperLabelTrace (w+1) row.beforeH W changes y out := by
  intro caller bank outer
  let hdr := fun i : Fin 6 => (i.castAdd 35).natAdd T
  let regs := (Fin.natAddEmb 6 (m := 35)).trans (Fin.natAddEmb T)
  obtain ⟨restore,C,finish⟩ := parentSlotChangesWithCharge changes (fan.trans (Fin.castAddEmb 41)) hdr regs capacity outer
  refine ⟨(embProg bank id sweep).seq restore,C,?_⟩
  intro row w V price positive W M size prepared effect run
  obtain ⟨initial,view,frame⟩ := packedInvocationFrame fan prepared row w
  refine ⟨initial,view,?_⟩
  intro x u S live fresh
  obtain ⟨inside,radix,unit,clock,headers,free,scratch⟩ := frame S fresh
  obtain ⟨v,D,t,y,exec,paid,user,ready,act⟩ := run x (embDn bank u) (embStk bank S) live inside
  obtain ⟨v',D',placed,_,same,project,off⟩ := exec_emb (ι := id) (body' := outer)
    bank.injective (fun _ => rfl) exec u rfl S rfl
  rw [← project] at ready paid
  have keep (j) (high : T ≤ j.val) := off j (fun i eq => by
    have h := congrArg Fin.val eq
    change i.val = j.val at h
    omega)
  obtain ⟨z,F,k,out,last,rest,bill,represented,trace,_⟩ := finish row w V positive size y v' D'
    ((keep _ (by change T ≤ T+(6+2); omega)).2.trans radix)
    ((keep _ (by change T ≤ T+(6+28); omega)).2.trans unit)
    (by rw [(keep _ (by change T ≤ T+(6+33); omega)).2]; exact clock)
    (fun i => (keep _ (by change T ≤ T+i.val; omega)).2.trans (headers i))
    (fun j => ⟨(keep _ (by change T ≤ T+41+j.val; omega)).1.trans (free j).1,
      (keep _ (by change T ≤ T+41+j.val; omega)).2.trans (free j).2⟩)
    (fun j => ⟨(keep _ (by change T ≤ T+41+273+j.val; omega)).1.trans (scratch j).1,
      (keep _ (by change T ≤ T+41+273+j.val; omega)).2.trans (scratch j).2⟩) ready
  refine ⟨z,F,t+k,y,out,placed.seq rest,?_,last.trans (same.trans user),represented,act,trace⟩
  intro js unique
  have sweepBill := placedCleanup_cost_le bank S D' cleanupWeight t price off paid js unique
  have restoreBill := bill js unique
  omega

/-- All 160 invocations followed by chart restoration, on one program across widths. -/
theorem restoredStageRunsWithCharge [M8.Machine.Net] (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U)
      (changes : List (Fin 142081 × Option (Fin 56) × Option (Fin 56))) (_ : columnCapacity ≤ Q),
    let caller := (Fin.castAddEmb 273 (n := T+41)).trans (Fin.castAddEmb LeafCore.small)
    let stageBank := (Fin.castAddEmb 41 (n := T)).trans caller
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let outer := fun f => embProg stageBank id (table f)
    ∃ program, ∃ C : ℝ, ∀ (w B W : ℕ) (row : Descriptor), row.Positive →
      row.beforeH = B*prime^(64*((w+1)*64)) → row.beforeRows*row.rows*row.between*row.afterD = W →
      ∀ (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^(w+1))^16*(B*prime^(64*((w+1)*64))*((prime^(w+1))^112*W))
    let children := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
    (∀ i (x : Fin 142081 → Fin V → ZMod 2) u S, HelperFan (ports i) x S →
      (∀ j, (∀ h, ports i h ≠ j) → S.L j = (initial i).L j ∧ S.R j = (initial i).R j) →
      ∃ z F t y, Exec (body i) (code i) (mk u S) t (mk z F) ∧ (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(localCost i + children i)) ∧
        z.user = u.user ∧ HelperFan (ports i) y F ∧ packedStageEffect n i (w+1) B W x y) →
    ∃ initial, embStk (fan.trans stageBank) initial = shared ∧ ∀ x u S, HelperFan (fan.trans stageBank) x S →
      (∀ j, (∀ h, (fan.trans stageBank) h ≠ j) → S.L j = initial.L j ∧ S.R j = initial.R j) →
      ∃ z F t y out, Exec outer program (mk u S) t (mk z F) ∧
        (∀ js : List _, js.Nodup → t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
          (stageRuns.map localCost).sum+((List.range' (stageChildStart n)
          (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1+
          ⌈C*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)⌉₊) ∧
        z.user = u.user ∧ HelperFan (fan.trans stageBank) out F ∧
        stageRuns.foldr (fun i next a => ∃ b, packedStageEffect n i (w+1) B W a b ∧ next b) (fun a => a = y) x ∧
        HelperLabelTrace (w+1) row.beforeH W changes y out := by
  obtain ⟨T,fan,bank,sharedPorts,stage⟩ := packedStageRunsWithCharge n tapes ports
  refine ⟨T,fan,bank,sharedPorts,?_⟩
  intro P U Q body code changes capacity caller stageBank table outer
  let sweep := Prog.seqList (stageRuns.map fun i => embProg (bank i) (Prod.mk i) (code i))
  obtain ⟨program,C,restore⟩ := restorePackedSweep fan table sweep changes capacity
  refine ⟨program,C,?_⟩
  intro w B W row positive label span localCost childTime initial shared V children run
  obtain ⟨prepared,owners,stageRun⟩ := stage (w := w+1) (B := B) (W := W) body code localCost childTime initial shared run
  have size : V = (prime^(w+1))^16*(row.beforeH*((prime^(w+1))^112*(row.beforeRows*row.rows*row.between*row.afterD))) := by
    rw [label,span]
  obtain ⟨seed,view,execute⟩ := restore row w V ((stageRuns.map localCost).sum+
    ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1)
    positive size prepared (fun x y => stageRuns.foldr (fun i next a => ∃ b, packedStageEffect n i (w+1) B W a b ∧ next b)
      (fun a => a = y) x) (by simpa only [Nat.add_assoc] using stageRun)
  refine ⟨seed,?_,?_⟩
  · change embStk fan (embStk stageBank seed) = shared
    rw [view,owners]
  intro x u S live fresh
  obtain ⟨z,F,t,y,out,exec,paid,user,rep,acts,trace⟩ := execute x u S live fresh
  exact ⟨z,F,t,y,out,exec,by simpa only [Nat.add_assoc] using paid,user,rep,acts,by simpa only [span] using trace⟩

private theorem handoffLinear {A B N K : ℕ} (ha : 0 < A) (hb : 0 < B) (hn : 0 < N) (hk : 0 < K) :
    let V := A*(B*N*K)
    scanCounterCost ![K,N,A*B]+1+(17760*(7021*(A*B)*(N*K)+6)+1+
      (14*V+14*(FlatCoordinateSchedule.bits V).length+33)*(142081+7)+6) ≤ 150000000*V := by
  intro V
  have eqn : A*B*(N*K) = V := by dsimp only [V]; ac_rfl
  have hd := Nat.mul_pos ha hb
  have hnk := Nat.mul_pos hn hk
  have hv : 0 < V := eqn ▸ Nat.mul_pos hd hnk
  have h₁ : N*K ≤ V := eqn ▸ Nat.le_mul_of_pos_left _ hd
  have h₂ : A*B ≤ V := eqn ▸ Nat.le_mul_of_pos_right _ hnk
  have counters := scanCounterCost_le ((Nat.le_mul_of_pos_left _ hn).trans h₁)
    ((Nat.le_mul_of_pos_right _ hk).trans h₁) h₂ hv
  have bits := FlatCoordinateDimensions.bits_length_le_twice (le_refl V) hv
  rw [Nat.mul_assoc 7021,eqn]
  omega

/-- Materialize the parent sweep output from restored owners and scanned target words, with linear cleanup cost. -/
theorem stageHandoffWithCharge {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q) (src : Fin 3 → Fin T)
    (body : P → Pr P ((T+142081*7)+142081+10) Q prime U) :
    ∃ code, ∃ rate : ℕ, ∀ w B W : ℕ, 0 < B → 0 < (prime^w)^112*W →
    let K := (prime^w)^112*W
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let port := stagePadPort fan
    let old := ((Fin.castAddEmb (142081*7) (n := T)).trans (Fin.castAddEmb 142081)).trans (Fin.castAddEmb 10)
    let label := firstRowLabel w
    let retained := fan.trans (((Fin.castAddEmb (142081*7)).trans (Fin.castAddEmb 142081)).trans (Fin.castAddEmb 10))
    ∀ x y out,
      stageRuns.foldr (fun p cont a => ∃ b, packedStageEffect n p w B W a b ∧ cont b)
        (fun a => a = y) (singleLabelBank label x) →
      HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
      let next := collapseLabelBank (B := B) (K := K) out
      ∀ u S, StageDimensionWords (fun i => old (src i)) K N (A*B) S →
      (∀ j, T+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) → StageControls retained (A*(B*N*K)) S → RestoredOwnerPayloads n retained out S →
      (∀ k, Cover.Fallback.RecordPayload (port (targetOwner n k) 0) (fun _ => blank) 0
        (stageTargetWord n k w B K x) S) →
      ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧
        (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*(A*(B*N*K))) ∧
        z.user = u.user ∧ HelperFan (stageOutputFan n fan)
          (singleLabelBank label (Function.update next (Fin.last 142080) (fun _ => 0))) F ∧
          (∀ j, (∀ i, fan i ≠ j) → F.L (old j) = S.L (old j) ∧ F.R (old j) = S.R (old j)) := by
  obtain ⟨code,run⟩ := stageHandoff_host (P := Empty) (U := U) n fan fits src Empty.elim
  let factor := 1+6*Fast.Main.mnProgPush code
  refine ⟨embProg id Empty.elim code,factor*150000000,?_⟩
  intro w B W hb hk K A N port old label retained x y out trace restore next u S dims fresh controls live inputs
  obtain ⟨z,F,t,exec,paid,user,ready,off⟩ := run w B W hb hk x y out trace restore u S dims fresh controls live inputs
  obtain ⟨placed,charge⟩ := placeClosedWithCharge body code exec
  refine ⟨z,F,t,placed,?_,user,ready,off⟩
  intro js unique
  have hA : 0 < A := pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _
  have hN : 0 < N := pow_pos Shared50ModularControl.prime_prime.pos _
  have bound := handoffLinear hA hb hN hk
  have price := Nat.mul_le_mul_left factor (paid.trans bound)
  rw [← Nat.mul_assoc] at price
  exact (charge js unique).trans (Nat.add_le_add_left price _)

/-- Scan just the restored target bank, preserving the recursive sweep budget already paid. -/
theorem scanRestoredTargetsWithCharge (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let inner := (Fin.castAddEmb 14 (n := T)).trans (Fin.castAddEmb (142081*7))
    let placedFan := fan.trans (Fin.castAddEmb 14)
    let bank := fun k : I => targetScanBank placedFan (targetOwner n k)
    let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb T (m := 14)).trans (Fin.castAddEmb (142081*7)))
    ∀ (body : P → Pr P ((T+14)+142081*7) Q prime U), ∃ code, ∃ rate : ℕ,
    ∀ (w B W : ℕ) (label : Cover.LabelPadding.Label 64 w) (x),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    0 < K → 0 < B → ∀ u S y out, HelperFan (fan.trans inner) out S →
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    (∀ i : Fin 3, S.L (reg (i.castAdd 7)) = [separator] ∧
      S.R (reg (i.castAdd 7)) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (reg (i.natAdd 3)) = []) →
    (∀ k (j : Fin 7), S.L (bank k j.succ) = [] ∧ S.R (bank k j.succ) = []) →
    let result := fun k => WordAtZero (stageTargetWord n k w B K x)
    ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧
      (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*(D*(N*K))) ∧ z.user = u.user ∧
      (∀ k, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
      StageControls (fan.trans inner) ((prime^w)^16*(B*N*K)) F ∧
      StageDimensionWords (fun i => reg (i.castAdd 7)) K N D F ∧
      F.R ((12 : Fin 14).natAdd T |>.castAdd (142081*7)) = S.R ((12 : Fin 14).natAdd T |>.castAdd (142081*7)) ∧
      RestoredOwnerPayloads n (fan.trans inner) out F := by
  intro I
  let order := stageRuns.product (List.finRange 111)
  obtain ⟨states,build⟩ := packedStageTargets_host n
  refine ⟨states,?_⟩
  intro T Q P U fan fits inner placedFan bank reg body
  obtain ⟨scan,run⟩ := build (P := Empty) (U := U) fan fits Empty.elim (.act .done)
  let factor := 1+6*Fast.Main.mnProgPush scan
  refine ⟨embProg id Empty.elim scan,factor*(4300*order.length+201),?_⟩
  intro w B W label x K N D hk hb u S y out ready trace restore dims free scratch result
  obtain ⟨z,F,t,exec,paid,user,words,controls,headers,saved,retained⟩ := run w B W label x hk hb u S
    (embDn inner u) (embStk inner S) 1 y out (Exec.act .done _) rfl ready trace restore dims free scratch
  have closed : Exec Empty.elim scan (mk u S) t (mk z F) := by
    convert exec using 1
  obtain ⟨placed,charge⟩ := placeClosedWithCharge body scan closed
  refine ⟨z,F,t,placed,?_,user,words,controls,headers,saved,retained⟩
  have positive : 0 < D*(N*K) := Nat.mul_pos (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb)
    (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hk)
  change t ≤ 1+(4300*order.length+200)*(D*(N*K)) at paid
  have cost : t ≤ (4300*order.length+201)*(D*(N*K)) := by
    rw [show 4300*order.length+201 = (4300*order.length+200)+1 by omega,Nat.add_mul,Nat.one_mul]
    omega
  intro js unique
  exact (charge js unique).trans (Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left factor cost) _)

private theorem addCharge {m t initial mid final sweep finish : ℕ}
    (a : m+mid ≤ initial+sweep) (b : t+final ≤ mid+finish) :
    m+t+final ≤ initial+sweep+finish := by omega

private theorem scanExtensionOff {T a b : ℕ} (j : Fin (T+a+b)) (high : T ≤ j.val) (i : Fin T) :
    (i.castAdd a).castAdd b ≠ j := by
  intro eq
  have h := congrArg Fin.val eq
  change i.val = j.val at h
  omega

private theorem scanHandoffSource {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (i : Fin 142081) :
    stagePadPort fan i 0 = ((targetScanBank fan i 1).castAdd 142081).castAdd 10 := by
  apply Fin.ext
  simp only [stagePadPort,Function.Embedding.coeFn_mk,Fin.val_zero,Fin.val_castAdd,ite_true]

/-- Place a scanned sweep and write the parent output while charging the sweep budget once. -/
theorem scannedStageWithHandoffCharge {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q) (src : Fin 3 → Fin T)
    (apart : ∀ i j, fan i ≠ src j)
    (body : P → Pr P (T+142081*7) Q prime U) (stage : Pr P (T+142081*7) Q prime U) :
    let extBank := (Fin.castAddEmb 142081 (n := T+142081*7)).trans (Fin.castAddEmb 10)
    let outer := fun g => embProg extBank id (body g)
    let base := Fin.castAddEmb (142081*7) (n := T)
    ∃ code, ∃ rate : ℕ, ∀ w B W : ℕ, 0 < B → 0 < (prime^w)^112*W →
    let K := (prime^w)^112*W
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let V := A*(B*N*K)
    let label := firstRowLabel w
    ∀ x y out u S v C m (price : ℕ), Exec body stage (mk (embDn extBank u) (embStk extBank S)) m (mk v C) →
      (∀ js : List _, js.Nodup → m+tapeCharge cleanupWeight js C ≤ tapeCharge cleanupWeight js (embStk extBank S)+price) →
      v.user = u.user →
      (∀ j, T+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
      StageDimensionWords (fun i => base (src i)) K N (A*B) C →
      StageControls (fan.trans base) V C → RestoredOwnerPayloads n (fan.trans base) out C →
      (∀ k, RecordPayload (targetScanBank fan (targetOwner n k) 1) (fun _ => blank) 0
        (stageTargetWord n k w B K x) C) →
      stageRuns.foldr (fun p cont a => ∃ b, packedStageEffect n p w B W a b ∧ cont b)
        (fun a => a = y) (singleLabelBank label x) →
      HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
      ∃ z F steps, Exec outer code (mk u S) steps (mk z F) ∧
        (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price+rate*V) ∧
        z.user = u.user ∧ HelperFan (stageOutputFan n fan)
          (singleLabelBank label (Function.update (collapseLabelBank (B := B) (K := K) out)
            (Fin.last 142080) (fun _ => 0))) F ∧
        StageDimensionWords (fun i => extBank (base (src i))) K N (A*B) F ∧
        (∀ j, (∀ i, fan i ≠ j) → F.R (extBank (base j)) = C.R (base j)) := by
  intro extBank outer base
  obtain ⟨handoff,rate,run⟩ := stageHandoffWithCharge n fan fits src outer
  refine ⟨.seq (embProg extBank id stage) handoff,rate,?_⟩
  intro w B W hb hk K A N V label x y out u S v C m price exec sweepBill same fresh dims controls live targets trace restore
  obtain ⟨v',C',placed,_,user,view,off⟩ := exec_emb (ι := id) (body' := outer)
    extBank.injective (fun _ => rfl) exec u rfl S rfl
  have blank (j : Fin ((T+142081*7)+142081+10)) (high : T+142081*7 ≤ j.val) : C'.L j = [] ∧ C'.R j = [] := by
    have keep := off j (scanExtensionOff j high)
    exact ⟨keep.1.trans (fresh j high).1,keep.2.trans (fresh j high).2⟩
  rw [← view] at dims controls live targets
  obtain ⟨z,F,t,finish,paid,unchanged,ready,stored⟩ := run w B W hb hk x y out trace restore v' C'
    (by simpa only [StageDimensionWords,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using dims)
    blank
    (by simpa only [StageControls,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using controls)
    (by simpa only [RestoredOwnerPayloads,RecordPayload,embStk,Function.comp_apply,extBank,base,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using live)
    (fun k => by
      rw [scanHandoffSource]
      simpa only [RecordPayload,embStk,Function.comp_apply,extBank,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using targets k)
  refine ⟨z,F,m+t,Exec.seq placed finish,?_,unchanged.trans (user.trans same),ready,?_,?_⟩
  · intro js unique
    rw [← view] at sweepBill
    have first := placedCleanup_cost_le extBank S C' cleanupWeight m price off sweepBill js unique
    have last := paid js unique
    change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js C'+rate*V at last
    exact addCharge first last
  · intro i
    have h := stored (src i) (fun j => apart j i)
    exact ⟨h.1.trans (dims i).1,h.2.trans (dims i).2⟩
  · intro j outside
    rw [← view]
    exact (stored j outside).2

end IntegerMultBounds.MathlibTM2.M6.BitNode
