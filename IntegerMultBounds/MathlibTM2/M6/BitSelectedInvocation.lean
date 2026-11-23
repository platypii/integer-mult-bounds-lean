module

public import IntegerMultBounds.MathlibTM2.M6.BitScalarMoveSequence

/-! A fixed PR589 invocation with charged executions of its scheduled children. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Shared50ModularControl (prime)
open Certificates.PR589 RecursiveInterchangeLayout

/-- The private worker directory for a component is fixed before the choice of
child procedures. Each child keeps its actual coordinate map and tape ports. -/
private def ComponentDirectory [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (slot : Fin 3) (count : ℕ) (child : Fin count → Fin nodeChildren5.length)
    (coords : ∀ (node : Descriptor) (i : Fin count) (w W : ℕ),
      (Fin (volume prime (scheduledChild prime node (child i))) ≃ Fin ((prime^w)^16*W)) → Prop) : Prop :=
  let I := Fin count
  ∃ (ts : I → ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts i)) (states : ℕ),
  ∀ {Q : ℕ}, states ≤ Q → ∀ (body : ∀ i, P → Pr P (ts i) Q prime U) (f : I → P),
  ∃ (T : ℕ) (fan : Fin (142081+2+1) ↪ Fin T) (host : I × P → Pr (I × P) T Q prime U)
    (code : Pr (I × P) T Q prime U) (work : ℕ → ℕ → ℕ),
  (∃ a b c : ℕ, ∀ w V, work w V = (a+b*swapVolumeRate w)*V+c) ∧
  ∀ (node : Descriptor) (w B rows : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
  node.beforeH = B*prime^(64*((w+1)*64)) →
  let M := prime^(w+1)
  let K := node.beforeRows*rows*node.between*node.afterD
  let blocks := M^112*B
  let W := blocks*prime^(64*((w+1)*64))*K
  let V := M^16*W
  let desc := fun i => scheduledChild prime node (child i)
  0 < W → ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
  (∀ i, coords node i (w+1) W (position i)) ∧
  ∀ record : I → List (Fin (prime+4)), ∃ initial : Stacks T prime, ∀ (budget : I → ℕ) word,
  (∀ i, ScheduledChildExec node (desc i) w W (ports i) (record i) (position i) (body i) (f i) (budget i) true) →
  ∀ (x : Fin 142081 → Fin V → ZMod 2) u S,
    PrivateTapes fan initial S → HelperFan (Fin.castAddEmb 1) x (embStk fan S) →
    S.R (fan (Fin.last (142081+2))) = word →
    ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ CleanupBound S F t (work w V+(List.ofFn budget).sum) ∧
      z.user = u.user ∧ HelperFan (Fin.castAddEmb 1) y (embStk fan F) ∧
      F.R (fan (Fin.last (142081+2))) = word ∧ InvocationComponentEffect n p (w+1) blocks K slot x y

private theorem sumRates [M8.Machine.Net] {I : Type} (xs : List I) (cost : I → ℕ → ℕ → ℕ)
    (rates : ∀ i, ∃ a b c : ℕ, ∀ w V, cost i w V = (a+b*swapVolumeRate w)*V+c) :
    ∃ a b c : ℕ, ∀ w V, (xs.map (fun i => cost i w V)).sum = (a+b*swapVolumeRate w)*V+c := by
  induction xs with
  | nil => exact ⟨0,0,0,by simp⟩
  | cons i xs ih =>
    obtain ⟨a,b,c,head⟩ := rates i
    obtain ⟨d,e,f,tail⟩ := ih
    exact ⟨a+d,b+e,c+f,fun w V => by simp only [List.map_cons,List.sum_cons,head,tail]; ring⟩

private theorem copyDirectory [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5) :
    ComponentDirectory P U n p 1 Copy.lifecycles.length (fun j => copyChildPosition (n,p,j))
      (fun node j w W pos => CopyIntervalPositions (scheduledChild prime node (copyChildPosition (n,p,j))) w W pos) := by
  obtain ⟨ts,regs,T,states,fan,bank,build⟩ := invocationCopyComponent n p
  refine ⟨ts,regs,states,?_⟩
  intro Q cap body f
  obtain ⟨base,code,run⟩ := build cap body f
  let host := fun f : CopyIndex × P => embProg (Fin.castAddEmb 1) id (embProg (bank f.1) (Prod.mk f.1) (body f.1 f.2))
  refine ⟨T+1,withCutoffPort fan,host,code,fun _ V => (List.ofFn (fun j => nativePrice true (base j*V+12))).sum+1,?_,?_⟩
  · obtain ⟨a,b,c,h⟩ := sumRates (List.finRange Copy.lifecycles.length) (fun j _ V => nativePrice true (base j*V+12))
      (fun j => ⟨13*base j,0,156,fun _ _ => by unfold nativePrice; simp; ring⟩)
    exact ⟨a,b,c+1,fun w V => by dsimp only; rw [List.ofFn_eq_map,h w V,Nat.add_assoc]⟩
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  obtain ⟨seed,run⟩ := prepare record
  refine ⟨seed,?_⟩
  intro budget word children x u S fresh live header
  obtain ⟨z,F,t,y,exec,cost,user,⟨out,kept⟩,act⟩ := run budget word children x u S fresh ⟨live,header⟩
  exact ⟨z,F,t,y,exec,by simpa only [Nat.add_right_comm _ 1] using cost,user,out,kept,act⟩

private theorem phaseDirectories [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5) (b : Bool) :
    let gs := if b then sectionB++sectionC else sectionD++sectionA
    let cur := if b then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let count := (phaseMoveBlocks gs cur).1.length
    let start := if b then ((Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0
    ∃ select : Fin count → MoveIndex, (∀ i, (select i).val = start+i.val) ∧
      ComponentDirectory P U n p (if b then 2 else 0) count (fun i => phaseChildPositions.choose (n,p,select i))
        (fun node i _ _ pos => ∀ h, (pos h).val =
          (CopyChildLayout.packActive (scheduledChild prime node (phaseChildPositions.choose (n,p,select i))) h).val) := by
  intro gs cur count start
  obtain ⟨select,index,steps⟩ := invocationPhaseComponent P U n p b
  obtain ⟨ts,regs,states,build⟩ := steps
  refine ⟨select,index,ts,regs,states,?_⟩
  intro Q cap body f
  obtain ⟨T,fan,host,code,overhead,base,swaps,run⟩ := build cap body f
  let extra := fun w V (i : Fin count) => nativePrice true ((base i+swaps i*swapVolumeRate w)*V)
  refine ⟨T,fan,host,code,fun w V => overhead*V+((List.finRange count).map (extra w V)).sum,?_,?_⟩
  · obtain ⟨a,b,c,h⟩ := sumRates (List.finRange count) (fun i w V => extra w V i)
      (fun i => ⟨13*base i,13*swaps i,0,fun w V => by simp [extra,nativePrice]; ring⟩)
    exact ⟨overhead+a,b,c,fun w V => by dsimp only; rw [h w V]; ring⟩
  intro node w B rows width split label M K blocks W V desc pos
  obtain ⟨position,coords,prepare⟩ := run node w B rows width split label pos
  refine ⟨position,coords,?_⟩
  intro record
  obtain ⟨seed,step⟩ := prepare record
  refine ⟨seed,?_⟩
  intro budget word children x u S fresh live header
  obtain ⟨z,F,t,exec,cost,user,out,kept⟩ := step budget word children x u S fresh ⟨live,header⟩
  refine ⟨z,F,t,_,exec,?_,user,out,kept,?_⟩
  · have bill {m : ℕ} (a : ℕ) (f g : Fin m → ℕ) :
        a+((List.finRange m).map (fun i => f i+g i)).sum =
          a+((List.finRange m).map g).sum+(List.ofFn f).sum := by
      rw [List.sum_map_add,List.ofFn_eq_map,Nat.add_right_comm]
      omega
    rw [← bill (overhead*V) budget (extra w V)]
    exact cost
  · cases b <;> rfl

/-- The invocation program is fixed across recursive sizes. Its local cost has
three fixed coefficients, and its remaining charge is exactly the child directory. -/
def SelectedInvocationExecution [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (count : Fin 3 → ℕ) (child : ∀ j, Fin (count j) → Fin nodeChildren5.length)
    (coords : ∀ j (node : Descriptor) (i : Fin (count j)) (w W : ℕ),
      (Fin (volume prime (scheduledChild prime node (child j i))) ≃ Fin ((prime^w)^16*W)) → Prop) : Prop :=
  ∃ (ts : ∀ j, Fin (count j) → ℕ) (ports : ∀ j i, Fin (rowSwapBlock.tapes+35) ↪ Fin (ts j i)) (states : ℕ),
  ∀ {Q : ℕ}, states ≤ Q → ∀ (body : ∀ j i, P → Pr P (ts j i) Q prime U) (f : ∀ j, Fin (count j) → P),
  ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (cut : Fin T) (host : (Σ j, Fin (count j) × P) → Pr (Σ j, Fin (count j) × P) T Q prime U)
    (code : Pr (Σ j, Fin (count j) × P) T Q prime U) (a b c : ℕ),
  (∃ D : ℝ, ∀ w V : ℕ, 0 < V → (((a+b*swapVolumeRate w)*V+c : ℕ) : ℝ) ≤
    D*(V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)) ∧
  ∀ (node : Descriptor) (w B rows : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
  node.beforeH = B*prime^(64*((w+1)*64)) →
  let M := prime^(w+1)
  let K := node.beforeRows*rows*node.between*node.afterD
  let blocks := M^112*B
  let W := blocks*prime^(64*((w+1)*64))*K
  let V := M^16*W
  let desc := fun j i => scheduledChild prime node (child j i)
  0 < W → ∃ position : ∀ j i, Fin (volume prime (desc j i)) ≃ Fin V,
  (∀ j i, coords j node i (w+1) W (position j i)) ∧
  ∀ (record : ∀ j, Fin (count j) → List (Fin (prime+4))) (time : ℕ → ℕ) (word : List (Fin (prime+4))),
  (∀ j i, ScheduledChildExec node (desc j i) w W (ports j i) (record j i) (position j i)
    (body j i) (f j i) (time (child j i).val) true) →
  ∀ shared, ∃ seed : Stacks T prime, embStk fan seed = shared ∧ seed.R cut = word ∧
    ∀ (x : Fin 142081 → Fin V → ZMod 2) u S, PrivateTapes fan seed S → HelperFan fan x S →
    ∃ z F t y, Exec host code (mk u S) t (mk z F) ∧ CleanupBound S F t
      ((a+b*swapVolumeRate w)*V+c+((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum) ∧
      z.user = u.user ∧ HelperFan fan y F ∧ BorrowedStep n (w+1) blocks K p x y

private theorem assembleInvocation [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    (count : Fin 3 → ℕ) (child : ∀ j, Fin (count j) → Fin nodeChildren5.length)
    (coords : ∀ j (node : Descriptor) (i : Fin (count j)) (w W : ℕ),
      (Fin (volume prime (scheduledChild prime node (child j i))) ≃ Fin ((prime^w)^16*W)) → Prop)
    (components : ∀ j, ComponentDirectory P U n p j (count j) (child j) (coords j))
    (bill : ∀ time : ℕ → ℕ, let price := fun j => (List.ofFn (fun i => time (child j i).val)).sum
      price 0+(price 1+price 2) = ((List.range' (stageChildStart n+runChildStart p) Geometry.Moves.localPaid.length).map time).sum) :
    SelectedInvocationExecution P U n p count child coords := by
  classical
  choose ts regs qs build using components
  refine ⟨ts,regs,Finset.univ.sup qs,?_⟩
  intro Q cap body f
  choose tapes fans workers programs work rates step using fun j => build j ((Finset.le_sup (Finset.mem_univ j)).trans cap) (body j) (f j)
  choose a b c rate using rates
  obtain ⟨T,fan,bank,place⟩ := chargedInvocation_host n p tapes fans
  let data := (Fin.castAddEmb 1 (n := 142081+2)).trans fan
  let host : (Σ j, Fin (count j) × P) → Pr (Σ j, Fin (count j) × P) T Q prime U := fun label => embProg (bank label.1) (Sigma.mk label.1) (workers label.1 label.2)
  obtain ⟨code,run⟩ := place workers programs
  refine ⟨T,data,fan (Fin.last (142081+2)),host,code,a 0+a 1+a 2,b 0+b 1+b 2,c 0+c 1+c 2,?_,?_⟩
  · simpa only [Nat.zero_mul,Nat.add_zero] using borrowedWorkerCost (a 0+a 1+a 2) (b 0+b 1+b 2) 0 (c 0+c 1+c 2)
  intro node w B rows width split label M K blocks W V desc pos
  choose position geometry prepare using fun j => step j node w B rows width split label pos
  refine ⟨position,geometry,?_⟩
  intro record time word children shared
  let price := fun j => (List.ofFn (fun i => time (child j i).val)).sum
  choose seeds execute using fun j => prepare j (record j)
  let extended : Stacks (142081+2+1) prime := ⟨shared.inp,shared.out,Fin.append shared.L (fun _ => []),
    Fin.append shared.R (fun _ => word)⟩
  obtain ⟨seed,view,exec⟩ := run (w+1) blocks K word (fun j => work j w V+price j) seeds (fun j x u S fresh live => by
    obtain ⟨z,F,t,y,h,cost,user,out,kept,act⟩ := execute j (fun i => time (child j i).val) word (children j) x u S fresh live.1 live.2
    exact ⟨z,F,t,y,h,cost,user,⟨out,kept⟩,act⟩) extended
  have project (S : Stacks T prime) : embStk data S = embStk (Fin.castAddEmb 1) (embStk fan S) := rfl
  have header := congrArg (fun (D : Stacks (142081+2+1) prime) => D.R (Fin.last (142081+2))) view
  have wordAt : seed.R (fan (Fin.last (142081+2))) = word := by
    change seed.R _ = Fin.append shared.R (fun _ : Fin 1 => word) ((0 : Fin 1).natAdd (142081+2)) at header
    simpa only [Fin.append_right] using header
  refine ⟨seed,?_,wordAt,?_⟩
  · rw [project,view]
    cases shared
    simp [extended,embStk,Function.comp_def]
    constructor <;> funext i <;> exact Fin.append_left ..
  intro x u S fresh live
  have cut : ∀ i, data i ≠ fan (Fin.last (142081+2)) := fun i => fan.injective.ne (fun eq => i.isLt.ne (congrArg Fin.val eq))
  obtain ⟨z,F,t,y,h,cost,user,out,act⟩ := exec x u S (fun j off => fresh j (fun i => off (i.castAdd 1))) ⟨live,by
    exact (fresh _ cut).2.trans wordAt⟩
  refine ⟨z,F,t,y,h,?_,user,out.1,act⟩
  have sum := bill time
  change price 0+(price 1+price 2) = _ at sum
  rw [← sum]
  apply workerCost.weaken (charged := true) cost
  simp only [rate,Nat.add_mul]
  omega

/-- Values for the pre-COPY, COPY, and post-COPY slots, including dependent
families such as the three distinct procedure-label types. -/
def invocationSlots {α : Fin 3 → Sort u} (pre : α 0) (copy : α 1) (post : α 2) : ∀ i, α i :=
  Fin.cases pre (Fin.cases copy (Fin.cases post (fun i => i.elim0)))

def invocationCounts (left right : ℕ) : Fin 3 → ℕ :=
  invocationSlots (α := fun _ => ℕ) left Copy.lifecycles.length right

noncomputable def invocationChildren (n : Fin 9) (p : Fin 32 × Fin 5) {l r : ℕ}
    (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex) :
    ∀ j, Fin (invocationCounts l r j) → Fin nodeChildren5.length :=
  invocationSlots (fun i => phaseChildPositions.choose (n,p,pre i)) (fun j => copyChildPosition (n,p,j))
    (fun i => phaseChildPositions.choose (n,p,post i))

def invocationCoordinates {v : Descriptor} (j : Fin 3) (w W : ℕ)
    (position : Fin (volume prime v) ≃ Fin ((prime^w)^16*W)) : Prop :=
  if j = 1 then CopyIntervalPositions v w W position else ∀ h, (position h).val = (CopyChildLayout.packActive v h).val

private theorem joinDirectories [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5)
    {l r : ℕ} (pre : Fin l → MoveIndex) (post : Fin r → MoveIndex)
    (first : ∀ i, (pre i).val = i.val) (last : ∀ i, (post i).val = l+i.val)
    (size : l+r = (Geometry.Moves.phaseEdges.filter positiveMove).length)
    (left : ComponentDirectory P U n p 0 l (fun i => phaseChildPositions.choose (n,p,pre i))
      (fun node i _ _ pos => ∀ h, (pos h).val = (CopyChildLayout.packActive
        (scheduledChild prime node (phaseChildPositions.choose (n,p,pre i))) h).val))
    (right : ComponentDirectory P U n p 2 r (fun i => phaseChildPositions.choose (n,p,post i))
      (fun node i _ _ pos => ∀ h, (pos h).val = (CopyChildLayout.packActive
        (scheduledChild prime node (phaseChildPositions.choose (n,p,post i))) h).val)) :
    SelectedInvocationExecution P U n p (invocationCounts l r) (invocationChildren n p pre post)
      (fun j _ _ w W pos => invocationCoordinates j w W pos) := by
  apply assembleInvocation
  · exact invocationSlots left (copyDirectory P U n p) right
  · intro time
    change (List.ofFn (fun i : Fin l => time (phaseChildPositions.choose (n,p,pre i)).val)).sum +
      ((List.ofFn (fun i : CopyIndex => time (copyChildPosition (n,p,i)).val)).sum +
       (List.ofFn (fun i : Fin r => time (phaseChildPositions.choose (n,p,post i)).val)).sum) = _
    simpa only [List.ofFn_eq_map] using invocationComponentChildSum n p time pre post first last size

/-- One fixed program executes the selected pre-COPY, all nine windows, and
the selected post-COPY. Recursive executions are required only at their
scheduled descriptors; the coefficients in the local bill are uniform. -/
theorem selectedInvocation [M8.Machine.Net] (P U : Type) (n : Fin 9) (p : Fin 32 × Fin 5) :
    let left := (phaseMoveBlocks (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)).1.length
    let right := (phaseMoveBlocks (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)).1.length
    ∃ (pre : Fin left → MoveIndex) (post : Fin right → MoveIndex),
      (∀ i, (pre i).val = i.val) ∧ (∀ i, (post i).val = left+i.val) ∧
      SelectedInvocationExecution P U n p (invocationCounts left right) (invocationChildren n p pre post)
        (fun j _ _ w W pos => invocationCoordinates j w W pos) := by
  intro left right
  obtain ⟨pre,first,before⟩ := phaseDirectories P U n p false
  obtain ⟨post,last,after⟩ := phaseDirectories P U n p true
  have len (gs : List RawGate) (cur : ℕ → ℕ) :
      (phaseMoveBlocks gs cur).1.length = ((Frames.edges gs cur).filter positiveMove).length := by
    simpa only [List.length_map] using congrArg List.length (phaseMoveBlocks_spec gs cur).1
  have size : left+right = (Geometry.Moves.phaseEdges.filter positiveMove).length := by
    simpa only [List.length_map,List.length_append] using congrArg List.length invocationMoveBlocks_order
  have a (i : Fin left) : (pre i).val = i.val := by simpa only [Bool.false_eq_true,ite_false,Nat.zero_add] using first i
  have b (i : Fin right) : (post i).val = left+i.val := by
    rw [show left = _ from len (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)]
    exact last i
  refine ⟨pre,post,a,b,joinDirectories P U n p pre post a b size ?_ ?_⟩
  · simpa only [Bool.false_eq_true,ite_false] using before
  · simpa only [ite_true] using after

end IntegerMultBounds.MathlibTM2.M6.BitNode
