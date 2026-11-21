module

public import IntegerMultBounds.MathlibTM2.M6.BitHostedOrdinaryChild
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodParentSetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRun

/-! The prepared good record with the scheduled weighted child installed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout Stack Host Fallback RecursiveInterchangeLayout
open GoodForm CrossWeightLayout M8.Exchange IntegerMultBounds.Swap.Shear
open HeadPivotLayout HeadWidthLayout M8.ReversedExchange GoodChildLayout

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Install one ordinary procedure per scheduled occurrence. Each calls the
same recursive transpose and uses the rank of its own occurrence. -/
noncomputable def ordinaryRecordTable [M8.Machine.Net] {P U : Type} {n T : ℕ}
    (caller : Fin 58 ↪ Fin n) (rootCut : Fin n) (host : Fin 64 ↪ Fin T)
    (aux : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (apart : ∀ i j, aux i ≠ host j)
    (root : P) (nodes : P → Pr (P ⊕ Fin nodeChildren5.length) (n+T) columnCapacity prime U) :
    P ⊕ Fin nodeChildren5.length → Pr (P ⊕ Fin nodeChildren5.length) (n+T) columnCapacity prime U :=
  Sum.elim nodes fun i =>
    let r := nodeChildren5[i.val]
    hostedWeightedOrdinaryProgram caller rootCut host aux apart r (64-r) (.inl root)

attribute [local irreducible] goodIncomingTime goodOutgoingTime childWeightTime dimensionTime

private theorem scheduledParentOverhead {U : Type} {T : ℕ} (machine : Fin 55 ↪ Fin T) :
    ∃ overhead : ℕ, ∀ i : Fin 65,
      let r := i.val
      let g := 64-r
      let hr := Nat.le_add_right r g
      ∀ w W budget, 0 < W →
        let M := prime^(w+1)
        let H := M.size
        let J := W.size
        1+goodIncomingTime (P := Empty) (U := U) (A := prime) Empty.elim machine prime w W H J r hr +
          ((((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
            (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7))) +
          (1+goodOutgoingTime (P := Empty) (U := U) (A := prime) Empty.elim machine prime w W H J r hr) ≤
          budget+overhead*(M^((r+g)+(r+g))*W) := by
  classical
  have price (i : Fin 65) :=
    goodRecordTime_volume_le (P := Empty) (A := prime) (U := U) (d := i.val+(64-i.val)) Empty.elim machine
      i.val (64-i.val) 0 rfl (by omega) (Nat.le_add_right ..)
  let overhead := Finset.univ.sup fun i => (price i).choose
  refine ⟨overhead,?_⟩
  intro i r g hr w W budget live M H J
  have bound := (price i).choose_spec w W budget live
  have uniform : (price i).choose ≤ overhead :=
    Finset.le_sup (f := fun j => (price j).choose) (Finset.mem_univ i)
  have cost := bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (M^((r+g)+(r+g))*W) uniform) budget)
  simpa only [Nat.zero_mul,Nat.zero_add,H,J,M,r,g,hr] using cost

/-- Execute the complete incoming, weighted-child and outgoing stages of the
ordinary record at its scheduled occurrence. -/
theorem hostedScheduledRecord_exec [M8.Machine.Net] {P U : Type} [Fintype P] {n T : ℕ}
    (callerBank : Fin 58 ↪ Fin n) (rootCut : Fin n) (host : Fin 64 ↪ Fin T)
    (aux : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (separate : ∀ i j, aux i ≠ host j)
    (cutOffBank : ∀ j, callerBank j ≠ rootCut) (root : P)
    (nodes : P → Pr (P ⊕ Fin nodeChildren5.length) (n+T) columnCapacity prime U) :
    let body := ordinaryRecordTable callerBank rootCut host aux separate root nodes
    let physical := Record.payloadBank (callerBank 24) (host 24)
    let caller := host.trans physical
    let work := aux.trans physical
    let apart := fun i j => physical.injective.ne (separate i j)
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    ∃ (A : ℝ) (overhead : ℕ), ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun (S : Stacks (n+T) prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks (n+T) prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      let full := callerBank.trans (Fin.castAddEmb T)
      let m := r+g
      let hr := Nat.le_add_right r g
      let cap : 217 ≤ columnCapacity := le_max_left ..
      let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
      let regs := adapterBank.trans machine
      let headHost := head.trans regs
      let c := HeadPivotLayout.child.trans headHost
      let h := (coeff true).trans headHost
      let shearPort := shear.trans headHost
      let ts := shear.trans (ordinaryHead.trans regs)
      ∀ (budget cutoff L : ℕ),
      cutoff < 2^L → desc.width.size ≤ L →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (nodes root) (mk u D) t (mk y G) ∧ onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j, j ≠ bank 24 → G.L j = D.L j ∧ G.R j = D.R j)) →
      let childBudget := ⌊((if cutoff < desc.width then budget else 0 : ℕ) : ℝ) +
        A*(((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^d*W : ℕ)+L+
          ((if cutoff < desc.width then 0 else desc.width*(M^d*W) : ℕ) : ℝ))⌋₊
      ∀ (G : Matrix (Fin m) (Fin m) (ZMod M)) (minor : ∀ j (hj : j < r), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
        (idem : G*G = G) (B : Matrix (Fin m) (Fin r) (ZMod M)) (E : Matrix (Fin r) (Fin m) (ZMod M)) (factor : G = B*E)
        (weights inv : Fin m → ZMod M) (inverse : ∀ j, weights j * inv j = 1),
      let H := M.size
      let J := W.size
      let words := fun j => if hj : j ≤ r then matrixWords prime H (stageAt G r hr minor j hj).M else []
      let stage := stageAt G r hr minor r le_rfl
      let parentWords := (List.ofFn fun i => binSyms H (weights i).val).flatten
      let ready := HeadColumnReady (d := m+m) (W := W) h (entry.trans regs) H J [] parentWords []
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      ∀ v S word, ready word S → S.R (regs 27) = [] →
        S.R (machine 54) = (List.ofFn fun j => binSyms H (inv j).val).flatten →
        (S.R (headHost 49),S.R (headHost 50)) = matrixArchive words (words 0) [] r →
        (S.R (headHost 51)).length = m*m*H →
        S.R (c 18) = (List.ofFn fun i : Fin r => binSyms H (stage.M (i.castLE hr) (i.castLE hr)).val).flatten →
        S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
        (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
        (∀ k ∈ [full 55,full 56,full 57], S.R k = []) →
        S.R (rootCut.castAdd T) = binSyms L cutoff →
        (∀ j : Fin (n+T), n ≤ j.val → S.L j = [] ∧ S.R j = []) →
        ∃ z F steps out, z.user = v.user ∧
          steps ≤ childBudget + overhead*(M^d*W) ∧
          Exec body (hostedGoodRecordAt cap full full (.inr i) prime r g hr) (mk v S) steps (mk z F) ∧ ready out F ∧ F.R (regs 27) = [] ∧
          (∀ j, (∀ i, shearPort i ≠ j) → (∀ i, ts i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
          ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev m) G (transform (diagonal inv) 1 x))
                 out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) := by
  intro body physical caller work apart placement ports cut
  obtain ⟨A,childRun⟩ := hostedOrdinaryChildDispatch_exec callerBank rootCut host aux separate body
  classical
  let recordPorts := GoodChildLayout.parent.trans (parentWithWeights.trans (callerBank.trans (Fin.castAddEmb T)))
  obtain ⟨overhead,parentBound⟩ := scheduledParentOverhead (U := U) recordPorts
  refine ⟨A,overhead,?_⟩
  intro node i w aligned r g parent W hW d M bank clean desc child eqn layout onTape full m hr cap machine regs headHost c h shearPort ts
    budget cutoff L cutFits widthFits recurse childBudget G minor idem B E factor weights inv inverse H J words stage parentWords ready
    v S word start empty invWords archive count pivots one clock scratch fresh cutWord privateFree
  let recordDesc : Descriptor := ⟨1,1,1,m,1,W⟩
  have outer := hostedGoodRecord_exec cap body full full (fun _ _ => rfl) recordDesc 1 (by change 1 < 2^1; decide) (.inr i) childBudget
    G g rfl hr minor idem B E factor weights inv inverse Shared50ModularControl.prime_prime H J
    (Nat.lt_size_self _) (Nat.lt_size_self _) hW [] [] [] [] [] SparseRoleCircuit.encode
    (fun _ => blank) (fun _ => blank) 0 0 (fun _ _ _ => rfl) v S word
    (by simpa only [List.append_nil] using start) empty (by simpa only [List.append_nil] using invWords)
    (by simpa only [List.append_nil] using archive) count (by simpa only [List.append_nil] using pivots)
    one clock scratch fresh (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨z,F,t,out,user,paid,run,done,blankPort,frame,effect⟩ := outer (by
    intro positive units u D before payload base width unitWord pos _ _ neg padded clockLen off
    let piv := fun j : Fin r => stage.M (j.castLE hr) (j.castLE hr)
    let pivot := pivotWeights hr weights inv inverse piv (fun j => stage.unit _ j.isLt)
    have cutSaved := off (rootCut.castAdd T) (fun j => (Fin.castAddEmb T).injective.ne (cutOffBank j))
    have freeD (j : Fin (n+T)) (hj : n ≤ j.val) : D.L j = [] ∧ D.R j = [] := by
      have kept := off j (fun i eq => by
        have val := congrArg Fin.val eq
        change (callerBank i).val = j.val at val
        have := (callerBank i).isLt
        omega)
      exact ⟨kept.1.trans (privateFree j hj).1,kept.2.trans (privateFree j hj).2⟩
    obtain ⟨z,F,t,after,user,run,paid,action,returned,frame⟩ := childRun node i w aligned hW u D before (.inl root) budget cutoff L pivot
      pos neg cutFits widthFits (cutSaved.2.trans cutWord) recurse base width unitWord padded clockLen freeD payload
    refine ⟨z,F,t,after,user,Nat.le_floor paid,run,?_,frame,returned⟩
    exact action)
  exact ⟨z,F,t,out,user,paid.trans (parentBound ⟨r,(nodeChildren5_le i).trans_lt (by decide)⟩ w W childBudget hW),run,by simpa only [List.append_nil] using done,blankPort,frame,effect⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
