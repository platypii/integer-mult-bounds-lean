module

public import IntegerMultBounds.MathlibTM2.M8.Machine.CallExecutionWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.Budget
public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeBoundary

/-! Bounded node assembly reuses the existing linear phase runs. The split's
actual head travel bounds every later data bank, whose parked heads are shared. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecutionWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (commonCount implementation widthSlot pcStack)
open BaseExecution (entryConfig)
open NodeExecution
open PieceExecution (dataBank actualCallBound overhead)
open NodeLayout (wires mergeRoute tempOps)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveViewedAction (Data)
open RecursiveRowsSerialization (sourceData roleData)
open SharedBankStageInput (raw)
variable {k b : ℕ} {v : Descriptor}

def Calls (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=Machine.width*b)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (C D : ℕ) (lo hi : ℤ) : Prop :=
  ∀ (site : Site) w i j, pieces[site] = .call w i j →
    ∀ data : Data payloadCount v, BinaryInvariant.Ready data →
    (∀ z, lo+(PieceExecution.callReserve D k w i j*volume prime v : ℕ) ≤
      (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
      (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z+
        (PieceExecution.callReserve D k w i j*volume prime v : ℕ) ≤ hi) →
      ∃ n ≤ actualCallBound (v := v) k C w i j,
        RunWithin (Control.program capacity widthSlot pcStack (implementation k))
          (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
          (entryConfig capacity (.piece site) (dataBank hs f p node st data))
        (entryConfig capacity (successor site) (dataBank hs f p node st
          (ChildPermutation.child hw w i j data)))

theorem split_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=Machine.width*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C D : ℕ) (lo hi : ℤ)
    (hD : 2*(Budget.base k+Budget.node k) ≤ D)
    (hold : ∀ j, (old j).length ≤ 2*volume prime v)
    (hrole : 2*volume prime (role v roleCount) ≤ volume prime v)
    (hbank : ∀ j, lo+(D*volume prime v : ℕ) ≤
      (raw (dataBank hs f p node
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
        (sourceData wires (encoded x))) (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw (dataBank hs f p node
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
        (sourceData wires (encoded x))) (tapeCount capacity widthSlot pcStack (implementation k))).head j+
        (D*volume prime v : ℕ) ≤ hi)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C D lo hi) :
    ∃ steps ≤ (entryCoefficient+exitCoefficient)*volume prime v+
        scheduleCoefficient k*volume prime (role v roleCount)+
        (Net.net).rankSum*C+RecursiveChildCallReturn.cost old hs+k+7,
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) steps
        (entryConfig capacity .split (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (sourceData wires (encoded x))))
        (entryConfig capacity target (dataBank old f p node st
          (sourceData wires (encoded (transpose (one_dvd _) x))))) := by
  let saved := RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))
  let nodeSaved := RecursiveViewFrame.savedStack hs node
  have hpRole := RecursiveRowsNodeLayout.role_positive roleCount v roleCount_pos hp hdiv
  obtain ⟨rs,hrs,ne,hne,hre⟩ := entry_run capacity hp hdiv hs hv f p node saved (encoded x)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hR := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le _ hpRole
  have hRle : volume prime (role v roleCount) ≤ volume prime v := by omega
  have hcoeff := hD
  dsimp only [Budget.node,scheduleCoefficient,tempCoefficient] at hcoeff
  have hentry : ne ≤ (entryCoefficient+1)*volume prime v := by
    have := Nat.mul_le_mul_left (entryCoefficient+1) hV
    nlinarith only [hne,hV]
  let reduced : Fin 6 → List Bool := RecursiveRowsNodeHeaders.headers hs rs
  have hnode (L : ℕ) (hL : ne+L ≤ D*volume prime v)
      (data : Data payloadCount (role v roleCount)) :
      ∀ j, lo+L ≤ (raw (dataBank reduced f p nodeSaved saved data)
        (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
        (raw (dataBank reduced f p nodeSaved saved data)
          (tapeCount capacity widthSlot pcStack (implementation k))).head j+L ≤ hi := by
    intro j
    rw [PieceExecution.dataBank_head_eq reduced f p nodeSaved saved _ data
      (roleData wires (Equiv.refl _) hdiv (encoded x))]
    have hh := run_head_travel hre j
    change (raw (dataBank hs f p node saved (sourceData wires (encoded x))) _).head j-(ne : ℕ) ≤
      (raw (dataBank reduced f p nodeSaved saved (roleData wires (Equiv.refl _) hdiv (encoded x))) _).head j ∧
      (raw (dataBank reduced f p nodeSaved saved (roleData wires (Equiv.refl _) hdiv (encoded x))) _).head j ≤
        (raw (dataBank hs f p node saved (sourceData wires (encoded x))) _).head j+(ne : ℕ) at hh
    have hm := hbank j
    dsimp only [saved] at hh ⊢
    omega
  have hsum (site : Site) : overhead k pieces[site] ≤ (pieces.map (overhead k)).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨pieces[site],List.getElem_mem site.isLt,rfl⟩)
  obtain ⟨ni,hni,hri⟩ := tempInit_run capacity (v := role v roleCount) hpRole reduced hrs f p
    nodeSaved saved (roleData wires (Equiv.refl _) hdiv (encoded x))
  rw [NodeData.init_encoded] at hri
  have hiBudget : ne+(RoleOpsClean.coefficient (tempOps (SparseRoleCircuit.encode (a := 0) 0))*
      volume prime (role v roleCount)+1) ≤ D*volume prime v := by
    have hb := Nat.mul_le_mul_right (volume prime v)
      (show entryCoefficient+1+RoleOpsClean.coefficient (tempOps (SparseRoleCircuit.encode (a := 0) 0))+1 ≤ D by omega)
    have hr := Nat.mul_le_mul_left (RoleOpsClean.coefficient (tempOps (SparseRoleCircuit.encode (a := 0) 0))) hRle
    nlinarith only [hb,hr,hentry,hV]
  have hwi := RunWithin.heads_of_run_le hri hni lo hi (hnode _ hiBudget _)
  have hwe := RunWithin.heads_of_run_le hre hne lo hi (by
    intro j
    have h := hbank j
    have hb := Nat.mul_le_mul_right (volume prime v) (show entryCoefficient+1 ≤ D by omega)
    change lo+(entryCoefficient*volume prime v+1 : ℕ) ≤
      (raw (dataBank hs f p node saved (sourceData wires (encoded x))) _).head j ∧
      (raw (dataBank hs f p node saved (sourceData wires (encoded x))) _).head j+
        (entryCoefficient*volume prime v+1 : ℕ) ≤ hi
    dsimp only [saved]
    rw [Nat.add_mul,Nat.one_mul] at hb
    omega)
  have hsBudget : ne+(pieces.map (overhead k)).sum*volume prime (role v roleCount) ≤
      D*volume prime v := by
    have hb := Nat.mul_le_mul_right (volume prime v)
      (show entryCoefficient+1+(pieces.map (overhead k)).sum ≤ D by omega)
    have hr := Nat.mul_le_mul_left ((pieces.map (overhead k)).sum) hRle
    nlinarith only [hb,hr,hentry]
  have hcalls := calls rs hrs
  have hcallMargin (w : Wire) (i j : Fin Machine.width) (site : Site) (hic : pieces[site] = .call w i j) :
      ne+PieceExecution.callReserve D k w i j*volume prime (role v roleCount) ≤ D*volume prime v := by
    have hc := hsum site
    rw [hic] at hc
    have hb := PieceExecution.callReserve_shrink D (entryCoefficient+1)
      (2*(pieces.map (overhead k)).sum) (volume prime v) (volume prime (role v roleCount)) k w i j
      (by omega) hrole (by omega)
    omega
  obtain ⟨ns,hns,hrsched⟩ := PieceExecution.schedule_run_within capacity
    (v := role v roleCount) hw (ChildPermutation.child hw) hpRole reduced hrs f p nodeSaved saved
    BinaryInvariant.Ready
    (fun piece data hd => BinaryInvariant.step (v := role v roleCount) hw _ (ChildPermutation.child_spec (v := role v roleCount) hw) piece data hd)
    (actualCallBound (v := role v roleCount) k C) ((pieces.map (overhead k)).sum) hsum lo hi
    (fun data _ => hnode _ hsBudget data)
    (fun site w i j hic data hd => hcalls site w i j hic data hd (hnode _ (hcallMargin w i j site hic) data))
    (encodedBits (NodeData.splitWire hdiv x) (fun _ => blank)) (BinaryInvariant.of_encoded _)
  have hns' := hns.trans (PieceExecution.bound_fixed (v := role v roleCount) k C hR)
  obtain ⟨nc,hnc,hrc⟩ := tempClear_run capacity (v := role v roleCount) hpRole reduced hrs f p
    nodeSaved saved (Transport.run hw (ChildPermutation.child hw) pieces
      (encodedBits (NodeData.splitWire hdiv x) (fun _ => blank)))
  rw [NodeData.clear_network hw hdiv _ (ChildPermutation.child_spec (v := role v roleCount) hw) x] at hrc
  obtain ⟨nm,hnm,hrm⟩ := merge_run capacity hp hdiv hs reduced hv hrs f p node saved hn
    (transpose hdiv (encoded x))
  obtain ⟨nr,hnr,hrr⟩ := restore_return capacity target
    (RecursiveRoleSerialization.roles (sourceData wires (transpose hdiv (encoded x))))
    old hs f p node st hd hpc
  have hout : transpose hdiv (encoded x) = encoded (transpose (one_dvd _) x) := by
    rw [Shared50RecursiveChildPermutation.transpose_independent roleCount_pos (by decide : 0 < 1)
      hdiv (one_dvd _)]
    rfl
  have hret := Budget.return_cost_bound (volume prime v) hV old hs hold
    (RecursiveRowsNode.header_length v hp hs hv)
  have htail := join (join hrc hrm) hrr
  have htBound : nc+nm+nr ≤
      (exitCoefficient+RoleOpsClean.coefficient (tempOps blank)+127+k+5)*volume prime v := by
    have hr := Nat.mul_le_mul_left (RoleOpsClean.coefficient (tempOps blank)) hRle
    have hk := Nat.mul_le_mul_left (k+5) hV
    nlinarith only [hnc,hnm,hnr,hret,hr,hk]
  have htBudget : ne+(exitCoefficient+RoleOpsClean.coefficient (tempOps blank)+127+k+5)*volume prime v ≤
      D*volume prime v := by
    have hb := Nat.mul_le_mul_right (volume prime v)
      (show entryCoefficient+1+(exitCoefficient+RoleOpsClean.coefficient (tempOps blank)+127+k+5) ≤ D by omega)
    nlinarith only [hb,hentry]
  have hwt := RunWithin.heads_of_run_le htail htBound lo hi (hnode _ htBudget _)
  refine ⟨ne+ni+ns+nc+nm+nr, ?_, ?_⟩
  · exact assembly_bound hne hni hns' hnc hnm hnr
  · have h := ((hwe.trans hwi).trans hrsched).trans hwt
    have heq : ne+ni+ns+nc+nm+nr = (ne+ni+ns)+(nc+nm+nr) := by omega
    rw [hout] at h
    rw [heq]
    exact h

theorem guard_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=Machine.width*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C D : ℕ) (lo hi : ℤ)
    (hD : 2*(Budget.base k+Budget.node k) ≤ D)
    (hold : ∀ j, (old j).length ≤ 2*volume prime v)
    (hrole : 2*volume prime (role v roleCount) ≤ volume prime v)
    (hbank : ∀ j, lo+(D*volume prime v : ℕ) ≤
      (raw (dataBank hs f p node
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
        (sourceData wires (encoded x))) (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw (dataBank hs f p node
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
        (sourceData wires (encoded x))) (tapeCount capacity widthSlot pcStack (implementation k))).head j+
        (D*volume prime v : ℕ) ≤ hi)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C D lo hi) :
    ∃ steps ≤ (entryCoefficient+exitCoefficient)*volume prime v+
        scheduleCoefficient k*volume prime (role v roleCount)+
        (Net.net).rankSum*C+RecursiveChildCallReturn.cost old hs+k+10,
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) steps
        (entryConfig capacity .guard (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (sourceData wires (encoded x))))
        (entryConfig capacity target (dataBank old f p node st
          (sourceData wires (encoded (transpose (one_dvd _) x))))) := by
  let before := dataBank hs f p node
    (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
    (sourceData wires (encoded x))
  obtain ⟨ng,hng,hg⟩ := Execution.guard_jump capacity widthSlot pcStack
    (implementation k) before (hs 3) (BankFacts.bank_header _ _ _ _ _ _ _ _ 3).1
    ((BankFacts.bank_header _ _ _ _ _ _ _ _ 3).2.trans
      (BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 3)).symm) (hv.2 3)
  have hbranch : Execution.branch (Counter.value (hs 3)) = PC.split := by
    unfold Execution.branch
    have hh : Counter.value (hs 3) = v.width := hv.1 3
    have hne : Counter.value (hs 3) ≠ 1 := by
      rw [hh, hw]
      intro h1
      have := two_le_width
      have := Nat.eq_one_of_mul_eq_one_right h1
      omega
    rw [ite_eq_right hne]
  rw [hbranch] at hg
  change Machine.run _ ng (entryConfig capacity .guard before) = some (entryConfig capacity .split before) at hg
  obtain ⟨nn,hnn,hr⟩ := split_return capacity target hw hp hdiv old hs hv f p node st hn hd hpc x C D lo hi hD hold hrole hbank calls
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hcoeff := hD
  dsimp only [Budget.node,scheduleCoefficient,tempCoefficient] at hcoeff
  have hbudget : 3 ≤ D*volume prime v := by
    have hc : 3 ≤ D := by omega
    nlinarith only [hc,hV]
  have hwg := RunWithin.heads_of_run_le hg hng lo hi (by
    intro j
    change lo+(3 : ℕ) ≤ (raw before _).head j ∧ (raw before _).head j+(3 : ℕ) ≤ hi
    dsimp only [before]
    have hm := hbank j
    omega)
  exact ⟨ng+nn,guard_assembly_bound hng hnn,hwg.trans hr⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecutionWithin
