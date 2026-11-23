module

public import IntegerMultBounds.MathlibTM2.M6.BitGeneratedIntervalCaller
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleCall
public import IntegerMultBounds.MathlibTM2.M6.BitChartCutoff

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout IntervalDescriptor
open Shared50ModularControl (prime)

private theorem physicalPositions {child wide full : Descriptor} {V : ℕ} (shape : wide = full)
    (size : volume prime full = V) (p : Fin (volume prime child) ≃ Fin V)
    (coords : InheritedIntervalPositions child full size p) :
    ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide), InheritedIntervalPositions child wide rfl position := by
  subst full
  subst V
  exact ⟨p,coords⟩

/-- Each idle directory occurrence runs its fixed interval program at the scheduled
child width and volume. The program is selected before the parent dimensions. -/
theorem scheduledIdleInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ (i : Fin 9) (j : Fin idleCopies.length), ∃ code : Pr Unit (72+N) Q prime U,
    ∀ (node : Descriptor) (a groups : ℕ), 0 < a → node.width = 64*a →
      node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let M := prime^a
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      let child := scheduledChild prime node (idleDirectoryIndex (i,j))
      0 < W → ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide),
      child.width < node.width ∧ InheritedIntervalPositions child wide rfl position ∧
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        t ≤ ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ ∧
        z.user = u.user ∧ RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        ∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,body,pos,build⟩ := generatedStoppedInterval (U := U) capacity mergeCap
  refine ⟨C,N,body,pos,?_⟩
  intro bank i j
  let e := idleInterval i idleCopies[j.val].2
  have rank := (nodeChildren5_bounds (idleDirectoryIndex (i,j))).1
  change 0 < nodeChildren5.get (idleDirectoryIndex (i,j)) at rank
  rw [idleDirectoryIndex_rank] at rank
  change 0 < e.2-e.1 at rank
  have ordered : e.1 < e.2 := by omega
  have fits := Nat.succ_le_succ (idleBounds i idleCopies[j.val].2).2
  obtain ⟨code,run⟩ := build (e.1+1) (e.2+1) (Nat.succ_lt_succ ordered) fits
  refine ⟨code,?_⟩
  intro node a groups live width split W M _ lane wide child positive
  let full := phaseIntervalChild (e.1+1) (e.2+1) a (W*142080) 64
  have shape : wide = full := by simp only [wide,lane,full,phaseIntervalChild,Nat.mul_assoc]; rfl
  have spectator : node.beforeRows*(142080*groups)*node.beforeH*node.between*node.afterD = W*142080 := by
    dsimp only [W]; ac_rfl
  have scheduled := idleChildPositions_offset node i j a (142080*groups) 1 fits live width split
  dsimp only at scheduled
  rw [spectator] at scheduled
  obtain ⟨p,same,smaller,coords⟩ := scheduled
  obtain ⟨position,inherited⟩ := physicalPositions shape _ p coords
  exact ⟨position,smaller,inherited,run a W live positive child position inherited same⟩

/-- Compare the scheduled rank width at runtime and charge only the selected child. -/
theorem scheduledIdleDispatch [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (body : Unit → Pr Unit (72+N) Q prime U), 0 ≤ C ∧
    let bank := Fin.castAddEmb N (n := 72)
    ∀ (i : Fin 9) (j : Fin idleCopies.length) (cmp : Fin 10 ↪ Fin (72+N)) (large : Pr Unit (72+N) Q prime U), ∃ code : Pr Unit (72+N) Q prime U,
    ∀ (node : Descriptor) (w groups : ℕ), let a := w+1
      node.width = 64*a →
      node.rows = 142080*(142080*groups) →
      let W := node.beforeRows*groups*node.beforeH*node.between*node.afterD
      let M := prime^a
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) a W 64
      let wide := {lane with afterD := lane.afterD*142080}
      let child := scheduledChild prime node (idleDirectoryIndex (i,j))
      0 < W → ∃ position : Fin (volume prime child) ≃ Fin (volume prime wide),
      child.width < node.width ∧ InheritedIntervalPositions child wide rfl position ∧
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      S.R (bank 2) = binSyms M.size M → S.R (bank 28) = binSyms 1 1 →
      S.R (bank 53) = binSyms W.size W → (S.R (bank 71)).length = a →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (bank i) = []) →
      RecordPayload (bank 24) (fun _ => blank) 0 word S → S.L (bank 59) = [] →
      (∀ i, S.L (bank (descriptorPorts i)) = [] ∧ S.R (bank (descriptorPorts i)) = []) →
      (∀ j : Fin N, S.L (j.natAdd 72) = [] ∧ S.R (j.natAdd 72) = []) →
      ∀ L cutoff recursiveBudget : ℕ, cutoff < 2^L → child.width.size ≤ L →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L cutoff →
      (∀ k : Fin 10, 2 ≤ k.val → S.R (cmp k) = []) →
      let result := fun F => ∃ changed, RecordPayload (bank 24) (fun _ => blank) 0 changed F ∧
        (∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k) ∧
        ∀ k, k ≠ bank 24 → F.L k = S.L k ∧ F.R k = S.R k
      (cutoff < child.width → ∀ v, ∃ z F t, Exec body large (mk v S) t (mk z F) ∧
        t ≤ recursiveBudget ∧ z.user = v.user ∧ result F) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ result F ∧
        t ≤ (4*w+23*child.width+22*L+51) + if cutoff < child.width then recursiveBudget
          else ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊ := by
  obtain ⟨C,N,body,pos,build⟩ := scheduledIdleInterval (U := U) capacity mergeCap
  refine ⟨C,N,body,pos,?_⟩
  intro bank i j cmp large
  obtain ⟨leaf,run⟩ := build i j
  let k := idleDirectoryIndex (i,j)
  let rank := nodeChildren5.get k
  refine ⟨(ordinaryCutoffTest cmp rank).seq (.cond (fun s => symBit (s.scan (cmp 7))) large leaf),?_⟩
  intro node w groups a width split W M e lane wide child positive
  obtain ⟨position,smaller,coords,execute⟩ := run node a groups (Nat.succ_pos _) width split positive
  refine ⟨position,smaller,coords,?_⟩
  intro word u S base unit suffix atom scratch payload left headers unused L cutoff recursiveBudget cut fits clock stored free result recurse
  have scaled : (w+1)*rank = child.width := by
    change _ = rank*(node.width/64)
    rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  let budget := if cutoff < child.width then recursiveBudget else
    ⌊C*(child.width : ℝ)^M8.Machine.BudgetBound.tau*volume prime child⌋₊
  have dispatch := chartCutoff_exec body cmp rank w L cutoff cut (scaled ▸ fits) large leaf u S clock stored free result (budget : ℝ)
  rw [scaled] at dispatch
  obtain ⟨z,F,t,same,paid,exec,out⟩ := dispatch (by
    intro v
    by_cases active : cutoff < child.width
    · obtain ⟨z,F,t,ran,time,user,out⟩ := recurse active v
      exact ⟨z,F,t,user,by simpa [budget,active] using (Nat.cast_le (α := ℝ)).mpr time,by simpa [active] using ran,out⟩
    · obtain ⟨z,F,t,y,ran,time,user,out,act,frame⟩ := execute word v S base unit suffix atom scratch payload left headers unused
      exact ⟨z,F,t,user,by simpa [budget,active] using (Nat.cast_le (α := ℝ)).mpr time,by simpa [active] using ran,y,out,act,frame⟩)
  exact ⟨z,F,t,exec,same,out,by exact_mod_cast paid⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
