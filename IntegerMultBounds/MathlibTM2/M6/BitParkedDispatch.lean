module

public import IntegerMultBounds.MathlibTM2.M6.BitParkedLeaf
public import IntegerMultBounds.MathlibTM2.M6.BitChartCutoff

/-! Width-based selection of a recursive entry or a stopped sweep over the parked owner rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

theorem parkedRowDispatch [M8.Machine.Net] {c T Q : ℕ} {P U : Type}
    (fan : Fin (c+2) ↪ Fin T) (fields : Fin 6 → Fin T) (hf : ∀ i j, fan i ≠ fields j)
    (capacity : columnCapacity ≤ Q) (rank : ℕ) :
    let work := LeafCore.small
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let full := withHelperPort (fan.trans ext)
    let place := parkedLeafPlace T work
    ∀ (cmp : Fin 10 ↪ Fin ((T+work)+1)) (entry : P),
    ∃ code : Pr P ((T+work)+1) Q prime U, ∀ body (lane : Descriptor) (w L cutoff budget : ℕ),
      (w+1)*rank = lane.width → cutoff < 2^L → lane.width.size ≤ L →
      ∀ (data : Fin c → Fin (volume prime lane) → ZMod 2) helper u S, 0 < volume prime lane →
      HelperFan full (Fin.lastCases helper data) S →
      (lane.width ≤ cutoff → ∀ i : Fin 6, S.R (place ((fields i).succ.castAdd work)) = (Routines.hdr lane i).map bitSymbol) →
      (lane.width ≤ cutoff → ∀ j : Fin work, let t := place (j.natAdd (T+1))
        S.L t = [] ∧ S.R t = []) →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L cutoff →
      (∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = []) →
      let result := fun F : Stacks ((T+work)+1) prime => HelperFan ((fan.trans ext).trans (Fin.succEmb _)) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        ∀ j, (∀ k, full k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j
      (cutoff < lane.width → ∀ z, ∃ y F t, Exec body (body entry) (mk z S) t (mk y F) ∧
        t ≤ budget ∧ y.user = z.user ∧ result F) →
      ∃ y F t, Exec body code (mk u S) t (mk y F) ∧ y.user = u.user ∧ result F ∧
        (t : ℝ) ≤ (4*w+23*lane.width+22*L+51 : ℕ) +
          (if cutoff < lane.width then (budget : ℝ)+2 else c*stoppedRowCost lane+1) := by
  intro work ext full place cmp entry
  obtain ⟨leaf,stop⟩ := parkedLeafRows (P := P) (U := U) fan fields hf capacity
  refine ⟨(ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) (.call entry) leaf),?_⟩
  intro body lane w L cutoff budget scaled cutFits fits data helper u S pos live hdr free clock word clear result recur
  rw [← scaled] at fits
  have dispatch := chartCutoff_exec body cmp rank w L cutoff cutFits fits (.call entry) leaf u S
    clock word clear result (if cutoff < lane.width then (budget : ℝ)+2 else c*stoppedRowCost lane+1)
  rw [scaled] at dispatch
  obtain ⟨y,F,t,user,paid,run,out⟩ := dispatch (by
    intro z
    by_cases active : cutoff < lane.width
    · simp only [if_pos active]
      obtain ⟨y,F,t,exec,paid,user,out⟩ := recur active z
      exact ⟨y,F,t+2,user,by exact_mod_cast Nat.add_le_add_right paid 2,Exec.call exec,out⟩
    · simp only [if_neg active]
      obtain ⟨y,F,t,exec,paid,user,out,frame⟩ := stop body lane data helper z S pos live (hdr (Nat.le_of_not_gt active)) (free (Nat.le_of_not_gt active))
      refine ⟨y,F,t,user,paid,exec,?_,fun j off => frame j (fun r => off (r.castSucc.castAdd 2))⟩
      exact returnedRowFan (fan.trans ext) _ _ F out)
  exact ⟨y,F,t,run,user,out,paid⟩

theorem parkedMoveDispatch [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (fields : Fin 6 → Fin T) (hs : ∀ i j, saved i ≠ fields j) (hf : ∀ i j, fan i ≠ fields j)
    (rank : ℕ) (capacity : columnCapacity ≤ Q)
    (splitCapacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let work := LeafCore.small
    let H := (T+work)+1
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    let full := withHelperPort (fan.trans ext)
    ∀ (cmp : Fin 10 ↪ Fin H), (∀ i j, bank i ≠ cmp j) → ∀ active : P,
    ∃ dispatch : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (entry : P), body entry = dispatch →
    ∃ code : Pr P H Q prime U, ∀ (lane : Descriptor) (w L cutoff budget : ℕ),
      (w+1)*rank = lane.width → cutoff < 2^L → lane.width.size ≤ L →
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime), 0 < m →
      S.R (ext (saved 0)).succ = List.ofFn (fun i : Fin (m*142080) => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (lane.width ≤ cutoff → ∀ i : Fin 6, S.R (ext (fields i)).succ = (Routines.hdr lane i).map bitSymbol) →
      (lane.width ≤ cutoff → ∀ j : Fin work, let t := place (j.natAdd (T+1)); S.L t = [] ∧ S.R t = []) →
      (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L cutoff →
      (∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = []) →
      let data := fun (r : Fin 142080) (i : Fin m) => x ((finProdFinEquiv (i,r)).cast size)
      let rows := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      (cutoff < lane.width → ∀ v D, HelperFan full (Fin.lastCases (fun _ => 0) data) D →
        (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F n, Exec body (body active) (mk v D) n (mk z F) ∧ n ≤ budget ∧ z.user = v.user ∧
          HelperFan ((fan.trans ext).trans (Fin.succEmb _)) rows F ∧
          ∀ j, (∀ k, full k ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) →
      let price := (4*w+23*lane.width+22*L+51 : ℕ) +
        (if cutoff < lane.width then (budget : ℝ)+2 else 142080*stoppedRowCost lane+1)
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        t ≤ ⌊price⌋₊+(298*(intervalSplitTapes+5)+37)*volume prime wide ∧
        z.user = u.user ∧ RecordPayload (ext (saved 0)).succ (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work H ext bank place full cmp outside active
  obtain ⟨dispatch,child⟩ := parkedRowDispatch (P := P) (U := U) fan fields hf capacity rank cmp active
  refine ⟨dispatch,?_⟩
  intro body entry installed
  have separate i j := ext.injective.ne (apart i j)
  obtain ⟨wrap,run⟩ := parkedMoveTranspose body (saved.trans ext) (fan.trans ext) separate (fan.trans ext) separate splitCapacity
  refine ⟨wrap entry,?_⟩
  intro lane w L cutoff budget scaled cutFits fits m wide size x u S pos source left empty headers free clock cut clear data rows recur price
  obtain ⟨z,F,t,exec,paid,user,out,frame⟩ := run entry ⌊price⌋₊ lane x u S pos source left empty (by
    intro v D live off
    have cmpRight (i) := (off (cmp i) (fun j => outside j i)).2
    have ready (small : lane.width ≤ cutoff) :=
      parkedLeafReady saved fan apart fields hs hf lane S D ⟨headers small,free small⟩ off
    obtain ⟨z,F,n,exec,user,⟨out,keep⟩,paid⟩ := child body lane w L cutoff budget scaled cutFits fits
      data (fun _ => 0) v D pos live (fun small => (ready small).1) (fun small => (ready small).2)
      (by rw [cmpRight]; exact clock) ((cmpRight 1).trans cut) (fun i hi => (cmpRight i).trans (clear i hi))
      (fun large z => recur large z D live off)
    refine ⟨z,F,n,installed ▸ exec,Nat.le_floor paid,user,out,?_,?_⟩
    · intro j
      exact keep _ (withHelperPort_avoids (fan.trans ext) _ (fun i => (separate j i).symm))
    · intro j outside _
      apply keep
      intro r
      have ports := DFunLike.congr_fun (ownerSplitBank_fan (saved.trans ext) (fan.trans ext) separate)
        r
      exact ports ▸ outside _)
  exact ⟨z,F,t,exec,paid,user,out,fun j off => frame j off (mergeOutside _ _ separate j off)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
