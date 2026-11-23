module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperFanRun

/-! Transpose the stopped PR589 rows with a single shared directory leaf. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

noncomputable def stoppedRowCost [M8.Machine.Net] (lane : Descriptor) : ℝ :=
  descriptorHeaderCost lane +
    ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
    ((volume prime lane : ℝ)*((max 1 lane.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)

theorem stoppedOwnerRows [M8.Machine.Net] {k n Q : ℕ} {P U : Type}
    (fan : Fin (k+2) ↪ Fin n) (src : Fin 6 → Fin n)
    (apart : ∀ i (r : Fin k), src i ≠ fan (r.castAdd 2)) (capacity : columnCapacity ≤ Q)
    (rs : List (Fin k)) (distinct : rs.Nodup) :
    let full := fan.trans (Fin.castAddEmb LeafCore.small)
    ∃ code : Pr P (n+LeafCore.small) Q prime U, ∀ body (lane : Descriptor),
      let cost := stoppedRowCost lane
      ∀ (data : Fin k → Fin (volume prime lane) → ZMod 2) u S, 0 < volume prime lane →
      HelperFan full data S →
      (∀ i, S.R ((src i).castAdd LeafCore.small) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ rs.length*cost+1 ∧
        z.user = u.user ∧ HelperFan full (fun r => if r ∈ rs then
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) else data r) F ∧
        ∀ j, (∀ r ∈ rs, full (r.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro full
  induction rs with
  | nil =>
    refine ⟨.act .done,?_⟩
    intro body lane cost data u S _ rep _ _
    exact ⟨u,S,1,Exec.act ..,by simp,rfl,by simpa using rep,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons r rs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp distinct
    obtain ⟨tail,run⟩ := ih rest
    let port := fan (r.castAdd 2)
    refine ⟨(hostedStoppedDirectory capacity src port).seq tail,?_⟩
    intro body lane cost data u S positive rep headers free
    obtain ⟨v,D,a,user,step,paid,out,_,keep,clean⟩ := hostedStoppedView_exec capacity body src port
      lane (data r) u S positive headers (fanPayload rep r) free
    have off (j) (ne : j ≠ full (r.castAdd 2)) : D.L j = S.L j ∧ D.R j = S.R j := by
      revert ne
      refine Fin.addCases (fun i ne => keep i (fun eq => ne (congrArg (Fin.castAddEmb LeafCore.small) eq)))
        (fun i _ => ⟨(clean i).1.trans (free i).1.symm,(clean i).2.trans (free i).2.symm⟩) j
    let next := Function.update data r (Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r))
    have live : HelperFan full next D := fanUpdate r _ rep out (fun i ne => off _ (full.injective.ne ne))
    obtain ⟨z,F,b,exec,bill,same,done,frame⟩ := run body lane next v D positive live
      (fun i => ((keep _ (apart i r)).2).trans (headers i)) clean
    refine ⟨z,F,_,step.seq exec,?_,same.trans user,?_,?_⟩
    · change (a : ℝ) ≤ cost at paid
      simp only [Nat.cast_add,List.length_cons,Nat.cast_one,add_mul,one_mul]
      linarith
    · convert done using 2
      rename_i i
      by_cases eq : i = r
      · subst i
        simp [next,fresh]
      · simp [next,eq,Function.update_of_ne]
    · intro j outside
      have h := frame j (fun i hi => outside i (List.mem_cons_of_mem _ hi))
      have g := off j (outside r List.mem_cons_self).symm
      exact ⟨h.1.trans g.1,h.2.trans g.2⟩

theorem stoppedMoveRows [M8.Machine.Net] {k n Q : ℕ} {P U : Type}
    (fan : Fin ((k+1)+2) ↪ Fin n) (src : Fin 6 → Fin n)
    (apart : ∀ i (r : Fin (k+1)), src i ≠ fan (r.castAdd 2)) (capacity : columnCapacity ≤ Q) :
    let full := fan.trans (Fin.castAddEmb LeafCore.small)
    ∃ code : Pr P (n+LeafCore.small) Q prime U, ∀ body (lane : Descriptor),
      let cost := stoppedRowCost lane
      ∀ (data : Fin k → Fin (volume prime lane) → ZMod 2) (helper : Fin (volume prime lane) → ZMod 2) u S, 0 < volume prime lane →
      HelperFan full (Fin.lastCases helper data) S →
      (∀ i, S.R ((src i).castAdd LeafCore.small) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ k*cost+1 ∧
        z.user = u.user ∧ HelperFan full (Fin.lastCases helper (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r))) F ∧
        ∀ j, (∀ r : Fin k, full (r.castSucc.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro full
  let rs := List.ofFn (Fin.castSucc : Fin k → Fin (k+1))
  obtain ⟨code,run⟩ := stoppedOwnerRows (P := P) (U := U) fan src apart capacity rs
    (List.nodup_ofFn.mpr (Fin.castSucc_injective k))
  refine ⟨code,?_⟩
  intro body lane cost data helper u S positive live headers free
  obtain ⟨z,F,t,exec,paid,user,out,frame⟩ := run body lane (Fin.lastCases helper data) u S positive live headers free
  refine ⟨z,F,t,exec,by simpa only [rs,List.length_ofFn] using paid,user,?_,?_⟩
  · convert out using 2
    rename_i r
    induction r using Fin.lastCases with
    | last => simp [rs,List.mem_ofFn]
    | cast r => simp [rs,List.mem_ofFn]
  · intro j off
    apply frame j
    intro i hi
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hi
    exact off r

theorem placedStoppedMoveRows [M8.Machine.Net] {k n T Q : ℕ} {P U : Type}
    (fan : Fin ((k+1)+2) ↪ Fin n) (src : Fin 6 → Fin n)
    (apart : ∀ i (r : Fin (k+1)), src i ≠ fan (r.castAdd 2)) (capacity : columnCapacity ≤ Q)
    (place : Fin (n+LeafCore.small) ↪ Fin T) :
    let full := (fan.trans (Fin.castAddEmb LeafCore.small)).trans place
    ∃ code : Pr P T Q prime U, ∀ body (lane : Descriptor),
      let cost := stoppedRowCost lane
      ∀ (data : Fin k → Fin (volume prime lane) → ZMod 2) (helper : Fin (volume prime lane) → ZMod 2) u S, 0 < volume prime lane →
      HelperFan full (Fin.lastCases helper data) S →
      (∀ i, S.R (place ((src i).castAdd LeafCore.small)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin LeafCore.small, S.L (place (j.natAdd n)) = [] ∧ S.R (place (j.natAdd n)) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ k*cost+1 ∧
        z.user = u.user ∧ HelperFan full (Fin.lastCases helper (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r))) F ∧
        ∀ j, (∀ r : Fin k, full (r.castSucc.castAdd 2) ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro full
  obtain ⟨code,run⟩ := stoppedMoveRows (P := Empty) (U := U) fan src apart capacity
  refine ⟨embProg place Empty.elim code,?_⟩
  intro body lane cost data helper u S pos live headers free
  obtain ⟨v,D,t,exec,paid,user,out,keep⟩ := run Empty.elim lane data helper (embDn place u)
    (embStk place S) pos live headers free
  obtain ⟨z,F,lifted,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    place.injective (fun e => nomatch e) exec u rfl S rfl
  refine ⟨z,F,t,lifted,paid,same.trans user,?_,?_⟩
  · rw [← view] at out
    exact out
  · intro j off
    by_cases inside : ∃ i, place i = j
    · obtain ⟨i,rfl⟩ := inside
      rw [← view] at keep
      exact keep i (fun r eq => off r (congrArg place eq))
    · exact frame j (fun i eq => inside ⟨i,eq⟩)

end IntegerMultBounds.MathlibTM2.M6.BitNode
