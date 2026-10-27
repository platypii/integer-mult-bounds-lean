module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyProcessHaloLengthKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightFamilyLoop

/-! Counted execution of the cached halo classes, with one final page-family restore.
The exact ledger charges weight-page traversal by total cell volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

noncomputable def familyHaloLengthKeyStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 151 Q A U :=
  .seq (.act (.pop (.rt 127) (fun v _ => v) .done))
    (.seq (familyProcessHaloLengthKey hR hQ) (.act (peekR 127)))

noncomputable def familyHaloLengthKeyLoop (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 151 Q A U :=
  .seq (.loop (·.flag) (familyHaloLengthKeyStep hR hQ)) restoreWeightKeyFamily

/-- Add the owned count pop and next-count test to an actual cached class execution. -/
theorem familyHaloLengthKeyStep_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (v v' : HS 151 Q A U) (S T : Stacks 151 A) (c : Fin (A+4)) (cs : List (Fin (A+4)))
    (n : ℕ) (hcount : S.R 127 = c::cs) (hcount' : T.R 127 = cs)
    (he : Exec body (familyProcessHaloLengthKey hR hQ)
      (mk v {S with R := Function.update S.R 127 cs}) n (mk v' T)) :
    Exec body (familyHaloLengthKeyStep hR hQ) (mk v S) (n+2)
      (mk {v' with flag := cs.head?.isSome} T) := by
  have hpop : (.pop (.rt 127) (fun v : HS 151 Q A U => fun _ => v) .done : Act 151 Q A U).run
      (mk v S) = mk v {S with R := Function.update S.R 127 cs} := by
    simp [Action.run,update_rt,hcount]
  have hp := Exec.act (body := body) (peekR 127) (mk v' T)
  rw [peekR_run,hcount'] at hp
  exact (Exec.seq (hpop ▸ Exec.act (body := body) (.pop (.rt 127) (fun v _ => v) .done) _)
    (Exec.seq he hp)).cast (by omega) rfl

def familyHaloLengthKeyLoopCost (A p l s t u target rhsExp V a b : ℕ) (keys : List ℕ) : ℕ :=
  (keys.map (fun L => familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b+3)).sum+
    2*(weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b keys)).length+3

/-- A numerical invariant can be supplied per parsed class, before adding count
control. The resulting execution restores the complete family for the next pass. -/
theorem familyHaloLengthKeyLoop_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p l s t u target rhsExp V a b : ℕ)
    (ready : List ℕ → Stacks 151 A → Prop) (tail : List (Fin (A+4)))
    (hcount : ∀ keys S, ready keys S → S.R 127 = List.replicate keys.length tick)
    (hcall : ∀ L keys v S, ready (L::keys) S →
      S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
        (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b (L::keys))++tail →
      ∃ v' T n, v'.user = v.user ∧
        n ≤ familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b ∧
        Exec body (familyProcessHaloLengthKey hR hQ)
          (mk v {S with R := Function.update S.R 127 (List.replicate keys.length tick)}) n (mk v' T) ∧
        T.inp = S.inp ∧ T.out = S.out ∧ T.L = S.L ∧ ready keys T ∧
        T.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
          (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b keys)++tail ∧
        T.R 150 = (weightKeyPacket (batchWeightPage A (executionWidth p l target rhsExp)
          (executionPrecision p l target rhsExp) (2^15*p) s t u
          (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L
          (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val))).reverse++S.R 150)
    (keys : List ℕ) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hready : ready keys S)
    (hsource : S.R 148 = weightKeyFamily (haloWeightKeyPages A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u (PhaseCellBand.width p u) a b keys)++tail)
    (hcomplete : S.R 150 = []) (hflag : v.flag = keys.head?.isSome) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ familyHaloLengthKeyLoopCost A p l s t u target rhsExp V a b keys ∧
      Exec body (familyHaloLengthKeyLoop hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R 148 = S.R 148 ∧ S'.R 150 = [] ∧
      ∃ T : Stacks 151 A, ready [] T ∧
        ∀ i : Fin 151, i ≠ 148 → i ≠ 150 → S'.R i = T.R i := by
  let page := fun L => batchWeightPage A (executionWidth p l target rhsExp)
    (executionPrecision p l target rhsExp) (2^15*p) s t u
    (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L
    (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val)
  apply weightFamilyLoop_restore_exec (familyHaloLengthKeyStep hR hQ) page
    (fun L => familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b+2)
    ready tail ?_ keys v S hready hsource hcomplete hflag
  intro L keys v S hr hs
  obtain ⟨v',T,n,hu,hn,he,hi,ho,hl,hr',hs',hc⟩ := hcall L keys v S hr hs
  refine ⟨{v' with flag := (List.replicate keys.length (tick : Fin (A+4))).head?.isSome},
    T,n+2,hu,?_,by omega,?_,hi,ho,hl,hr',hs',hc⟩
  · cases keys <;> simp
  · exact familyHaloLengthKeyStep_exec hR hQ v v' S T tick _ n
      (by simpa [List.replicate_succ] using hcount (L::keys) S hr)
      (hcount keys T hr') he

theorem familyHaloLengthKeyLoopCost_eq (A p l s t u target rhsExp V a b : ℕ) (keys : List ℕ) :
    familyHaloLengthKeyLoopCost A p l s t u target rhsExp V a b keys =
      (keys.map (fun L => (6*L+19*V+14)+cachedConditionalHaloClassCost p l L s t u target rhsExp a b)).sum+
      44*executionWidth p l target rhsExp*
        (keys.map (fun L => (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length*L)).sum+
      33*keys.length+3 := by
  unfold familyHaloLengthKeyLoopCost
  rw [haloWeightKeyFamily_length]
  suffices h :
      (keys.map (fun L => familyProcessHaloLengthKeyCost p l L s t u target rhsExp V a b+3)).sum =
        (keys.map (fun L => (6*L+19*V+14)+cachedConditionalHaloClassCost p l L s t u target rhsExp a b)).sum+
        36*executionWidth p l target rhsExp*
          (keys.map (fun L => (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length*L)).sum+
        31*keys.length by rw [h]; ring
  induction keys with
  | nil => simp
  | cons L keys ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [ih]
    unfold familyProcessHaloLengthKeyCost
    ring

theorem familyHaloLengthKeyLoopCost_le (A p l s t u target rhsExp V a b : ℕ)
    [NeZero s] (hst : s < t) :
    familyHaloLengthKeyLoopCost A p l s t u target rhsExp V a b
      (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      ((haloLengthKeys s t (PhaseCellBand.width p u) a b).map (fun L =>
        (6*L+19*V+14)+cachedConditionalHaloClassCost p l L s t u target rhsExp a b)).sum+
      44*s*executionWidth p l target rhsExp+
      33*(haloLengthKeys s t (PhaseCellBand.width p u) a b).length+3 := by
  rw [familyHaloLengthKeyLoopCost_eq,haloLengthKeys_volume hst]
  have hcard : (haloInterior s t (PhaseCellBand.width p u) a b).card ≤ s := by
    simpa using Finset.card_le_univ (s := haloInterior s t (PhaseCellBand.width p u) a b)
  have h := Nat.mul_le_mul_left (44*executionWidth p l target rhsExp) hcard
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
