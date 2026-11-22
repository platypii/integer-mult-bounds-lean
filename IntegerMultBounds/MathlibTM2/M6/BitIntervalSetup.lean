module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalCounter
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChart

/-! Initialize the cyclic COPY splitter on its own source and empty role tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Shared50ModularControl (prime)

abbrev intervalSplitTapes := ((1+142080)+2)+2

/-- The quotient goes directly to the outer loop header. The remaining
workspace borrows seven role tapes while they are still empty. -/
def intervalCounterPorts : Fin 9 ↪ Fin intervalSplitTapes :=
  ⟨![0,1,roleSplitControls 142080 3,2,3,4,5,6,7],by decide⟩

noncomputable def intervalPrepare {P U : Type} {Q : ℕ} : Pr P intervalSplitTapes Q prime U :=
  (intervalCounter intervalCounterPorts).seq
    ((Prog.act (.push (.rt (roleSplitControls 142080 1)) (fun _ => bitSymbol true) .done)).seq
      (Prog.act (pushMarkers ((List.finRange 4).map (roleSplitControls 142080)))))

theorem intervalPrepare_exec {P U : Type} {Q : ℕ} (body : P → Pr P intervalSplitTapes Q prime U)
    (m : ℕ) (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (size : (S.R 0).length = m*142080) (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    ∃ z D t, z.user = u.user ∧ t ≤ 4*(m*142080)+23*m+18 ∧
      Exec body intervalPrepare (mk u S) t (mk z D) ∧
      RepT (CyclicRowSplit.bank (CyclicRowCopy.bank (putWord (fun _ => blank) 0 (S.R 0))
        (fun _ _ => blank) 0 (fun _ => 0) (FlatCoordinateSchedule.bits 1))
        (FlatCoordinateSchedule.bits m)) D.L D.R := by
  let ctrl := roleSplitControls 142080
  obtain ⟨z,t,user,time,count⟩ := intervalCounter_exec body intervalCounterPorts m u S size
    (fun i hi => empty _ (intervalCounterPorts.injective.ne hi))
  let B := {S with R := Function.update S.R (ctrl 3) ((FlatCoordinateSchedule.bits m).map bitSymbol)}
  let C := {B with R := Function.update B.R (ctrl 1) (bitSymbol true :: B.R (ctrl 1))}
  have push : Exec body (.act (.push (.rt (ctrl 1)) (fun _ => bitSymbol true) .done))
      (mk z B) 1 (mk z C) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,C,get_rt,update_rt]
  have nonzero (i) : ctrl i ≠ 0 := by intro h; have := congrArg Fin.val h; change 1+142080+i.val = 0 at this; omega
  obtain ⟨mark,repr⟩ := prepareRoleSplit_exec body z C (S.R 0) 1 m left
    (by change C.R 0 = _; simp [C,B,Ne.symm (nonzero 1),Ne.symm (nonzero 3)])
    (by intro j
        have off (i) : ((j.natAdd 1).castAdd 2).castAdd 2 ≠ ctrl i := by
          intro h; have := congrArg Fin.val h; change 1+j.val = 1+142080+i.val at this; omega
        have nz : ((j.natAdd 1).castAdd 2).castAdd 2 ≠ (0 : Fin intervalSplitTapes) := by
          intro h; have := congrArg Fin.val h; change 1+j.val = 0 at this; omega
        exact (Function.update_of_ne (off 1) ..).trans ((Function.update_of_ne (off 3) ..).trans (empty _ nz)))
    (by intro i
        change C.R (ctrl i) = _
        fin_cases i <;> simp [C,B,Function.update_apply,ctrl.injective.eq_iff,roleSplitControls,
          empty,nonzero,canonicalBits_symbols,ctrl] <;> first | rfl | apply empty <;> decide | change bitSymbol true :: S.R (ctrl 1) = binSyms 1 1; rw [empty _ (nonzero 1)]; rfl)
  exact ⟨z,_,_,user,by omega,Exec.seq count (Exec.seq push mark),repr⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
