module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalMultiplierRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrivateRuler

/-! Complete diagonal multiplier setup with borrowed width storage retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalMultiplierBorrowed (source header word saved tmp carry : Fin tapes) : Pr P tapes Q A U :=
  withPrivateRuler source (diagonalMultiplierTable .wr) tmp (diagonalMultiplierFinished header word saved tmp carry)

theorem diagonalMultiplierBorrowed_exec (source header word saved tmp carry : Fin tapes)
    (hcopy : [source,diagonalMultiplierTable .wr,tmp].Nodup)
    (hheader : ∀ r, diagonalMultiplierTable r ≠ header)
    (hregs : ∀ src ∈ diagonalMultiplierInputs.map Prod.snd,
      [src,diagonalMultiplierTable .wr,word,saved,tmp,header].Nodup)
    (B p w : ℕ) (hpw : p ≤ w) (hw : 1 ≤ w) (hroom : 4*w+2 < 2^B)
    (v : HS tapes Q A U) (S : Stacks tapes A) (hB : (S.R source).length = B)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hwide : (S.R (recovery (.control .packet))).length = w)
    (hblank : ∀ r : TblR 5, S.R (diagonalMultiplierTable r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) (hcm : ∀ c : CR, S.R (diagonalCr c) = []) :
    let cost := diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11)
    ∃ v' steps, v'.user = v.user ∧ steps ≤ (4*B+4)+cost+(2*B+2) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(4*B+4)+3*cost)) depth (diagonalMultiplierBorrowed source header word saved tmp carry)
        (Host.mk v S) steps (Host.mk v' {S with R := diagonalCounterR p w S.R})) ∧
      RsbReady (fun r => diagonalCounterR p w S.R (diagonalRole r)) w p := by
  dsimp only
  let ruler := diagonalMultiplierTable .wr
  let cost := diagonalMultiplierFromUnaryCost B p w+(2*(5*B)+11)
  let Post : Stacks tapes A → Prop := fun F => F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    ∀ k, k ≠ ruler → F.R k = diagonalCounterR p w S.R k
  have hretire : ∀ F, Post F → Post {F with R := Function.update F.R ruler []} := by
    intro F hF
    refine ⟨hF.1,hF.2.1,hF.2.2.1,?_⟩
    intro k hk
    exact (Function.update_of_ne hk _ _).trans (hF.2.2.2 k hk)
  have hconv := hregs (recovery (.control .precision)) (by simp [diagonalMultiplierInputs])
  regs_ne hconv
  obtain ⟨v',F,steps,hu,hn,ht,hpost,hzero⟩ := withPrivateRuler_exec (body := body) source ruler tmp hcopy
    (diagonalMultiplierFinished header word saved tmp carry) B cost (3*cost) Post hretire v S hB (hblank .wr)
    (hwork tmp (by simp)) (by
      intro v₁
      let M : Stacks tapes A := {S with R := Function.update S.R ruler (List.replicate B tick)}
      have hm k (hk : k ≠ ruler) : M.R k = S.R k := Function.update_of_ne hk _ _
      have hprec : recovery (.control .precision) ≠ ruler := by
        simp [ruler,diagonalMultiplierTable,diagonalTable,recovery_injective.eq_iff]
      have hpacket : recovery (.control .packet) ≠ ruler := by
        simp [ruler,diagonalMultiplierTable,diagonalTable,recovery_injective.eq_iff]
      have hcmRead c : M.R (diagonalCr c) = S.R (diagonalCr c) :=
        hm _ (diagonalTable_ne_role _ (.cm c)).symm
      obtain ⟨v₂,steps₂,hu₂,hn₂,_,ht₂,_⟩ := diagonalMultiplierFinished_exec (body := body)
        header word saved tmp carry hheader hregs B p w hpw hw hroom (List.replicate B tick) (by simp) v₁ M
        ((hm _ hprec) ▸ hp) ((hm _ hpacket) ▸ hwide) (by simp [M,ruler])
        (by
          intro r hr
          have hne : diagonalMultiplierTable r ≠ ruler := fun he => hr (diagonalMultiplierTable_injective he)
          exact (hm _ hne).trans (hblank r))
        (by
          intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with hk | hk | hk <;> subst k <;>
            exact (hm _ (Ne.symm (by assumption))).trans (hwork _ (by simp)))
        (fun c => (hcmRead c).trans (hcm c))
      refine ⟨v₂,{M with R := diagonalCounterR p w M.R},steps₂,hu₂,hn₂,?_,?_,ht₂⟩
      · exact (diagonalCounter_off_table p w M.R .wr).trans (Function.update_self ..)
      · refine ⟨rfl,rfl,rfl,?_⟩
        intro k hk
        apply unaryCopiesR_congr_base
        · intro a ha
          simp only [chirpMultiplierAssignments,List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl | rfl <;> exact hcmRead _
        · exact hm k hk)
  have hfinal : F = {S with R := diagonalCounterR p w S.R} := by
    refine Stacks.ext hpost.1 hpost.2.1 hpost.2.2.1 ?_
    funext k
    by_cases hk : k = ruler
    · subst k
      exact hzero.trans ((diagonalCounter_off_table p w S.R .wr).trans (hblank .wr)).symm
    · exact hpost.2.2.2 k hk
  rw [hfinal] at ht
  exact ⟨v',steps,hu,hn,ht,diagonalCounter_ready p w S.R hcm⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
