module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGeometry

/-! Run the consumer-format list once, retaining the actual endpoint and its
readiness/frame contract rather than expanding a concrete nine-word state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

def geometryBankProgram {Q : ℕ} {P U : Type} (T : ℕ) : List (Fin 3) → Pr P (MachineTapes T) Q A U
  | [] => .act .done
  | f::fs => .seq
      (copyBinaryHeaderBank (rulers T f) (seedReg T (.z 0)) (seedReg T (.z 1)) (geometryCopies T f))
      (geometryBankProgram T fs)

def geometryBankCost (bits : Fin 3 → ℕ) (fs : List (Fin 3)) : ℕ :=
  (fs.map (fun f => 3*(10*bits f+10)+1)).sum+1

theorem geometryBankProgram_native {Q : ℕ} {P U : Type} (T : ℕ) (fs : List (Fin 3)) :
    mnNativePushBound 3 (geometryBankProgram (Q := Q) (P := P) (A := A) (U := U) T fs) := by
  induction fs with
  | nil => exact Nat.zero_le _
  | cons f fs ih => exact ⟨copyBinaryHeaderBank_native _ _ _ _,ih⟩

/-- Only the listed geometry destinations can change. Freshness and distinct
formats suffice; all wide scalar words and setup scratch are restored. -/
theorem prepareGeometryBank_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (fs : List (Fin 3)) (hnd : fs.Nodup)
    (S : Stacks (MachineTapes T) A)
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (hbits : ∀ f ∈ fs, formatWidths B Vg Vr f ≤ D)
    (hblank : ∀ f ∈ fs, ∀ i, S.R (fullHeader T (.geometry f i)) = [])
    (v : HS (MachineTapes T) Q A U) :
    ∃ v' F, v'.user = v.user ∧
      SetupInput T A D p u l target s t B W N radius width Vg Vr F ∧
      (∀ f ∈ fs, ∀ i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ f ∈ fs, ∀ i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      Exec body (geometryBankProgram T fs) (Host.mk v S)
        (geometryBankCost (formatWidths B Vg Vr) fs) (Host.mk v' F) := by
  induction fs generalizing v S with
  | nil =>
    refine ⟨v,S,rfl,input,by simp,rfl,rfl,rfl,fun _ _ => rfl,?_⟩
    simpa [geometryBankProgram,geometryBankCost] using Exec.act (body := body) .done (Host.mk v S)
  | cons f fs ih =>
    have hn := List.nodup_cons.mp hnd
    obtain ⟨v₁,hu₁,he₁⟩ := prepareGeometry_exec_within body input f (hbits f (by simp))
      (hblank f (by simp)) v 0
    let M := geometryLoaded (p := p) (u := u) (l := l) (target := target) (s := s) (t := t)
      (B := B) (W := W) (N := N) (radius := radius) (width := width) (Vg := Vg) (Vr := Vr) f S
    have hM (k) (hk : ∀ i, k ≠ fullHeader T (.geometry f i)) : M.R k = S.R k := by
      apply copyWordHeadersR_off
      intro q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact (hk i).symm
    obtain ⟨v₂,F,hu₂,hinput,hwords,hleft,hI,hO,hframe,he₂⟩ := ih hn.2 M (input.prepareGeometry f)
      (fun g hg => hbits g (by simp [hg]))
      (by
        intro g hg i
        rw [hM]
        · exact hblank g (by simp [hg]) i
        · intro j he
          have hgf := (Role.geometry.inj (fullHeader_injective T he)).1
          exact hn.1 (hgf ▸ hg)) v₁
    refine ⟨v₂,F,hu₂.trans hu₁,hinput,?_,hleft,hI,hO,?_,?_⟩
    · intro g hg i
      rcases List.mem_cons.mp hg with hg | hg
      · subst g
        rw [hframe]
        · exact geometryLoaded_word f i S (hblank f (by simp) i)
        · intro g hg j he
          have hfg := (Role.geometry.inj (fullHeader_injective T he)).1
          exact hn.1 (hfg ▸ hg)
      · exact hwords g hg i
    · intro k hk
      exact (hframe k (fun g hg => hk g (by simp [hg]))).trans (hM k (hk f (by simp)))
    · exact (Exec.seq he₁.toExec he₂).cast (by simp [geometryBankCost]; omega) rfl

theorem prepareGeometryBank_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (fs : List (Fin 3)) (hnd : fs.Nodup)
    (S : Stacks (MachineTapes T) A)
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (hbits : ∀ f ∈ fs, formatWidths B Vg Vr f ≤ D)
    (hblank : ∀ f ∈ fs, ∀ i, S.R (fullHeader T (.geometry f i)) = [])
    (v : HS (MachineTapes T) Q A U) (depth : ℕ) :
    ∃ v' F, v'.user = v.user ∧
      SetupInput T A D p u l target s t B W N radius width Vg Vr F ∧
      (∀ f ∈ fs, ∀ i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ f ∈ fs, ∀ i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*geometryBankCost (formatWidths B Vg Vr) fs) depth
        (geometryBankProgram T fs) (Host.mk v S)
        (geometryBankCost (formatWidths B Vg Vr) fs) (Host.mk v' F) := by
  obtain ⟨v',F,hu,hi,hw,hL,hI,hO,hframe,he⟩ := prepareGeometryBank_exec body fs hnd S input hbits hblank v
  exact ⟨v',F,hu,hi,hw,hL,hI,hO,hframe,mn_native_exec_within he 3 (geometryBankProgram_native _ _) depth _ (by omega)⟩

/-- All nine geometry words are produced together; the witness F is the state
returned by this actual execution, with its retained setup contract. -/
theorem prepareAllGeometry_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (S : Stacks (MachineTapes T) A)
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr S)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (hblank : ∀ f i, S.R (fullHeader T (.geometry f i)) = [])
    (v : HS (MachineTapes T) Q A U) (depth : ℕ) :
    ∃ v' F, v'.user = v.user ∧
      SetupInput T A D p u l target s t B W N radius width Vg Vr F ∧
      (∀ f i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i)) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+3*(30*(B+Vg+Vr)+94)) depth
        (geometryBankProgram T (List.finRange 3)) (Host.mk v S)
        (30*(B+Vg+Vr)+94) (Host.mk v' F) := by
  have hcost : geometryBankCost (formatWidths B Vg Vr) (List.finRange 3) = 30*(B+Vg+Vr)+94 := by
    simp [geometryBankCost,List.finRange_succ,formatWidths]
    omega
  obtain ⟨v',F,hu,hi,hw,hL,hI,hO,hframe,he⟩ := prepareGeometryBank_exec_within body (List.finRange 3)
    (List.nodup_finRange 3) S input (fun f _ => hbits f) (fun f _ => hblank f) v depth
  rw [hcost] at he
  exact ⟨v',F,hu,hi,(fun f => hw f (List.mem_finRange f)),hL,hI,hO,
    (fun k hk => hframe k (fun f _ => hk f)),he⟩

/-- Instantiate numerical readiness on a returned whole-geometry endpoint.
The frame transports the original fresh bank/table hypotheses. -/
theorem allGeometryNumericalInput {S F : Stacks (MachineTapes T) A}
    (input : SetupInput T A D p u l target s t B W N radius width Vg Vr F)
    (hwords : ∀ f i, F.R (fullHeader T (.geometry f i)) = binSyms (formatWidths B Vg Vr f) (![s,width,radius] i))
    (hL : F.L = S.L)
    (hframe : ∀ k, (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k)
    (clipped : Bool) (hwidth : 0 < width) (hgeometry : width+2*radius < 2^D)
    (hfit : ∀ i, globalValues p u l target s t B W N radius width i < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (b : ComputedClassBank → Fin T)
    (htable : ∀ r, S.R (numericTable T r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank (bank b) j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank (bank b)) (.work j)) = []) :
    let c := makeSetup input clipped hwidth hgeometry hfit hbits
    c.NumericalInput (fullExposedClassBank (bank b)) (numericTable T) (geometrySources T) (masterSources T) := by
  apply setupNumericalInput input clipped hwidth hgeometry hfit hbits b
  · intro j
    have hj : geometrySources T (Fin.castAdd 1 j) = fullHeader T (.geometry 0 j) := by
      fin_cases j <;> rfl
    rw [hj]
    exact hwords 0 j
  · intro r
    rw [hframe]
    · exact htable r
    · intro f i
      exact (fullHeader_injective T).ne (by intro h; cases r <;> cases h)
  · intro j hj
    rw [hframe]
    · exact hbank j hj
    · intro f i
      exact (fullHeader_ne_numerical b (.geometry f i) j).symm
  · rw [hL]
    exact hleft

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
