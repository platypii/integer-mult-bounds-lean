import IntegerMultBounds.Machine.UnitPhasePolynomialLoop
import IntegerMultBounds.Machine.UnitPhaseStreamData
import IntegerMultBounds.Machine.ButterflyStreamEndpoint

/-! Exact literal serialization for a polynomial coefficient array whose
phase flags are shared. Contexts are readable only below the real count;
there is no read of a fictitious terminal coefficient. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialArray
noncomputable section
open ButterflyStreamData (Coefficient full prefixTape position)
open UnitPhasePolynomialLoop (state flagsAt coreBlank)
variable {n : ℕ}

def components (a : Coefficient) : ℕ → List (Fin 2) := fun j => if j=0 then a.1 else a.2
def result (q : Fin 4) (xs : Fin n → Coefficient) (i : Fin n) : Coefficient :=
  (UnitPhaseNumerator.words q 0 (components (xs i)),UnitPhaseNumerator.words q 1 (components (xs i)))

theorem sources (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (i : Fin n) :
    UnitPhaseSharedCoefficient.sources (UnitPhaseStreamData.contexts f p xs i.val)=components (xs i) := by
  funext j
  unfold UnitPhaseSharedCoefficient.sources components
  rw [(UnitPhaseStreamData.components f p xs i.val i.isLt).1,
    (UnitPhaseStreamData.components f p xs i.val i.isLt).2]

theorem output_prefix (v : Tapes 60 2) (q : Fin 4) (f g : ℤ → Fin 6) (p r : ℤ)
    (xs : Fin n → Coefficient) (hflags : flagsAt v q) (hcore : coreBlank v)
    (ho : v.tape 58=g ∧ v.head 58=r) (k : ℕ) (hk : k≤n) :
    (state v (UnitPhaseStreamData.contexts f p xs) q k).tape 58=prefixTape g r (result q xs) k ∧
      (state v (UnitPhaseStreamData.contexts f p xs) q k).head 58=position r (result q xs) k := by
  induction k with
  | zero => simpa [state,prefixTape,position,CyclicRowCycle.rowPrefix,putWord] using ho
  | succ k ih =>
    have hi : k<n := by omega
    have h := ih (by omega)
    rw [state,UnitPhaseSharedCoefficient.output_eq _ _ _
      (UnitPhasePolynomialLoop.state_flags v _ q hflags k)
      (UnitPhasePolynomialLoop.state_core v _ q hcore k)]
    simp only [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,
      Function.update_apply,ite_true,show (58 : Fin 60)≠56 by decide,ite_false]
    rw [h.1,h.2,sources f p xs ⟨k,hi⟩]
    constructor
    · exact ButterflyStreamData.prefixTape_succ g r (result q xs) ⟨k,hi⟩
    · exact (ButterflyStreamData.position_succ r (result q xs) ⟨k,hi⟩).symm

theorem result_width (q : Fin 4) (xs : Fin n → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) (i : Fin n) :
    (result q xs i).1.length=w ∧ (result q xs i).2.length=w := by
  have hc : ∀ j,(components (xs i) j).length=w := by
    intro j
    dsimp [components]
    split_ifs <;> first | exact (hw i).1 | exact (hw i).2
  exact ⟨UnitPhaseNumerator.words_length _ _ _ w hc,UnitPhaseNumerator.words_length _ _ _ w hc⟩

theorem output_endpoint (v : Tapes 60 2) (q : Fin 4) (f g : ℤ → Fin 6) (p r : ℤ)
    (xs : Fin n → Coefficient) (hflags : flagsAt v q) (hcore : coreBlank v)
    (ho : v.tape 58=g ∧ v.head 58=r) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (state v (UnitPhaseStreamData.contexts f p xs) q n).tape 58=full g r (result q xs) ∧
      (state v (UnitPhaseStreamData.contexts f p xs) q n).head 58=r+n*(2*(w+1)) := by
  have h := output_prefix v q f g p r xs hflags hcore ho n le_rfl
  rw [prefixTape,CyclicRowCycle.prefix_all] at h
  rw [ButterflyStreamEndpoint.position_all r (result q xs) w (result_width q xs w hw)] at h
  exact h

theorem runs (v : Tapes 60 2) (q : Fin 4) (f : ℤ → Fin 6) (p : ℤ)
    (xs : Fin n → Coefficient) (hn : 0<n) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hflags : flagsAt v q) (hcore : coreBlank v)
    (hs : v.tape 56=full f p xs ∧ v.head 56=p) :
    HoareTime UnitPhasePolynomialLoop.program
      (fun z => z=CountedLoopHeaderClean.bank (UnitPhasePolynomialLoop.counted v (UnitPhaseStreamData.contexts f p xs) q n 0))
      (fun z => z=CountedLoopHeaderClean.bank (UnitPhasePolynomialLoop.counted v (UnitPhaseStreamData.contexts f p xs) q n n))
      (n*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits n).length+35) := by
  apply UnitPhasePolynomialLoop.runs v _ q n w (UnitPhaseStreamData.widths f p xs w hw) hflags hcore _
    (UnitPhaseStreamData.adjacent f p xs)
  rw [UnitPhaseStreamData.tape _ _ _ _ hn,UnitPhaseStreamData.start _ _ _ _ hn]
  simpa [position,CyclicRowCycle.rowPrefix] using hs

theorem source_endpoint (v : Tapes 60 2) (q : Fin 4) (f : ℤ → Fin 6) (p : ℤ)
    (xs : Fin n → Coefficient) (hn : 0<n) (hflags : flagsAt v q) (hcore : coreBlank v) :
    (state v (UnitPhaseStreamData.contexts f p xs) q n).tape 56=full f p xs ∧
      (state v (UnitPhaseStreamData.contexts f p xs) q n).head 56=position p xs n := by
  have hi : n-1<n := by omega
  have he := congrArg (state v (UnitPhaseStreamData.contexts f p xs) q) (show n=(n-1)+1 by omega)
  rw [state] at he
  rw [he,UnitPhaseSharedCoefficient.output_eq _ _ _
    (UnitPhasePolynomialLoop.state_flags v _ q hflags (n-1))
    (UnitPhasePolynomialLoop.state_core v _ q hcore (n-1))]
  simp only [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,
    Function.update_apply,show (56 : Fin 60)≠58 by decide,ite_false,ite_true]
  rw [UnitPhaseStreamData.tape _ _ _ _ hi,UnitPhaseStreamData.start _ _ _ _ hi,
    (UnitPhaseStreamData.components f p xs (n-1) hi).1,(UnitPhaseStreamData.components f p xs (n-1) hi).2]
  have hx : n-1+1=n := by omega
  exact ⟨rfl,by simpa only [hx] using (ButterflyStreamData.position_succ p xs ⟨n-1,hi⟩).symm⟩

end
end IntegerMultBounds.Machine.UnitPhasePolynomialArray
