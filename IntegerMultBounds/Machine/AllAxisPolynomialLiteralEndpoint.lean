import IntegerMultBounds.Machine.AllAxisPolynomialLiteral
import IntegerMultBounds.Machine.UnitPhasePolynomialArray

/-! The nested physical phase traversal emits the literal flattened result
array, with phase selected by the address quotient rather than the flat
coefficient index. This is the exact serialization endpoint. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialLiteralEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient prefixTape position full)
variable {s : Shape} {N R : ℕ}

def phase (v : Stage s) (m : ℕ) (ws : List (ZMod 4)) (i : ℕ) :=
  AllAxisPhaseFlagsCaller.phase v m ws (BinaryAddressTableData.row s.bits i)
def result (v : Stage s) (m : ℕ) (ws : List (ZMod 4))
    (xs : Fin (N*R) → Coefficient) (k : Fin (N*R)) : Coefficient :=
  let q := phase v m ws (k.val/R)
  (UnitPhaseNumerator.words q 0 (UnitPhasePolynomialArray.components (xs k)),
    UnitPhaseNumerator.words q 1 (UnitPhasePolynomialArray.components (xs k)))

theorem inner_prefix (v : Stage s) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (N*R) → Coefficient) (i : ℕ) (hi : i<N)
    (b : Tapes 60 2) (hf : UnitPhasePolynomialLoop.flagsAt b (phase v m ws i))
    (hc : UnitPhasePolynomialLoop.coreBlank b)
    (ho : b.tape 58=prefixTape g r (result v m ws xs) (i*R) ∧
      b.head 58=position r (result v m ws xs) (i*R))
    (k : ℕ) (hk : k≤R) :
    (UnitPhasePolynomialLoop.state b (AllAxisPolynomialLiteral.contexts f p xs i) (phase v m ws i) k).tape 58=
      prefixTape g r (result v m ws xs) (i*R+k) ∧
    (UnitPhasePolynomialLoop.state b (AllAxisPolynomialLiteral.contexts f p xs i) (phase v m ws i) k).head 58=
      position r (result v m ws xs) (i*R+k) := by
  induction k with
  | zero => simpa only [UnitPhasePolynomialLoop.state,Nat.add_zero] using ho
  | succ k ih =>
    have hkr : k<R := by omega
    have hidx := AllAxisPolynomialLiteral.index_lt i k hi hkr
    have h := ih (by omega)
    rw [UnitPhasePolynomialLoop.state,UnitPhaseSharedCoefficient.output_eq _ _ _
      (UnitPhasePolynomialLoop.state_flags b _ _ hf k)
      (UnitPhasePolynomialLoop.state_core b _ _ hc k)]
    simp only [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,
      Function.update_apply,ite_true,show (58 : Fin 60)≠56 by decide,ite_false]
    rw [h.1,h.2]
    have hs : UnitPhaseSharedCoefficient.sources (AllAxisPolynomialLiteral.contexts f p xs i k)=
        UnitPhasePolynomialArray.components (xs ⟨i*R+k,hidx⟩) := by
      funext j
      unfold UnitPhaseSharedCoefficient.sources UnitPhasePolynomialArray.components AllAxisPolynomialLiteral.contexts
      rw [(UnitPhaseStreamData.components f p xs (i*R+k) hidx).1,
        (UnitPhaseStreamData.components f p xs (i*R+k) hidx).2]
    have hdiv : (i*R+k)/R=i := by
      rw [Nat.mul_comm i R,Nat.mul_add_div (by omega : 0<R),Nat.div_eq_of_lt hkr,Nat.add_zero]
    rw [hs]
    have hr : result v m ws xs ⟨i*R+k,hidx⟩=
        (UnitPhaseNumerator.words (phase v m ws i) 0 (UnitPhasePolynomialArray.components (xs ⟨i*R+k,hidx⟩)),
          UnitPhaseNumerator.words (phase v m ws i) 1 (UnitPhasePolynomialArray.components (xs ⟨i*R+k,hidx⟩))) := by
      simp only [result,hdiv]
    constructor
    · simpa only [hr,ButterflyStreamData.encoded,Nat.add_assoc] using
        ButterflyStreamData.prefixTape_succ g r (result v m ws xs) ⟨i*R+k,hidx⟩
    · simpa only [hr,ButterflyStreamData.encoded,Nat.add_assoc] using
        (ButterflyStreamData.position_succ r (result v m ws xs) ⟨i*R+k,hidx⟩).symm

theorem output_prefix (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (xs : Fin (N*R) → Coefficient) (z : Tapes 4 2)
    (ho : z.tape 2=g ∧ z.head 2=r) (k : ℕ) (hk : k≤N) :
    (AllAxisPolynomialStreamLoop.tails order v rows m ws
      (AllAxisPolynomialLiteral.contexts f p xs) z R k).tape 2=prefixTape g r (result v m ws xs) (k*R) ∧
    (AllAxisPolynomialStreamLoop.tails order v rows m ws
      (AllAxisPolynomialLiteral.contexts f p xs) z R k).head 2=position r (result v m ws xs) (k*R) := by
  induction k with
  | zero => simpa [AllAxisPolynomialStreamLoop.tails,prefixTape,position,CyclicRowCycle.rowPrefix,putWord] using ho
  | succ k ih =>
    have hi : k<N := by omega
    have h := ih (by omega)
    let z' := AllAxisPolynomialStreamLoop.tails order v rows m ws
      (AllAxisPolynomialLiteral.contexts f p xs) z R k
    let b := AllAxisPolynomialRecord.prepared order v rows m ws
      (BinaryAddressTableData.row s.bits k) (AllAxisPolynomialFull.advanced s.bits k z')
    have hinner := inner_prefix v m ws f g p r xs k hi b
      (AllAxisPolynomialRecord.prepared_flags _ _ _ _ _ _ _)
      (AllAxisPolynomialRecord.prepared_core _ _ _ _ _ _ _) h R le_rfl
    have he : k*R+R=(k+1)*R := by nlinarith
    rw [he] at hinner
    exact hinner

theorem result_width (v : Stage s) (m : ℕ) (ws : List (ZMod 4))
    (xs : Fin (N*R) → Coefficient) (w : ℕ)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) (i : Fin (N*R)) :
    (result v m ws xs i).1.length=w ∧ (result v m ws xs i).2.length=w := by
  have hc : ∀ j,(UnitPhasePolynomialArray.components (xs i) j).length=w := by
    intro j
    dsimp [UnitPhasePolynomialArray.components]
    split_ifs <;> first | exact (hw i).1 | exact (hw i).2
  exact ⟨UnitPhaseNumerator.words_length _ _ _ w hc,UnitPhaseNumerator.words_length _ _ _ w hc⟩

theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (m : ℕ) (ws : List (ZMod 4))
    (f g : ℤ → Fin 6) (p r : ℤ) (ell w : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (AllAxisPolynomialStream.output order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs)
      (AllAxisPolynomialLiteral.tail f g p r xs) ell).tape 58=full g r (result v m ws xs) ∧
    (AllAxisPolynomialStream.output order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs)
      (AllAxisPolynomialLiteral.tail f g p r xs) ell).head 58=r+((rows*2^s.bits)*2^ell)*(2*(w+1)) := by
  have h := output_prefix order v rows m ws f g p r xs
    (AllAxisFullStreamInit.readyTail (s := s) rows (AllAxisPolynomialLiteral.tail f g p r xs))
    ⟨rfl,rfl⟩ (rows*2^s.bits) le_rfl
  rw [prefixTape,CyclicRowCycle.prefix_all] at h
  rw [ButterflyStreamEndpoint.position_all r (result v m ws xs) w (result_width v m ws xs w hw)] at h
  exact h

end
end IntegerMultBounds.Machine.AllAxisPolynomialLiteralEndpoint
