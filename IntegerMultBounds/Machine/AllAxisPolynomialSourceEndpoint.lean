import IntegerMultBounds.Machine.AllAxisPolynomialLiteralEndpoint

/-! The complete polynomial phase machine retains the literal source array
and reaches its real EOF. The last-source proof refers only to the last
actual coefficient, not the dummy context beyond the stream. -/
namespace IntegerMultBounds.Machine.AllAxisPolynomialSourceEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient full position)
variable {s : Shape}

theorem endpoint (order : Order) (v : Stage s) (rows : ℕ) (hr : 0<rows) (m : ℕ)
    (ws : List (ZMod 4)) (f g : ℤ → Fin 6) (p r : ℤ) (ell w : ℕ)
    (xs : Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (AllAxisPolynomialStream.output order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs)
      (AllAxisPolynomialLiteral.tail f g p r xs) ell).tape 56=full f p xs ∧
    (AllAxisPolynomialStream.output order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs)
      (AllAxisPolynomialLiteral.tail f g p r xs) ell).head 56=p+((rows*2^s.bits)*2^ell)*(2*(w+1)) := by
  let N := rows*2^s.bits
  let R := 2^ell
  have hN : 0<N := by dsimp [N]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  let z := AllAxisFullStreamInit.readyTail (s := s) rows (AllAxisPolynomialLiteral.tail f g p r xs)
  have h := AllAxisPolynomialAdvance.source order v rows m ws (N-1)
    (AllAxisPolynomialStreamLoop.tails order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs) z R (N-1))
    (AllAxisPolynomialLiteral.contexts f p xs (N-1)) R hR
  have hi := AllAxisPolynomialLiteral.index_lt (N-1) (R-1) (by omega : N-1<N) (by omega : R-1<R)
  have hprev : (N-1)*R+(R-1)+1=N*R := by
    calc
      _ = (N-1)*R+R := by omega
      _ = ((N-1)+1)*R := by ring
      _ = N*R := by rw [Nat.sub_add_cancel (show 1≤N by omega)]
  have he : (N-1)*R+(R-1)=N*R-1 := by omega
  have hidx : N*R-1<N*R := by simpa only [he] using hi
  dsimp only [AllAxisPolynomialLiteral.contexts] at h
  rw [he,UnitPhaseStreamData.tape _ _ _ _ hidx,UnitPhaseStreamData.start _ _ _ _ hidx,
    (UnitPhaseStreamData.components f p xs (N*R-1) hidx).1,
    (UnitPhaseStreamData.components f p xs (N*R-1) hidx).2] at h
  have hs := ButterflyStreamData.position_succ p xs ⟨N*R-1,hidx⟩
  have hprod : N*R-1+1=N*R := by have : 0<N*R := Nat.mul_pos hN hR; omega
  rw [hprod] at hs
  rw [← hs,ButterflyStreamEndpoint.position_all p xs w hw] at h
  have ht : AllAxisPolynomialStreamLoop.tails order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs) z R N=
      AllAxisPolynomialFull.nextTail order v rows m ws (N-1)
        (AllAxisPolynomialStreamLoop.tails order v rows m ws (AllAxisPolynomialLiteral.contexts f p xs) z R (N-1))
        (AllAxisPolynomialLiteral.contexts f p xs (N-1)) R := by
    conv_lhs => rw [show N=(N-1)+1 by omega]
    rfl
  rw [← ht] at h
  exact h

end
end IntegerMultBounds.Machine.AllAxisPolynomialSourceEndpoint
