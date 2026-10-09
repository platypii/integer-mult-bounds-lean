import IntegerMultBounds.Machine.UnitPhaseFullStreamClean
import IntegerMultBounds.Machine.ButterflyStreamEndpoint

/-! The source coefficient stream is retained literally and its head finishes
at the exact serialized EOF, with no fabricated readable terminal record. -/
namespace IntegerMultBounds.Machine.UnitPhaseSourceEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ButterflyStreamData (Coefficient full position)
variable {s : Shape} {n : ℕ}

theorem final (v : Stage s) (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4))
    (f : ℤ → Fin 6) (p : ℤ) (xs : Fin n → Coefficient) (tail : Tapes 4 2) (hn : 0<n) :
    (UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail n).tape 0=full f p xs ∧
      (UnitPhaseStreamLoop.tails v axis m ws (UnitPhaseStreamData.contexts f p xs) tail n).head 0=position p xs n := by
  cases n with
  | zero => omega
  | succ k =>
    change (UnitPhaseStreamData.contexts f p xs k).tape=full f p xs ∧
      (UnitPhaseStreamData.contexts f p xs k).start+(UnitPhaseStreamData.contexts f p xs k).re.length+
        (UnitPhaseStreamData.contexts f p xs k).im.length+2=position p xs (k+1)
    rw [UnitPhaseStreamData.tape _ _ _ _ (by omega),UnitPhaseStreamData.start _ _ _ _ (by omega),
      (UnitPhaseStreamData.components f p xs k (by omega)).1,
      (UnitPhaseStreamData.components f p xs k (by omega)).2]
    exact ⟨rfl,(ButterflyStreamData.position_succ p xs ⟨k,by omega⟩).symm⟩

theorem clean (order : ActivePrefixStageHeadersData.Order) (v : Stage s) (rows : ℕ) (hr : 0<rows)
    (axis : Fin v.f) (m : ℕ) (ws : List (ZMod 4)) (f g : ℤ → Fin 6) (p r : ℤ)
    (xs : Fin (rows*2^s.bits) → Coefficient) (w : ℕ) (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w) :
    (UnitPhaseFullStreamClean.output order v rows axis m ws f g p r xs).tape 56=full f p xs ∧
      (UnitPhaseFullStreamClean.output order v rows axis m ws f g p r xs).head 56=p+(rows*2^s.bits)*(2*(w+1)) := by
  have h := final v axis m ws f p xs
    (UnitPhaseFullStreamInit.readyTail (s := s) rows (UnitPhaseFullStreamArray.tail f g p r xs))
    (Nat.mul_pos hr (by positivity))
  rw [ButterflyStreamEndpoint.position_all p xs w hw] at h
  exact h

end
end IntegerMultBounds.Machine.UnitPhaseSourceEndpoint
