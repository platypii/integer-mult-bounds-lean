module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizationBanks

/-! Ordinary shared unary/scalar tapes supply the complete computed-call
readiness, including normalization, without a second input-bank witness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
namespace RecoveryBanks
variable {T A s : ℕ} [NeZero s] (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)

def liveControls : List RecoveryControl := [.precision,.packet,.replicas,.cropOffset,.cropRows,.cropDst,.result]

theorem localReady (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (S : Stacks T A)
    (hp : (S.R (bank (.control .precision))).length = r.p)
    (hW : (S.R (bank (.control .packet))).length = r.W)
    (hN : (S.R (bank (.control .replicas))).length = r.Fs.length)
    (hparameters : ∀ i, (S.R (bank (.parameter i))).length = r.masterInput.values i)
    (hwidth : S.R (bank (.scalar .wr)) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ liveControls → S.R (bank (.control i)) = [])
    (hwork : ∀ i, i ≠ 124 → S.R (bank (.work i)) = [])
    (hleft : ∀ i, S.L (bank (.work i)) = [])
    (hpayload : S.R (bank (.work 124)) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten)
    (hoffset : (S.R (bank (.control .cropOffset))).length = r.radius)
    (hrows : (S.R (bank (.control .cropRows))).length = coreLength s r.coreWidth r.k) :
    (plan bank hinj).LocalReady (normalize bank hinj) (queue bank hinj) (crop bank hinj) r wl S := by
  have hc (i : RecoveryControl) (hi : i ∉ liveControls) := hcontrols i hi
  refine ⟨?_,hp,hW,hN,hparameters,hwidth,hscalar,hmasters,?_,hwork,hleft,hpayload,?_,?_,?_,?_,hoffset,hrows⟩
  · refine ⟨hwidth,hscalar,?_,?_,hp,hW,hrows,hN,?_,?_⟩
    · intro i; exact hparameters i
    · change ∀ k ∈ [bank (.control .masterWord),bank (.control .masterSaved),bank (.control .masterTmp)], S.R k = []
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hc .masterWord (by decide)
      · exact hc .masterSaved (by decide)
      · exact hc .masterTmp (by decide)
    · change ∀ k ∈ [bank (.work 204),bank (.work 205),bank (.work 206),bank (.work 207),
        bank (.work 208),bank (.work 209),bank (.work 210)], S.R k = []
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hwork _ (by decide)
    · intro i; exact hwork (normalizePortIndex i) (normalizePortIndex_ne_payload i)
  · change ∀ k ∈ [bank (.control .masterWord),bank (.control .masterSaved),bank (.control .masterTmp),
      bank (.control .masterQueue)], S.R k = []
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hc .masterWord (by decide)
    · exact hc .masterSaved (by decide)
    · exact hc .masterTmp (by decide)
    · exact hc .masterQueue (by decide)
  · change ∀ k ∈ [bank (.control .count),bank (.control .tmp),bank (.control .spare)], S.R k = []
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact hc .count (by decide)
    · exact hc .tmp (by decide)
    · exact hc .spare (by decide)
  · exact hc .clock (by decide)
  · exact hc .saved (by decide)
  · exact hc .savedClock (by decide)

end RecoveryBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
