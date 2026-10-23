module

public import IntegerMultBounds.MathlibTM2.Routing.FramedExactSelective
public import IntegerMultBounds.MathlibTM2.Routing.RepairPriceFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleReady
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedScheduleTrace

/-! Data for one real exact-repair call in a fixed-size stream schedule.
Geometry may vary, but every stage acts on the same number and width of records. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def castRankPerm {M N : ℕ} (h : M = N) (π : Equiv.Perm (Fin M)) : Equiv.Perm (Fin N) := h ▸ π

theorem castRankPerm_apply_val {M N : ℕ} (h : M = N) (π : Equiv.Perm (Fin M)) (i : Fin N) :
    (castRankPerm h π i).val = (π (Fin.cast h.symm i)).val := by
  cases h
  rfl

theorem moveRecs_castRankPerm {M N : ℕ} (h : M = N) (π : Equiv.Perm (Fin M))
    {α : Type*} (l : List (List α)) : moveRecs (castRankPerm h π) l = moveRecs π l := by
  cases h
  rfl

/-- A framed list of rank moves has the same record effect as their composed
permutation. This generic statement is independent of any stage packaging. -/
theorem repairStreamEffects_moveRecs {I : Type} {M B A : ℕ}
    (perm : I → Equiv.Perm (Fin M)) (stages : List I)
    (l : List (List (Fin (A + 4)))) (hl : l.length = M)
    (hlen : ∀ r ∈ l, r.length = B) :
    delimitedScheduleEffect (fun i => repairStreamEffect (perm i) B) stages l.flatten =
      (moveRecs (stages.foldr (fun i π => (perm i).trans π) (Equiv.refl _)) l).flatten := by
  induction stages generalizing l with
  | nil => simp only [delimitedScheduleEffect, List.foldr_nil, moveRecs_refl l hl]
  | cons i stages ih =>
    rw [delimitedScheduleEffect]
    have hfirst : repairStreamEffect (perm i) B l.flatten = (moveRecs (perm i) l).flatten :=
      (flatten_moveRecs (perm i) l hlen).symm
    rw [hfirst, ih (moveRecs (perm i) l) (length_moveRecs _ _)
      (fun r hr => hlen r (mem_moveRecs (perm i) hl hr)), List.foldr_cons]
    exact congrArg List.flatten (moveRecs_trans (perm i) _ l hl).symm

structure RepairScheduleStage (K M B : ℕ) where
  p : Par
  X : ℕ
  rb : ℕ
  wb : ℕ
  wm : ℕ
  wp : ℕ
  wk : ℕ
  rows : ℕ
  hG : 0 < p.G
  hK : 0 < p.K
  guard : p.G + 1 < p.K
  scale : ℝ
  scale_pos : 0 < scale
  digits_le : (p.n : ℝ) ≤ scale
  radix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G
  gap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G)
  active : Fin p.n → Bool
  sources : Fin p.n → SlotSource p X
  allowed : ∀ c, (sources c).Allowed active
  rows_pos : 0 < rows
  rows_fit : rows ≤ 2 ^ rb
  count : rows * 2 ^ fieldsLen (selectiveLen p X) = M
  words : Fin repairT → List (Fin (prime + K + 4))
  data : RepairSetupData p X rb hG hK active sources wb wm wp wk rows B
    (repairCanonicalHeaders p X rb rows B) words
  blank : ∀ j, RepairBlank j → words j = []

variable {K M B : ℕ}

def RepairScheduleStage.perm (stage : RepairScheduleStage K M B) : Equiv.Perm (Fin M) :=
  castRankPerm stage.count (selectiveIdealPerm stage.hK stage.active stage.sources stage.rows stage.allowed)

def RepairScheduleStage.frame (stage : RepairScheduleStage K M B) (delimiter : Fin (prime + K + 4)) :=
  delimitedBankFrames delimiter (repairConfigLoadJobs stage.words)

def RepairScheduleStage.bank (stage : RepairScheduleStage K M B) : Stacks repairT (prime + K) :=
  ⟨[], [], fun _ => [], stage.words⟩

def RepairScheduleStage.price (stage : RepairScheduleStage K M B) : ℝ :=
  repairRawPrice stage.p stage.X stage.rb stage.wb stage.wm stage.wp stage.wk stage.rows B stage.scale stage.bank

def RepairScheduleStage.stepPrice (stage : RepairScheduleStage K M B) (delimiter : Fin (prime + K + 4)) : ℝ :=
  stage.price + (6 * (stage.frame delimiter).length + 2 * (repairConfigLoadJobs stage.words).length + 2 : ℕ)

end
end IntegerMultBounds.MathlibTM2.Routing
