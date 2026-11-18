module

public import IntegerMultBounds.MathlibTM2.Cover.LabelPrepare
public import IntegerMultBounds.Machine.CleanExecution

/-! Clean label-view preparation retains the caller's header words and the three new dimensions. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelPrepareClean
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateSchedule (bits)
open LabelPrepare (input)

def right (i : Fin 22) : Bool := decide (i ∈ [3,6,7,10,11,12,20,21])
def keep (i : Fin 22) : Bool := right i || decide (i ∈ [8,15,13])

def program {q : ℕ} (hq : 2 ≤ q) := CleanExecution.program (LabelPrepare.program hq) right keep

/-- The view width already occupies slot 6. Only the other three dimensions need new slots. -/
def output (q : ℕ) (v : Descriptor) (k s t c B : ℕ) :=
  let u := LabelView.colView q c k s t B v
  let d := input v k s t c
  let d := Function.update d 8 (some (bits u.beforeH))
  let d := Function.update d 15 (some (bits u.between))
  Function.update d 13 (some (bits u.afterD))

theorem prepares {q : ℕ} (hq : 2 ≤ q) (v : Descriptor) (k s t c B : ℕ) (hs : s < t)
    (ht : t < k) (hc : 0 < c) (hb : 0 < B) (hp : v.Positive) (hv : v.beforeH = B*q^(k*c)) :
    HoareTime (program hq)
      (fun x => x = (Headers.bank (input v k s t c)).append (SharedBank.empty 22 q))
      (fun x => x = (Headers.bank (output q v k s t c B)).append (SharedBank.empty 22 q))
      (3808246 * volume q v) := by
  obtain ⟨d, h8, _, h15, h13, hframe, hrun⟩ := LabelPrepare.prepares hq v k s t c B hs ht hc hb hp hv
  have hclean := CleanExecution.realizes _ right keep _ _ _ (by funext i; fin_cases i <;> rfl)
    (by intro i hi; fin_cases i <;> first | rfl | contradiction) hrun
  have hret : TrackedCleanupList.retained keep (Headers.bank (q := q) d) =
      Headers.bank (output q v k s t c B) := by
    have hslot (i : Fin 22) : (if keep i then d i else none) = output q v k s t c B i := by
      fin_cases i <;> first | rfl | exact h8 | exact h15 | exact h13 | exact hframe _ rfl
    apply congrArg₂ Tapes.mk <;> funext i <;>
      cases hk : keep i <;>
      simp [Headers.bank, ← hslot i, hk,
        CounterDimensions.descriptorHead, CounterDimensions.descriptorTape]
  rw [hret] at hclean
  apply hclean.consequence (fun _ h => h) (fun _ h => h)
  have := RecursiveAffinePrepare.volume_positive hq v hp
  omega

/-- After the supplier releases the view, erase the three generated words in reverse order. -/
def release (q : ℕ) :=
  seq (seq (Headers.eraseAt (q := q) 13) (Headers.eraseAt 15)) (Headers.eraseAt 8)

theorem restores {q : ℕ} (v : Descriptor) (k s t c B : ℕ) :
    let u := LabelView.colView q c k s t B v
    HoareTime (release q) (fun x => x = Headers.bank (output q v k s t c B))
      (fun x => x = Headers.bank (input v k s t c))
      (2*((bits u.afterD).length + (bits u.between).length + (bits u.beforeH).length) + 14) := by
  let u := LabelView.colView q c k s t B v
  let d := output q v k s t c B
  have h₁ := Headers.erase_step (q := q) (d := d) (j := 13) (xs := bits u.afterD) rfl
  let d₁ := Function.update d (13 : Fin 22) none
  have h₂ := Headers.erase_step (q := q) (d := d₁) (j := 15) (xs := bits u.between) rfl
  let d₂ := Function.update d₁ (15 : Fin 22) none
  have h₃ := Headers.erase_step (q := q) (d := d₂) (j := 8) (xs := bits u.beforeH) rfl
  have hf : Function.update d₂ 8 none = input v k s t c := by
    funext i
    fin_cases i <;> rfl
  have h := (h₁.seq h₂).seq h₃
  apply h.consequence (fun _ h => h) (fun _ hx => hx.trans (congrArg Headers.bank hf)) (by dsimp [u]; omega)

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPrepareClean
