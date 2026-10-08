import IntegerMultBounds.Machine.PrefixCounterInit

/-! Static full-bank wiring of the actual prefix initializer. The generated
fields remain on the same physical tapes; clocks, immutable width descriptors,
and the spare tape form an exact frame of subsequent computation. -/
namespace IntegerMultBounds.Machine.PrefixCounterInitPlacement
open PrefixCounterInit
variable {q c : ℕ}

def extras (c : ℕ) := 2*c+1

/-- Group the field tapes first, then clock/descriptor pairs and the spare. -/
def wiring (c : ℕ) : Fin (c+extras c) ≃ Fin (tapeCount c) where
  toFun i := ⟨if i.val < c then 3*i.val else
    if i.val < 3*c then 3*((i.val-c)/2)+1+(i.val-c)%2 else 3*c, by
      have hi := i.isLt
      rw [tapeCount_eq]
      unfold extras at hi
      split_ifs <;> omega⟩
  invFun i := ⟨if i.val < 3*c then
    if i.val%3 = 0 then i.val/3 else c+2*(i.val/3)+(i.val%3-1) else 3*c, by
      have hi := i.isLt
      simp only [tapeCount_eq] at hi
      unfold extras
      split_ifs <;> omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    have hi := i.isLt
    unfold extras at hi
    dsimp
    split_ifs <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    have hi := i.isLt
    simp only [tapeCount_eq] at hi
    dsimp
    split_ifs <;> omega

theorem fieldSlot_val (i : Fin c) : (fieldSlot c i).val = 3*i.val := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simp only [fieldSlot_succ,Fin.val_natAdd,Fin.val_succ,ih]; omega

@[simp] theorem wiring_field (i : Fin c) : wiring c (Fin.castAdd (extras c) i) = fieldSlot c i := by
  apply Fin.ext
  simp [wiring,i.isLt,fieldSlot_val]

theorem active_wiring (v : Tapes (tapeCount c) q) :
    Placement.active (wiring c) v = fields c v := by
  unfold Placement.active fields
  simp only [wiring_field]

/-- Lift a tape permutation while keeping an arbitrary right frame fixed. -/
def appendEquiv {s t : ℕ} (e : Fin s ≃ Fin t) (r : ℕ) : Fin (s+r) ≃ Fin (t+r) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin r))).trans finSumFinEquiv)

@[simp] theorem appendEquiv_left {s t r : ℕ} (e : Fin s ≃ Fin t) (i : Fin s) :
    appendEquiv e r (Fin.castAdd r i) = Fin.castAdd r (e i) := by simp [appendEquiv]

@[simp] theorem appendEquiv_right {s t r : ℕ} (e : Fin s ≃ Fin t) (i : Fin r) :
    appendEquiv e r (Fin.natAdd s i) = Fin.natAdd t i := by simp [appendEquiv]

/-- Put the subsequent whole machine on its generated prefix and existing
metadata frame. This changes only tape names in a finite transition table. -/
def handoff {t r : ℕ} (e : Fin (c+r) ≃ Fin t) :
    Fin (t+extras c) ≃ Fin (tapeCount c+r) :=
  (appendEquiv e.symm (extras c)).trans (FamilyPlacement.withFrame (wiring c))

theorem active_handoff {t r : ℕ} (e : Fin (c+r) ≃ Fin t)
    (v : Tapes (tapeCount c) q) (frame : Tapes r q) :
    Placement.active (handoff e) (v.append frame) =
      Placement.combine e (fields c v) frame := by
  have h := FamilyPlacementAlphabet.active_withFrame (wiring c) v frame
  rw [active_wiring] at h
  unfold Placement.active handoff Placement.combine Tapes.reindex
  apply congrArg₂ Tapes.mk
  · funext i
    have hh := congrArg Tapes.head h
    simpa only [Equiv.trans_apply,appendEquiv_left,Placement.active] using congrFun hh (e.symm i)
  · funext i
    have hh := congrArg Tapes.tape h
    simpa only [Equiv.trans_apply,appendEquiv_left,Placement.active] using congrFun hh (e.symm i)

variable (hq : 2 ≤ q)

/-- Initialization and execution are literally sequential physical programs. -/
def program {t r k : ℕ} (M : Program t k q) (e : Fin (c+r) ≃ Fin t) :
    Program (tapeCount c+r) (stateCount c+k) q :=
  seq (extend (PrefixCounterInit.program hq c) r) (Placement.placed M (handoff e))

/-- A proved machine specification consumes the fields actually generated from
blank tapes. The complete complementary initializer tapes survive as a frame. -/
theorem initialize_then {t r k cost : ℕ} {M : Program t k q}
    (e : Fin (c+r) ≃ Fin t) (bs : Fin c → List Bool) (width : Fin c → ℕ)
    (hn : ∀ i, Counter.value (bs i) = width i) (hc : ∀ i, GrowingCounterData.Canonical (bs i))
    (v w : Tapes t q)
    (hv : Placement.active e v = PrefixCounter.tapes (fun _ => RadixZeroFill.radixEmpty)
      (fun i => RadixCounterData.zeros hq (width i)))
    (hm : HoareTime M (fun x => x = v) (fun x => x = w) cost) :
    HoareTime (program hq M e)
      (fun x => x = (PrefixCounterInit.input c bs).append (Placement.extra e v))
      (fun x => x = Placement.replace (handoff e)
        ((output hq c bs width).append (Placement.extra e v)) w)
      (15*(∑ i, width i)+29*c+cost+1) := by
  have hi := FamilyPlacementAlphabet.extend_hoare (initialize_hoare hq c bs width hn hc) (Placement.extra e v)
  have ha : Placement.active (handoff e) ((output hq c bs width).append (Placement.extra e v)) = v := by
    rw [active_handoff,output_fields,← hv]
    exact Placement.view e v
  have hh := Placement.hoare_at hm (handoff e) _ ha
  have hh' : HoareTime (Placement.placed M (handoff e))
      (fun x => x = (output hq c bs width).append (Placement.extra e v))
      (fun x => x = Placement.replace (handoff e)
        ((output hq c bs width).append (Placement.extra e v)) w) cost :=
    hh.consequence (fun _ h => h) (by rintro x ⟨y,rfl,rfl⟩; rfl) le_rfl
  exact (hi.seq hh').consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.PrefixCounterInitPlacement
