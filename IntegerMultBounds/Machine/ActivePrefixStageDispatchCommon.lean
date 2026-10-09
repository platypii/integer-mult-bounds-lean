import IntegerMultBounds.Machine.ActivePrefixStageOrderCompare
import IntegerMultBounds.Machine.Branch

/-! Symbolic native conditional contracts with the actual flag read and paid
branch transition. Impossible alternatives add no artificial runtime. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchCommon
noncomputable section
variable {t q r a B : ℕ}

theorem branch_true (test : (Fin t → Fin (a+4)) → Bool)
    (M : Program t q a) (N : Program t r a) (v w : Tapes t a)
    (ht : test v.reads=true) (h : HoareTime M (fun x => x=v) (fun x => x=w) B) :
    HoareTime (branch test M N) (fun x => x=v) (fun x => x=w) (B+1) := by
  have hm : HoareTime M (fun x => x=v ∧ test x.reads=true) (fun x => x=w) B := h.consequence (fun _ hx => hx.1) (fun _ hx => hx) le_rfl
  have hn : HoareTime N (fun x => x=v ∧ test x.reads=false) (fun x => x=w) 0 := by
    rintro x ⟨rfl,hf⟩; rw [ht] at hf; contradiction
  simpa using branch_hoare test hm hn

theorem branch_false (test : (Fin t → Fin (a+4)) → Bool)
    (M : Program t q a) (N : Program t r a) (v w : Tapes t a)
    (ht : test v.reads=false) (h : HoareTime N (fun x => x=v) (fun x => x=w) B) :
    HoareTime (branch test M N) (fun x => x=v) (fun x => x=w) (B+1) := by
  have hm : HoareTime M (fun x => x=v ∧ test x.reads=true) (fun x => x=w) 0 := by
    rintro x ⟨rfl,hf⟩; rw [ht] at hf; contradiction
  have hn : HoareTime N (fun x => x=v ∧ test x.reads=false) (fun x => x=w) B := h.consequence (fun _ hx => hx.1) (fun _ hx => hx) le_rfl
  simpa using branch_hoare test hm hn

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchCommon
