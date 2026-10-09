import IntegerMultBounds.Machine.SharedBankFamily

/-! Raw extension preserves any selected public port view and physically blank
private bank. Tape counts and port maps remain symbolic. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullPlacedCommon
noncomputable section
variable {k c n a : ℕ}

theorem raw_payload {n : ℕ} (hn : k≤n) (v : Tapes k a) (ports : Fin c → Fin k) :
    SharedBank.payload (SharedBankStageInput.raw v n)
      (fun i => Fin.castLE hn (ports i))=
        SharedBank.payload v ports := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [SharedBankStageInput.raw,(ports i).isLt]

theorem raw_private {n : ℕ} (hn : k≤n) (v : Tapes k a) (ports : Fin c → Fin k)
    (hclean : SharedBank.strip v ports=SharedBank.empty k a) :
    SharedBank.strip (SharedBankStageInput.raw v n)
      (fun i => Fin.castLE hn (ports i))=SharedBank.empty n a := by
  have hh (i : Fin n) :
      (SharedBank.strip (SharedBankStageInput.raw v n)
        (fun j => Fin.castLE hn (ports j))).head i=0 ∧
      (SharedBank.strip (SharedBankStageInput.raw v n)
        (fun j => Fin.castLE hn (ports j))).tape i=(fun _ => blank) := by
    by_cases hk : i.val<k
    · have he : (∃j,Fin.castLE hn (ports j)=i) ↔
          ∃j,ports j=⟨i.val,hk⟩ := by
        constructor
        · rintro ⟨j,hj⟩; exact ⟨j,Fin.ext (congrArg (fun z : Fin n => z.val) hj)⟩
        · rintro ⟨j,hj⟩; exact ⟨j,Fin.ext (congrArg (fun z : Fin k => z.val) hj)⟩
      have hhead := congrFun (congrArg Tapes.head hclean) ⟨i.val,hk⟩
      have htape := congrFun (congrArg Tapes.tape hclean) ⟨i.val,hk⟩
      exact ⟨by simpa [SharedBank.strip,SharedBankStageInput.raw,hk,he,SharedBank.empty] using hhead,
        by simpa [SharedBank.strip,SharedBankStageInput.raw,hk,he,SharedBank.empty] using htape⟩
    · have hi : ¬∃j,Fin.castLE hn (ports j)=i := by
        rintro ⟨j,hj⟩
        have hx := congrArg Fin.val hj
        exact hk (hx ▸ (ports j).isLt)
      simp [SharedBank.strip,SharedBankStageInput.raw,hk,hi]
  apply congrArg₂ Tapes.mk
  · funext i; exact (hh i).1
  · funext i; exact (hh i).2

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullPlacedCommon
