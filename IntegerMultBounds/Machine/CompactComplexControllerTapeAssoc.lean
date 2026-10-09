import IntegerMultBounds.Machine.CompactComplexRootPieceQueue

/-! Zero-cost reassociation of the numeric43, queue1 and arbitrary appended
native/controller bank. All persistent recursive storage may be placed in
this appended bank, beyond the original native66 private workspace. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerTapeAssoc
variable {a t q : ℕ}

def placement : Fin (44+t) ≃ Fin (43+(1+t)) := finCongr (by omega)

theorem associate (v : Tapes 43 a) (queue : Tapes 1 a) (tail : Tapes t a) :
    ((v.append queue).append tail).reindex placement=v.append (queue.append tail) := by
  unfold Tapes.reindex Tapes.append
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin.append (Fin.append v.head queue.head) tail.head (placement.symm i)= _
    rw [Fin.append_assoc]
    change Fin.append v.head (Fin.append queue.head tail.head)
      (Fin.cast (Nat.add_assoc 43 1 t) (placement.symm i))=
        Fin.append v.head (Fin.append queue.head tail.head) i
    apply congrArg (Fin.append v.head (Fin.append queue.head tail.head))
    apply Fin.ext
    rfl
  · funext i
    change Fin.append (Fin.append v.tape queue.tape) tail.tape (placement.symm i)= _
    rw [Fin.append_assoc]
    change Fin.append v.tape (Fin.append queue.tape tail.tape)
      (Fin.cast (Nat.add_assoc 43 1 t) (placement.symm i))=
        Fin.append v.tape (Fin.append queue.tape tail.tape) i
    apply congrArg (Fin.append v.tape (Fin.append queue.tape tail.tape))
    apply Fin.ext
    rfl

def program {k : ℕ} (M : Program (44+t) k a) := reindex M placement

theorem hoare {M : Program (44+t) q a} {v v' : Tapes 43 a}
    {queue queue' : Tapes 1 a} {tail tail' : Tapes t a} {B : ℕ}
    (h : HoareTime M (fun w => w=(v.append queue).append tail)
      (fun w => w=(v'.append queue').append tail') B) :
    HoareTime (program M) (fun w => w=v.append (queue.append tail))
      (fun w => w=v'.append (queue'.append tail')) B := by
  have hp := h.reindex placement
  apply hp.consequence _ _ le_rfl
  · rintro w rfl
    exact ⟨_,rfl,by rw [associate]⟩
  · rintro w ⟨u,rfl,rfl⟩
    exact associate _ _ _

end IntegerMultBounds.Machine.CompactComplexControllerTapeAssoc
