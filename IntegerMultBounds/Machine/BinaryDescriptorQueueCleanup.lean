import IntegerMultBounds.Machine.BinaryDescriptorQueueRewind

/-! Physically erase a completed forward field queue and restore its entire
blank tape/head zero. The EOF cursor is rewound with paid transitions before
the already verified counted-free word eraser runs. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorQueueCleanup
noncomputable section
open MarkedWordCleanup (one)
variable {a : ℕ}

def program : Program 1 13 a :=
  seq (seq BinaryDescriptorQueueRewind.program
    (BinaryDescriptorQueueRewind.moveProgram .left)) MarkedWordCleanup.program

private theorem left_runs (f : ℤ → Fin (a+4)) :
    HoareTime (BinaryDescriptorQueueRewind.moveProgram .left)
      (fun v => v=one f 1) (fun v => v=one f 0) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (one f 1)).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i z
    by_cases hz : z=1 <;> simp [one,hz]

theorem runs (xs : List (Fin (a+4))) (hn : ∀ x∈xs, x≠blank) :
    HoareTime program
      (fun v => v=one (putWord (fun _ => blank) 1 xs) (1+xs.length))
      (fun v => v=one (fun _ => blank) 0) (3*xs.length+13) := by
  have hr := BinaryDescriptorQueueRewind.runs xs hn
  have hl := left_runs (putWord (fun _ => blank) 1 xs)
  have hc := MarkedWordCleanup.cleanup_hoare xs hn
  exact ((hr.seq hl).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem fields_runs (ds : List ℕ) :
    HoareTime (program (a := a))
      (fun v => v=one (putWord (fun _ => blank) 1 (CompactComplexRootDigits.fields ds))
        (1+(CompactComplexRootDigits.fields (a := a) ds).length))
      (fun v => v=one (fun _ => blank) 0)
      (3*(CompactComplexRootDigits.fields (a := a) ds).length+13) :=
  runs _ (BinaryDescriptorQueueRewind.fields_nonblank ds)

end
end IntegerMultBounds.Machine.BinaryDescriptorQueueCleanup
