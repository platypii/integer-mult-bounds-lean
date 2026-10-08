import IntegerMultBounds.Machine.SharedBankSkeleton

/-! Literal initial banks for compiled initialized stages: only the permanent
leading bank is supplied, and every remaining tape is blank at head zero. -/
namespace IntegerMultBounds.Machine.SharedBankStageInput
open SharedBankStage
universe u
variable {X : Type u} {k a : ℕ} {common : X → Tapes k a}
noncomputable section

def raw (common : Tapes k a) (t : ℕ) : Tapes t a :=
  ⟨fun i => if h : i.val < k then common.head ⟨i.val,h⟩ else 0,
   fun i => if h : i.val < k then common.tape ⟨i.val,h⟩ else fun _ => blank⟩

theorem compile_slots_val (hk : 0 < k) (ss : List (Stage X k a common)) (i : Fin k) :
    ((compile common hk ss).slots i).val = i.val := by
  cases ss <;> rfl

theorem eq_raw {t : ℕ} (v : Tapes t a) (c : Tapes k a) (slots : Fin k → Fin t)
    (hv : ∀ i, (slots i).val = i.val) (hp : SharedBank.payload v slots = c)
    (hs : SharedBank.strip v slots = SharedBank.empty t a) : v = raw c t := by
  have hh (i : Fin t) : v.head i = (raw c t).head i ∧ v.tape i = (raw c t).tape i := by
    by_cases hi : i.val < k
    · let j : Fin k := ⟨i.val,hi⟩
      have hj : slots j = i := Fin.ext (hv j)
      have hhead := congrFun (congrArg Tapes.head hp) j
      have htape := congrFun (congrArg Tapes.tape hp) j
      simp only [SharedBank.payload,hj] at hhead htape
      exact ⟨by simpa only [raw,dite_eq_left hi] using hhead,
        by simpa only [raw,dite_eq_left hi] using htape⟩
    · have hn : ¬∃ j, slots j = i := by
        rintro ⟨j,hj⟩
        have he := congrArg Fin.val hj
        rw [hv] at he
        exact hi (he ▸ j.isLt)
      have hhead := congrFun (congrArg Tapes.head hs) i
      have htape := congrFun (congrArg Tapes.tape hs) i
      simp only [SharedBank.strip,SharedBank.empty,hn,ite_false] at hhead htape
      exact ⟨by simpa only [raw,dite_eq_right hi] using hhead,
        by simpa only [raw,dite_eq_right hi] using htape⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (hh i).1
  · funext i; exact (hh i).2

theorem compile_input_raw (hk : 0 < k) (ss : List (Stage X k a common))
    (hblank : ∀ s ∈ ss, s.metadata = SharedBank.empty s.tapes a) (x : X) :
    (compile common hk ss).input x = raw (common x) (compile common hk ss).tapes :=
  eq_raw _ _ _ (compile_slots_val hk ss) ((compile common hk ss).input_payload x)
    (((compile common hk ss).strip_input x).trans (compile_metadata_empty hk ss hblank))

/-- A previously chosen fixed machine starts with the literal common input and
blank private storage, and pays the complete sum of stage costs and joins. -/
theorem fixed_compile_hoare (hk : 0 < k) (ss : List (Stage X k a common))
    (hblank : ∀ s ∈ ss, s.metadata = SharedBank.empty s.tapes a)
    (sk : SharedBankSkeleton.Skeleton k a)
    (hsk : SharedBankSkeleton.ofStage (compile common hk ss) = sk) :
    ∃ output : X → Tapes sk.tapes a,
      ∀ x, HoareTime sk.program (fun v => v = raw (common x) sk.tapes)
        (fun v => v = output x ∧ SharedBank.payload v sk.slots = common (execute ss x))
        ((ss.map Stage.cost).sum+ss.length) := by
  subst sk
  refine ⟨(compile common hk ss).output,?_⟩
  intro x
  apply (compile_hoare hk ss x).consequence ?_ (fun _ h => h) le_rfl
  intro v hv
  exact hv.trans (compile_input_raw hk ss hblank x).symm

end
end IntegerMultBounds.Machine.SharedBankStageInput
