import IntegerMultBounds.Machine.ActivePrefixStageFullCompose

/-! A proved involutive array action gives the actual same-machine return
execution and an exact paid round trip, for arbitrary physical caller banks. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageInverseMachine
noncomputable section
variable {t q a B : ℕ} {X : Type*}

def twice (M : Program t q a) := seq M M

theorem undo (M : Program t q a) (bank : X → Tapes t a) (f : X → X)
    (hf : Function.Involutive f)
    (h : ∀ x, HoareTime M (fun w => w=bank x) (fun w => w=bank (f x)) B) (x : X) :
    HoareTime M (fun w => w=bank (f x)) (fun w => w=bank x) B := by
  have hr := h (f x)
  rw [hf x] at hr
  exact hr

theorem pair (M : Program t q a) (bank : X → Tapes t a) (f : X → X)
    (hf : Function.Involutive f)
    (h : ∀ x, HoareTime M (fun w => w=bank x) (fun w => w=bank (f x)) B) (x : X) :
    HoareTime (twice M) (fun w => w=bank x) (fun w => w=bank x) (2*B+1) :=
  ((h x).seq (undo M bank f hf h x)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ActivePrefixStageInverseMachine
