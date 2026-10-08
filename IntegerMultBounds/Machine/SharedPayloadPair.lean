import IntegerMultBounds.Machine.SharedPayload
import IntegerMultBounds.Machine.FamilyPlacementAlphabet

/-! Two actual stages use the same permanent payload pair and separate private
metadata. The second stage's private payload slots remain blank throughout;
its input comes solely from the first stage's physical common output. -/
namespace IntegerMultBounds.Machine.SharedPayloadPair
variable {t u q r a : ℕ}

/-- Keep the two common payloads fixed while selecting the second metadata bank. -/
def placement (t u : ℕ) : Fin ((2+u)+t) ≃ Fin ((2+t)+u) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd u (Fin.castAdd t i)) (Fin.natAdd (2+t)))
    (fun i => Fin.castAdd u (Fin.natAdd 2 i))
  invFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd t (Fin.castAdd u i)) (Fin.natAdd (2+u)))
    (fun i => Fin.castAdd t (Fin.natAdd 2 i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp

theorem active_bank (common : Tapes 2 a) (left : Tapes t a) (right : Tapes u a) :
    Placement.active (placement t u) ((common.append left).append right) = common.append right := by
  unfold Placement.active placement Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_bank (common : Tapes 2 a) (left : Tapes t a) (right : Tapes u a) :
    Placement.extra (placement t u) ((common.append left).append right) = left := by
  unfold Placement.extra placement Tapes.append
  congr 1 <;> funext i <;> simp

theorem combine_bank (common : Tapes 2 a) (left : Tapes t a) (right : Tapes u a) :
    Placement.combine (placement t u) (common.append right) left = (common.append left).append right := by
  have hh := Placement.view (placement t u) ((common.append left).append right)
  simpa only [active_bank,extra_bank] using hh

def input (v : Tapes t a) (x : Tapes u a) (source dest : Fin t) (source' dest' : Fin u) : Tapes ((2+t)+u) a :=
  (SharedPayload.bank v source dest).append (SharedPayload.strip x source' dest')

def output (w : Tapes t a) (y : Tapes u a) (source dest : Fin t) (source' dest' : Fin u) : Tapes ((2+t)+u) a :=
  ((SharedPayload.payload y source' dest').append (SharedPayload.strip w source dest)).append
    (SharedPayload.strip y source' dest')

noncomputable def program (M : Program t q a) (N : Program u r a)
    (source dest : Fin t) (hne : source ≠ dest) (source' dest' : Fin u) (hne' : source' ≠ dest') :=
  seq (extend (Placement.placed M (SharedPayload.placement source dest hne)) u)
    (Placement.placed (Placement.placed N (SharedPayload.placement source' dest' hne')) (placement t u))

/-- A physical two-stage handoff with literal private frames. Compatibility
identifies only the existing common pair, never copied per-stage payloads. -/
theorem pair_hoare {M : Program t q a} {N : Program u r a} {v w : Tapes t a} {x y : Tapes u a}
    {k l : ℕ} (hM : HoareTime M (fun z => z = v) (fun z => z = w) k)
    (hN : HoareTime N (fun z => z = x) (fun z => z = y) l)
    (source dest : Fin t) (hne : source ≠ dest) (source' dest' : Fin u) (hne' : source' ≠ dest')
    (hcommon : SharedPayload.payload w source dest = SharedPayload.payload x source' dest') :
    HoareTime (program M N source dest hne source' dest' hne')
      (fun z => z = input v x source dest source' dest')
      (fun z => z = output w y source dest source' dest') (k+l+1) := by
  have hm := FamilyPlacementAlphabet.extend_hoare (SharedPayload.stage_hoare hM source dest hne)
    (SharedPayload.strip x source' dest')
  have hn := SharedPayload.stage_hoare hN source' dest' hne'
  have hactive : Placement.active (placement t u)
      ((SharedPayload.bank w source dest).append (SharedPayload.strip x source' dest')) =
      SharedPayload.bank x source' dest' := by
    rw [SharedPayload.bank,active_bank,hcommon]
    rfl
  have hh := Placement.hoare_at hn (placement t u)
    ((SharedPayload.bank w source dest).append (SharedPayload.strip x source' dest')) hactive
  have hh' : HoareTime (Placement.placed (Placement.placed N (SharedPayload.placement source' dest' hne')) (placement t u))
      (fun z => z = (SharedPayload.bank w source dest).append (SharedPayload.strip x source' dest'))
      (fun z => z = output w y source dest source' dest') l := by
    apply hh.consequence (fun _ h => h) ?_ le_rfl
    rintro z ⟨small,hsmall,rfl⟩
    subst small
    simp only [Placement.replace,SharedPayload.bank,extra_bank,combine_bank,output]
  exact (hm.seq hh').consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.SharedPayloadPair
