import IntegerMultBounds.Machine.Hoare

/-! Sigma-packaged finite programs compose with their exact state indices,
physical join cost and unchanged tape predicates. -/
namespace IntegerMultBounds.Machine.ProgramPairSequence
noncomputable section
variable {t a : ℕ}
def pair (P Q : Σ q,Program t q a) : Σ q,Program t q a :=
  ⟨P.1+Q.1,seq P.2 Q.2⟩
theorem runs (P Q : Σ q,Program t q a) {pre middle post : TapePred t a} {b c : ℕ}
    (hp : HoareTime P.2 pre middle b) (hq : HoareTime Q.2 middle post c) :
    HoareTime (pair P Q).2 pre post (b+1+c) := hp.seq hq
theorem bound {q : ℕ} {P : Program t q a} {pre post : TapePred t a} {b c : ℕ}
    (hp : HoareTime P pre post b) (hc : b≤c) : HoareTime P pre post c :=
  hp.consequence (fun _ h => h) (fun _ h => h) hc
end
end IntegerMultBounds.Machine.ProgramPairSequence

