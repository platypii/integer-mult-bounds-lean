import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyRun

namespace IntegerMultBounds.Machine.ActivePrefixStageFullCompose
open ActiveRepairLayoutRecordsPayloadEarlyRun (two two_runs)
variable {t a q r s b c d : ℕ} {M : Program t q a} {N : Program t r a} {K : Program t s a}
  {P Q R S : TapePred t a}
def three (M : Program t q a) (N : Program t r a) (K : Program t s a) := two (two M N) K
theorem three_runs (hM : HoareTime M P Q b) (hN : HoareTime N Q R c) (hK : HoareTime K R S d) :
    HoareTime (three M N K) P S (b+c+d+2) :=
  (two_runs (M := two M N) (N := K) (two_runs (M := M) (N := N) hM hN) hK).consequence
    (fun _ h => h) (fun _ h => h) (by omega)
end IntegerMultBounds.Machine.ActivePrefixStageFullCompose
