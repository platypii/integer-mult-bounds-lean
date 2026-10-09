import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersEndpoint

/-! Dirty-control layout headers are physically derived from the original
fourteen numeric words. U and the later-source T starts are retained-word
subtractions/additions on the genuine constructed prefix widths. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersData
noncomputable section
open ActiveRepairRankHeadersCommands ActivePrefixLayoutHeadersData
inductive Kind | target | compact | source deriving DecidableEq

def mode : Kind → Mode | .target => .target | _ => .compactAfter
def startU (k : Kind) (d : Inputs) := prefixWidth (mode k) d-d.w-(match k with | .source => d.H | _ => 0)
def startT (k : Kind) (d : Inputs) := match k with | .source => d.sourceOffset+d.rho | _ => targetStart (mode k) d
def values (k : Kind) (d : Inputs) : Fin 10 → ℕ :=
  ![prefixWidth (mode k) d,startT k d,startU k d,d.q,d.b,d.n,d.rho,d.n+1,d.rows,suffix (mode k) d]
def finished (k : Kind) (d : Inputs) : State := fun i =>
  if h : i.val<14 then some (originalValues d ⟨i.val,h⟩)
  else if h : i.val<24 then some (values k d ⟨i.val-14,by omega⟩) else none

def patch : Kind → List Command
  | .target | .compact => [.erase 16,.difference 14 6 16 (by decide)]
  | .source => [.erase 15,.copy 11 15 (by decide),.add 15 10 (by decide),
    .erase 16,.difference 14 6 26 (by decide),.difference 26 0 16 (by decide),.erase 26]

theorem patch_valid (k : Kind) (d : Inputs) (hw : d.w≤d.H) :
    validSchedule (patch k) (ActivePrefixLayoutHeadersData.finished (mode k) d) := by
  have h₁ : d.w≤prefixWidth .target d := by unfold prefixWidth; omega
  have h₂ : d.H+d.w≤prefixWidth .compactAfter d := by unfold prefixWidth; omega
  cases k <;> simp [patch,mode,validSchedule,valid,eval,ActivePrefixLayoutHeadersData.finished,
    ActivePrefixLayoutHeadersData.values,put,Function.update,originalValues]
  all_goals omega

theorem patch_eq (k : Kind) (d : Inputs) :
    execute (patch k) (ActivePrefixLayoutHeadersData.finished (mode k) d)=finished k d := by
  cases k <;> funext i <;> fin_cases i
  all_goals simp [patch,mode,execute,eval,ActivePrefixLayoutHeadersData.finished,
    ActivePrefixLayoutHeadersData.values,finished,values,startT,startU,put,Function.update,originalValues]

theorem cleanup_valid (k : Kind) (d : Inputs) : validSchedule outputCleanup (finished k d) := by
  simp [outputCleanup,validSchedule,valid,eval,finished]
theorem cleanup_eq (k : Kind) (d : Inputs) : execute outputCleanup (finished k d)=initial d := by
  funext i; fin_cases i
  all_goals simp [outputCleanup,execute,eval,finished,initial,Function.update]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersData
