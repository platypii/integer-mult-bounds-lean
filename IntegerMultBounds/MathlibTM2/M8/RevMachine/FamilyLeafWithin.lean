module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.BlocksWithinReserve
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyControlBounds

/-! The complete leaf wrapper pays linear preparation and recovery around
its bounded stage-1 core. A smaller interval for the core reserves recovery
space independently of the core's runtime and returned payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open CommonBank (bank K)
open Routines (hdr)
open Blocks (seqB seq_runs seq_within Leading)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {T : ℕ}

def leafSpaceConstant (C : ℕ) : ℕ := C+2000

/-- Uniform prefix space for a core on equal-volume views. Concrete execution
suppliers prove this predicate; it carries no endpoint or runtime oracle. -/
def CoreSpace (core : Graph.Block (count T) prime) (Good : Descriptor → Tapes T prime → Prop)
    (C : ℕ) : Prop :=
  ∀ (v u : Descriptor), u.Positive → volume prime u = volume prime v →
    ∀ roles f p node scalar c st, Good v roles → ∀ lo hi : ℤ,
    (∀ n j, lo+(C*volume prime v : ℕ) ≤
      (raw (bank roles (hdr u) f p node scalar c st) n).head j ∧
      (raw (bank roles (hdr u) f p node scalar c st) n).head j+(C*volume prime v : ℕ) ≤ hi) →
    ∀ z, RunInvariant core.program (· = raw (bank roles (hdr u) f p node scalar c st) core.tapes) z →
      ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi

variable {roles : Tapes T prime} {f : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {st : Tapes 2 prime}

theorem leaf_runs_within {core : Graph.Block (count T) prime}
    {Good : Descriptor → Tapes T prime → Prop} {coreCost : ℕ → ℕ → ℕ} {C : ℕ}
    (hcore : LeafCore core Good coreCost) (hspace : CoreSpace core Good C) {v : Descriptor} {b m n r : ℕ}
    (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hfree : NodeFree node) (hg : Good v roles) (lo hi : ℤ)
    (hmargin : ∀ s j, lo+(leafSpaceConstant C*volume prime v : ℕ) ≤
      (raw (bank roles (hdr v) f p node scalar (leafC b m n r) st) s).head j ∧
      (raw (bank roles (hdr v) f p node scalar (leafC b m n r) st) s).head j+
        (leafSpaceConstant C*volume prime v : ℕ) ≤ hi) :
    ∃ roles', Good v roles' ∧ HoareWithin (leaf core).program
      (· = raw (bank roles (hdr v) f p node scalar (leafC b m n r) st) (leaf core).tapes)
      (· = raw (bank roles' (hdr v) f p node scalar (leafC b m n (r-1)) st) (leaf core).tapes)
      (leafCost coreCost v b n) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  set c₁ := Function.update (Function.update (Function.update (leafC b m n r) 12 (some (r - 1)))
    13 (some 1)) 14 (some (n - (r - 1) - 1))
  obtain ⟨B₁, hB₁, h₁⟩ := LeafRoutines.offsets_runs (roles := roles) (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := leafC b m n r) hr hrn
    (by simp [leafC]) (by simp [leafC]) (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
    (by simp [leafC, Prepare.rest]) (by simp [leafC, Prepare.rest])
  have h₂ := Blocks.push_runs roles (hdr v) f p node scalar c₁ st
  have h₃ := LeafRoutines.view_runs (roles := roles) (f := f) (p := p)
    (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st) (c := c₁)
    (Routines.hdr_headers v) hpos hb hw (s := r - 1) (cc := 1) (by omega) rfl
    (by simp [c₁, leafC, Prepare.rest]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  set u := RevMachine.sub prime b n (r - 1) 1 v
  have hu : Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1) = hdr u :=
    Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers v) rfl)
  have hvol : volume prime u = volume prime v := RevMachine.sub_volume prime b n (r - 1) 1 v hw (by omega)
  obtain ⟨roles', hg', h₄⟩ := hcore.2 v u b (hu ▸ Headers.child_headers (Routines.hdr_headers v) rfl)
    (by simp [u, RevMachine.sub]) hvol _ hu roles f p (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st hg
  have h₅ := Blocks.restore_runs roles' (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1))
    f p node scalar c₁ st (hdr v) (nodeFree_free hfree _)
  obtain ⟨B₆, hB₆, h₆⟩ := LeafRoutines.advance_runs (roles := roles') (hs := hdr v) (f := f) (p := p)
    (node := node) (scalar := scalar) (st := st) (c := c₁) (n := n) (r := r) (s := r - 1) (cc := 1)
    (e := n - (r - 1) - 1) hrn (by omega) (by omega) (by omega)
    (by simp [c₁, leafC]) (by simp [c₁]) (by simp [c₁]) (by simp [c₁])
  have hc : Function.update (Function.update (Function.update (Function.update c₁ 11 (some (r - 1))) 12 none)
      13 none) 14 none = leafC b m n (r - 1) := by
    funext j; fin_cases j <;> rfl
  rw [hc] at h₆

  have hp := RecursiveViewFrame.pushCost_le (hdr v) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
  have hq := RecursiveViewFrame.restoreCost_le (hdr v)
    (Headers.childHeaders (q := prime) v (hdr v) b (r - 1) 1 (n - (r - 1) - 1)) (hlen v)
    (fun z => RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le v hpos _
      (Routines.hdr_headers v) z)
    (fun z => by
      rw [hu]
      have := RecursiveAffinePrepare.header_log Networks.Shared50ModularControl.prime_prime.two_le u
        (sub_positive hpos) _ (Routines.hdr_headers u) z
      rwa [hvol] at this)
  have hV := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hpos
  have hnwidth : n ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_right _ hb
  have hnV : n ≤ volume prime v := hnwidth.trans
    ((show v.width ≤ (v.width+1)^2 by nlinarith).trans (width_square_le_volume v hpos))
  have hlenV : hlen v ≤ 2*volume prime v := by
    have h := Nat.log2_le_self (volume prime v)
    unfold hlen
    omega
  have hsetup : B₁+RecursiveViewFrame.pushCost (hdr v)+1500*volume prime v+2 ≤ 1800*volume prime v := by
    omega
  have htail : RecursiveViewFrame.restoreCost (hdr v)
      (Headers.childHeaders (q := prime) v (hdr v) b (r-1) 1 (n-(r-1)-1))+B₆ ≤ 200*volume prime v := by
    omega
  have hw₄ : Blocks.RawWithin core
      (bank roles (Headers.childHeaders (q := prime) v (hdr v) b (r-1) 1 (n-(r-1)-1)) f p
        (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st)
      (bank roles' (Headers.childHeaders (q := prime) v (hdr v) b (r-1) 1 (n-(r-1)-1)) f p
        (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st)
      (coreCost (volume prime v) b) (C*volume prime v) := by
    intro lower upper hm
    apply HoareWithin.of_time_invariant h₄
    intro z hz
    apply hspace v u (sub_positive hpos) hvol roles f p
      (RecursiveViewFrame.savedStack (hdr v) node) scalar c₁ st hg lower upper
    · simpa only [hu] using hm
    · simpa only [hu] using hz
  have htailRun := seq_runs (fun _ => rfl) (fun _ => rfl) h₅ h₆
  have L4 := Blocks.after_within hcore.1 (fun _ => rfl) hw₄ htailRun
  have L3 := Blocks.before_within (fun _ => rfl) (fun _ => rfl) h₃ L4
  have L2 := Blocks.before_within (fun _ => rfl) (fun _ => rfl) h₂ L3
  have L1 := Blocks.before_within (fun _ => rfl) (fun _ => rfl) h₁ L2
  refine ⟨roles',hg',?_⟩
  apply (L1 lo hi ?_).consequence (fun _ h => h) (fun _ h => h) ?_ (fun _ h => h)
  · intro length j
    have hm := hmargin length j
    have hreserve : B₁+(RecursiveViewFrame.pushCost (hdr v)+(1500*volume prime v+
        (C*volume prime v+
          (RecursiveViewFrame.restoreCost (hdr v)
            (Headers.childHeaders (q := prime) v (hdr v) b (r-1) 1 (n-(r-1)-1))+B₆+1)))) ≤
        leafSpaceConstant C*volume prime v := by
      unfold leafSpaceConstant
      rw [Nat.add_mul]
      omega
    omega
  · unfold leafCost
    omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
