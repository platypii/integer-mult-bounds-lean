module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataInstall

/-!
# Executed routing metadata cleanup

Clear exactly the installed metadata destinations, with a structural exact cost.
Configuration tapes, the record stream and every unrelated register are retained.
Clearing an installed bank restores the original register file when its destinations
were initially empty, including after the record stream has changed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def metadataCleared (R : Fin T → List (Fin (A + 4))) : List (Fin T) → Fin T → List (Fin (A + 4))
  | [] => R
  | k :: ks => Function.update (metadataCleared R ks) k []

def metadataClean : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | k :: ks => .seq (metadataClean ks) (bclear k)

def metadataCleanCost (R : Fin T → List (Fin (A + 4))) : List (Fin T) → ℕ
  | [] => 1
  | k :: ks => metadataCleanCost R ks + (2 * (R k).length + 2)

/-- Exact cleanup cost is bounded by destination count and a common word width. -/
theorem metadataCleanCost_le (R : Fin T → List (Fin (A + 4))) (keys : List (Fin T)) (L : ℕ)
    (hL : ∀ j ∈ keys, (R j).length ≤ L) :
    metadataCleanCost R keys ≤ keys.length * (2 * L + 2) + 1 := by
  induction keys with
  | nil => simp [metadataCleanCost]
  | cons j keys ih =>
    have hj := hL j (by simp)
    have ht := ih (fun k hk => hL k (by simp [hk]))
    simp only [metadataCleanCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Every installed destination contains exactly its specified metadata word. -/
theorem metadataInstalled_at (R : Fin T → List (Fin (A + 4))) (jobs : List (MetadataJob T))
    (hdst : (jobs.map MetadataJob.dst).Nodup) (job : MetadataJob T) (hj : job ∈ jobs) :
    metadataInstalled R jobs job.dst = job.contents R := by
  induction jobs with
  | nil => simp at hj
  | cons head jobs ih =>
    have hn := List.nodup_cons.mp hdst
    rcases List.mem_cons.mp hj with rfl | hj
    · simp [metadataInstalled]
    · have hne : job.dst ≠ head.dst := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨job, hj, he⟩)
      rw [metadataInstalled, Function.update_of_ne hne]
      exact ih hn.2 hj

/-- Installed metadata is priced from its contents, independently of the old bank. -/
theorem metadataInstalled_cleanCost_le (R : Fin T → List (Fin (A + 4)))
    (jobs : List (MetadataJob T)) (hdst : (jobs.map MetadataJob.dst).Nodup) (L : ℕ)
    (hcontents : ∀ job ∈ jobs, (job.contents R).length ≤ L) :
    metadataCleanCost (metadataInstalled R jobs) (jobs.map MetadataJob.dst) ≤
      jobs.length * (2 * L + 2) + 1 := by
  have hc := metadataCleanCost_le (metadataInstalled R jobs) (jobs.map MetadataJob.dst) L (by
    intro j hj
    obtain ⟨job, hjob, rfl⟩ := List.mem_map.mp hj
    rw [metadataInstalled_at R jobs hdst job hjob]
    exact hcontents job hjob)
  simpa only [List.length_map] using hc

theorem metadataCleared_keep (R : Fin T → List (Fin (A + 4))) (ks : List (Fin T))
    (k : Fin T) (hk : k ∉ ks) : metadataCleared R ks k = R k := by
  induction ks with
  | nil => rfl
  | cons j js ih =>
    have hne : k ≠ j := by intro he; exact hk (by simp [he])
    rw [metadataCleared, Function.update_of_ne hne]
    exact ih (fun hm => hk (by simp [hm]))

theorem metadataCleared_at (R : Fin T → List (Fin (A + 4))) (ks : List (Fin T))
    (k : Fin T) (hk : k ∈ ks) : metadataCleared R ks k = [] := by
  induction ks with
  | nil => simp at hk
  | cons j js ih =>
    by_cases hkj : k = j
    · subst k; simp [metadataCleared]
    · rw [metadataCleared, Function.update_of_ne hkj]
      apply ih
      rcases List.mem_cons.mp hk with he | hj
      · exact (hkj he).elim
      · exact hj

/-- Concrete cleanup with its exact cost, preserving all other stacks. -/
theorem metadataClean_exec (body : P → Pr P T Q A U) (ks : List (Fin T)) (hks : ks.Nodup)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean ks) (mk v S) (metadataCleanCost S.R ks)
        (mk v' { S with R := metadataCleared S.R ks }) := by
  induction ks generalizing v S with
  | nil => exact ⟨v, rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons k ks ih =>
    have hn := List.nodup_cons.mp hks
    obtain ⟨v₁, hu₁, he₁⟩ := ih hn.2 v S
    obtain ⟨v₂, hu₂, _, he₂⟩ := bclear_exec body k v₁ { S with R := metadataCleared S.R ks }
    have hk : (metadataCleared S.R ks k).length = (S.R k).length := by
      rw [metadataCleared_keep S.R ks k hn.1]
    dsimp only at he₂
    rw [hk] at he₂
    exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

/-- Cleanup restores the original empty metadata destinations, not the configuration. -/
theorem metadataClean_restore (R : Fin T → List (Fin (A + 4))) (jobs : List (MetadataJob T))
    (hempty : ∀ job ∈ jobs, R job.dst = []) :
    metadataCleared (metadataInstalled R jobs) (jobs.map MetadataJob.dst) = R := by
  funext k
  by_cases hk : k ∈ jobs.map MetadataJob.dst
  · rw [metadataCleared_at _ _ k hk]
    obtain ⟨job, hj, rfl⟩ := List.mem_map.mp hk
    exact (hempty job hj).symm
  · rw [metadataCleared_keep _ _ k hk, metadataInstalled_keep _ _ k hk]

/-- Updating the stream commutes with cleanup of disjoint metadata registers. -/
theorem metadataCleared_update (R : Fin T → List (Fin (A + 4))) (ks : List (Fin T))
    (str : Fin T) (w : List (Fin (A + 4))) (hstr : str ∉ ks) :
    metadataCleared (Function.update R str w) ks = Function.update (metadataCleared R ks) str w := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hne : str ≠ k := by intro he; exact hstr (by simp [he])
    rw [metadataCleared, ih (fun hm => hstr (by simp [hm])), metadataCleared]
    exact Function.update_comm hne w [] (metadataCleared R ks)

theorem metadataCleanCost_congr {R R' : Fin T → List (Fin (A + 4))}
    (ks : List (Fin T)) (h : ∀ k ∈ ks, R k = R' k) :
    metadataCleanCost R ks = metadataCleanCost R' ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [metadataCleanCost, metadataCleanCost, h k (by simp), ih (fun j hj => h j (by simp [hj]))]

end IntegerMultBounds.MathlibTM2.Routing
