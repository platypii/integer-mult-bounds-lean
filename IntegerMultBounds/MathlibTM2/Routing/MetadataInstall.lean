module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-!
# Structural installation of a fixed routing metadata bank

All sources are restored configuration tapes, all destinations start empty, and
three shared work registers return empty. Jobs execute from the end of their fixed
list; numerical sizes remain tape data and proof annotations rather than unrolled
program structure. The theorem charges every job, including unary construction.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def metadataInstalled (R : Fin T → List (Fin (A + 4))) :
    List (MetadataJob T) → Fin T → List (Fin (A + 4))
  | [] => R
  | job :: jobs => Function.update (metadataInstalled R jobs) job.dst (job.contents R)

def metadataInstall (work tmp ctmp : Fin T) : List (MetadataJob T) → Pr P T Q A U
  | [] => .act .done
  | job :: jobs => .seq (metadataInstall work tmp ctmp jobs) (job.program work tmp ctmp)

def metadataInstallCost (R : Fin T → List (Fin (A + 4))) : List (MetadataJob T) → ℕ
  | [] => 1
  | job :: jobs => metadataInstallCost R jobs + job.cost R

theorem metadataInstallCost_le (R : Fin T → List (Fin (A + 4)))
    (jobs : List (MetadataJob T)) (budget : ℕ)
    (hcost : ∀ job ∈ jobs, job.cost R ≤ budget) :
    metadataInstallCost R jobs ≤ jobs.length * budget + 1 := by
  induction jobs with
  | nil => simp [metadataInstallCost]
  | cons job jobs ih =>
    have hc := hcost job (by simp)
    have ht := ih (fun other hm => hcost other (List.mem_cons_of_mem _ hm))
    simp only [metadataInstallCost, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem metadataInstalled_keep (R : Fin T → List (Fin (A + 4))) (jobs : List (MetadataJob T))
    (k : Fin T) (hk : k ∉ jobs.map MetadataJob.dst) : metadataInstalled R jobs k = R k := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    have hne : k ≠ job.dst := by intro he; exact hk (by simp [he])
    simp only [metadataInstalled, Function.update_of_ne hne]
    exact ih (fun hm => hk (by simp [hm]))

namespace MetadataJob

theorem contents_congr (job : MetadataJob T) {R R' : Fin T → List (Fin (A + 4))}
    (h : R job.src = R' job.src) : job.contents R = job.contents R' := by
  cases job <;> simp_all [contents, src]

theorem cost_congr (job : MetadataJob T) {R R' : Fin T → List (Fin (A + 4))}
    (h : R job.src = R' job.src) : job.cost R = job.cost R' := by
  cases job <;> simp_all [cost, src]

theorem data_congr (job : MetadataJob T) {R R' : Fin T → List (Fin (A + 4))}
    (h : R job.src = R' job.src) : job.Data R ↔ job.Data R' := by
  cases job <;> simp_all [Data, src]

end MetadataJob

/-- Install an arbitrary fixed metadata bank using concrete host operations. -/
theorem metadataInstall_exec (body : P → Pr P T Q A U) (jobs : List (MetadataJob T))
    (work tmp ctmp : Fin T) (hdst : (jobs.map MetadataJob.dst).Nodup)
    (hregs : ∀ job ∈ jobs, [job.src, job.dst, work, tmp, ctmp].Nodup)
    (hsource : ∀ job ∈ jobs, ∀ other ∈ jobs, job.src ≠ other.dst)
    (v : HS T Q A U) (S : Stacks T A)
    (hdata : ∀ job ∈ jobs, job.Data S.R) (hempty : ∀ job ∈ jobs, S.R job.dst = [])
    (hw : S.R work = []) (ht : S.R tmp = []) (hc : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ metadataInstallCost S.R jobs ∧
      Exec body (metadataInstall work tmp ctmp jobs) (mk v S) m
        (mk v' { S with R := metadataInstalled S.R jobs }) := by
  induction jobs generalizing v S with
  | nil =>
    exact ⟨v, 1, rfl, le_rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons job jobs ih =>
    have hn := List.nodup_cons.mp hdst
    have htail : ∀ j ∈ jobs, j ∈ job :: jobs := fun j hj => by simp [hj]
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := ih hn.2
      (fun j hj => hregs j (htail j hj))
      (fun j hj k hk => hsource j (htail j hj) k (htail k hk)) v S
      (fun j hj => hdata j (htail j hj)) (fun j hj => hempty j (htail j hj)) hw ht hc
    let R₁ := metadataInstalled S.R jobs
    have hs : R₁ job.src = S.R job.src := by
      apply metadataInstalled_keep
      intro hm
      obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
      exact hsource job (by simp) other (htail other ho) he.symm
    have hd : R₁ job.dst = [] := by
      change metadataInstalled S.R jobs job.dst = []
      rw [metadataInstalled_keep S.R jobs job.dst hn.1]
      exact hempty job (by simp)
    have hscratch (k : Fin T) (hk : k ∈ [work, tmp, ctmp]) : R₁ k = S.R k := by
      apply metadataInstalled_keep
      intro hm
      obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
      have hother := hregs other (htail other ho)
      have hn := (List.nodup_cons.mp (List.nodup_cons.mp hother).2).1
      exact hn (by simpa [he] using hk)
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := MetadataJob.exec body job work tmp ctmp
      (hregs job (by simp)) v₁ { S with R := R₁ }
      ((job.data_congr hs).mpr (hdata job (by simp))) hd
      (by simpa only [hscratch work (by simp)] using hw)
      (by simpa only [hscratch tmp (by simp)] using ht)
      (by simpa only [hscratch ctmp (by simp)] using hc)
    rw [job.contents_congr hs] at he₂
    rw [job.cost_congr hs] at hm₂
    exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
