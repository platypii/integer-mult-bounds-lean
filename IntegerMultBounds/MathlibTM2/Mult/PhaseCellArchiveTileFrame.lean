module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlan

/-! Readiness depends only on an explicit finite bank. A preceding transpose
may change its own source without invalidating a disjoint next tile. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q c d W K N : ℕ}

def roles (plan : ArchiveTilePlan t₀ T Q c d W) : List (Fin T) :=
  [plan.src,plan.base,plan.one,plan.width,plan.exponent,plan.powTmp,plan.powSaved,
    plan.a,plan.half,plan.par,plan.bits,plan.cnt,plan.work,plan.count,plan.tmp,plan.saved,plan.reRev,plan.imRev]

noncomputable def support (plan : ArchiveTilePlan t₀ T Q c d W) : List (Fin T) :=
  plan.roles++plan.ps++plan.bs++List.ofFn plan.ι

theorem embedded_mem_support (plan : ArchiveTilePlan t₀ T Q c d W) (j : Fin (swapT t₀)) :
    plan.ι j ∈ plan.support := by
  simp only [support,List.mem_append]
  exact Or.inr (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem BankReady.of_frame {plan : ArchiveTilePlan t₀ T Q c d W}
    {S F : Stacks T (prime+K)}
    (h : plan.BankReady S) (hR : ∀ i ∈ plan.support, F.R i = S.R i) (hL : F.L = S.L) :
    plan.BankReady F := by
  have hroles (i : Fin T) (hi : i ∈ plan.roles) : F.R i = S.R i := hR i (by simp [support,hi])
  have hbank (j : Fin (swapT t₀)) : F.R (plan.ι j) = S.R (plan.ι j) :=
    hR _ (embedded_mem_support plan j)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hroles _ (by simp [roles])]; exact h.hbase
  · rw [hroles _ (by simp [roles])]; exact h.hone
  · rw [hroles _ (by simp [roles])]; exact h.hwidth
  · rw [hroles _ (by simp [roles])]; exact h.hexponent
  · intro i hi
    have hm : i ∈ plan.support := by
      simp only [List.mem_append] at hi
      simp only [support,List.mem_append]
      rcases hi with hi | hi
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
    rw [hR i hm]; exact h.hblank i hi
  · rw [hroles _ (by simp [roles])]; exact h.htmp
  · rw [hroles _ (by simp [roles])]; exact h.hsaved
  · intro i; rw [hL]; exact h.hL i
  · intro j hj; rw [hbank]; exact h.hpriv j hj
  · intro k; rw [hbank]; exact h.hhdr k
  · intro i hi
    have hm : i ∈ plan.roles := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roles]
    rw [hroles i hm]; exact h.hgenBlank i hi
  · rw [hroles _ (by simp [roles])]; exact h.hcount
  · intro i hi
    have he : F.R i = S.R i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbank _
      · exact hbank _
      all_goals apply hroles; simp [roles]
    rw [he]; exact h.hcodecBlank i hi
  · intro i hre him hhd
    rw [hbank]
    exact h.hother i hre him hhd

theorem Ready.of_frame {plan : ArchiveTilePlan t₀ T Q c d W} {w : ℕ}
    {rows : Fin N → Fin (2^d) → List GaussianInt} {S F : Stacks T (prime+K)}
    (h : plan.Ready w rows S) (hR : ∀ i ∈ plan.support, F.R i = S.R i) (hL : F.L = S.L) :
    plan.Ready w rows F := by
  refine ⟨h.toBankReady.of_frame hR hL,?_⟩
  rw [hR plan.src (by simp [support,roles])]
  exact h.hsrc

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
