module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHeaders

/-! The descriptor loop owns only its queue, counter and packed output.
Every retained scalar, borrowed source and scratch invariant survives a step. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host

def replicaLoopR {A : ℕ} (R : Regs 144 A) (queue count output : List (Fin (A+4))) : Regs 144 A :=
  Function.update (Function.update (Function.update R 126 queue) 127 count) 93 output

theorem replicaLoopR_off {A : ℕ} (R : Regs 144 A) (queue count output : List (Fin (A+4)))
    (k : Fin 144) (h126 : k ≠ 126) (h127 : k ≠ 127) (h93 : k ≠ 93) :
    replicaLoopR R queue count output k = R k := by simp [replicaLoopR,h126,h127,h93]

theorem replicaLoopR_comp {A : ℕ} (R : Regs 144 A)
    (queue count output queue' count' output' : List (Fin (A+4))) :
    replicaLoopR (replicaLoopR R queue count output) queue' count' output' =
      replicaLoopR R queue' count' output' := by
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h93 : k = 93 <;>
    simp [replicaLoopR,Function.update_apply,h126,h127,h93]

theorem replicaLoopR_self {A : ℕ} (R : Regs 144 A) : replicaLoopR R (R 126) (R 127) (R 93) = R := by
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h93 : k = 93 <;>
    simp_all [replicaLoopR]

structure ReplicaCellReady {A : ℕ} (P N q l s t u band B V w : ℕ)
    (input : List (Fin (A+4))) (S : Stacks 144 A) : Prop where
  masters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length = groupHeaderValue P N q l s t u band 0 r.1
  left : ∀ k : Fin 144, k.val < 117 → S.L k = []
  blank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = []
  source : S.R 110 = input
  replicas : (S.R 142).length = B
  origin : S.R 141 = []
  countSaved : S.R 129 = []
  headerTemp : S.R 133 = []
  wordWidth : (S.R 130).length = w
  keyWidth : (S.R 125).length = V
  fresh : ∀ k ∈ [(128 : Fin 144),131,134,135,136,137], S.R k = []

theorem ReplicaCellReady.of_frame {A P N q l s t u band B V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 144 A}
    (h : ReplicaCellReady P N q l s t u band B V w input S)
    (queue count output : List (Fin (A+4))) (hL : S'.L = S.L)
    (hR : S'.R = replicaLoopR S.R queue count output) :
    ReplicaCellReady P N q l s t u band B V w input S' := by
  constructor
  · intro r hr
    have hh := h.masters r hr
    rw [hR]
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [replicaLoopR] using hh
  · intro k hk; rw [hL]; exact h.left k hk
  · intro k hk hk93 hk110
    rw [hR,replicaLoopR_off _ _ _ _ k (by intro he; subst k; norm_num at hk)
      (by intro he; subst k; norm_num at hk) hk93]
    exact h.blank k hk hk93 hk110
  · simpa [hR,replicaLoopR] using h.source
  · simpa [hR,replicaLoopR] using h.replicas
  · simpa [hR,replicaLoopR] using h.origin
  · simpa [hR,replicaLoopR] using h.countSaved
  · simpa [hR,replicaLoopR] using h.headerTemp
  · simpa [hR,replicaLoopR] using h.wordWidth
  · simpa [hR,replicaLoopR] using h.keyWidth
  · intro k hk
    have h126 : k ≠ 126 := by intro he; subst k; norm_num at hk
    have h127 : k ≠ 127 := by intro he; subst k; norm_num at hk
    have h93 : k ≠ 93 := by intro he; subst k; norm_num at hk
    rw [hR,replicaLoopR_off _ _ _ _ k h126 h127 h93]
    exact h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
