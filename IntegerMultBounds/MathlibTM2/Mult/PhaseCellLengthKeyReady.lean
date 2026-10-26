module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyFrame

/-! The reusable register invariant between decoded-key iterations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

structure LengthKeyReady {A : ℕ} (P N q l s t u band V w : ℕ)
    (input : List (Fin (A+4))) (S : Stacks 144 A) : Prop where
  masters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length = groupHeaderValue P N q l s t u band 0 r.1
  left : ∀ k : Fin 144, k.val < 117 → S.L k = []
  blank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = []
  source : S.R 110 = input
  countSaved : S.R 129 = []
  headerTemp : S.R 133 = []
  wordWidth : (S.R 130).length = w
  keyWidth : (S.R 125).length = V
  fresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137,140], S.R k = []

theorem LengthKeyReady.of_frame {A P N q l s t u band V w : ℕ} {input : List (Fin (A+4))}
    {S S' : Stacks 144 A} (h : LengthKeyReady P N q l s t u band V w input S)
    (keys count output : List (Fin (A+4))) (hL : S'.L = S.L) (hR : S'.R = keyLoopR S.R keys count output) :
    LengthKeyReady P N q l s t u band V w input S' := by
  constructor
  · rw [hR]
    exact keyLoopR_headers S.R keys count output (groupHeaderValue P N q l s t u band 0) h.masters
  · intro k hk
    rw [hL]
    exact h.left k hk
  · intro k hk hk93 hk110
    rw [hR,keyLoopR_off S.R keys count output k (by omega) (by omega) (by omega)]
    exact h.blank k hk hk93 hk110
  · simpa [hR,keyLoopR] using h.source
  · simpa [hR,keyLoopR] using h.countSaved
  · simpa [hR,keyLoopR] using h.headerTemp
  · simpa [hR,keyLoopR] using h.wordWidth
  · simpa [hR,keyLoopR] using h.keyWidth
  · intro k hk
    have h126 : k ≠ 126 := by intro he; subst k; norm_num at hk
    have h127 : k ≠ 127 := by intro he; subst k; norm_num at hk
    have h132 : k ≠ 132 := by intro he; subst k; norm_num at hk
    rw [hR,keyLoopR_off S.R keys count output k h126 h127 h132]
    exact h.fresh k hk

theorem LengthKeyReady.update_output {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S) (output : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w input
      {S with R := Function.update S.R 132 output} := by
  apply h.of_frame (S' := {S with R := Function.update S.R 132 output})
    (S.R 126) (S.R 127) output rfl
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h132 : k = 132 <;>
    simp [keyLoopR,h126,h127,h132]

theorem LengthKeyReady.update_source {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S) (source : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w source
      {S with R := Function.update S.R 110 source} := by
  constructor
  · intro r hr
    have hr110 : r.1 ≠ 110 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hr110] using h.masters r hr
  · exact h.left
  · intro k hk hk93 hk110
    simpa only [Function.update_of_ne hk110] using h.blank k hk hk93 hk110
  · simp
  · simpa using h.countSaved
  · simpa using h.headerTemp
  · simpa using h.wordWidth
  · simpa using h.keyWidth
  · intro k hk
    have hk110 : k ≠ 110 := by intro he; subst k; norm_num at hk
    simpa only [Function.update_of_ne hk110] using h.fresh k hk

theorem count_head_isSome {A : ℕ} (keys : List ℕ) :
    (List.replicate keys.length (IntegerMultBounds.MathlibTM2.Node.tick : Fin (A+4))).head?.isSome = keys.head?.isSome := by
  cases keys <;> rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
