module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbedHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbeGeometryHaloGatherStock

/-! The runtime probe produces its controlled bank with the geometry reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem probeAndGatherHaloControls_exec_within (P q s t u band a b L : ℕ)
    (_hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (_hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116, 88, 89, 90], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧ m ≤ probeAndGatherHaloControlsCost P q s t u band a b L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+probeGeometryHaloGatherWorkspace P q s t u band a b L)
        depth probeAndGatherHaloControls (mk v S) m
        (mk v' { S with R := probedHaloGatherR A P q s t u band a b L S.R })) := by
  simpa only [probeAndGatherHaloControls,probeAndGatherHaloControlsCost,probedHaloGatherR,probedGeometryHaloGatherR] using
    probeGeometryHaloGather_exec_within (body := body) P q s t u band a b L
      hs hst hband has hbs hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hblank hfresh

namespace ScalarPlacement

theorem probeHaloGroupInputBank_exec_within (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧ n ≤ probeAndGatherHaloControlsCost P q s t u band a b L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v (haloGroupInputBank P N q l s t u band a b L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out))+depth+
          probeGeometryHaloGatherWorkspace P q s t u band a b L)
        depth probeAndGatherHaloControls
        (mk v (haloGroupInputBank P N q l s t u band a b L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)) n
        (mk v' (probedHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out))) := by
  let w := 2*q+8
  let raw := cstream A w (chirpLine s C)
  let S := haloGroupInputBank P N q l s t u band a b L raw borrowed outTail inp out
  obtain ⟨v₁, n₁, hu₁, hflag₁, hn₁, he₁⟩ := probeAndGatherHaloControls_exec_within (body := body)
    P q s t u band a b L hP hs hst hu hband has hbs hL hLs hA v S
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff, hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 111 (by decide), hn 113 (by decide), hn 109 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
  refine ⟨v₁,n₁,hu₁,hflag₁,hn₁,?_⟩
  intro depth
  refine (he₁ depth).cast rfl ?_
  congr 1
  by_cases hB : 0 < (haloLengthGroup s t band a b L).length
  · simp only [probedHaloGroupInputBank,probedHaloGatherR,ite_eq_left hB]
    rfl
  · simp only [probedHaloGroupInputBank,probedHaloGatherR,ite_eq_right hB]
    rfl

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
