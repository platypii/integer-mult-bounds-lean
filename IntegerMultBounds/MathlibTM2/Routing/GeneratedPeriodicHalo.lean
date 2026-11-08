module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloMetadata
public import IntegerMultBounds.MathlibTM2.Routing.PreparedPeriodicHalo

/-! Complete current-fiber target-halo supplier. All transient controls, window
metadata and loop counts are generated from retained ordinary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.GeneratedPeriodicHalo
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloIntervalLayout RegularHaloLayout PeriodicHaloStream
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def emit : Pr P 117 Q A U :=
  .seq RegularHaloMetadata.prepare
    (PreparedPeriodicHalo.run 31 32 33 34 35 36 114 115 109 96 95 94 37 38 39 40 41 42 93 92)

def cost (M H w N V L : ℕ) : ℕ :=
  RegularHaloMetadata.prepareCost N V+(M+H)*(8*w+9)+(30*M+28*H)*w+
    34*((N*L+2*H)*w)+N*(76*V+149)+79

theorem emit_exec (w V L H N : ℕ) (xs : List GaussianInt) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hlen : xs.length = N*L) (hfit : (N*L+2*H)*w < 2^V) (hwide : N+2 < 2^V) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hM : (S.R 31).length = xs.length) (hH : (S.R 32).length = H) (hw : (S.R 33).length = w)
    (hV : (S.R 115).length = V) (hNb : S.R 97 = binSyms V N)
    (hLb : S.R 98 = binSyms V (L*w)) (hBb : S.R 100 = binSyms V (2*(H*w))) (hz : S.R 116 = [])
    (hsrc : S.R 39 = cstream A w xs++tail)
    (hblank : ∀ i : Fin 117, i.val < 31 ∨ i ∈ [34,35,36,96,95,94,37,38,40,41,42,93,92,114] → S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost xs.length H w N V L ∧
      Exec body emit (mk v S) n (mk vf {S with R := (Function.update S.R 39
        ((List.range' 0 N).flatMap (fun j => slice (extended A w H xs)
          (j*(L*w)) ((j+1)*(L*w)+2*(H*w)))++tail))}) := by
  have hgapb : 2*(H*w) ≤ L*w := by nlinarith only [Nat.mul_le_mul_right w hgap]
  have hsize : L*w+2*(H*w) < 2^V := by
    have hh := Nat.mul_le_mul_right w (Nat.le_mul_of_pos_left L hN)
    nlinarith only [hh,hfit]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := RegularHaloMetadata.prepare_exec (body := body)
    hgapb hwide hsize hA v S hV hNb hLb hBb hz
    (by intro i hi; exact hblank i (Or.inl hi)) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  let F : Stacks 117 A := {S with R := (Function.update (Function.update S.R 109
    (metadata V 0 (pairs (L*w) (H*w) 0 N)++S.R 109)) 114
    (List.replicate (pairs (L*w) (H*w) 0 N).length tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := PreparedPeriodicHalo.run_exec (body := body)
    31 32 33 34 35 36 114 115 109 96 95 94 37 38 39 40 41 42 93 92 (by decide)
    w V L H N xs hN hgap hlen hfit tail (S.R 109) v₁ F
    (by simpa [F] using hM) (by simpa [F] using hH) (by simpa [F] using hw)
    (by simp [F]) (by simpa [F] using hV) (by simp [F]) (by simpa [F] using hsrc) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [F] using hblank _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by unfold cost; omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases his : i = 39
  · subst i; simp
  by_cases hic : i = 114
  · subst i; simp [his,hblank]
  by_cases hiq : i = 109
  · subst i; simp [his]
  · simp [F,his,hic,hiq]

theorem emit_native : mnNativePushBound 3 (emit (P := P) (Q := Q) (A := A) (U := U)) :=
  ⟨RegularHaloMetadata.prepare_native,PreparedPeriodicHalo.run_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

theorem emit_within_stock {v vf : HS 117 Q A U} {S F : Stacks 117 A} {n C : ℕ}
    (hex : Exec body emit (mk v S) n (mk vf F)) (hn : n ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*C) depth emit
      (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 3 emit_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.GeneratedPeriodicHalo
