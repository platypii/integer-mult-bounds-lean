module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPassHeaderSetup
public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisCoordinates

/-! Generate every derived pass header, execute the ordered halo axis, then
retire the headers. Only the tensor source changes; ordinary masters restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisFromDimensions
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv HaloPassContext
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U := .seq HaloPassHeaderSetup.run
  (.seq PreparedHaloPrefixScan.run (clearWords HaloPassHeaderSetup.owned))

def headerSize (p : Parameters) := p.N*p.L*p.B+p.H*p.B+p.w+(p.L+2*p.H)+3*p.V

def cost (p : Parameters) (prefixes : ℕ) := HaloPassHeaderSetup.cost p+
  PreparedHaloPrefixScan.cost p prefixes+2*headerSize p+15

def reserve (p : Parameters) (prefixes : ℕ) := HaloPassHeaderSetup.reserve p+
  PreparedHaloPrefixScan.reserve p prefixes

theorem run_exec (p : Parameters) (fibers : List (List (List (List GaussianInt))))
    (hshape : ∀ matrices ∈ fibers, Shape p matrices) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S)
    (hprefix : (S.R 64).length = fibers.length)
    (hb : ∀ i ∈ HaloPassHeaderSetup.blank ++ [(56 : Fin 117),59,60,61,62,63], S.R i = [])
    (hsrc : S.R 39 = fibers.flatMap (input A p)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p fibers.length ∧
      Exec body run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          ((HaloAxisCoordinates.transform p fibers).flatMap (input A p)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p fibers.length)
        depth run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          ((HaloAxisCoordinates.transform p fibers).flatMap (input A p)++tail))})) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := HaloPassHeaderSetup.run_exec (body := body) p v S hm
    (fun i hi => hb i (List.mem_append_left _ hi))
  let F := HaloPassHeaderSetup.result p S
  have hframe (i : Fin 117) (hi : i ∉ HaloPassHeaderSetup.owned) : F.R i = S.R i :=
    HaloPassHeaderSetup.result_other p S i hi
  have hf' : Fresh F := by
    intro i hi
    have ho : i ∉ HaloPassHeaderSetup.owned := by
      intro ho
      simp only [HaloPassHeaderSetup.owned,List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [scratch] at hi
    rw [hframe i ho]
    exact hf i hi
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloAxisCoordinates.run_exec (body := body) p fibers hshape hA tail v₁ F
    (HaloPassHeaderSetup.result_holds p S hm) hf' (by rw [hframe 64 (by decide)]; exact hprefix) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hframe _ (by decide)] <;> exact hb _ (by simp [HaloPassHeaderSetup.blank]))
    (by rw [hframe 39 (by decide)]; exact hsrc)
  let out := (HaloAxisCoordinates.transform p fibers).flatMap (input A p)++tail
  let G : Stacks 117 A := {F with R := Function.update F.R 39 out}
  obtain ⟨vf,hu₃,he₃⟩ := clearWords_exec (body := body) HaloPassHeaderSetup.owned (by decide) v₂ G
  have hsize : (HaloPassHeaderSetup.owned.map fun i => (G.R i).length).sum = headerSize p := by
    simp [G,F,HaloPassHeaderSetup.owned,HaloPassHeaderSetup.result,HaloWidthHeaders.result,
      HaloBinaryHeaders.result,HaloUnaryHeaders.result,headerSize]
    omega
  have hlen : HaloPassHeaderSetup.owned.length = 7 := by rfl
  rw [hsize,hlen] at he₃
  have hfinal : {G with R := fun i => if i ∈ HaloPassHeaderSetup.owned then [] else G.R i} =
      {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases ho : i ∈ HaloPassHeaderSetup.owned
    · have hi39 : i ≠ 39 := by intro he; subst i; simp [HaloPassHeaderSetup.owned] at ho
      simp only [ho,ite_true,Function.update_of_ne hi39]
      exact (hb i (List.mem_append_left _ (List.mem_append_left _ ho))).symm
    · by_cases hi39 : i = 39
      · subst i; simp [G,ho]
      · simp [G,ho,hi39,hframe i ho]
  refine ⟨vf,n₁+(n₂+(2*headerSize p+2*7+1)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk vf) hfinal),?_⟩
  · dsimp only [cost]; omega
  · intro depth
    have hs₃ := mn_native_exec_within he₃ 0 (clearWords_native _) depth
      (mnSize (mk v₂ G)+depth+0) (by simp)
    have hs := mn_seq_within_add (hs₁ depth) (mn_seq_within_add (hs₂ depth) hs₃)
    refine (hs.mono ?_).cast rfl (congrArg (mk vf) hfinal)
    intro d z hz
    dsimp only [reserve]
    omega

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisFromDimensions
