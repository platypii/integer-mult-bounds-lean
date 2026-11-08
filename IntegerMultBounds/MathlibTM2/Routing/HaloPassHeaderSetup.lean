module

public import IntegerMultBounds.MathlibTM2.Routing.HaloUnaryHeaders
public import IntegerMultBounds.MathlibTM2.Routing.HaloBinaryHeaders
public import IntegerMultBounds.MathlibTM2.Routing.HaloWidthHeaders

/-! Complete halo-pass header production from ordinary retained dimensions.
All products, binary words and the enlarged local width are generated here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloPassHeaderSetup
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main HaloPassContext
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

structure Masters (p : Parameters) (S : Stacks 117 A) : Prop where
  count : (S.R 44).length = p.N
  rows : (S.R 45).length = p.B
  length : (S.R 55).length = p.L
  halo : (S.R 65).length = p.H
  width : (S.R 47).length = p.w
  metadata : (S.R 115).length = p.V
  forwardExponent : (S.R 54).length = p.k
  returnExponent : (S.R 43).length = p.r
  zero : S.R 116 = []

def owned : List (Fin 117) := [31,32,33,46,97,98,100]
def blank : List (Fin 117) := owned ++ [66,67,68,69,57,58]

def run : Pr P 117 Q A U :=
  .seq HaloUnaryHeaders.run (.seq HaloBinaryHeaders.run HaloWidthHeaders.run)

def cost (p : Parameters) := HaloUnaryHeaders.cost p.N p.L p.H p.B+
  HaloBinaryHeaders.cost p.N p.L p.H p.B p.w p.V+HaloWidthHeaders.cost p.w p.L p.H

def reserve (p : Parameters) := 2*HaloUnaryHeaders.cost p.N p.L p.H p.B+
  HaloBinaryHeaders.reserve p.L p.H p.B p.w p.V+2*HaloWidthHeaders.cost p.w p.L p.H

def result (p : Parameters) (S : Stacks 117 A) : Stacks 117 A :=
  HaloWidthHeaders.result (HaloBinaryHeaders.result (HaloUnaryHeaders.result S p.N p.L p.H p.B)
    p.N p.L p.H p.B p.w p.V) p.w p.L p.H

theorem result_holds (p : Parameters) (S : Stacks 117 A) (h : Masters p S) : Holds p (result p S) := by
  constructor <;> simp [result,HaloWidthHeaders.result,HaloBinaryHeaders.result,HaloUnaryHeaders.result,
    h.count,h.rows,h.length,h.width,h.metadata,h.forwardExponent,h.returnExponent,h.zero,Nat.mul_assoc]

theorem result_other (p : Parameters) (S : Stacks 117 A) (i : Fin 117) (hi : i ∉ owned) :
    (result p S).R i = S.R i := by
  simp only [owned,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp [result,HaloWidthHeaders.result,HaloBinaryHeaders.result,HaloUnaryHeaders.result,
    hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2]

theorem run_exec (p : Parameters) (v : HS 117 Q A U) (S : Stacks 117 A) (h : Masters p S)
    (hb : ∀ i ∈ blank, S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ cost p ∧
      Exec body run (mk v S) n (mk vf (result p S)) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reserve p)
        depth run (mk v S) n (mk vf (result p S))) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hs₁⟩ := HaloUnaryHeaders.run_exec_within (body := body)
    p.N p.L p.H p.B v S h.count h.length h.halo h.rows (by
      intro i hi
      exact hb i (by simp only [blank,owned,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto))
  let F := HaloUnaryHeaders.result S p.N p.L p.H p.B
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := HaloBinaryHeaders.run_exec (body := body)
    p.N p.L p.H p.B p.w p.V v₁ F
    (by simp [F,HaloUnaryHeaders.result,h.count]) (by simp [F,HaloUnaryHeaders.result,h.length])
    (by simp [F,HaloUnaryHeaders.result,h.halo]) (by simp [F,HaloUnaryHeaders.result,h.rows])
    (by simp [F,HaloUnaryHeaders.result,h.width]) (by simp [F,HaloUnaryHeaders.result,h.metadata]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [F,HaloUnaryHeaders.result] <;> exact hb _ (by simp [blank,owned]))
  let G := HaloBinaryHeaders.result F p.N p.L p.H p.B p.w p.V
  obtain ⟨vf,hu₃,he₃⟩ := HaloWidthHeaders.run_exec (body := body) p.w p.L p.H v₂ G
    (by simp [G,F,HaloBinaryHeaders.result,HaloUnaryHeaders.result,h.width])
    (by simp [G,F,HaloBinaryHeaders.result,HaloUnaryHeaders.result,h.length])
    (by simp [G,F,HaloBinaryHeaders.result,HaloUnaryHeaders.result,h.halo]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;>
        simp [G,F,HaloBinaryHeaders.result,HaloUnaryHeaders.result] <;> exact hb _ (by simp [blank,owned]))
  refine ⟨vf,n₁+(n₂+HaloWidthHeaders.cost p.w p.L p.H),hu₃.trans (hu₂.trans hu₁),by dsimp [cost]; omega,
    Exec.seq he₁ (Exec.seq he₂ he₃),?_⟩
  intro depth
  have hs₃ := mn_native_exec_within he₃ 2 HaloWidthHeaders.run_native depth
    (mnSize (mk v₂ G)+depth+2*HaloWidthHeaders.cost p.w p.L p.H) (by omega)
  have hs := mn_seq_within_add (hs₁ depth) (mn_seq_within_add (hs₂ depth) hs₃)
  exact hs.mono (by intro d z hz; dsimp only [reserve]; omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloPassHeaderSetup
