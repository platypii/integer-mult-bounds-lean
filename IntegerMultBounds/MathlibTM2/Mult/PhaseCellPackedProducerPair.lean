module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPlan

/-! Two actual packed producers compose from ordinary input readiness. The
second input frame is derived from the first returned output update; numerical
certificates, time and execution-wide stock refer to those same executions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Mathematical data for a rectangular batch; no machine executions are fields. -/
structure PackedExactBatch (A s t B L : ℕ) [NeZero s] [NeZero t] where
  records : List (PackedNormalizedJob A s)
  W : ℕ
  hwidth : ∀ r ∈ records, r.W = W
  ht : ∀ r ∈ records, r.t = t
  hp : ∀ r ∈ records, 4 ≤ r.p
  htarget : ∀ r ∈ records, r.p+2 ≤ r.targetOut
  hlocal : ∀ r ∈ records, r.localityTarget = r.targetOut
  J : PackedNormalizedJob A s → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)
  hJ : ∀ r ∈ records, J r ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1
  hreplicas : ∀ r ∈ records, r.Fs.length = B
  hcore : ∀ r ∈ records, IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L

namespace PackedExactBatch
variable {A s t B L : ℕ} [NeZero s] [NeZero t]

structure Rows (batch : PackedExactBatch A s t B L) where
  values : Fin batch.records.length → Fin B → List GaussianInt
  length : ∀ i j, (values i j).length = L
  exactOutput : ∀ i : Fin batch.records.length,
    (batch.records.get i).ExactRowOutput (batch.J (batch.records.get i)) (List.ofFn (values i))

def Rows.stream {batch : PackedExactBatch A s t B L} (rows : batch.Rows) : List (Fin (A+4)) :=
  (List.ofFn fun i => (List.ofFn fun j => cstream A batch.W (rows.values i j)).flatten).flatten
end PackedExactBatch

namespace PackedProducerPlan
variable {T Q A s t B L₁ L₂ : ℕ} [NeZero s] [NeZero t]

def appendOutput (plan : PackedProducerPlan T Q) (raw : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := Function.update S.R plan.result (raw++S.R plan.result)}

theorem appendOutput_stock (plan : PackedProducerPlan T Q) (raw : List (Fin (A+4)))
    {U : Type} (v v' : HS T Q A U) (S : Stacks T A) :
    mnSize (Host.mk v' (plan.appendOutput raw S)) = mnSize (Host.mk v S)+raw.length := by
  have he : mnSize (Host.mk v' (plan.appendOutput raw S))+(S.R plan.result).length =
      mnSize (Host.mk v S)+(raw++S.R plan.result).length := by
    simpa only [Host.mk,appendOutput,update_rt,get_rt] using
      mn_size_update (Host.mk v S) v' (.rt plan.result) (raw++S.R plan.result)
  simp only [List.length_append] at he
  omega

/-- Scratch is reused within each class. Only the first returned output
is retained between classes; temporary workspace is charged by the maximum. No
readiness or execution witness is requested at the intermediate state. -/
theorem pair_exec {P U : Type} (plan₁ plan₂ : PackedProducerPlan T Q)
    (body : P → Pr P T Q A U) (hA : 96 ≤ A)
    (batch₁ : PackedExactBatch A s t B L₁) (batch₂ : PackedExactBatch A s t B L₂)
    (rest₁ rest₂ : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready₁ : plan₁.Ready batch₁.records rest₁ S) (hready₂ : plan₂.Ready batch₂.records rest₂ S)
    (hsep : plan₁.result ∉ plan₂.support) :
    ∃ rows₁ : batch₁.Rows, ∃ rows₂ : batch₂.Rows, ∃ v' n,
      v'.user = v.user ∧ n ≤ plan₁.timeCost (U := U) batch₁.records+plan₂.timeCost (U := U) batch₂.records ∧
      Exec body (.seq plan₁.program plan₂.program) (Host.mk v S) n
        (Host.mk v' (plan₂.appendOutput rows₂.stream (plan₁.appendOutput rows₁.stream S))) ∧
      ∀ C, mnProgPush (plan₁.program (P := P) (U := U) (A := A)) ≤ C →
        mnProgPush (plan₂.program (P := P) (U := U) (A := A)) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+rows₁.stream.length+depth+
          (C+1)*max (plan₁.workspace (U := U) batch₁.records) (plan₂.workspace (U := U) batch₂.records))
          depth (.seq plan₁.program plan₂.program) (Host.mk v S) n
          (Host.mk v' (plan₂.appendOutput rows₂.stream (plan₁.appendOutput rows₁.stream S))) := by
  obtain ⟨v₁,n₁,values₁,hu₁,hn₁,he₁,hlen₁,hcert₁,hs₁⟩ := plan₁.exec body hA
    batch₁.records batch₁.W batch₁.hwidth t batch₁.ht batch₁.hp batch₁.htarget batch₁.hlocal batch₁.J batch₁.hJ
    B L₁ batch₁.hreplicas batch₁.hcore rest₁ v S hready₁
  let rows₁ : batch₁.Rows := ⟨values₁,hlen₁,hcert₁⟩
  let M := plan₁.appendOutput rows₁.stream S
  have hreadyM : plan₂.Ready batch₂.records rest₂ M := hready₂.update plan₁.result hsep _
  obtain ⟨v₂,n₂,values₂,hu₂,hn₂,he₂,hlen₂,hcert₂,hs₂⟩ := plan₂.exec body hA
    batch₂.records batch₂.W batch₂.hwidth t batch₂.ht batch₂.hp batch₂.htarget batch₂.hlocal batch₂.J batch₂.hJ
    B L₂ batch₂.hreplicas batch₂.hcore rest₂ v₁ M hreadyM
  let rows₂ : batch₂.Rows := ⟨values₂,hlen₂,hcert₂⟩
  refine ⟨rows₁,rows₂,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,?_⟩
  intro C hp₁ hp₂ hb depth
  have hw₁ := hs₁ C hp₁ hb depth
  have hw₂ := hs₂ C hp₂ hb depth
  have hM : mnSize (Host.mk v₁ M) = mnSize (Host.mk v S)+rows₁.stream.length :=
    plan₁.appendOutput_stock rows₁.stream v v₁ S
  have hmax₁ := Nat.mul_le_mul_left (C+1) (le_max_left
    (plan₁.workspace (U := U) batch₁.records) (plan₂.workspace (U := U) batch₂.records))
  have hmax₂ := Nat.mul_le_mul_left (C+1) (le_max_right
    (plan₁.workspace (U := U) batch₁.records) (plan₂.workspace (U := U) batch₂.records))
  apply ExecWithin.seq
  · exact hw₁.mono (by intro d z hz; omega)
  · exact hw₂.mono (by intro d z hz; omega)

end PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
