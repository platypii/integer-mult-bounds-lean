module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPrefixPadRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadGatherPayload

/-! The actual gathered payload is padded from retained class dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem generatedPadCoreGatherPayload_exec_within
    (rows capacity blockWidth rowSymbols padSymbols missing src acc saved tmp replicas savedReplicas : Fin T)
    (hreg : [rows,capacity,blockWidth,rowSymbols,padSymbols,missing,src,acc,saved,tmp,replicas,savedReplicas].Nodup)
    (C width radius L w : ℕ) (hfit : (coreGatherIndices s width radius L).length ≤ C)
    (Fs : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = (coreGatherIndices s width radius L).length)
    (hcapacity : (S.R capacity).length = C) (hwidth : (S.R blockWidth).length = L*w)
    (hrow : S.R rowSymbols = []) (hpad : S.R padSymbols = []) (hmissing : S.R missing = [])
    (hsrc : S.R src = cstream A w (coreGatherPayload width radius L Fs)++tail) (hacc : S.R acc = [])
    (hreplicas : (S.R replicas).length = Fs.length) (hsavedReplicas : S.R savedReplicas = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ gatherCounterSetupCost (coreGatherIndices s width radius L).length C (L*w) +
        (Fs.length*(6*(C*L*w)+13)+6) + (2*(C*L*w)+4) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*gatherCounterSetupCost (coreGatherIndices s width radius L).length C (L*w) +
          (Fs.length*((C-(coreGatherIndices s width radius L).length)*L*w)+2*(4*(C*L*w)+10)))) depth
        (generatedPrefixPadRows rows capacity blockWidth rowSymbols padSymbols missing src acc saved tmp replicas savedReplicas
          (pairSym A false false)) (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R src
            (cstream A w (paddedCoreGatherPayload C width radius L Fs)++tail))}) := by
  let xs := Fs.map (fun F => cstream A w (coreGatherPayload width radius L [F]))
  have hlen : ∀ x ∈ xs, x.length = (coreGatherIndices s width radius L).length*(L*w) := by
    intro x hx
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hx
    simp only [length_cstream,coreGatherPayload_length,List.length_singleton,Nat.one_mul,Nat.mul_assoc]
  obtain ⟨v',n,hu,hn,he⟩ := generatedPrefixPadRows_exec_within rows capacity blockWidth rowSymbols padSymbols missing
    src acc saved tmp replicas savedReplicas hreg (pairSym A false false) _ C (L*w) hfit xs hlen tail v S
    hrows hcapacity hwidth hrow hpad hmissing
    (by
      change S.R src = (Fs.map (fun F => cstream A w (coreGatherPayload width radius L [F]))).flatten++tail
      rw [←coreGatherPayload_symbols_rows]
      exact hsrc) hacc (by simpa only [xs,List.length_map] using hreplicas) hsavedReplicas hsaved htmp depth
  have hout : xs.flatMap (fun x => List.replicate ((C-(coreGatherIndices s width radius L).length)*(L*w))
      (pairSym A false false)++x) = cstream A w (paddedCoreGatherPayload C width radius L Fs) := by
    rw [paddedCoreGatherPayload_symbols]
    simp only [xs,List.flatMap_map,Nat.mul_assoc]
  rw [hout] at he
  simp only [xs,List.length_map] at hn he
  simp only [Nat.mul_assoc]
  exact ⟨v',n,hu,hn,he⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
