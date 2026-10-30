module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedReplicaTile

/-! Retain the actual real-payload length before allocating dummy replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retainedReplicaPadding (c : ℕ) (exponent width src totalExponent pad tmp saved keep : Fin T) : Pr P T Q A U :=
  .seq (ucopy src keep saved)
    (generatedTilePrefixPadding c exponent width src totalExponent pad tmp saved (pairSym A false false))

/-- The real-symbol count is scanned from the source before padding. It is
owned by the tile lifecycle and available for position-based output erasure. -/
theorem retainedReplicaPadding_exec {N : ℕ} (c : ℕ)
    (exponent width src totalExponent pad tmp saved keep : Fin T)
    (hreg : [exponent,width,src,totalExponent,pad,tmp,saved,keep].Nodup)
    (d w : ℕ) (hw : 0 < w) (hN : N ≤ (2^d)^c)
    (realBits imagBits : Fin N → Fin (2^d) → Fin w → Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hd : (S.R exponent).length = d) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = replicaKeyWords (fun r k b => pairSym A (realBits r k b) (imagBits r k b)))
    (htotal : S.R totalExponent = []) (hpad : S.R pad = []) (htmp : S.R tmp = [])
    (hsaved : S.R saved = []) (hkeep : S.R keep = []) :
    let V := (2^d)^c*(2^d*w)
    ∃ (r i : Fin ((2^d)^c) → Fin (2^d) → Fin w → Bool), ∃ v' n,
      v'.user = v.user ∧ n ≤ 33*V+24 ∧
      Exec body (retainedReplicaPadding c exponent width src totalExponent pad tmp saved keep)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R keep
          (List.replicate (N*(2^d*w)) tick)) src
            (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))))}) ∧
      (replicaKeyWords (fun a k b => pairSym A (r a k b) (i a k b))).drop
        (((2^d)^c-N)*(2^d*w)) = S.R src := by
  dsimp only
  have hr := hreg
  regs_ne hr
  have hlen : (S.R src).length = N*(2^d*w) := by simp [hsrc,replicaKeyWords]
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹src ≠ keep› ‹src ≠ saved›
    ‹saved ≠ keep›.symm v S hsaved
  let M : Stacks T A := {S with R := Function.update S.R keep (List.replicate (N*(2^d*w)) tick)}
  have he₁' : Exec body (ucopy src keep saved) (mk v S) (4*(N*(2^d*w))+4) (mk v₁ M) := by
    simpa [M,hlen,hkeep] using he₁
  obtain ⟨r,i,v₂,n₂,hu₂,hn₂,he₂,hsuffix⟩ := generatedReplicaTilePadding_exec (body := body)
    c exponent width src totalExponent pad tmp saved (by regs_nodup) d w hw hN realBits imagBits v₁ M
    (by simpa [M,‹exponent ≠ keep›] using hd)
    (by simpa [M,‹width ≠ keep›] using hwidth)
    (by simpa [M,‹src ≠ keep›] using hsrc)
    (by simpa [M,‹totalExponent ≠ keep›] using htotal)
    (by simpa [M,‹pad ≠ keep›] using hpad)
    (by simpa [M,‹tmp ≠ keep›] using htmp)
    (by simpa [M,‹saved ≠ keep›] using hsaved)
  refine ⟨r,i,v₂,(4*(N*(2^d*w))+4)+n₂,hu₂.trans hu₁,?_,Exec.seq he₁' he₂,?_⟩
  · have hfit := Nat.mul_le_mul_right (2^d*w) hN
    omega
  · simpa [M,‹src ≠ keep›] using hsuffix

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
