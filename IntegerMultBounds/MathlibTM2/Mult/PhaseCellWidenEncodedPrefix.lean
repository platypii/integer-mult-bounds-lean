module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenPackedPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalOutput

/-! Widen actual encoded output without assuming its existential coefficient
witness fits. Signed canonicalization preserves the narrow bytes exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The returned coefficients are the signed values of the original words.
Only the counted prefix changes; controls, scratch and the suffix restore. -/
theorem widenEncodedPrefix_exec {wide width count src work saved tmp extra : Fin T}
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W) (xs : List GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hcount : (S.R count).length = xs.length*w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenPackedPrefixCost w W xs.length ∧
      Exec body (widenPackedPrefix wide width count src work saved tmp extra) (mk v S) n
        (mk v' {S with R := Function.update S.R src (cstream A W (xs.map (symZ w))++tail)}) := by
  have hfit : ∀ z ∈ xs.map (symZ w), TopFitsZ w z := by
    intro z hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact topFitsZ_symZ hw x
  obtain ⟨v',n,hu,hn,he⟩ := widenPackedPrefix_exec (body := body) hreg w W hw hwidth
    (xs.map (symZ w)) hfit tail v S hwide hword
    (by simpa only [List.length_map] using hcount)
    (by simpa only [cstream_symZ] using hsrc) hblank
  exact ⟨v',n,hu,by simpa only [List.length_map] using hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
