module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormat

/-! Export an ordinary scalar bank into one consumer's narrower binary format.
The structural list proof shares the counted-prefix copier and header endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def copyBinaryHeaderBank (count saved tmp : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src,dst)::rs => .seq (copyPrefix count src dst saved tmp) (copyBinaryHeaderBank count saved tmp rs)

theorem copyBinaryHeaderBank_native (count saved tmp : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 3 (copyBinaryHeaderBank (P := P) (Q := Q) (A := A) (U := U) count saved tmp rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨copyBinaryHeader_native _ _ _ _ _,ih⟩

theorem copyBinaryHeaderBank_exec (body : P → Pr P T Q A U)
    (count saved tmp : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [count,r.1,r.2,saved,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (hnd : (rs.map Prod.snd).Nodup) (B D : ℕ) (hBD : B ≤ D) (value : Fin T → ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ r ∈ rs, S.R r.1 = binSyms D (value r.1))
    (hcount : (S.R count).length = B)
    (hblank : ∀ r ∈ rs, S.R r.2 = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyBinaryHeaderBank count saved tmp rs) (Host.mk v S) (rs.length*(10*B+10)+1)
        (Host.mk v' {S with R := copyWordHeadersR (fun k => binSyms B (value k)) rs S.R}) := by
  induction rs generalizing v S with
  | nil =>
    exact ⟨v,rfl,by simpa [copyBinaryHeaderBank,copyWordHeadersR] using Exec.act (body := body) .done (Host.mk v S)⟩
  | cons r rs ih =>
    have hr := hregs r (by simp)
    regs_ne hr
    obtain ⟨v₁,hu₁,he₁⟩ := copyBinaryHeader_exec_within body count r.1 r.2 saved tmp (hregs r (by simp)) B D (value r.1) hBD v S
      hcount (hsrc r (by simp)) (hblank r (by simp)) hsaved htmp 0
    let M : Stacks T A := {S with R := Function.update S.R r.2 (binSyms B (value r.1))}
    have htail : ∀ p ∈ rs, p.2 ≠ r.2 := by
      intro p hp he
      exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨p,hp,he⟩)
    obtain ⟨v₂,hu₂,he₂⟩ := ih (fun p hp => hregs p (by simp [hp]))
      (fun p hp q hq => hsep p (by simp [hp]) q (by simp [hq]))
      (List.nodup_cons.mp hnd).2 v₁ M
      (by intro p hp; simpa [M,(hsep r (by simp) p (by simp [hp])).symm] using hsrc p (by simp [hp]))
      (by simpa [M,‹count ≠ r.2›] using hcount)
      (by intro p hp; simpa [M,htail p hp] using hblank p (by simp [hp]))
      (by simpa [M,‹r.2 ≠ saved›.symm] using hsaved)
      (by simpa [M,‹r.2 ≠ tmp›.symm] using htmp)
    refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁.toExec he₂).cast (by simp only [List.length_cons,Nat.succ_mul]; omega) ?_⟩
    simp only [copyWordHeadersR,hblank r (by simp),List.append_nil]
    rfl

theorem copyBinaryHeaderBank_exec_within (body : P → Pr P T Q A U)
    (count saved tmp : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [count,r.1,r.2,saved,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (hnd : (rs.map Prod.snd).Nodup) (B D : ℕ) (hBD : B ≤ D) (value : Fin T → ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ r ∈ rs, S.R r.1 = binSyms D (value r.1))
    (hcount : (S.R count).length = B)
    (hblank : ∀ r ∈ rs, S.R r.2 = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+3*(rs.length*(10*B+10)+1)) depth
        (copyBinaryHeaderBank count saved tmp rs) (Host.mk v S) (rs.length*(10*B+10)+1)
        (Host.mk v' {S with R := copyWordHeadersR (fun k => binSyms B (value k)) rs S.R}) := by
  obtain ⟨v',hu,he⟩ := copyBinaryHeaderBank_exec body count saved tmp rs hregs hsep hnd B D hBD value
    v S hsrc hcount hblank hsaved htmp
  exact ⟨v',hu,mn_native_exec_within he 3 (copyBinaryHeaderBank_native _ _ _ _) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
