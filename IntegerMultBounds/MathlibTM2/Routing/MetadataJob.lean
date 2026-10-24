module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-!
# Executed routing metadata installation

Install a descriptor word, a canonical-header word with its separator, a zero
field counter, or a unary stream/block counter. Sources are input configuration
tapes and are restored. Binary widths/values on unary jobs are proof annotations:
the executed program reads the binary tape and never unrolls those numbers.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive MetadataJob (T : ℕ) where
  | copy (src dst : Fin T) (header : Bool)
  | zero (src dst : Fin T)
  | unary (src dst : Fin T) (width value : ℕ)

namespace MetadataJob

variable {T Q A : ℕ} {P U : Type}

def src : MetadataJob T → Fin T
  | .copy s _ _ | .zero s _ | .unary s _ _ _ => s

def dst : MetadataJob T → Fin T
  | .copy _ d _ | .zero _ d | .unary _ d _ _ => d

def contents (R : Fin T → List (Fin (A + 4))) : MetadataJob T → List (Fin (A + 4))
  | .copy s _ h => (if h then [separator] else []) ++ R s
  | .zero s _ => binSyms (R s).length 0
  | .unary _ _ _ n => List.replicate n tick

def cost (R : Fin T → List (Fin (A + 4))) : MetadataJob T → ℕ
  | .copy s _ _ => 6 * (R s).length + 7
  | .zero s _ => 4 * (R s).length + 4
  | .unary _ _ w n => 6 * n + 11 * w + 6

theorem cost_le (R : Fin T → List (Fin (A + 4))) (job : MetadataJob T)
    (wordBound widthBound valueBound : ℕ) (hword : (R job.src).length ≤ wordBound)
    (hunary : match job with
      | .unary _ _ w n => w ≤ widthBound ∧ n ≤ valueBound
      | _ => True) :
    job.cost R ≤ 6 * wordBound + 7 +
      6 * valueBound + 11 * widthBound + 6 := by
  cases job with
  | copy s d header =>
    change (R s).length ≤ wordBound at hword
    simp only [cost]
    omega
  | zero s d =>
    change (R s).length ≤ wordBound at hword
    simp only [cost]
    omega
  | unary s d w n =>
    obtain ⟨hw, hn⟩ := hunary
    simp only [cost]
    omega

def Data (R : Fin T → List (Fin (A + 4))) : MetadataJob T → Prop
  | .unary s _ w n => n < 2 ^ w ∧ R s = binSyms w n
  | _ => True

def copyFinish (d : Fin T) (header : Bool) : Act T Q A U :=
  if header then .push (.rt d) (fun _ => separator) .done else .done

def program (work tmp ctmp : Fin T) : MetadataJob T → Pr P T Q A U
  | .copy s d h => .seq (bcopy s d tmp ctmp) (.act (copyFinish d h))
  | .zero s d => bzero s d tmp
  | .unary s d _ _ => toUnary s d work tmp ctmp

/-- Numerical annotations do not change the counter-construction program. -/
theorem unary_program_eq (work tmp ctmp s d : Fin T) (w n w' n' : ℕ) :
    (program work tmp ctmp (.unary s d w n) : Pr P T Q A U) =
      program work tmp ctmp (.unary s d w' n') := rfl

/-- Install one metadata word with actual host execution and complete frame. -/
theorem exec (body : P → Pr P T Q A U) (job : MetadataJob T) (work tmp ctmp : Fin T)
    (hreg : [job.src, job.dst, work, tmp, ctmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hdata : job.Data S.R)
    (hd : S.R job.dst = []) (hw : S.R work = []) (ht : S.R tmp = []) (hct : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ job.cost S.R ∧
      Exec body (job.program work tmp ctmp) (mk v S) m
        (mk v' { S with R := Function.update S.R job.dst (job.contents S.R) }) := by
  cases job with
  | copy s d header =>
    have hn := hreg
    simp only [src, dst] at hn
    regs_ne hn
    have hregs : [s, d, tmp, ctmp].Nodup := by regs_nodup
    obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hregs v S ht hct
    change S.R d = [] at hd
    rw [hd, List.append_nil] at he₁
    let R₁ := Function.update S.R d (S.R s)
    have hfinish : (copyFinish d header : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
        mk v₁ { S with R := Function.update S.R d ((if header then [separator] else []) ++ S.R s) } := by
      cases header <;> simp [copyFinish, Action.run, update_rt, R₁]
    refine ⟨v₁, (6 * (S.R s).length + 6) + 1, hu₁, by simp [cost], ?_⟩
    exact Exec.seq he₁ (hfinish ▸ Exec.act (body := body) (copyFinish d header) _)
  | zero s d =>
    have hn := hreg
    simp only [src, dst] at hn
    regs_ne hn
    have hregs : [s, d, tmp].Nodup := by regs_nodup
    obtain ⟨v', hu, he⟩ := bzero_exec body hregs v S ht
    change S.R d = [] at hd
    rw [hd, List.append_nil] at he
    exact ⟨v', _, hu, le_rfl, he⟩
  | unary s d w n =>
    simp only [src, dst] at hreg
    obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec_linear body hreg hdata.1 v S hdata.2 hw ht hct
    change S.R d = [] at hd
    rw [hd, List.append_nil] at he
    exact ⟨v', m, hu, hm, he⟩

end MetadataJob
end IntegerMultBounds.MathlibTM2.Routing
