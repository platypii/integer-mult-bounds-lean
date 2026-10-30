module

public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.MathlibTM2.Host.RightWrites

/-! Translate an arbitrary bank of fixed-width binary coordinates by a shared
binary displacement. The structural proof checks each distinct word once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def translateBinaryWords (delta work saved tmp carry : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | k::ks => .seq (baddTo k delta work saved tmp carry)
      (translateBinaryWords delta work saved tmp carry ks)

theorem translateBinaryWords_exec {delta work saved tmp carry : Fin T}
    (words : List (Fin T × ℕ)) (hnd : (words.map Prod.fst).Nodup)
    (hreg : ∀ k ∈ words.map Prod.fst, [k,delta,work,saved,tmp,carry].Nodup)
    {V d : ℕ} (hd : d < 2^V) (hbound : ∀ w ∈ words, w.2+d < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : ∀ w ∈ words, S.R w.1 = binSyms V w.2)
    (hdelta : S.R delta = binSyms V d)
    (hwork : S.R work = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (translateBinaryWords delta work saved tmp carry (words.map Prod.fst))
        (mk v S) (words.length*(8*V+8)+1)
        (mk v' (writeRight (words.map (fun w => (w.1,binSyms V (w.2+d)))) S)) := by
  induction words generalizing v S with
  | nil =>
    refine ⟨v,rfl,?_⟩
    simpa only [List.map_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,
      translateBinaryWords,writeRight,Action.run] using Exec.act (body := body) .done (mk v S)
  | cons w words ih =>
    obtain ⟨k,x⟩ := w
    have hr := hreg k (by simp)
    regs_ne hr
    have hx : x+d < 2^V := hbound (k,x) (by simp)
    obtain ⟨v₁,hu₁,_,_,he₁⟩ := baddTo_exec body
      (a := k) (b := delta) (tx := work) (ty := saved) (tz := tmp) (cy := carry)
      (by regs_nodup) ‹k ≠ carry›.symm ‹delta ≠ carry›.symm
      (by omega) hd v S (hwords (k,x) (by simp)) hdelta hwork hsaved htmp
    let H : Stacks T A := {S with R := Function.update S.R k (binSyms V (x+d))}
    have he₁' : Exec body (baddTo k delta work saved tmp carry) (mk v S) (8*V+8) (mk v₁ H) := by
      simpa only [H,Nat.mod_eq_of_lt hx] using he₁
    have hnd' : k ∉ words.map Prod.fst ∧ (words.map Prod.fst).Nodup := by
      simpa only [List.map_cons,List.nodup_cons] using hnd
    obtain ⟨v₂,hu₂,he₂⟩ := ih hnd'.2
      (fun j hj => hreg j (by simp only [List.map_cons,List.mem_cons]; exact Or.inr hj))
      (fun w hw => hbound w (List.mem_cons_of_mem _ hw)) v₁ H
      (by
        intro w hw
        have hn : w.1 ≠ k := by
          intro he
          apply hnd'.1
          exact List.mem_map.mpr ⟨w,hw,he⟩
        simpa only [H,Function.update_of_ne hn] using hwords w (List.mem_cons_of_mem _ hw))
      (by simpa [H,‹k ≠ delta›.symm] using hdelta)
      (by simpa [H,‹k ≠ work›.symm] using hwork)
      (by simpa [H,‹k ≠ saved›.symm] using hsaved)
      (by simpa [H,‹k ≠ tmp›.symm] using htmp)
    refine ⟨v₂,hu₂.trans hu₁,?_⟩
    exact (Exec.seq he₁' he₂).cast (by
      simp only [List.length_cons,Nat.succ_mul]
      omega) rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
