module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Release private unary header copies while preserving retained masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem releaseUnaryHeaders_exec (rs : List (Fin n × Fin T)) (hnd : (rs.map Prod.snd).Nodup)
    (value : Fin n → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hfresh : ∀ r ∈ rs, S.R r.2 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords (rs.map Prod.snd)) (mk v { S with R := unaryCopiesR value S.R rs })
        (2*(rs.map (fun r => value r.1)).sum+2*rs.length+1) (mk v' S) := by
  let S₁ : Stacks T A := { S with R := unaryCopiesR value S.R rs }
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (rs.map Prod.snd) hnd v S₁
  have hsum : ((rs.map Prod.snd).map (fun k => (S₁.R k).length)).sum = (rs.map (fun r => value r.1)).sum := by
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    simp [S₁,Function.comp_apply,unaryCopiesR_at value S.R rs hnd r hr,hfresh r hr]
  refine ⟨v',hu,he.cast (by rw [hsum,List.length_map]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k ∈ rs.map Prod.snd
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hk
    have hz : S.R k = [] := he ▸ hfresh r hr
    simp [hk,hz]
  have hoff : ∀ r ∈ rs, r.2 ≠ k := by
    intro r hr he
    exact hk (List.mem_map.mpr ⟨r,hr,he⟩)
  simpa [hk,S₁] using unaryCopiesR_off value S.R rs k hoff

namespace ScalarPlacement

variable {body144 : P → Pr P 144 Q A U}

def releaseGroupHeaders : Pr P 144 Q A U := clearWords (groupHeaderCopies.map Prod.snd)

theorem releaseGroupHeaders_exec (P N q l s t u band L : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hfresh : ∀ r ∈ groupHeaderCopies, S.R r.2 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body144 releaseGroupHeaders (mk v { S with R := copiedGroupR P N q l s t u band L S.R })
        (2*(P+N+q+l+s+t+u+band+2*L)+21) (mk v' S) := by
  obtain ⟨v',hu,he⟩ := releaseUnaryHeaders_exec (body := body144) groupHeaderCopies (by decide)
    (groupHeaderValue P N q l s t u band L) v S hfresh
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp [groupHeaderCopies,groupHeaderValue]
  ring

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
