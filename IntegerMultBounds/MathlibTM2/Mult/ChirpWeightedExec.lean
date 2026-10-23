module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams

/-! # Executing weighted chirp input production

The existing real stream multiplier consumes the gathered windows and generated weight
rows in one pass, retaining both sources. Its complete tape frame is made explicit here
so the resulting weighted rows can feed coefficient reversal and shared S1 packing.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

/-- Convert an output-only register-file contract to an exact whole-stack equation. -/
theorem cruns_output_exec (hcr : Function.Injective cr)
    {prog : Pr P T Q A U} {ρ : CR → List (Fin (A + 4))} {words : List (Fin (A + 4))} {K : ℕ}
    (run : CRuns body cr ι prog ρ (Function.update ρ .out (words ++ ρ .out)) K)
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ K ∧ Exec body prog (mk v S) n
      (mk v' { S with R := Function.update S.R (cr .out) (words ++ S.R (cr .out)) }) := by
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := run v S hc hS
  have hR : S'.R = Function.update S.R (cr .out) (words ++ S.R (cr .out)) := by
    funext k
    by_cases hk : ∃ r, cr r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [hS' r, upd_comp hcr, hS .out]
      by_cases hr : r = .out
      · subst r; simp
      · simp only [Function.update_of_ne hr]
        exact (hS r).symm
    · rw [hf.2.2.2 k (fun r hr => hk ⟨r, hr⟩)]
      exact (Function.update_of_ne (fun h => hk ⟨.out, h.symm⟩) _ _).symm
  have hstate : S' = { S with R := Function.update S.R (cr .out) (words ++ S.R (cr .out)) } := by
    cases S
    cases S'
    simp only [Stacks.mk.injEq]
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hR⟩
  exact ⟨v', n, hu, hn, hstate ▸ he⟩

/-- One traversal produces all weighted rows and restores every other tape. -/
theorem chirpWeighted_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {s t α q w m M : ℕ} (hs : 0 < s) (ht : 0 < t) (hα : 0 < α) (hq : 13 ≤ q)
    (hw : q + 3 ≤ w) (hblocks : ∀ n < M, n * m < t)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w ((List.range M).flatMap fun n => chirpWindow s t m n u))
    (hY : ρ .ys = chirpBlockStream M (fun n => chirpEntryStream A w (3 * m + 1)
      (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (3 * m + 1) * (rmulCost w + 6 * w + 2) + 8 ∧
      Exec body (cmulStream cr (rmulOne ι hι hT hQ cr)) (mk v S) n
        (mk v' { S with R := (Function.update S.R (cr .out)
          (cstream A w ((List.range M).flatMap fun n =>
            chirpWeighted s t q m n (chirpInputNumerators s t α q m) u) ++ S.R (cr .out))) }) := by
  rw [← chirpWeightStream_eq s t α q w m M] at hY
  have hlenX : ((List.range M).flatMap fun n => chirpWindow s t m n u).length =
      M * (3 * m + 1) := by
    have h := length_flatten_const ((List.range M).map fun n => chirpWindow s t m n u)
      (L := 3 * m + 1) (by
        intro b hb
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hb
        exact length_chirpWindow hs (hblocks n (List.mem_range.mp hn)) u)
    simpa [Function.comp_def] using h
  have hlenY : ((List.range M).flatMap fun n => chirpWeightRow s t α q m n).length =
      M * (3 * m + 1) := by
    simp [chirpWeightRow]
  have run := rmulStream_runs (body := body) hcr hdisj hι hT hQ hA hr
    (by omega) (by omega) _ _ (hlenX.trans hlenY.symm) (by
      intro x hx
      obtain ⟨n, hn, hx⟩ := List.mem_flatMap.mp hx
      exact chirpWindow_fits hs (hblocks n (List.mem_range.mp hn)) (by omega) u hu x hx)
    (by
      intro y hy
      obtain ⟨n, hn, hy⟩ := List.mem_flatMap.mp hy
      exact chirpWeightRow_fits hq ht hα hw y hy) hX hY hxsv hysv hacc
  rw [hlenX, chirpWeightedStream_eq α hs hblocks u] at run
  exact cruns_output_exec hcr run v S hc hS

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
