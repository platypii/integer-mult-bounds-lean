module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassCallerReady

/-! Derive numerical readiness from the shared formatted class endpoint.
All class-specific words are outputs of the initialized prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry
variable {N A : ℕ}

/-- A retained port lies outside both masters and every format destination. -/
def classInputPortOff (masters : Fin 12 → Fin N) (rs : List (Fin N × Fin N)) (k : Fin N) : Prop :=
  k ≠ masters 10 ∧ k ≠ masters 11 ∧ ∀ r ∈ rs, r.2 ≠ k

theorem classCallerReady_of_formats
    (bank : ComputedClassBank → Fin N) (rg : TblR 12 → Fin N)
    (src : Fin 4 → Fin N) (masters : Fin 12 → Fin N) (hinj : Function.Injective masters)
    (widthMaster zeroMaster : Fin N) (rs : List (Fin N × Fin N))
    (hnd : (rs.map Prod.snd).Nodup) (bits : Fin N → ℕ)
    (B D : ℕ) (clipped : Bool) (p u l target s t W rowCount radius width : ℕ)
    (value : Fin N → ℕ) (S : Stacks N A)
    (hvalues : ∀ j, value (masters j) =
      commonInputValues p u l target s t B W rowCount radius (haloRows clipped s width radius) j)
    (hprefix : ∀ j, j ≠ 10 → j ≠ 11 → S.R (masters j) =
      binSyms D (seedValues p u l target s t B W rowCount radius width (Fin.castAdd 1 j)))
    (hhaloSource : ∃ r ∈ rs, r.2 = src 3 ∧ bits r.1 = B)
    (hgeometryOff : ∀ j, j ≠ 3 → classInputPortOff masters rs (src j))
    (hgeometry : ∀ j, j ≠ 3 → S.R (src j) =
      binSyms B (![s,width,radius,haloRows clipped s width radius] j))
    (hmastersOff : ∀ j r, r ∈ rs → r.2 ≠ masters j)
    (hblank : ∀ r ∈ rs, S.R r.2 = [])
    (hwidthOff : classInputPortOff masters rs widthMaster)
    (hzeroOff : classInputPortOff masters rs zeroMaster)
    (htableOff : ∀ r, classInputPortOff masters rs (rg r))
    (hbankOff : ∀ j, classInputPortOff masters rs (bank j))
    (hwidth : (S.R widthMaster).length = D) (hzero : S.R zeroMaster = [])
    (htable : ∀ r, S.R (rg r) = [])
    (hbank : ∀ j, j ≠ .control .source → S.R (bank j) = [])
    (hleft : ∀ j, S.L (recovery bank (.work j)) = []) :
    ClassCallerReady bank rg src masters widthMaster zeroMaster B D s width radius
      (haloRows clipped s width radius) value
      (formattedClassLoaded (masters 10) (masters 11) D clipped s width radius bits rs S) := by
  let M := masterLoaded (masters 10) (masters 11) D clipped s width radius S
  let F := formattedClassLoaded (masters 10) (masters 11) D clipped s width radius bits rs S
  have hM (k : Fin N) (hc : k ≠ masters 10) (hh : k ≠ masters 11) : M.R k = S.R k := by
    simp only [M,masterLoaded,Function.update_of_ne hc,Function.update_of_ne hh]
  have hF (k : Fin N) (hk : classInputPortOff masters rs k) : F.R k = S.R k :=
    (copyWordHeadersR_off _ rs M.R k hk.2.2).trans (hM k hk.1 hk.2.1)
  refine ⟨?_,?_,?_,?_,?_,?_,hleft⟩
  · intro j
    by_cases hj : j = 3
    · subst j
      obtain ⟨r,hr,hdst,hbits⟩ := hhaloSource
      have hh := copyWordHeadersR_get (fun k => binSyms (bits k) (haloRows clipped s width radius))
        rs hnd M.R r hr
      have hb : M.R r.2 = [] := (hM r.2 (hmastersOff 10 r hr) (hmastersOff 11 r hr)).trans (hblank r hr)
      change copyWordHeadersR _ rs M.R (src 3) = binSyms B (haloRows clipped s width radius)
      simpa only [←hdst,hbits,hb,List.append_nil] using hh
    · exact (hF _ (hgeometryOff j hj)).trans (hgeometry j hj)
  · rw [hF _ hwidthOff]; exact hwidth
  · exact (hF _ hzeroOff).trans hzero
  · intro j
    change copyWordHeadersR _ rs M.R (masters j) = _
    rw [copyWordHeadersR_off _ rs M.R (masters j) (hmastersOff j),hvalues j]
    exact masterLoaded_words masters hinj D clipped p u l target s t B W rowCount radius width S hprefix j
  · intro r; exact (hF _ (htableOff r)).trans (htable r)
  · intro j hj; exact (hF _ (hbankOff j)).trans (hbank j hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
