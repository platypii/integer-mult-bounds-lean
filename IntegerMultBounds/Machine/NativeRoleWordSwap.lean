import IntegerMultBounds.Machine.WordBankSwap
import IntegerMultBounds.Machine.NativePolynomialConjugationRows

/-! Actual exchange of two complete native role arrays on fixed caller ports.
Uniform record widths derive equal serialized lengths; encoded nonblank
interiors and blank exteriors discharge the physical scanner requirements. -/
namespace IntegerMultBounds.Machine.NativeRoleWordSwap
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open WordBankCleanup (write)

def program {t : ℕ} (src dst : Fin t) (hne : src≠dst) (ht : 2≤t) :=
  WordBankSwap.program src dst hne ht 2

theorem runs {t : ℕ} (v : Tapes t 2) (src dst : Fin t) (hne : src≠dst) (ht : 2≤t)
    (sh : Shape) (rows ell p : ℕ) (f g : Array sh rows ell)
    (hf : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hg : ∀ i,(g i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (g i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hs : v.tape src=NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hd : v.tape dst=NativeZeroPadding.word (NativeZeroPaddingArray.word g))
    (hhs : v.head src=0) (hhd : v.head dst=0) :
    HoareTime (program src dst hne ht) (fun w => w=v)
      (fun w => w=write (write v src (NativeZeroPadding.word (NativeZeroPaddingArray.word g)))
        dst (NativeZeroPadding.word (NativeZeroPaddingArray.word f)))
      (3*CompactNativeRoleTransferBudget.volume rows sh ell p+6) := by
  have hlen : (NativeZeroPaddingArray.word f).length=(NativeZeroPaddingArray.word g).length := by
    rw [NativePolynomialConjugationRows.word_volume sh rows ell p f hf,
      NativePolynomialConjugationRows.word_volume sh rows ell p g hg]
  have h := WordBankSwap.runs v src dst hne ht (fun _ => blank) (fun _ => blank)
    (NativeZeroPaddingArray.word f) (NativeZeroPaddingArray.word g) hlen
    (by simpa only [hhs,NativeZeroPadding.word] using hs)
    (by simpa only [hhd,NativeZeroPadding.word] using hd)
    (fun x hx => NativeZeroPaddingArray.nonblank f x hx)
    (fun x hx => NativeZeroPaddingArray.nonblank g x hx) rfl rfl rfl
  simpa only [program,hhs,hhd,NativeZeroPadding.word,
    NativePolynomialConjugationRows.word_volume sh rows ell p f hf] using h

/-- All head restoration and frame preservation is literal in the endpoint;
the complete exchange costs at most nine native volumes for positive rows. -/
theorem runs_linear {t : ℕ} (v : Tapes t 2) (src dst : Fin t) (hne : src≠dst) (ht : 2≤t)
    (sh : Shape) (rows ell p : ℕ) (hr : 0<rows) (f g : Array sh rows ell)
    (hf : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hg : ∀ i,(g i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (g i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hs : v.tape src=NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hd : v.tape dst=NativeZeroPadding.word (NativeZeroPaddingArray.word g))
    (hhs : v.head src=0) (hhd : v.head dst=0) :
    HoareTime (program src dst hne ht) (fun w => w=v)
      (fun w => w=write (write v src (NativeZeroPadding.word (NativeZeroPaddingArray.word g)))
        dst (NativeZeroPadding.word (NativeZeroPaddingArray.word f)))
      (9*CompactNativeRoleTransferBudget.volume rows sh ell p) := by
  apply (runs v src dst hne ht sh rows ell p f g hf hg hs hd hhs hhd).consequence
    (fun _ h => h) (fun _ h => h)
  have hv : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  omega

end
end IntegerMultBounds.Machine.NativeRoleWordSwap
