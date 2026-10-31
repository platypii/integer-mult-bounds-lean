module

public import IntegerMultBounds.Machine.FiniteFlowWithin
public import IntegerMultBounds.Machine.HoareWithin

/-! A bounded selector block jumps to a bounded terminal block on the same bank. -/
@[expose] public section
namespace IntegerMultBounds.Machine.FiniteFlow
noncomputable section
variable {N t a : ℕ} {states : Fin N → ℕ}

theorem jump_then_halt_within
    (family : ∀ pc, Program t (states pc) a) (next : Next states)
    (entry pc : Fin N) {v : Tapes t a} {c : Config t (states entry) a}
    {H : TapePred t a} {n B : ℕ} {post : TapePred t a}
    (hr : RunWithin (family entry) H n (v.start (family entry)) c)
    (hh : step (family entry) c = none) (he : next entry c.state = some pc)
    (tail : HoareWithin (family pc) (· = c.tapes) post B H)
    (halt : ∀ st, next pc st = none) :
    HoareWithin (program family next entry) (· = v) post (n+1+B) H := by
  rintro input rfl
  obtain ⟨m,hm,d,hd,hdh,hdout⟩ := tail c.tapes rfl
  have hfirst := block_then_jump_within family next entry entry pc hr hh he
  have hlast := block_within family next entry pc hd
  refine ⟨n+1+m,by omega,d.mapState (embed states pc),?_,?_,hdout⟩
  · exact hfirst.trans hlast
  · exact FiniteFlow.halt family next entry pc d hdh (halt d.state)

end
end IntegerMultBounds.Machine.FiniteFlow
