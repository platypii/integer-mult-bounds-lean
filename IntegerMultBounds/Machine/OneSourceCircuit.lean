import IntegerMultBounds.Machine.SparseRoleCircuit
import IntegerMultBounds.Networks.GlobalCircuit
import IntegerMultBounds.Networks.BoundedCircuit

/-! A proof-carrying fixed compiler for scalar lists consisting of one-source
XORs. The list is preserved literally, including reversal and role renaming;
only its finite register names are enumerated as physical role tape slots. -/
namespace IntegerMultBounds.Machine.OneSourceCircuit
open Networks
variable {ι κ : Type*}

/-- Each actual scalar instruction is a distinct-source XOR. -/
def IsXor (p : Circuit.Program ι (ZMod 2)) : Prop :=
  ∀ g ∈ p, ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src

theorem append {p q : Circuit.Program ι (ZMod 2)} (hp : IsXor p) (hq : IsXor q) : IsXor (p++q) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hp g hg
  · exact hq g hg

theorem reverse {p : Circuit.Program ι (ZMod 2)} (hp : IsXor p) : IsXor p.reverse := by
  intro g hg
  exact hp g (List.mem_reverse.mp hg)

theorem embed (f : ι ↪ κ) {p : Circuit.Program ι (ZMod 2)} (hp : IsXor p) :
    IsXor (GlobalCircuit.embed f p) := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  obtain ⟨dst,src,hne,rfl⟩ := hp g' hg'
  exact ⟨f dst,f src,f.injective.ne hne,rfl⟩

theorem rename (e : ι ≃ κ) {p : Circuit.Program ι (ZMod 2)} (hp : IsXor p) :
    IsXor (Circuit.rename e p) := by
  intro g hg
  obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
  obtain ⟨dst,src,hne,rfl⟩ := hp g' hg'
  exact ⟨e dst,e src,e.injective.ne hne,rfl⟩

theorem copies {α β : Type*} (dst : α → ι) (src : β → ι) (entries : List (α × β))
    (hne : ∀ x y, dst x ≠ src y) : IsXor (Networks.SparseCircuit.copies dst src entries) := by
  intro g hg
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hg
  exact ⟨dst e.1,src e.2,hne e.1 e.2,rfl⟩

private theorem finiteGate_xor (capacity : ℕ) (g : Circuit.Gate ℕ (ZMod 2))
    (hb : BoundedCircuit.GateBounded capacity g)
    (hg : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src) :
    ∃ dst src, dst ≠ src ∧ BoundedCircuit.finiteGate capacity g hb = ReversibleFanout.add dst src := by
  obtain ⟨dst,src,hne,rfl⟩ := hg
  have hd : dst < capacity := hb.1
  have hs : src < capacity := hb.2 (src,1) (by simp [ReversibleFanout.add])
  refine ⟨⟨dst,hd⟩,⟨src,hs⟩,?_,?_⟩
  · intro h; exact hne (congrArg Fin.val h)
  · simp [BoundedCircuit.finiteGate,ReversibleFanout.add]

theorem finiteProgram (capacity : ℕ) (p : Circuit.Program ℕ (ZMod 2))
    (hb : BoundedCircuit.Bounded capacity p) (hp : IsXor p) :
    IsXor (BoundedCircuit.finiteProgram capacity p hb) := by
  intro g hg
  obtain ⟨g,_,rfl⟩ := List.mem_map.mp hg
  exact finiteGate_xor capacity g.val (hb g.val g.property) (hp g.val g.property)

noncomputable section
variable {t a n : ℕ}

private def chosen (e : Fin t ≃ ι) (g : Circuit.Gate ι (ZMod 2))
    (h : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src) : PointwiseRoleGate.Gate t where
  dst := e.symm (Classical.choose h)
  src := e.symm (Classical.choose (Classical.choose_spec h))
  distinct := e.symm.injective.ne (Classical.choose_spec (Classical.choose_spec h)).1.symm

private theorem chosen_scalar (e : Fin t ≃ ι) (g : Circuit.Gate ι (ZMod 2))
    (h : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src) :
    SparseRoleCircuit.scalar (chosen e g h) = g.rename e.symm := by
  conv_rhs => rw [(Classical.choose_spec (Classical.choose_spec h)).2]
  rfl

def gates (e : Fin t ≃ ι) (p : Circuit.Program ι (ZMod 2)) (hp : IsXor p) :
    List (PointwiseRoleGate.Gate t) := p.attach.map (fun g => chosen e g.val (hp g.val g.property))

theorem gates_length (e : Fin t ≃ ι) (p : Circuit.Program ι (ZMod 2)) (hp : IsXor p) :
    (gates e p hp).length = p.length := by simp [gates]

theorem gates_scalar (e : Fin t ≃ ι) (p : Circuit.Program ι (ZMod 2)) (hp : IsXor p) :
    (gates e p hp).map SparseRoleCircuit.scalar = Circuit.rename e.symm p := by
  simp only [gates,List.map_map,Function.comp_def,chosen_scalar,Circuit.rename]
  exact List.attach_map_val

def program (e : Fin t ≃ ι) (p : Circuit.Program ι (ZMod 2)) (hp : IsXor p) :=
  PointwiseRoleCircuit.program (PointwiseBinary.xorSymbol (a := a)) (gates e p hp)

/-- Exact realization of the original scalar list at each position of its
literal bit streams. All background cells, heads, and controls are preserved. -/
theorem circuit_hoare [DecidableEq ι] (e : Fin t ≃ ι) (p : Circuit.Program ι (ZMod 2)) (hp : IsXor p)
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : ι → Fin n → ZMod 2) (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program e p hp)
      (fun w => w = PointwiseRoleGate.bank background origins (SparseRoleCircuit.encoded (fun k i => data (e k) i)) bs)
      (fun w => w = PointwiseRoleGate.bank background origins
        (SparseRoleCircuit.encoded (fun k i => Circuit.run p (fun k => data k i) (e k))) bs)
      (p.length*(14*n+14*bs.length+34)) := by
  have hh := PointwiseRoleCircuit.circuit_hoare PointwiseBinary.xorSymbol (gates e p hp)
    background origins (SparseRoleCircuit.encoded (fun k i => data (e k) i)) bs hn
  rw [SparseRoleCircuit.execute_encoded,gates_scalar] at hh
  have he (i : Fin n) (k : Fin t) :
      Circuit.run (Circuit.rename e.symm p) (fun k => data (e k) i) k = Circuit.run p (fun k => data k i) (e k) := by
    have h := congrFun (Circuit.run_rename e.symm p (fun k => data (e k) i)) (e k)
    simpa only [Function.comp_apply,Function.comp_def,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using h
  apply hh.consequence (fun _ h => h) _ (le_of_eq (by rw [gates_length]))
  intro w hw
  simpa only [he] using hw

end
end IntegerMultBounds.Machine.OneSourceCircuit
