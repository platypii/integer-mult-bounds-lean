import IntegerMultBounds.Networks.ComplexPhaseRowSchedule

/-! Literal recursive call occurrences retain the wire and edge position of
the actual complex25 label-update trace. Repeated equal labels remain distinct
call sites. This is the fixed finite call schema, not a tape controller. -/
namespace IntegerMultBounds.Networks.ComplexRecursiveCallSchema
noncomputable section
open ComplexPhaseBudget ComplexPhaseRowSchedule
abbrev Wire := Wires.ComplexRole 25

private theorem trace_length {ι L : Type*} [DecidableEq ι]
    (current : ι → L) (us : List (ι × L)) : (RankTrace.edges current us).length = us.length := by
  induction us generalizing current with
  | nil => rfl
  | cons u us ih => simp only [RankTrace.edges, List.length_cons, ih]

theorem edge_length : edges.length = updates.length :=
  trace_length (GlobalLabels.source ComplexRank25.vector) updates

def sites : List Edge := edges.attach
abbrev Occurrence := Fin sites.length

def edge (site : Occurrence) : Edge := sites[site.val]

def role (site : Occurrence) : Wire := (updates[site.val]'(by
  have hi := site.isLt
  simpa only [sites, List.length_attach, edge_length] using hi)).1

structure CallFor (es : List Edge) where
  site : Fin es.length
  coordinate : Fin (dimension es[site.val])

abbrev Call := CallFor sites

def Call.role (call : Call) : Wire := ComplexRecursiveCallSchema.role call.site
def Call.slot (call : Call) : Fin (25 ^ 3) := ComplexPhaseRowSchedule.slot (edge call.site) call.coordinate
def Call.inverse (call : Call) : Bool := direction (edge call.site)

def callsAtFor (es : List Edge) (site : Fin es.length) : List (CallFor es) :=
  List.ofFn (fun i => ⟨site,i⟩)
def callsFor (es : List Edge) : List (CallFor es) := (List.ofFn (callsAtFor es)).flatten

theorem callsFor_length (es : List Edge) : (callsFor es).length =
    ∑ site : Fin es.length, dimension es[site.val] := by
  simp only [callsFor, List.length_flatten, List.map_ofFn]
  have hh : (fun site : Fin es.length => (callsAtFor es site).length) =
      (fun site => dimension es[site.val]) := by
    funext site
    exact List.length_ofFn
  change (List.ofFn (fun site : Fin es.length => (callsAtFor es site).length)).sum = _
  rw [hh, List.sum_ofFn]

def callsAt (site : Occurrence) : List Call := callsAtFor sites site
def calls : List Call := callsFor sites

theorem callsAt_length (site : Occurrence) : (callsAt site).length = dimension (edge site) :=
  List.length_ofFn

theorem calls_length : calls.length = ∑ site : Occurrence, dimension (edge site) :=
  callsFor_length sites

/-- Every site uses all and only its actual residual coordinates, in original
slot order. Equal edges on different wires are never identified. -/
theorem callsAt_site (site : Occurrence) (call : Call) (hc : call ∈ callsAt site) : call.site = site := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  rfl

theorem callsAt_complete (call : Call) : call ∈ callsAt call.site :=
  List.mem_ofFn.mpr ⟨call.coordinate, rfl⟩

theorem slot_val (call : Call) : call.slot.val = call.coordinate.val := rfl

theorem calls_complete (call : Call) : call ∈ calls := by
  apply List.mem_flatten.mpr
  refine ⟨callsAt call.site, List.mem_ofFn.mpr ⟨call.site,rfl⟩, callsAt_complete call⟩

/-- Every site's child count equals its original projector-difference rank. -/
theorem dimension_eq_rank (e : Edge) : dimension e =
    ProjectionTrace.edgeRank form formSymm e.val.1 e.val.2 := by
  have hd : dimension e = Module.finrank (ZMod 2) (upper (direction e) e.val) -
      Module.finrank (ZMod 2) (lower (direction e) e.val) := by
    change Module.finrank (ZMod 2)
      (ProjectionRank.residual (Labels.binary (25 ^ 3)) (low e) (high e)) = _
    unfold low high
    rw [← LabelTransport.residual form (Labels.binary (25 ^ 3))
      (TensorCoordinates.coordinates 25) (TensorCoordinates.coordinates_isometry 25)]
    rw [LabelTransport.finrank_label, ProjectionRank.residual_finrank form formSymm
      _ _ (valid e).2.1 (valid e).1]
  have hn := edges_nondegenerate e.val e.property
  have hr := ProjectionTrace.edgeRank_eq form formSymm e.val.1 e.val.2 hn.1 hn.2
    (by
      cases hb : direction e
      · exact Or.inl (by simpa [lower,upper,hb] using (valid e).1)
      · exact Or.inr (by simpa [lower,upper,hb] using (valid e).1))
  rw [hr]
  cases hb : direction e
  · have hle : e.val.1 ≤ e.val.2 := by simpa [lower,upper,hb] using (valid e).1
    have hm := Submodule.finrank_mono hle
    rw [hb] at hd
    change dimension e = Module.finrank (ZMod 2) e.val.2 - Module.finrank (ZMod 2) e.val.1 at hd
    simpa only [Nat.sub_eq_zero_of_le hm, Nat.add_zero] using hd
  · have hle : e.val.2 ≤ e.val.1 := by simpa [lower,upper,hb] using (valid e).1
    have hm := Submodule.finrank_mono hle
    rw [hb] at hd
    change dimension e = Module.finrank (ZMod 2) e.val.1 - Module.finrank (ZMod 2) e.val.2 at hd
    simpa only [Nat.sub_eq_zero_of_le hm, Nat.zero_add] using hd

private theorem sum_dimensions (es : List Edge) :
    (∑ site : Fin es.length, dimension es[site.val]) =
      (es.map (fun e => ProjectionTrace.edgeRank form formSymm e.val.1 e.val.2)).sum := by
  rw [← List.ofFn_getElem_eq_map es, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro site _
  exact dimension_eq_rank _

/-- Exactly the proved actual complex-network rank sum many child calls. -/
theorem calls_rankSum : calls.length = ComplexRank25.rankSum := by
  rw [calls_length]
  change (∑ site : Fin sites.length, dimension sites[site.val]) = _
  rw [sum_dimensions sites]
  have hh : (sites.map (fun e => ProjectionTrace.edgeRank form formSymm e.val.1 e.val.2)).sum =
      (edges.map (fun p => ProjectionTrace.edgeRank form formSymm p.1 p.2)).sum := by
    exact congrArg List.sum (List.attach_map_val (l := edges)
      (f := fun p => ProjectionTrace.edgeRank form formSymm p.1 p.2))
  exact hh.trans rank_sum_eq

/-- The manuscript's exact integer stop test for beta=1/1000. Exponent-zero
nodes are leaves even in the finite small-d regime. -/
def stopped (globalAxes remainingExponent : ℕ) : Bool :=
  decide (remainingExponent = 0 ∨ ((25 ^ 3)^remainingExponent)^1000 < globalAxes)

theorem stopped_iff (globalAxes remainingExponent : ℕ) : stopped globalAxes remainingExponent = true ↔
    remainingExponent = 0 ∨ ((25 ^ 3)^remainingExponent)^1000 < globalAxes := by
  simp [stopped]

end
end IntegerMultBounds.Networks.ComplexRecursiveCallSchema
