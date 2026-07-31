import Pom.Lpo.Operations.Seq
import Pom.Linearization

open Linearization

/-- If `p` depends only on `s`, `q` only on `u`, these are disjoint and `q` is satisfiable,
then conjoining `q` does not change the satisfiability of `p`. -/
lemma sat_and_indep {α : Type} {p q : Form α} {s u : Set α}
    (hp : p.DependsOn s) (hq : q.DependsOn u) (hd : Disjoint s u) (hqsat : q.sat) :
    Form.sat (p.and q) ↔ Form.sat p := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, hv.1⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := hqsat
    have hsd1 : Disjoint (symmDiff v ((v \ u) ∪ (w ∩ u))) s := by
      rw [Set.disjoint_left]; intro x hx hxs
      have hxu : x ∉ u := fun hxu => Set.disjoint_left.mp hd hxs hxu
      rcases Set.mem_symmDiff.mp hx with ⟨hxv, hxv'⟩ | ⟨hxv', hxv⟩
      · exact hxv' (Or.inl ⟨hxv, hxu⟩)
      · rcases hxv' with ⟨hxvv, _⟩ | ⟨_, hxuu⟩
        · exact hxv hxvv
        · exact hxu hxuu
    have hsd2 : Disjoint (symmDiff w ((v \ u) ∪ (w ∩ u))) u := by
      rw [Set.disjoint_left]; intro x hx hxu
      rcases Set.mem_symmDiff.mp hx with ⟨hxw, hxv'⟩ | ⟨hxv', hxw⟩
      · exact hxv' (Or.inr ⟨hxw, hxu⟩)
      · rcases hxv' with ⟨_, hxuu⟩ | ⟨hxww, _⟩
        · exact hxuu hxu
        · exact hxw hxww
    refine ⟨(v \ u) ∪ (w ∩ u), (hp v _ hsd1) ▸ hv, (hq w _ hsd2) ▸ hw⟩

namespace Lpofin

variable {act test : Type}

/-! ### Structural facts about `seq α β f`. -/
/-- On the nodes of `α`, `seq α β f` has the same formula as `α`. -/
lemma seq_form_alpha (α β : Lpofin (Label act test)) (f : CopyFn α β) {x : Node}
    (hx : x ∈ α.nodes) : (seq α β f).form x = α.form x := by
  ext v; constructor
  · rintro (hform | ⟨φ, hform, _⟩)
    · exact hform
    · exfalso
      refine Set.disjoint_left.mp (f.property φ).2.1 hx ?_
      exact ((f φ).val.property.form_dom x).mp ⟨_, hform⟩
  · exact Or.inl

/-- On the nodes of `α`, `seq α β f` has the same label as `α`. -/
lemma seq_lab_alpha (α β : Lpofin (Label act test)) (f : CopyFn α β) {x : Node} (hx : x ∈ α.nodes) :
    (seq α β f).lab x = α.lab x := by
  have hf : ¬ ∃ φ : α.branches, x ∈ (f φ).nodes := by
    rintro ⟨φ, hφ⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hx hφ
  simp only [seq, lab, Lpo.lab, seq_base, dif_neg hf]

/-- On the nodes of a copy `f φ`, the `seq` formula is the copy formula conjoined with the
branch condition `φ`. -/
lemma seq_form_copy (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).form z = ((f φ).form z).and φ.val.toForm := by
  have hz' : z ∉ α.nodes := Set.disjoint_right.mp (f.property φ).2.1 hz
  ext v; constructor
  · rintro (hform | ⟨ψ, hform, hψ⟩)
    · exfalso
      refine Set.disjoint_right.mp (f.property φ).2.1 hz ?_
      exact (α.val.property.form_dom z).mp ⟨_, hform⟩
    · have : φ = ψ := by
        by_contra hc
        exact Set.disjoint_left.mp ((f.property φ).2.2 ψ hc) hz
          (((f ψ).val.property.form_dom z).mp ⟨v, hform⟩)
      subst this; exact ⟨hform, hψ⟩
  · intro hform; right; exact ⟨φ, hform⟩

/-- On the nodes of a copy `f φ`, the `seq` label agrees with the copy label. -/
lemma seq_lab_copy (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).lab z = (f φ).lab z := by
  have hex : ∃ ψ : α.branches, z ∈ (f ψ).nodes := ⟨φ, hz⟩
  simp only [seq, lab, Lpo.lab, seq_base, dif_pos hex]
  have hchoose : hex.choose = φ := by
    by_contra hc
    exact Set.disjoint_left.mp ((f.property hex.choose).2.2 φ hc) hex.choose_spec hz
  rw [hchoose]

/-- The formula attached to a copy node depends only on the nodes of that copy. -/
lemma copy_form_dependsOn (α β : Lpofin (Label act test)) (f : CopyFn α β)
    (φ : α.branches) {y : Node} (hy : y ∈ (f φ).nodes) :
    ((f φ).form y).DependsOn (f φ).nodes := by
  refine Form.DependsOn.monotone _ ?_ ((f φ).val.property.form y hy).1
  intro z hz; exact ((f φ).val.property.rel_dom hz).1

/-- Guard-equivalence for the copy phase: on a copy node `y`, the `seq` guard
`(φ.and ψ) ≤ (seq α β f).form y` agrees with the copy guard `ψ ≤ (f φ).form y`,
provided the accumulator `ψ` depends only on the copy's nodes.  The extra `φ`
conjunct is harmless because `φ` depends on the (disjoint) nodes of `α` and is
satisfiable, so it can always be satisfied without changing the copy formulas. -/
lemma seq_guard_copy (α β : Lpofin (Label act test)) (f : CopyFn α β)
    (φ : α.branches) {ψ : Form Node} {y : Node}
    (hy : y ∈ (f φ).nodes) (hψ : ψ.DependsOn (f φ).nodes) :
    ((φ.val.toForm.and ψ) ≤ (seq α β f).form y) ↔ (ψ ≤ (f φ).form y) := by
  have hg : ((f φ).form y).DependsOn (f φ).nodes := copy_form_dependsOn α β f φ hy
  have hφdep : φ.val.toForm.DependsOn α.nodes := by
    refine φ.val.dependsOn.monotone _ ?_
    exact φ.val.tests_valid.trans tests_sub_nodes
  have hd : Disjoint α.nodes (f φ).nodes := (f.property φ).2.1
  rw [seq_form_copy α β f φ hy]
  constructor
  · intro h v hv
    obtain ⟨w, hw⟩ := φ.val.sat
    set v' : Set Node := (v \ α.nodes) ∪ (w ∩ α.nodes) with hv'def
    -- `v'` agrees with `w` on `α.nodes` and with `v` on `(f φ).nodes`.
    have hsdφ : Disjoint (symmDiff w v') α.nodes := by
      rw [Set.disjoint_left]; intro x hx hxα
      rcases Set.mem_symmDiff.mp hx with ⟨hxw, hxv'⟩ | ⟨hxv', hxw⟩
      · exact hxv' (Or.inr ⟨hxw, hxα⟩)
      · rcases hxv' with ⟨_, hxnα⟩ | ⟨hxw', _⟩
        · exact hxnα hxα
        · exact hxw hxw'
    have hsdψ : Disjoint (symmDiff v v') (f φ).nodes := by
      rw [Set.disjoint_left]; intro x hx hxfφ
      have hxnα : x ∉ α.nodes := Set.disjoint_left.mp hd.symm hxfφ
      rcases Set.mem_symmDiff.mp hx with ⟨hxv, hxv'⟩ | ⟨hxv', hxv⟩
      · exact hxv' (Or.inl ⟨hxv, hxnα⟩)
      · rcases hxv' with ⟨hxvv, _⟩ | ⟨_, hxα⟩
        · exact hxv hxvv
        · exact hxnα hxα
    have hφv' : φ.val.toForm v' := (hφdep w v' hsdφ) ▸ hw
    have hψv' : ψ v' := (hψ v v' hsdψ) ▸ hv
    have hgoal := (h v' ⟨hφv', hψv'⟩).1
    exact (hg v v' hsdψ).symm ▸ hgoal
  · intro h v hv
    exact ⟨h v hv.2, hv.1⟩

/-! ### The copy phase: once the remaining set lies inside a single copy `f φ`,
`seq α β f` linearizes exactly like that copy. -/
/-- Within a copy, `seq`'s minimal elements coincide with the copy's. -/
lemma seq_next_copy (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes)
    (ψ : Form Node) (hψ : ψ.DependsOn (f φ).nodes) :
    (seq α β f).next w (φ.val.toForm.and ψ) = (f φ).next w ψ := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨_, hyw, himp, hmin⟩
    refine ⟨hw hyw, hyw, ?_, ?_⟩
    · exact (seq_guard_copy α β f φ (hw hyw) hψ).mp himp
    · intro z hz hzw; exact hmin z (Or.inr ⟨φ, Or.inl hz⟩) hzw
  · rintro ⟨hyφ, hyw, himp, hmin⟩
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨φ, hyφ⟩), hyw, ?_, ?_⟩
    · exact (seq_guard_copy α β f φ (hw hyw) hψ).mpr himp
    · intro z hz hzw
      rcases hz with hz | ⟨ψ, hz | ⟨hform, hz⟩⟩
      · exact Set.disjoint_left.mp (f.property φ).2.1 (α.val.property.rel_dom hz).2 hyφ
      · have hψφ : ψ = φ := by
          by_contra hc
          exact Set.disjoint_left.mp ((f.property ψ).2.2 φ hc)
            ((f ψ).val.property.rel_dom hz).2 hyφ
        subst hψφ; exact hmin z hz hzw
      · exact Set.disjoint_left.mp (f.property φ).2.1 (branch_implies_node ψ hform) (hw hzw)

/-- Within a copy, `seq`'s outcome filter coincides with the copy's.  The extra branch
conjunct `φ` in the `seq` formula does not change satisfiability because `φ` is satisfiable
and ranges over the (disjoint) nodes of `α`. -/
lemma seq_filter_copy (α β : Lpofin (Label act test)) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) {x : Node} (hx : x ∈ w) (r : Bool) :
    (seq α β f).filter_by_outcome w x r = (f φ).filter_by_outcome w x r := by
  classical
  unfold filter_by_outcome
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hze => ?_
  have hz : z ∈ (f φ).nodes := hw (Finset.mem_of_mem_erase hze)
  have hxz : x ∈ (f φ).nodes := hw hx
  rw [seq_form_copy α β f φ hz, Form.and_comm_assoc]
  have hA : ((f φ).form z).DependsOn (f φ).nodes := by
    refine Form.DependsOn.monotone _ ?_ ((f φ).val.property.form z hz).1
    intro y hy; exact ((f φ).val.property.rel_dom hy).1
  have hlit : (bif r then Form.literal x else (Form.literal x).not).DependsOn (f φ).nodes := by
    cases r <;> simp only [cond_true, cond_false]
    · exact Form.DependsOn.monotone _ (by simpa using hxz) (Form.DependsOn.literal (x := x)).not
    · exact Form.DependsOn.monotone _ (by simpa using hxz) (Form.DependsOn.literal (x := x))
  have hp : (((f φ).form z).and
      (bif r then Form.literal x else (Form.literal x).not)).DependsOn (f φ).nodes := by
    have := Form.DependsOn.and hA hlit; rwa [Set.union_self] at this
  refine sat_and_indep hp ?_ ((f.property φ).2.1.symm) φ.val.sat
  refine φ.val.dependsOn.monotone _ ?_
  exact φ.val.tests_valid.trans tests_sub_nodes

variable {t : Type → Type} {s : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)]
    [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β)

/-! ### The copy phase, mirror of `lin_rec_guard_right_aux`, using `seq_next_copy`,
Mirror of `lin_rec_guard_right_aux`, using `seq_next_copy`, `seq_lab_copy`,
`seq_lab_copy`, `seq_filter_copy`. -/

/-- The test literal accumulated at a copy node depends only on the nodes of that copy. -/
lemma copy_literal_dependsOn (φ : α.branches) {y : Node} (hy : y ∈ (f φ).nodes) (rr : Bool) :
    (if rr then Form.literal y else (Form.literal y).not).DependsOn (f φ).nodes := by
  have hsub : ({y} : Set Node) ⊆ (f φ).nodes := by simpa using hy
  cases rr <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y)).not
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y))

/-- Generalized copy phase, by strong induction on the remaining set `w ⊆ (f φ).nodes`,
with an arbitrary accumulator `ψ` that depends only on the copy's nodes. -/
lemma seq_lin_rec_copy_gen (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) (ψ : Form Node)
    (hψ : ψ.DependsOn (f φ).nodes) :
    ((seq α β f).lin_rec w (φ.val.toForm.and ψ) : s → t s) = (f φ).lin_rec w ψ := by
  classical
  induction w using Finset.strongInduction generalizing ψ with
  | H w ih =>
    ext σ
    unfold lin_rec
    refine if_congr ?_ rfl ?_
    · rw [seq_next_copy α β f φ w hw ψ hψ]
    · refine Nondet.finset_congr (seq_next_copy α β f φ w hw ψ hψ) ?_
      ext ⟨y, hy⟩
      have hyw : y ∈ w := (Finset.mem_filter.mp hy).2.1
      have hyφ : y ∈ (f φ).nodes := hw hyw
      simp only [lin_node, Function.comp_apply]
      rw [seq_lab_copy α β f φ hyφ]
      match hl : (f φ).lab y with
      | Label.bot => rfl
      | Label.fork =>
        exact congrFun (ih (w.erase y) (Finset.erase_ssubset hyw)
          (fun _ h ↦ hw (Finset.mem_of_mem_erase h)) ψ hψ) σ
      | Label.act ac =>
        refine congrArg₂ Bind.bind rfl ?_; funext τ
        exact congrFun (ih (w.erase y) (Finset.erase_ssubset hyw)
          (fun _ h ↦ hw (Finset.mem_of_mem_erase h)) ψ hψ) τ
      | Label.test bb =>
        refine congrArg₂ Bind.bind rfl ?_; funext rr
        rw [seq_filter_copy α β f φ w hw hyw rr, Form.and_assoc]
        have hψ' : (ψ.and (if rr then Form.literal y else (Form.literal y).not)).DependsOn
            (f φ).nodes := by
          have := Form.DependsOn.and hψ (copy_literal_dependsOn α β f φ hyφ rr)
          rwa [Set.union_self] at this
        exact congrFun (ih ((f φ).filter_by_outcome w y rr)
          (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
            (Finset.erase_ssubset hyw))
          (fun z hz ↦ hw (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))
          (ψ.and (if rr then Form.literal y else (Form.literal y).not)) hψ') σ

lemma seq_lin_rec_copy (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) :
    ((seq α β f).lin_rec w φ.val.toForm : s → t s) = (f φ).lin_rec w Form.true := by
  have h : ((seq α β f).lin_rec w (φ.val.toForm.and Form.true) : s → t s)
      = (f φ).lin_rec w Form.true :=
    seq_lin_rec_copy_gen α β f φ w hw Form.true
      (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true)
  rwa [Form.and_comm, Form.true_and] at h

/-- Linearizing `seq` on a whole copy equals linearizing `β` (copies are isomorphic to `β`). -/
lemma seq_lin_copy (φ : α.branches) :
    ((seq α β f).lin_rec (f φ).nodes_finset φ.val.toForm : s → t s) = lin β := by
  rw [seq_lin_rec_copy α β f φ (f φ).nodes_finset
    (fun _ hx ↦ (f φ).property.mem_toFinset.mp hx)]
  exact lin_isomorphic (f.property φ).1

open Classical in
noncomputable def active_branches (φ : PathCond α) : Finset ↑α.branches :=
  Set.Finite.toFinset (s := { ψ : α.branches | φ ≤ ψ })
    (by {
      have := α.branches_finite.to_subtype
      exact Set.toFinite _
    })

lemma mem_active (φ : PathCond α) (ψ : α.branches) :
    ψ ∈ α.active_branches φ ↔ φ ≤ ψ := by
  constructor
  · intro h; have := (Set.Finite.mem_toFinset _).mp h; exact this
  · intro h; apply (Set.Finite.mem_toFinset _).mpr; exact h

noncomputable def seq_nodes (u : Finset Node) (φ : PathCond α) : Finset Node :=
    u ∪ (active_branches α φ).biUnion fun φ ↦ (f φ).nodes_finset

/-- The minimal elements of `seq α β f` on `seq_nodes α β f u φ` are exactly the minimal
elements of `α` on `u`.  The copy nodes never contribute a minimal element because every
active branch `ψ` has, by `hreach`, some `α`-node `z ∈ u` with `ψ ≤ α.form z`, and every
such `z` precedes every node of the copy `f ψ` in `seq`. -/
lemma seq_next_alpha
    (u : Finset Node)
    (φ : PathCond α)
    (hu : ↑u ⊆ α.nodes)
    (hnext : (next α u φ.toForm).Nonempty) :
    next (seq α β f) (seq_nodes α β f u φ) φ.toForm = next α u φ.toForm := by
  classical
  ext x; constructor <;> (
    intro hx; have ⟨hx, hxu, himp, hmin⟩ := Finset.mem_filter.mp hx)
  · have hxu : x ∈ u := by
      rcases Finset.mem_union.mp hxu with hxu | h
      · exact hxu
      · exfalso; have ⟨ψ, h', hy⟩ := Finset.mem_biUnion.mp h
        have himp' := (mem_active _ _ _).mp h'
        have ⟨z, hz⟩ := hnext
        have ⟨_, hzu, hzimp, _⟩ := Finset.mem_filter.mp hz
        refine hmin z ?_ ?_
        · right; use ψ; right; constructor
          · intro v hψ
            exact hψ |> PathCond.toForm_antitone himp' _ |> hzimp _
          · exact (f ψ).property.mem_toFinset.mp hy
        · apply Finset.mem_union_left _ hzu
    refine Finset.mem_filter.mpr ⟨?_, hxu, ?_, ?_⟩
    · exact α.property.mem_toFinset.mpr <| hu hxu
    · intro v hv; rw [seq_form_alpha α β f (hu hxu)] at himp
      exact himp _ hv
    · intro y hrel hy
      exact hmin y (Or.inl hrel) (Finset.mem_union_left _ hy)
  · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine (Set.Finite.mem_toFinset _).mpr ?_; left
      exact α.property.mem_toFinset.mp hx
    · exact Finset.mem_union_left _ hxu
    · intro v hv; rw [seq_form_alpha α β f (hu hxu)]
      exact himp _ hv
    · intro y hrel hy; rcases hrel with hrel | ⟨ψ, h⟩
      · rcases Finset.mem_union.mp hy with hy | hy
        · exact hmin _ hrel hy
        · have ⟨ψ, _, hy⟩ := Finset.mem_biUnion.mp hy
          exact Set.disjoint_left.mp (f.property ψ).2.1
            (α.val.property.rel_dom hrel |>.1)
            ((f ψ).property.mem_toFinset.mp hy)
      · refine Set.disjoint_left.mp (f.property ψ).2.1 (hu hxu) ?_
        rcases h with hrel | ⟨_, hx⟩
        · exact (f ψ).val.property.rel_dom hrel |>.2
        · exact hx

/-- Erasing an `α`-node from `seq_nodes` only affects the `α` part. -/
lemma seq_erase_alpha (u : Finset Node) (φ : PathCond α) {x : Node} (hx : x ∈ α.nodes) :
    (α.seq_nodes β f u φ).erase x = α.seq_nodes β f (u.erase x) φ := by
  classical
  have hxB : x ∉ (α.active_branches φ).biUnion fun ψ ↦ (f ψ).nodes_finset := by
    rw [Finset.mem_biUnion]; rintro ⟨ψ, _, hxψ⟩
    exact Set.disjoint_left.mp (f.property ψ).2.1 hx ((Set.Finite.mem_toFinset _).mp hxψ)
  unfold seq_nodes
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxB]

/-- If `u` contains a reachable element, then the set of next nodes (which are ready
to schedule) is nonempty. -/
lemma next_nonempty_of_reachable
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hcomp : ∀ z ∈ α.tests, ∀ y ∈ u, α.rel z y → z ∉ u → z ∈ φ.tests)
    {x : Node} (hx : x ∈ u) (hr : α.ReachableWith φ x) : (α.next u φ.toForm).Nonempty := by
  have ⟨ψ, hext, himp⟩ := hr
  classical
  have ⟨z, hz, hmin⟩ :=
    @Finset.exists_minimal _ ⟨α.rel⟩ ⟨fun _ _ _ ↦ α.val.property.rel.trans⟩
      { y ∈ u | y = x ∨ α.rel y x }
      ⟨x, Finset.mem_filter.mpr ⟨hx, Or.inl rfl⟩⟩
  have ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
  have hyx {y} (hyz : α.rel y z) : α.rel y x := by
    rcases hzx with rfl | hzx
    · exact hyz
    · exact α.val.property.rel.trans hyz hzx
  have hmin {y} (hyz : α.rel y z) : y ∉ u := by
    intro hy
    have hzy := hmin (Finset.mem_filter.mpr ⟨hy, Or.inr (hyx hyz)⟩) hyz
    obtain rfl := α.val.property.rel.antisymm hyz hzy
    exact α.val.property.rel.irrefl _ hyz
  refine ⟨z, Finset.mem_filter.mpr ⟨?_, hz, ?_, ?_⟩⟩
  · exact α.property.mem_toFinset.mpr <| hu hz
  · refine PathCond.implies_weaken hext ?_ ?_
    · rcases hzx with rfl | hzx
      · exact himp
      · exact himp.trans <| (α.val.property.form z (hu hz)).2 _ hzx
    · refine (α.val.property.form z (hu hz)).1.monotone _ ?_
      intro y hyz ⟨hyt, hyt'⟩; apply hyt'
      apply hcomp _ (ψ.tests_valid hyt) _ hx (hyx hyz)
      exact hmin hyz
  · intro y; exact hmin

lemma active_branches_singleton
    (u : Finset Node)
    (φ : PathCond α)
    (hu : ↑u ⊆ α.nodes)
    -- Completeness: all tests below `u` must be accounted for in the
    -- path condition `φ`
    (hcomp : ∀ z ∈ α.tests, ∀ y ∈ u, α.rel z y → z ∉ u → z ∈ φ.tests)
    (hreach : ∀ z ∈ φ.tests, φ.toForm ≤ α.form z)
    (hbr :
      -- The execution is stuck
      (∀ {ψ}, φ ≤ ψ →
        ∃ x ∈ u, α.lab x = ⊥ ∧ α.ReachableWith ψ x) ∨
      -- Or φ is on the way to becoming a branch
      ((∀ x ∈ α.val.bots, α.ReachableWith φ x → x ∈ u) ∧
        ∀ {x},
          x ∉ φ.tests →
          α.isTest x →
          ¬ (∀ {ψ}, φ ≤ ψ → α.form x ≤ α.stuck ψ) →
          α.ReachableWith φ x →
          x ∈ u))
    (hemp : α.next u φ.toForm = ∅) :
    ∃ hφ, α.active_branches φ = {⟨φ, hφ⟩} := by
  have hφ : φ ∈ α.branches := by
    rcases hbr with hstk | ⟨hstuck, hmax⟩
    · exfalso; refine Finset.nonempty_iff_ne_empty.mp ?_ hemp
      have ⟨z, hz, _, hr⟩ := hstk (le_refl _)
      exact α.next_nonempty_of_reachable u φ hu hcomp hz hr
    · refine ⟨hreach, ?_, ?_⟩
      · intro v hform ⟨⟨x, hx, hbot, hr⟩, hxf⟩
        refine Finset.nonempty_iff_ne_empty.mp ?_ hemp
        exact α.next_nonempty_of_reachable u φ hu hcomp (hstuck x ⟨hx, hbot⟩ hr) hr
      · intro x hx hxt hnstk hr
        refine Finset.nonempty_iff_ne_empty.mp ?_ hemp
        refine α.next_nonempty_of_reachable u φ hu hcomp ?_ hr
        refine hmax hx hxt ?_ hr
        intro hstk; apply hnstk; exact hstk (le_refl _)
  use hφ; ext ⟨ψ, hψ⟩; constructor
  · intro h; refine Finset.mem_singleton.mpr ?_; ext1; simp only
    by_contra hne; have := branches_not_mutually_sat hψ hφ hne
    have himp := (mem_active _ _ _).mp h
    have ⟨v, hsat⟩ := ψ.sat
    exact this v ⟨hsat, PathCond.toForm_antitone himp _ hsat⟩
  · intro h; obtain rfl := Finset.mem_singleton.mp h |> congrArg Subtype.val
    refine (mem_active _ _ _).mpr ?_
    exact le_refl _

lemma lin_rec_seq
    (u : Finset Node)
    (φ : PathCond α)
    (hu : ↑u ⊆ α.nodes)
    -- Completeness: all tests below `u` must be accounted for in the
    -- path condition `φ`
    (hcomp : ∀ z ∈ α.tests, ∀ y ∈ u, α.rel z y → z ∉ u → z ∈ φ.tests)
    (hreach : ∀ z ∈ φ.tests, φ.toForm ≤ α.form z)
    (hbr :
      -- The execution is stuck
      (∀ {ψ}, φ ≤ ψ →
        ∃ x ∈ u, α.lab x = ⊥ ∧ α.ReachableWith ψ x) ∨
      -- Or φ is on the way to becoming a branch
      ((∀ x ∈ α.val.bots, α.ReachableWith φ x → x ∈ u) ∧
        ∀ {x},
          x ∉ φ.tests →
          α.isTest x →
          ¬ (∀ {ψ}, φ ≤ ψ → α.form x ≤ α.stuck ψ) →
          α.ReachableWith φ x →
          x ∈ u)) :
    (lin_rec (seq α β f) (seq_nodes α β f u φ) φ.toForm : s → t s) =
    fun σ ↦ lin_rec α u φ.toForm σ >>= lin β := by
  classical
  induction u using Finset.strongInduction generalizing φ with
  | H u ih =>
    ext σ; nth_rw 2 [lin_rec]; by_cases hemp : α.next u φ.toForm = ∅
    · simp only [↓reduceIte, hemp, pure_bind]
      have ⟨hφ, hactv⟩ := α.active_branches_singleton u φ hu hcomp hreach hbr hemp
      have hn : seq_nodes α β f u φ = (f ⟨φ, hφ⟩).nodes_finset := by
        sorry
      rw [hn]; exact congrFun (seq_lin_copy _ _ _ _) _
    · unfold lin_rec
      have hnext := seq_next_alpha α β f u φ hu (Finset.nonempty_of_ne_empty hemp)
      conv => lhs; arg 1; lhs; exact hnext
      simp only [hemp, ↓reduceIte]; rw [Linearizable.bind_additive]
      refine Nondet.finset_congr hnext ?_
      ext ⟨x, hx⟩; simp only [Function.comp_apply, lin_node]
      rw [hnext] at hx; have hxu := (Finset.mem_filter.mp hx).2.1
      rw [seq_lab_alpha α β f (hu hxu)]
      cases hl : α.lab x with
      | bot => symm; exact ContinuousMonad.bind_strict
      | fork =>
        simp only
        rw [seq_erase_alpha _ _ _ _ _ (hu hxu)]
        refine congrFun (ih (u.erase x) ?_ φ ?_ ?_ hreach ?_) _
        · exact Finset.erase_ssubset hxu
        · intro y hy; exact hu <| Finset.erase_subset _ _ hy
        · intro z hz y hy hzy hz'
          refine hcomp z hz y ?_ hzy ?_
          · exact Finset.erase_subset _ _ hy
          · intro hzu; refine Finset.mem_erase.mpr ⟨?_, hzu⟩ |> hz'
            rintro rfl; have ⟨_, heq⟩ := (Label.isTest_iff _).mp hz
            rw [heq] at hl; contradiction
        · rcases hbr with hstuck | ⟨hbots, hmax⟩
          · left; intro ψ hext
            have ⟨z, hzu, hzb, hzr⟩ := hstuck hext; refine ⟨z, ?_, hzb, hzr⟩
            refine Finset.mem_erase.mpr ⟨?_, hzu⟩; rintro rfl
            rw [hzb] at hl; contradiction
          · right; constructor
            · intro z hz hr; refine Finset.mem_erase.mpr ⟨?_, hbots z hz hr⟩
              rintro rfl; have := hz.2.symm.trans hl; contradiction
            · intro z hz hzt hnstk hr; refine Finset.mem_erase.mpr ⟨?_, hmax hz hzt hnstk hr⟩
              rintro rfl; have ⟨_, heq⟩ := (Label.isTest_iff _).mp hzt
              rw [heq] at hl; contradiction
      | act a =>
        simp only; rw [bind_assoc, seq_erase_alpha _ _ _ _ _ (hu hxu)]
        refine congrArg₂ Bind.bind rfl ?_
        refine ih (u.erase x) ?_ φ ?_ ?_ hreach ?_
        · exact Finset.erase_ssubset hxu
        · intro y hy; exact hu <| Finset.erase_subset _ _ hy
        · intro z hz y hy hzy hz'
          refine hcomp z hz y ?_ hzy ?_
          · exact Finset.erase_subset _ _ hy
          · intro hzu; refine Finset.mem_erase.mpr ⟨?_, hzu⟩ |> hz'
            rintro rfl; have ⟨_, heq⟩ := (Label.isTest_iff _).mp hz
            rw [heq] at hl; contradiction
        · rcases hbr with hstuck | ⟨hbots, hmax⟩
          · left; intro ψ hext
            have ⟨z, hzu, hzb, hzr⟩ := hstuck hext; refine ⟨z, ?_, hzb, hzr⟩
            refine Finset.mem_erase.mpr ⟨?_, hzu⟩; rintro rfl
            rw [hzb] at hl; contradiction
          · right; constructor
            · intro z hz hr; refine Finset.mem_erase.mpr ⟨?_, hbots z hz hr⟩
              rintro rfl; have := hz.2.symm.trans hl; contradiction
            · intro z hz hzt hnstk hr; refine Finset.mem_erase.mpr ⟨?_, hmax hz hzt hnstk hr⟩
              rintro rfl; have ⟨_, heq⟩ := (Label.isTest_iff _).mp hzt
              rw [heq] at hl; contradiction
      | test b =>
        simp only; rw [bind_assoc]; refine congrArg₂ Bind.bind rfl ?_
        ext r; have hxt := (Label.isTest_iff _).mpr ⟨_, hl⟩
        have hx_nt : x ∉ φ.tests := by
          sorry
        rw [← PathCond.extend_toForm _ hxt _ hx_nt]
        have :
            (α.seq β f).filter_by_outcome (α.seq_nodes β f u φ) x r =
            α.seq_nodes β f (α.filter_by_outcome u x r) (φ.extend hxt r) := sorry
        rw [this]
        refine congrFun (ih _ ?_ _ ?_ ?_ ?_ ?_) _
        · exact ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase (Finset.erase_ssubset hxu)
        · intro y hy; have ⟨hy', _⟩ := Finset.mem_filter.mp hy
          exact hu <| Finset.erase_subset _ _ hy'
        · intro z hz y hy hzy hz'
          by_cases heq : z = x
          · subst heq; exact Set.mem_insert _ _
          · refine Set.mem_insert_of_mem _ ?_
            have ⟨hy, ⟨v, hyf, hv⟩⟩ := Finset.mem_filter.mp hy
            have ⟨hne, hy⟩ := Finset.mem_erase.mp hy
            refine hcomp _ hz _ hy hzy ?_
            intro hzu
            apply (Finset.mem_filter.mpr.mt hz' |> not_and.mp) <| Finset.mem_erase.mpr ⟨heq, hzu⟩
            refine ⟨v, ?_, hv⟩
            exact (α.val.property.form _ (hu hzu)).2 _ hzy _ hyf
        · rintro z hz; refine (PathCond.toForm_antitone <| φ.extend_le hx_nt _ _).trans ?_
          rcases hz with rfl | hz
          · exact (Finset.mem_filter.mp hx).2.2.1
          · exact hreach _ hz
        · rcases hbr with hstuck | ⟨hbots, hmax⟩
          · left; intro ψ hext
            have ⟨z, hzu, hzb, hzr⟩ := hstuck <| (φ.extend_le hx_nt _ _).trans hext
            refine ⟨z, ?_, hzb, hzr⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hzu⟩, ?_⟩
            · rintro rfl; rw [hzb] at hl; contradiction
            · have ⟨ψ', hext', himp⟩ := hzr
              have ⟨v, hψ'⟩ := ψ'.sat
              refine ⟨v, himp _ hψ', ?_⟩
              have hform := PathCond.toForm_antitone (hext.trans hext') _ hψ' ⟨x, Set.mem_insert _ _⟩
              conv at hform => simp only; arg 1; lhs; exact dif_pos rfl
              rwa [Bool.cond_eq_ite]
          · right; constructor
            · intro z hz ⟨ψ, hext, himp⟩
              refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
              · rintro rfl; have := hz.2.symm.trans hl; contradiction
              · refine hbots z hz ⟨ψ, ?_, himp⟩
                exact (φ.extend_le hx_nt _ _).trans hext
              · have ⟨v, hψ⟩ := ψ.sat
                refine ⟨v, himp _ hψ, ?_⟩
                have hform := PathCond.toForm_antitone hext _ hψ ⟨x, Set.mem_insert _ _⟩
                conv at hform => simp only; arg 1; lhs; exact dif_pos rfl
                rwa [Bool.cond_eq_ite]
            · intro z hz hzt hnstk hr
              refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
              · rintro rfl; apply hz; exact Set.mem_insert _ _
              · refine hmax ?_ hzt ?_ ?_
                · intro h; apply hz
                  exact Set.mem_insert_of_mem _ h
                · intro hstk; apply hnstk; intro ψ hext
                  apply hstk; exact (φ.extend_le hx_nt _ _).trans hext
                · have ⟨ψ, hext, himp⟩ := hr
                  refine ⟨ψ, ?_, himp⟩
                  exact (φ.extend_le hx_nt _ _).trans hext
              · have ⟨ψ, hext, himp⟩ := hr; have ⟨v, hψ⟩ := ψ.sat
                refine ⟨v, himp _ hψ, ?_⟩
                have hform := PathCond.toForm_antitone hext _ hψ ⟨x, Set.mem_insert _ _⟩
                conv at hform => simp only; arg 1; lhs; exact dif_pos rfl
                rwa [Bool.cond_eq_ite]

lemma lin_seq :
    (lin (seq α β f) : s → t s) = fun σ ↦ lin α σ >>= lin β := by
  unfold lin
  have hnodes : (α.seq β f).nodes_finset = α.seq_nodes β f α.nodes_finset ⊥ := sorry
  rw [hnodes]; nth_rw 1 2 [← PathCond.empty_toForm]
  refine α.lin_rec_seq β f _ ⊥ ?_ ?_ ?_ ?_
  · intro x hx; exact α.property.mem_toFinset.mp hx
  · intro z hz _ _ _ hz'; exfalso; apply hz'
    exact α.property.mem_toFinset.mpr <| tests_sub_nodes hz
  · intro z hz; exfalso; exact Set.notMem_empty _ hz
  · right; constructor
    · intro z ⟨hz, _⟩ _; exact α.property.mem_toFinset.mpr hz
    · intro z _ hz _ _; exact α.property.mem_toFinset.mpr <| tests_sub_nodes hz

end Lpofin
