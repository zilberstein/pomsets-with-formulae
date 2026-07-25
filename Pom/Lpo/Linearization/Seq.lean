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

variable {l : Type} [PartialOrder l] [OrderBot l]
/-- A branch formula is satisfiable. -/
lemma branch_sat (α : Lpofin l) {φ : Form Node} (hφ : φ ∈ α.branches) : φ.sat := by
  obtain ⟨S, ⟨_, _, hsat, _, _⟩, rfl⟩ := hφ; exact hsat
/-- A branch formula depends only on the nodes of `α`. -/
lemma branch_dependsOn (α : Lpofin l) {φ : Form Node} (hφ : φ ∈ α.branches) :
    φ.DependsOn α.nodes := by
  obtain ⟨S, ⟨_, hsub, _, _, _⟩, rfl⟩ := hφ
  unfold Lpofin.conj
  refine Form.DependsOn.monotone _ ?_ (Form.DependsOn.sAnd (s := fun _ : S ↦ α.nodes)
    (fun x => ?_))
  · exact Set.iUnion_subset fun _ => le_refl _
  · have hx : x.val ∈ α.nodes := (hsub x.property).1
    refine Form.DependsOn.monotone _ ?_ (α.val.property.form x.val hx).1
    intro y hy; exact (α.val.property.rel_dom hy).1

/-! ### Structural facts about `seq α β f`. -/
/-- On the nodes of `α`, `seq α β f` has the same formula as `α`. -/
lemma seq_form_alpha (α β : Lpofin l) (f : CopyFn α β) {x : Node} (hx : x ∈ α.nodes) :
    (seq α β f).form x = α.form x := by
  simp only [seq, form, Lpo.form, seq_base, if_pos hx]

/-- On the nodes of `α`, `seq α β f` has the same label as `α`. -/
lemma seq_lab_alpha (α β : Lpofin l) (f : CopyFn α β) {x : Node} (hx : x ∈ α.nodes) :
    (seq α β f).lab x = α.lab x := by
  have hf : ¬ ∃ φ : α.branches, x ∈ (f φ).nodes := by
    rintro ⟨φ, hφ⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hx hφ
  simp only [seq, lab, Lpo.lab, seq_base, dif_neg hf]

/-- On the nodes of a copy `f φ`, the `seq` formula is the copy formula conjoined with the
branch condition `φ`. -/
lemma seq_form_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).form z = ((f φ).form z).and φ.val := by
  have hz' : z ∉ α.nodes := Set.disjoint_right.mp (f.property φ).2.1 hz
  simp only [seq, form, Lpo.form, seq_base, if_neg hz']
  ext v; constructor
  · rintro ⟨ψ, hψ, hφv⟩
    have : φ = ψ := by
      by_contra hc
      exact Set.disjoint_left.mp ((f.property φ).2.2 ψ hc) hz
        (((f ψ).val.property.form_dom z).mp ⟨v, hψ⟩)
    subst this; exact ⟨hψ, hφv⟩
  · rintro ⟨h1, h2⟩; exact ⟨φ, h1, h2⟩

/-- On the nodes of a copy `f φ`, the `seq` label agrees with the copy label. -/
lemma seq_lab_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches) {z : Node}
    (hz : z ∈ (f φ).nodes) :
    (seq α β f).lab z = (f φ).lab z := by
  have hex : ∃ ψ : α.branches, z ∈ (f ψ).nodes := ⟨φ, hz⟩
  simp only [seq, lab, Lpo.lab, seq_base, dif_pos hex]
  have hchoose : hex.choose = φ := by
    by_contra hc
    exact Set.disjoint_left.mp ((f.property hex.choose).2.2 φ hc) hex.choose_spec hz
  rw [hchoose]

/-! ### The copy phase: once the remaining set lies inside a single copy `f φ`,
`seq α β f` linearizes exactly like that copy. -/
/-- Within a copy, `seq`'s minimal elements coincide with the copy's. -/
lemma seq_next_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) :
    (seq α β f).next w = (f φ).next w := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨_, hyw, hmin⟩
    exact ⟨hw hyw, hyw, fun z hz hzw ↦ hmin z (Or.inr ⟨φ, Or.inl hz⟩) hzw⟩
  · rintro ⟨hyφ, hyw, hmin⟩
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨φ, hyφ⟩), hyw, ?_⟩
    intro z hz hzw
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
lemma seq_filter_copy (α β : Lpofin l) (f : CopyFn α β) (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) {x : Node} (hx : x ∈ w) (r : Bool) :
    (seq α β f).filter_by_outcome w x r = (f φ).filter_by_outcome w x r := by
  classical
  unfold filter_by_outcome
  ext z
  simp only [Finset.mem_filter]
  refine and_congr_right fun hze => ?_
  have hz : z ∈ (f φ).nodes := hw (Finset.mem_of_mem_erase hze)
  have hxz : x ∈ (f φ).nodes := hw hx
  rw [seq_form_copy α β f φ hz]
  have hreassoc :
      (((f φ).form z).and φ.val).and (bif r then Form.literal x else (Form.literal x).not) =
      (((f φ).form z).and (bif r then Form.literal x else (Form.literal x).not)).and φ.val := by
    ext v; simp only [Form.and]; tauto
  rw [hreassoc]
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
  exact sat_and_indep hp (branch_dependsOn α φ.property) ((f.property φ).2.1.symm)
    (branch_sat α φ.property)

variable {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β)

/-! ### The copy phase, mirror of `lin_rec_guard_right_aux`, using `seq_next_copy`,
Mirror of `lin_rec_guard_right_aux`, using `seq_next_copy`, `seq_lab_copy`,
`seq_lab_copy`, `seq_filter_copy`. -/

/-- The formula attached to a copy node depends only on the nodes of that copy. -/
lemma copy_form_dependsOn (φ : α.branches) {y : Node} (hy : y ∈ (f φ).nodes) :
    ((f φ).form y).DependsOn (f φ).nodes := by
  refine Form.DependsOn.monotone _ ?_ ((f φ).val.property.form y hy).1
  intro z hz; exact ((f φ).val.property.rel_dom hz).1

/-- The test literal accumulated at a copy node depends only on the nodes of that copy. -/
lemma copy_literal_dependsOn (φ : α.branches) {y : Node} (hy : y ∈ (f φ).nodes) (rr : Bool) :
    (if rr then Form.literal y else (Form.literal y).not).DependsOn (f φ).nodes := by
  have hsub : ({y} : Set Node) ⊆ (f φ).nodes := by simpa using hy
  cases rr <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y)).not
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y))

/-- Guard-equivalence for the copy phase: on a copy node `y`, the `seq` guard
`(φ.and ψ) ≤ (seq α β f).form y` agrees with the copy guard `ψ ≤ (f φ).form y`,
provided the accumulator `ψ` depends only on the copy's nodes.  The extra `φ`
conjunct is harmless because `φ` depends on the (disjoint) nodes of `α` and is
satisfiable, so it can always be satisfied without changing the copy formulas. -/
lemma seq_guard_copy (φ : α.branches) {ψ : Form Node} {y : Node}
    (hy : y ∈ (f φ).nodes) (hψ : ψ.DependsOn (f φ).nodes) :
    ((φ.val.and ψ) ≤ (seq α β f).form y) ↔ (ψ ≤ (f φ).form y) := by
  have hg : ((f φ).form y).DependsOn (f φ).nodes := copy_form_dependsOn α β f φ hy
  have hφdep : φ.val.DependsOn α.nodes := branch_dependsOn α φ.property
  have hd : Disjoint α.nodes (f φ).nodes := (f.property φ).2.1
  rw [seq_form_copy α β f φ hy]
  constructor
  · intro h v hv
    obtain ⟨w, hw⟩ := branch_sat α φ.property
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
    have hφv' : φ.val v' := (hφdep w v' hsdφ) ▸ hw
    have hψv' : ψ v' := (hψ v v' hsdψ) ▸ hv
    have hgoal := (h v' ⟨hφv', hψv'⟩).1
    exact (hg v v' hsdψ).symm ▸ hgoal
  · intro h v hv
    exact ⟨h v hv.2, hv.1⟩

/-- Generalized copy phase, by strong induction on the remaining set `w ⊆ (f φ).nodes`,
with an arbitrary accumulator `ψ` that depends only on the copy's nodes. -/
lemma seq_lin_rec_copy_gen (φ : α.branches)
    (w : Finset Node) (hw : ↑w ⊆ (f φ).nodes) (ψ : Form Node)
    (hψ : ψ.DependsOn (f φ).nodes) :
    ((seq α β f).lin_rec w (φ.val.and ψ) : s → t s) = (f φ).lin_rec w ψ := by
  classical
  induction w using Finset.strongInduction generalizing ψ with
  | H w ih =>
    ext σ
    unfold lin_rec
    refine if_congr (Iff.refl _) rfl ?_
    refine Nondet.finset_congr (seq_next_copy α β f φ w hw) ?_
    ext ⟨y, hy⟩
    have hyw : y ∈ w := (Finset.mem_filter.mp hy).2.1
    have hyφ : y ∈ (f φ).nodes := hw hyw
    refine if_congr (seq_guard_copy α β f φ hyφ hψ) ?_ rfl
    simp only [lin_node]
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
    ((seq α β f).lin_rec w φ.val : s → t s) = (f φ).lin_rec w Form.true := by
  have h : ((seq α β f).lin_rec w (φ.val.and Form.true) : s → t s)
      = (f φ).lin_rec w Form.true :=
    seq_lin_rec_copy_gen α β f φ w hw Form.true
      (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true)
  rwa [Form.and_comm, Form.true_and] at h

/-- Linearizing `seq` on a whole copy equals linearizing `β` (copies are isomorphic to `β`). -/
lemma seq_lin_copy (φ : α.branches) :
    ((seq α β f).lin_rec (f φ).nodes_finset φ.val : s → t s) = lin β := by
  rw [seq_lin_rec_copy α β f φ (f φ).nodes_finset
    (fun _ hx ↦ (f φ).property.mem_toFinset.mp hx)]
  exact lin_isomorphic (f.property φ).1

open Classical in
noncomputable def active_branches (φ : Form Node) : Finset ↑α.branches :=
  Set.Finite.toFinset (s := { ψ : α.branches | (φ.and ψ).sat })
    (by {
      have := α.branches_finite.to_subtype
      exact Set.toFinite _
    })

lemma mem_active (φ : Form Node) (ψ : α.branches) :
    ψ ∈ α.active_branches φ ↔ (φ.and ψ).sat := by
  constructor
  · intro h; have := (Set.Finite.mem_toFinset _).mp h; exact this
  · intro h; apply (Set.Finite.mem_toFinset _).mpr; exact h

noncomputable def seq_nodes (u : Finset Node) (φ : Form Node) : Finset Node :=
    u ∪ (active_branches α φ).biUnion fun φ ↦ (f φ).nodes_finset

/-- The minimal elements of `seq α β f` on `seq_nodes α β f u φ` are exactly the minimal
elements of `α` on `u`.  The copy nodes never contribute a minimal element because every
active branch `ψ` has, by `hreach`, some `α`-node `z ∈ u` with `ψ ≤ α.form z`, and every
such `z` precedes every node of the copy `f ψ` in `seq`. -/
lemma seq_next_alpha
    (u : Finset Node) (φ : Form Node) (hu : ↑u ⊆ α.nodes)
    (hreach : ∀ ψ ∈ α.active_branches φ, ∃ z ∈ u, (ψ : Form Node) ≤ α.form z) :
    next (seq α β f) (seq_nodes α β f u φ) = next α u := by
  classical
  have hmemseq : ∀ z : Node, z ∈ seq_nodes α β f u φ ↔
      z ∈ u ∨ ∃ ψ ∈ α.active_branches φ, z ∈ (f ψ).nodes := by
    intro z
    constructor
    · intro h; rcases Finset.mem_union.mp h with h | h
      · exact Or.inl h
      · rw [Finset.mem_biUnion] at h; obtain ⟨ψ, hψ, hz⟩ := h
        exact Or.inr ⟨ψ, hψ, (Set.Finite.mem_toFinset _).mp hz⟩
    · rintro (h | ⟨ψ, hψ, hz⟩)
      · exact Finset.mem_union_left _ h
      · refine Finset.mem_union_right _ ?_
        rw [Finset.mem_biUnion]; exact ⟨ψ, hψ, (Set.Finite.mem_toFinset _).mpr hz⟩
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel, seq, seq_base, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨_, hyseq, hymin⟩
    have hynocopy : ¬ ∃ ψ ∈ α.active_branches φ, y ∈ (f ψ).nodes := by
      rintro ⟨ψ, hψact, hyψ⟩
      obtain ⟨z, hzu, hzle⟩ := hreach ψ hψact
      exact hymin z (Or.inr ⟨ψ, Or.inr ⟨hzle, hyψ⟩⟩) ((hmemseq z).mpr (Or.inl hzu))
    have hyu : y ∈ u := by
      rcases (hmemseq y).mp hyseq with h | h
      · exact h
      · exact absurd h hynocopy
    refine ⟨hu hyu, hyu, ?_⟩
    intro z hzrel hzu
    exact hymin z (Or.inl hzrel) ((hmemseq z).mpr (Or.inl hzu))
  · rintro ⟨hyα, hyu, hymin⟩
    refine ⟨Or.inl hyα, (hmemseq y).mpr (Or.inl hyu), ?_⟩
    rintro z (hzrel | ⟨ψ, hzrel | ⟨hzle, hyψ⟩⟩) hzseq
    · rcases (hmemseq z).mp hzseq with hzu | ⟨χ, hχact, hzχ⟩
      · exact hymin z hzrel hzu
      · exact Set.disjoint_left.mp (f.property χ).2.1 (α.val.property.rel_dom hzrel).1 hzχ
    · exact Set.disjoint_left.mp (f.property ψ).2.1 hyα ((f ψ).val.property.rel_dom hzrel).2
    · exact Set.disjoint_left.mp (f.property ψ).2.1 hyα hyψ

  --   (u : Finset Node)
  --   (hne : u.Nonempty)
  --   (φ : Form Node)
  --   (hu : ↑u ⊆ α.nodes)
  --   (hsat : φ.sat)
  --   (hvalid : ∀ x ∈ u, (φ.and (α.form x)).sat)
  --   (hbr :
  --     -- The execution is stuck
  --     (∀ {v}, φ v → ∃ x ∈ u, α.form x v ∧ α.lab x = ⊥) ∨
  --     -- Or φ is on the way to becoming a branch
  --     (∃ T ⊆ α.extens,
  --       φ = α.conj T ∧
  --       (∀ x ∈ α.val.bots, ((α.conj T).and (α.form x)).sat → x ∈ u) ∧
  --       ∀ x ∉ T, x ∈ α.extens → Form.sat ((α.conj T).and (α.form x)) → x ∈ u)) :
  --   next (seq α β f) (seq_nodes α β f u φ) = next α u := by
  -- classical
  -- ext x; constructor <;> (
  --   intro hx; have ⟨hx, hxu, hmin⟩ := Finset.mem_filter.mp hx)
  -- · have : x ∈ u := by
  --     rcases Finset.mem_union.mp hxu with hxu | h
  --     · exact hxu
  --     · exfalso; have ⟨ψ, h', hy⟩ := Finset.mem_biUnion.mp h
  --       have ⟨_, v, hφ, hψ⟩ := Finset.mem_filter.mp h'
  --       rcases hbr with hstk | ⟨T, hext, rfl, hstk, hmax⟩
  --       · have ⟨z, hz, hform, hbot⟩:= hstk hφ
  --         have ⟨T, ⟨hne, hext, hsat, hstk, hmax⟩, heq⟩ :=
  --           α.branches_finite.mem_toFinset.mp ψ.property
  --         apply ((heq ▸ hstk) _ hψ |> not_exists.mp) ⟨z, hu hz, hbot⟩
  --         exact hform
  --       · have ⟨z, hz⟩ := hne
  --         refine hmin z ?_ ?_
  --         · right; use ψ; right; constructor
  --           · intro v hψ



  --             have ⟨T, ⟨hne, hext, hsat, hstk, hmax⟩, heq⟩ :=
  --               α.branches_finite.mem_toFinset.mp ψ.property

  --           · exact (f ψ).property.mem_toFinset.mp hy
  --         · apply Finset.mem_union_left _ hz
  --   refine Finset.mem_filter.mpr ⟨?_, this, ?_⟩
  --   · exact α.property.mem_toFinset.mpr <| hu this
  --   · intro y hrel hy
  --     exact hmin y (Or.inl hrel) (Finset.mem_union_left _ hy)
  -- · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  --   · refine (Set.Finite.mem_toFinset _).mpr ?_; left
  --     exact α.property.mem_toFinset.mp hx
  --   · exact Finset.mem_union_left _ hxu
  --   · intro y hrel hy; rcases hrel with hrel | ⟨ψ, h⟩
  --     · rcases Finset.mem_union.mp hy with hy | hy
  --       · exact hmin _ hrel hy
  --       · have ⟨ψ, _, hy⟩ := Finset.mem_biUnion.mp hy
  --         exact Set.disjoint_left.mp (f.property ψ).2.1
  --           (α.val.property.rel_dom hrel |>.1)
  --           ((f ψ).property.mem_toFinset.mp hy)
  --     · refine Set.disjoint_left.mp (f.property ψ).2.1 (hu hxu) ?_
  --       rcases h with hrel | ⟨_, hx⟩
  --       · exact (f ψ).val.property.rel_dom hrel |>.2
  --       · exact hx


      --     · exact hrel
      --     ·
      --     rcases hrel with hrel | ⟨ψ, h⟩
      --     · exfalso; refine Set.disjoint_left.mp (f.property ψ).2.1 (hu hxu) ?_
      --     rcases h with hrel | ⟨_, hx⟩
      --     · exact (f ψ).val.property.rel_dom hrel |>.2
      --     · exact hx
      -- · have ⟨ψ, hψ, hy⟩ := Finset.mem_biUnion.mp hy
      --   rcases hrel with hrel | ⟨ψ', h⟩
      --   · exact Set.disjoint_left.mp (f.property ψ).2.1
      --       (α.val.property.rel_dom hrel |>.1)
      --       ((f ψ).property.mem_toFinset.mp hy)
      --   ·






/-- Erasing an `α`-node from `seq_nodes` only affects the `α` part. -/
lemma seq_erase_alpha (u : Finset Node) (φ : Form Node) {x : Node} (hx : x ∈ α.nodes) :
    (α.seq_nodes β f u φ).erase x = α.seq_nodes β f (u.erase x) φ := by
  classical
  have hxB : x ∉ (α.active_branches φ).biUnion fun ψ ↦ (f ψ).nodes_finset := by
    rw [Finset.mem_biUnion]; rintro ⟨ψ, _, hxψ⟩
    exact Set.disjoint_left.mp (f.property ψ).2.1 hx ((Set.Finite.mem_toFinset _).mp hxψ)
  unfold seq_nodes
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hxB]

lemma lin_rec_seq
    (u : Finset Node)
    (φ : Form Node)
    (hu : ↑u ⊆ α.nodes)
    (hsat : φ.sat)
    (hvalid : ∀ x ∈ u, (φ.and (α.form x)).sat)
    (hbr :
      -- The execution is stuck
      (∀ {v}, φ v → ∃ x ∈ u, α.form x v ∧ α.lab x = ⊥) ∨
      -- Or φ is on the way to becoming a branch
      (∃ T ⊆ α.extens,
        φ = α.conj T ∧
        (∀ x ∈ α.val.bots, ((α.conj T).and (α.form x)).sat → x ∈ u) ∧
        ∀ x ∉ T, x ∈ α.extens → Form.sat ((α.conj T).and (α.form x)) → x ∈ u)) :
    (lin_rec (seq α β f) (seq_nodes α β f u φ) φ : s → t s) =
    fun σ ↦ lin_rec α u φ σ >>= lin β := by
  classical
  induction u using Finset.strongInduction generalizing φ with
  | H u ih =>
    ext σ; nth_rw 2 [lin_rec]; by_cases hemp : u = ∅
    · subst hemp; simp only [↓reduceIte, pure_bind]
      have hφ : φ ∈ α.branches := by
        refine (Set.mem_image _ _ _).mpr ?_
        rcases hbr with hstk | ⟨T, hext, rfl, hstk, hmax⟩
        · have ⟨v, hform⟩ := hsat
          have ⟨_, hc, _⟩ := hstk hform
          contradiction
        · refine ⟨T, ⟨?_, hext, hsat, ?_, ?_⟩, rfl⟩
          · have ⟨x, hx, hroot⟩ := α.val.property.rel.single_rooted
            refine ⟨x, ?_⟩; by_contra hT
            refine hmax _ hT ?_ ?_ |> Finset.notMem_empty _
            · refine ⟨hx, ?_⟩
              · conv => arg 1; lhs; exact form_root_true hx hroot
                have ⟨v, hform⟩ := hsat
                intro h; have ⟨⟨y, hy⟩, hyf⟩ := h v True.intro
                exact Finset.notMem_empty _ <| hstk _ hy ⟨v, hform, hyf⟩
            · conv => arg 1; arg 2; exact form_root_true hx hroot
              have ⟨v, hform⟩ := hsat; exact ⟨v, hform, True.intro⟩
          · intro v hform ⟨⟨x, hx⟩, hxf⟩
            refine Finset.notMem_empty _ <| hstk _ hx ⟨_, hform, hxf⟩
          · intro T' hssub he hsat
            have ⟨x, hT', hT⟩ := Set.exists_of_ssubset hssub
            refine hmax x hT (he hT') ?_ |> Finset.notMem_empty _
            have ⟨v, hform⟩ := hsat; refine ⟨v, ?_, ?_⟩
            · intro ⟨y, hy⟩; exact hform y (hssub.subset hy)
            · exact hform _ hT'
      have hactv : α.active_branches φ = {⟨φ, hφ⟩} := by
        ext ⟨ψ, hψ⟩; constructor
        · intro h; refine Finset.mem_singleton.mpr ?_; ext1; simp only
          by_contra hne; have := branches_not_mutually_sat hψ hφ hne
          have ⟨v, h₁, h₂⟩ := (mem_active _ _ _).mp h
          exact this v ⟨h₂, h₁⟩
        · intro h; obtain rfl := Finset.mem_singleton.mp h |> congrArg Subtype.val
          refine (mem_active _ _ _).mpr ?_
          have ⟨v, hform⟩ := hsat
          exact ⟨v, hform, hform⟩
      have hn : seq_nodes α β f ∅ φ = (f ⟨φ, hφ⟩).nodes_finset := by
        unfold seq_nodes; rw [Finset.empty_union, hactv, Finset.singleton_biUnion]
      rw [hn]; exact congrFun (seq_lin_copy _ _ _ _) _
    · simp only [hemp, ↓reduceIte]
      have : (α.seq_nodes β f u φ) ≠ ∅ := by
        intro h; apply hemp; exact Finset.union_eq_empty.mp h |> And.left
      unfold lin_rec; simp only [this, ↓reduceIte]
      rw [Linearizable.bind_additive]
      refine Nondet.finset_congr (seq_next_alpha _ _ _ _ _ hu ?_) ?_
      · sorry
      · ext ⟨x, hx⟩; simp only [Function.comp_apply, lin_node]
        have hlab : (α.seq β f).lab x = α.lab x := sorry
        have hform : (α.seq β f).form x = α.form x := sorry
        rw [hlab, hform]; by_cases himp : φ ≤ α.form x
        · simp only [himp, ↓reduceIte]
          cases hl : α.lab x with
          | bot => symm; exact ContinuousMonad.bind_strict
          | fork =>
            simp only
            have : (α.seq_nodes β f u φ).erase x = α.seq_nodes β f (u.erase x) φ := sorry
            rw [this]
            refine congrFun (ih (u.erase x) ?_ φ ?_ hsat ?_ ?_) _
            · sorry
            · intro y hy; exact hu <| Finset.erase_subset _ _ hy
            · intro y hy; exact hvalid _ <| Finset.erase_subset _ _ hy
            · rcases hbr with hstk | ⟨T, hsub, rfl, hstk, hmax⟩
              · left; intro v hv; have ⟨z, hz, h⟩ := hstk hv
                refine ⟨z, ?_, h⟩; refine Finset.mem_erase.mpr ⟨?_, hz⟩
                rintro rfl; rw [h.2] at hl; contradiction
              · by_cases hst : α.form x ≤ α.stuck
                · left; intro v hv
                  have ⟨⟨z, hz⟩, hb⟩ := hst _ <| himp _ hv
                  refine ⟨z, ?_, hb, hz.2⟩
                  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
                  · rintro rfl; have := hz.2.symm.trans hl; contradiction
                  · exact hstk z hz ⟨v, hv, hb⟩
                · right; refine ⟨insert x T, ?_, ?_, ?_, ?_⟩
                  · refine Set.insert_subset ?_ hsub
                    refine ⟨?_, hst⟩
                    · sorry
                  · ext v; constructor;
                    · intro h ⟨y, hy⟩; rcases Set.mem_insert_iff.mp hy with rfl | hy
                      · exact himp _ h
                      · exact h ⟨_, hy⟩
                    · intro h ⟨y, hy⟩; exact h ⟨y, Set.mem_insert_of_mem _ hy⟩
                  · intro z hz hform; sorry
                  · sorry
          | act a => sorry
          | test b => sorry
        · simp only [himp, ↓reduceIte]; symm; exact ContinuousMonad.bind_strict

lemma lin_seq {t : Type → Type} {s act test : Type}
    [Linearizable t s]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act s (t s)]
    [PartialOrder test] [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β) :
    (lin (seq α β f) : s → t s) = fun σ ↦ lin α σ >>= lin β := by
  unfold lin
  have : (α.seq β f).nodes_finset = α.seq_nodes β f α.nodes_finset Form.true := sorry
  rw [this]
  refine α.lin_rec_seq β f _ _ ?_ ⟨∅, True.intro⟩ ?_ ?_
  · intro x hx; exact α.property.mem_toFinset.mp hx
  · intro x hx; rw [Form.true_and]; apply (α.val.property.form_dom x).mpr
    exact α.property.mem_toFinset.mp hx
  · by_cases hstk : ∀ v, α.stuck v
    · left; intro v _; have ⟨⟨x, hx, hbot⟩, hform⟩ := hstk v
      refine ⟨x, ?_, hform, hbot⟩
      exact α.property.mem_toFinset.mpr hx
    · right; refine ⟨∅, Set.empty_subset _, ?_, ?_, ?_⟩
      · ext v; constructor
        · intro _ ⟨_, h⟩; contradiction
        · intro _; trivial
      · intro x hx _; exact α.property.mem_toFinset.mpr hx.1
      · classical
        intro x _ hext _
        exact α.property.mem_toFinset.mpr hext.1

end Lpofin
