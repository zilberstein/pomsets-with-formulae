import Pom.Lpo.Operations.Seq
import Pom.Linearization

open Linearization

namespace Lpofin

variable {act test : Type}

variable {t : Type → Type} {s : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)]
    [Sem test s (t Bool)]
    (α β : Lpofin (Label act test)) (f : CopyFn α β)

/-- The test literal accumulated at a copy node depends only on the nodes of that copy. -/
lemma copy_literal_dependsOn (φ : α.branches) {y : Node} (hy : y ∈ (f φ).nodes) (rr : Bool) :
    (if rr then Form.literal y else (Form.literal y).not).DependsOn (f φ).nodes := by
  have hsub : ({y} : Set Node) ⊆ (f φ).nodes := by simpa using hy
  cases rr <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y)).not
  · exact Form.DependsOn.monotone _ hsub (Form.DependsOn.literal (x := y))

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
    @Finset.exists_minimal _ ⟨α.rel⟩ ⟨fun _ _ _ hle₁ hle₂ ↦ α.val.property.rel.trans hle₂ hle₁⟩
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
    (hbots : ∀ x ∈ α.val.bots, α.ReachableWith φ x → x ∈ u)
    (hmax : ∀ {x},
        x ∉ φ.tests →
        α.isTest x →
        α.ReachableWith φ x →
        x ∈ u)
    (hemp : α.next u φ.toForm = ∅) :
    ∃ hφ, α.active_branches φ = {⟨φ, hφ⟩} := by
  have hφ : φ ∈ α.branches := by
    refine ⟨hreach, ?_, ?_⟩
    · intro v hform ⟨⟨x, hx, hbot, hr⟩, hxf⟩
      refine Finset.nonempty_iff_ne_empty.mp ?_ hemp
      exact α.next_nonempty_of_reachable u φ hu hcomp (hbots x ⟨hx, hbot⟩ hr) hr
    · intro x hx hxt hnstk hr
      refine Finset.nonempty_iff_ne_empty.mp ?_ hemp
      refine α.next_nonempty_of_reachable u φ hu hcomp ?_ hr
      refine hmax hx hxt hr
  use hφ; ext ⟨ψ, hψ⟩; constructor
  · intro h; refine Finset.mem_singleton.mpr ?_; ext1; simp only
    by_contra hne; have := branches_not_mutually_sat hψ hφ hne
    have himp := (mem_active _ _ _).mp h
    have ⟨v, hsat⟩ := ψ.sat
    exact this v ⟨hsat, PathCond.toForm_antitone himp _ hsat⟩
  · intro h; obtain rfl := Finset.mem_singleton.mp h |> congrArg Subtype.val
    refine (mem_active _ _ _).mpr ?_
    exact le_refl _

/-- If no `α` node is ready, no remaining `α` node can have a formula implied by
the current path condition. -/
lemma no_guarded_alpha_node_of_next_empty
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hemp : α.next u φ.toForm = ∅) {x : Node}
    (hxu : x ∈ u) (hguard : φ.toForm ≤ α.form x) : False := by
  classical
  have ⟨z, hz, hmin⟩ :=
    @Finset.exists_minimal _ ⟨α.rel⟩ ⟨fun _ _ _ hle₁ hle₂ ↦ α.val.property.rel.trans hle₂ hle₁⟩
      { y ∈ u | y = x ∨ α.rel y x }
      ⟨x, Finset.mem_filter.mpr ⟨hxu, Or.inl rfl⟩⟩
  have ⟨hzu, hzx⟩ := Finset.mem_filter.mp hz
  have hzguard : φ.toForm ≤ α.form z := by
    rcases hzx with rfl | hzx
    · exact hguard
    · exact hguard.trans ((α.val.property.form z (hu hzu)).2 x hzx)
  have hznext : z ∈ α.next u φ.toForm := by
    refine Finset.mem_filter.mpr ⟨α.property.mem_toFinset.mpr (hu hzu), hzu, hzguard, ?_⟩
    intro y hyz hyu
    have hyx : y = x ∨ α.rel y x := by
      rcases hzx with rfl | hzx
      · exact Or.inr hyz
      · exact Or.inr (α.val.property.rel.trans hyz hzx)
    have hzy := hmin (Finset.mem_filter.mpr ⟨hyu, hyx⟩) hyz
    obtain rfl := α.val.property.rel.antisymm hyz hzy
    exact α.val.property.rel.irrefl _ hyz
  rw [hemp] at hznext
  exact Finset.notMem_empty z hznext

/-- Once no `α` node is ready and `φ` is the unique active branch, the next
sequence nodes are exactly the next nodes of the selected copy. -/
lemma seq_next_after_alpha
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hφ : φ ∈ α.branches) (hactive : α.active_branches φ = {⟨φ, hφ⟩})
    (hemp : α.next u φ.toForm = ∅) :
    (α.seq β f).next (α.seq_nodes β f u φ) φ.toForm =
      (f ⟨φ, hφ⟩).next (f ⟨φ, hφ⟩).nodes_finset Form.true := by
  classical
  ext x
  simp only [next, Finset.mem_filter]
  constructor
  · rintro ⟨hxnode, hxu, himp, hmin⟩
    have hxcopy : x ∈ (f ⟨φ, hφ⟩).nodes := by
      rcases Finset.mem_union.mp hxu with hxu | hxu
      · exfalso
        have hxα : x ∈ α.nodes := hu hxu
        have hxnext : x ∈ α.next u φ.toForm := by
          refine Finset.mem_filter.mpr ⟨α.property.mem_toFinset.mpr hxα, hxu, ?_, ?_⟩
          · rw [seq_form_alpha α β f hxα] at himp; exact himp
          · intro y hy hyu; exact hmin y (Or.inl hy) (Finset.mem_union_left _ hyu)
        rw [hemp] at hxnext
        exact Finset.notMem_empty x hxnext
      · rw [hactive] at hxu
        simp only [Finset.mem_biUnion, Finset.mem_singleton] at hxu
        rcases hxu with ⟨ψ, hψ, hxψ⟩
        subst ψ
        exact (f ⟨φ, hφ⟩).property.mem_toFinset.mp hxψ
    constructor
    · exact (f ⟨φ, hφ⟩).property.mem_toFinset.mpr hxcopy
    constructor
    · exact (f ⟨φ, hφ⟩).property.mem_toFinset.mpr hxcopy
    constructor
    · have hg := (seq_guard_copy α β f ⟨φ, hφ⟩ hxcopy
        (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true)).mp
      apply hg
      rwa [Form.and_comm, Form.true_and]
    · intro y hy hycopy
      exact hmin y (Or.inr ⟨⟨φ, hφ⟩, Or.inl hy⟩)
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨⟨φ, hφ⟩, (mem_active α φ _).mpr (le_refl _), hycopy⟩))
  · rintro ⟨hxnode, hxcopy, himpcopy, hmin⟩
    have hxcopy' := (f ⟨φ, hφ⟩).property.mem_toFinset.mp hxcopy
    constructor
    · exact (α.seq β f).property.mem_toFinset.mpr
        (Or.inr (Set.mem_iUnion.mpr ⟨⟨φ, hφ⟩, hxcopy'⟩))
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨⟨φ, hφ⟩, (mem_active α φ _).mpr (le_refl _), hxcopy⟩)
    constructor
    · have hg := (seq_guard_copy α β f ⟨φ, hφ⟩ hxcopy'
        (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true)).mpr himpcopy
      rwa [Form.and_comm, Form.true_and] at hg
    · intro y hy hyseq
      rcases hy with hy | ⟨ψ, hy | ⟨hguard, hxψ⟩⟩
      · exact Set.disjoint_left.mp (f.property ⟨φ, hφ⟩).2.1
          (α.val.property.rel_dom hy).2 hxcopy'
      · have hψ : ψ = ⟨φ, hφ⟩ := by
          by_contra hne
          exact Set.disjoint_left.mp ((f.property ψ).2.2 ⟨φ, hφ⟩ hne)
            ((f ψ).val.property.rel_dom hy).2 hxcopy'
        subst ψ
        exact hmin y hy ((f ⟨φ, hφ⟩).property.mem_toFinset.mpr
          ((f ⟨φ, hφ⟩).val.property.rel_dom hy).1)
      · have hψ : ψ = ⟨φ, hφ⟩ := by
          by_contra hne
          exact Set.disjoint_left.mp ((f.property ψ).2.2 ⟨φ, hφ⟩ hne) hxψ hxcopy'
        subst ψ
        rcases Finset.mem_union.mp hyseq with hyu | hyu
        · exact no_guarded_alpha_node_of_next_empty α u φ hu hemp hyu hguard
        · rw [hactive] at hyu
          simp only [Finset.mem_biUnion, Finset.mem_singleton] at hyu
          rcases hyu with ⟨η, hη, hyη⟩
          subst η
          exact Set.disjoint_left.mp (f.property ⟨φ, hφ⟩).2.1
            (branch_implies_node ⟨φ, hφ⟩ hguard)
            ((f ⟨φ, hφ⟩).property.mem_toFinset.mp hyη)

/-- Filtering on a test in the selected copy leaves the inactive `α` nodes unchanged
and filters only that copy. -/
lemma seq_filter_after_alpha
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hφ : φ ∈ α.branches) {w : Finset Node} (hw : ↑w ⊆ (f ⟨φ, hφ⟩).nodes)
    {x : Node} (hx : x ∈ (f ⟨φ, hφ⟩).nodes) (r : Bool) :
    (α.seq β f).filter_by_outcome (u ∪ w) x r =
      u ∪ (f ⟨φ, hφ⟩).filter_by_outcome w x r := by
  classical
  unfold filter_by_outcome
  ext z
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_union]
  constructor
  · rintro ⟨⟨hzx, hzu | hzcopy⟩, hsat⟩
    · left; exact hzu
    · right
      refine ⟨⟨hzx, hzcopy⟩, ?_⟩
      rw [seq_form_copy α β f ⟨φ, hφ⟩
        (hw hzcopy), Form.and_comm_assoc] at hsat
      have hp : (((f ⟨φ, hφ⟩).form z).and
          (bif r then Form.literal x else (Form.literal x).not)).DependsOn
          (f ⟨φ, hφ⟩).nodes := by
        have := Form.DependsOn.and
          (copy_form_dependsOn α β f ⟨φ, hφ⟩
            (hw hzcopy))
          (copy_literal_dependsOn α β f ⟨φ, hφ⟩ hx r)
        simpa only [Bool.cond_eq_ite, Set.union_self] using this
      exact (Form.sat_and_indep hp
        (φ.dependsOn.monotone _ (φ.tests_valid.trans tests_sub_nodes))
        (f.property ⟨φ, hφ⟩).2.1.symm φ.sat).mp hsat
  · rintro (hzu | ⟨⟨hzx, hzcopy⟩, hsat⟩)
    · have hzα := hu hzu
      have hzne : z ≠ x := fun h ↦ Set.disjoint_left.mp
        (f.property ⟨φ, hφ⟩).2.1 hzα (h ▸ hx)
      refine ⟨⟨hzne, Or.inl hzu⟩, ?_⟩
      rw [seq_form_alpha α β f hzα]
      have hp : (α.form z).DependsOn α.nodes := by
        refine (α.val.property.form z hzα).1.monotone _ ?_
        intro y hy; exact (α.val.property.rel_dom hy).1
      have hq : (bif r then Form.literal x else (Form.literal x).not).DependsOn
          (f ⟨φ, hφ⟩).nodes := by
        cases r <;> simp only [cond_false, cond_true]
        · exact Form.DependsOn.monotone _ (by simpa using hx)
            (Form.DependsOn.literal (x := x)).not
        · exact Form.DependsOn.monotone _ (by simpa using hx)
            (Form.DependsOn.literal (x := x))
      have hqsat : (bif r then Form.literal x else (Form.literal x).not).sat := by
        cases r
        · refine ⟨∅, ?_⟩
          change x ∉ (∅ : Set Node)
          exact Set.notMem_empty x
        · exact ⟨{x}, by simp [Form.literal]⟩
      exact (Form.sat_and_indep hp hq (f.property ⟨φ, hφ⟩).2.1 hqsat).2
        ((α.val.property.form_dom z).mpr hzα)
    · refine ⟨⟨hzx, Or.inr hzcopy⟩, ?_⟩
      rw [seq_form_copy α β f ⟨φ, hφ⟩
        (hw hzcopy), Form.and_comm_assoc]
      have hp : (((f ⟨φ, hφ⟩).form z).and
          (bif r then Form.literal x else (Form.literal x).not)).DependsOn
          (f ⟨φ, hφ⟩).nodes := by
        have := Form.DependsOn.and
          (copy_form_dependsOn α β f ⟨φ, hφ⟩
            (hw hzcopy))
          (copy_literal_dependsOn α β f ⟨φ, hφ⟩ hx r)
        simpa only [Bool.cond_eq_ite, Set.union_self] using this
      exact (Form.sat_and_indep hp
        (φ.dependsOn.monotone _ (φ.tests_valid.trans tests_sub_nodes))
        (f.property ⟨φ, hφ⟩).2.1.symm φ.sat).mpr hsat

/-- A satisfiable copy-local accumulator does not strengthen a guard on an `α` node. -/
lemma seq_guard_alpha_indep
    (φ : PathCond α) (hφ : φ ∈ α.branches) {x : Node} (hx : x ∈ α.nodes) (ψ : Form Node)
    (hψ : ψ.DependsOn (f ⟨φ, hφ⟩).nodes) (hψsat : ψ.sat) :
    (φ.toForm.and ψ ≤ α.form x) ↔ (φ.toForm ≤ α.form x) := by
  constructor
  · intro himp v hφv
    obtain ⟨w, hψw⟩ := hψsat
    set v' := (v \ (f ⟨φ, hφ⟩).nodes) ∪ (w ∩ (f ⟨φ, hφ⟩).nodes)
    have hdα : Disjoint (symmDiff v v') α.nodes := by
      rw [Set.disjoint_left]
      intro y hy hyα
      have hyn : y ∉ (f ⟨φ, hφ⟩).nodes :=
        Set.disjoint_left.mp (f.property ⟨φ, hφ⟩).2.1 hyα
      rcases Set.mem_symmDiff.mp hy with ⟨hyv, hyv'⟩ | ⟨hyv', hyv⟩
      · exact hyv' (Or.inl ⟨hyv, hyn⟩)
      · rcases hyv' with ⟨hyv'', _⟩ | ⟨_, hycopy⟩
        · exact hyv hyv''
        · exact hyn hycopy
    have hdcopy : Disjoint (symmDiff w v') (f ⟨φ, hφ⟩).nodes := by
      rw [Set.disjoint_left]
      intro y hy hycopy
      rcases Set.mem_symmDiff.mp hy with ⟨hyw, hyv'⟩ | ⟨hyv', hyw⟩
      · exact hyv' (Or.inr ⟨hyw, hycopy⟩)
      · rcases hyv' with ⟨_, hyn⟩ | ⟨hyw', _⟩
        · exact hyn hycopy
        · exact hyw hyw'
    have hφv' := (φ.dependsOn.monotone _
      (φ.tests_valid.trans tests_sub_nodes) v v' hdα) ▸ hφv
    have hψv' := (hψ w v' hdcopy) ▸ hψw
    have hform := himp v' ⟨hφv', hψv'⟩
    have hdrel : Disjoint (symmDiff v v') {y | α.rel y x} := by
      exact hdα.mono_right fun y hy ↦ (α.val.property.rel_dom hy).1
    exact ((α.val.property.form x hx).1 v v' hdrel).mpr hform
  · intro himp v hv; exact himp v hv.1

/-- General terminal-phase recursion: inactive `α` nodes do not affect execution of an
arbitrary remaining subset of the selected copy. -/
lemma seq_lin_rec_after_alpha_gen
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hφ : φ ∈ α.branches)
    (hemp : α.next u φ.toForm = ∅)
    (w : Finset Node) (hw : ↑w ⊆ (f ⟨φ, hφ⟩).nodes)
    (ψ : Form Node)
    (hψ : ψ.DependsOn ((f ⟨φ, hφ⟩).nodes \ w))
    (hψsat : ψ.sat) :
    ((α.seq β f).lin_rec (u ∪ w) (φ.toForm.and ψ) : s → t s) =
      (f ⟨φ, hφ⟩).lin_rec w ψ := by
  classical
  induction w using Finset.strongInduction generalizing ψ with
  | H w ih =>
    ext σ; unfold lin_rec
    have hnext : (α.seq β f).next (u ∪ w) (φ.toForm.and ψ) =
        (f ⟨φ, hφ⟩).next w ψ := by
      ext x; constructor
      · intro hx; have ⟨hx, huw, himp, hmin⟩ := Finset.mem_filter.mp hx
        rcases Finset.mem_union.mp huw with hxu | hxw
        · exfalso; apply α.no_guarded_alpha_node_of_next_empty u φ hu hemp hxu
          refine (seq_guard_alpha_indep α β f φ hφ (hu hxu) ψ ?_ hψsat).mp ?_
          · refine hψ.monotone _ ?_; intro _ ⟨hy, _⟩; exact hy
          · rwa [← seq_form_alpha α β f (hu hxu)]
        · refine Finset.mem_filter.mpr ⟨?_, hxw, ?_, ?_⟩
          · exact (f ⟨φ, hφ⟩).property.mem_toFinset.mpr <| hw hxw
          · refine (seq_guard_copy α β f ⟨φ, hφ⟩ (hw hxw) ?_).mp himp
            refine hψ.monotone _ ?_; intro _ ⟨hy, _⟩; exact hy
          · intro y hy hyw
            exact hmin y (Or.inr ⟨⟨φ, hφ⟩, Or.inl hy⟩) (Finset.mem_union_right _ hyw)
      · intro hx; have ⟨hx, hxw, himp, hmin⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
        · apply (α.seq β f).property.mem_toFinset.mpr
          right; exact Set.mem_iUnion.mpr ⟨⟨φ, hφ⟩, hw hxw⟩
        · exact Finset.mem_union_right _ hxw
        · refine (seq_guard_copy α β f ⟨φ, hφ⟩ (hw hxw) ?_).mpr himp
          refine hψ.monotone _ ?_; intro _ ⟨hy, _⟩; exact hy
        · intro y hrel huw; rcases Finset.mem_union.mp huw with hyu | hyw
          · apply α.no_guarded_alpha_node_of_next_empty u φ hu hemp hyu
            refine (α.seq_guard_alpha_indep β f φ hφ (hu hyu) ψ ?_ hψsat).mp ?_
            · refine hψ.monotone _ ?_; intro _ ⟨hy, _⟩; exact hy
            · have ⟨hy', _⟩ := (α.seq β f).val.property.rel_dom hrel
              intro v ⟨hφv, hψv⟩
              have himp' := ((α.seq β f).val.property.form _ hy').2 _ hrel
              conv at himp' => lhs; exact α.seq_form_copy β f ⟨φ, hφ⟩ (hw hxw)
              rw [← α.seq_form_alpha β f (hu hyu)]
              exact himp' _ ⟨himp _ hψv, hφv⟩
          · refine hmin _ ?_ hyw
            exact seq_rel_copy (hw hyw) (hw hxw) hrel
    refine if_congr (Iff.of_eq (congrArg (· = ∅) hnext)) rfl ?_
    refine Nondet.finset_congr hnext ?_
    ext ⟨x, hx⟩
    rw [hnext] at hx
    have hxw := (Finset.mem_filter.mp hx).2.1
    have hxcopy := hw hxw
    simp only [lin_node, Function.comp_apply]
    rw [seq_lab_copy α β f ⟨φ, hφ⟩ hxcopy]
    match hl : (f ⟨φ, hφ⟩).lab x with
    | Label.bot => rfl
    | Label.fork =>
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem
        (fun hxu ↦ Set.disjoint_left.mp (f.property ⟨φ, hφ⟩).2.1 (hu hxu) hxcopy)]
      refine congrFun (ih (w.erase x) (Finset.erase_ssubset hxw) ?_ ψ ?_ hψsat) σ
      · intro z hz; exact hw (Finset.mem_of_mem_erase hz)
      · refine hψ.monotone _ ?_
        exact Set.sdiff_subset_sdiff (le_refl _) (Finset.erase_subset _ _)
    | Label.act a =>
      refine congrArg₂ Bind.bind rfl ?_
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem
        (fun hxu ↦ Set.disjoint_left.mp (f.property ⟨φ, hφ⟩).2.1 (hu hxu) hxcopy)]
      refine ih (w.erase x) (Finset.erase_ssubset hxw) ?_ ψ ?_ hψsat
      · intro z hz; exact hw (Finset.mem_of_mem_erase hz)
      · refine hψ.monotone _ ?_
        exact Set.sdiff_subset_sdiff (le_refl _) (Finset.erase_subset _ _)
    | Label.test b =>
      refine congrArg₂ Bind.bind rfl ?_; funext r
      rw [seq_filter_after_alpha α β f u φ hu hφ hw hxcopy r, Form.and_assoc]
      refine congrFun (ih ((f ⟨φ, hφ⟩).filter_by_outcome w x r) ?_ ?_ _ ?_ ?_) σ
      · exact Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
          (Finset.erase_ssubset hxw)
      · intro z hz; apply hw
        exact (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase)
      · conv => arg 2; exact (Set.union_self _).symm
        refine Form.DependsOn.and ?_ ?_
        · refine hψ.monotone _ ?_
          apply Set.sdiff_subset_sdiff (le_refl _)
          exact filter_by_outcome_sub_erase.trans (Finset.erase_subset _ _)
        · refine Form.DependsOn.monotone _ (?_ : ({x} : Set Node) ⊆ _) ?_
          · rintro x rfl; refine ⟨hxcopy, ?_⟩; intro h
            apply (Finset.mem_erase.mp (filter_by_outcome_sub_erase h)).1; rfl
          · cases r <;> simp only [Bool.false_eq_true, ↓reduceIte]
            · exact Form.DependsOn.literal.not
            · exact Form.DependsOn.literal
      · refine (Form.sat_and_indep hψ ?_ ?_ ?_ (u := {x})).mpr hψsat
        · cases r <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · exact Form.DependsOn.literal.not
          · exact Form.DependsOn.literal
        · apply Set.disjoint_right.mpr; rintro x rfl ⟨_, h⟩
          exact h hxw
        · cases r <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · exact ⟨∅, Set.notMem_empty _⟩
          · exact ⟨{x}, Set.mem_singleton _⟩

/-- Once no `α` node is ready, the remaining inactive `α` nodes can be ignored and
linearization continues with the unique active copy. -/
lemma seq_lin_rec_after_alpha
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hcomp : ∀ z ∈ α.tests, ∀ y ∈ u, α.rel z y → z ∉ u → z ∈ φ.tests)
    (hreach : ∀ z ∈ φ.tests, φ.toForm ≤ α.form z)
    (hbots : ∀ x ∈ α.val.bots, α.ReachableWith φ x → x ∈ u)
    (hmax : ∀ {x}, x ∉ φ.tests → α.isTest x → α.ReachableWith φ x → x ∈ u)
    (hemp : α.next u φ.toForm = ∅) :
    ((α.seq β f).lin_rec (α.seq_nodes β f u φ) φ.toForm : s → t s) = lin β := by
  obtain ⟨hφ, hactive⟩ := α.active_branches_singleton u φ hu hcomp hreach hbots hmax hemp
  rw [← lin_isomorphic (f.property ⟨φ, hφ⟩).1]
  have hnodes : α.seq_nodes β f u φ = u ∪ (f ⟨φ, hφ⟩).nodes_finset := by
    unfold seq_nodes; rw [hactive]; ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_singleton]
    constructor
    · rintro (hx | ⟨ψ, rfl, hx⟩) <;> simp_all only [true_or, or_true]
    · rintro (hx | hx)
      · exact Or.inl hx
      · exact Or.inr ⟨⟨φ, hφ⟩, rfl, hx⟩
  rw [hnodes]
  have h := α.seq_lin_rec_after_alpha_gen (t := t) (s := s) β f u φ hu hφ hemp
    (f ⟨φ, hφ⟩).nodes_finset
    (fun _ hx ↦ (f ⟨φ, hφ⟩).property.mem_toFinset.mp hx) Form.true
    (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true) ⟨∅, trivial⟩
  rwa [Form.and_comm, Form.true_and] at h

/-- An active branch compatible with the outcome of a ready test extends the path
condition updated by that outcome. -/
lemma extend_le_branch_of_outcome_sat
    (φ : PathCond α) {u : Finset Node} {x : Node} (hx : x ∈ α.next u φ.toForm)
    (hxt : α.isTest x) (hx_nt : x ∉ φ.tests)
    (r : Bool) (ψ : α.branches) (hφψ : φ ≤ ψ.val)
    (hsat : (ψ.val.toForm.and
      (bif r then Form.literal x else (Form.literal x).not)).sat) :
    φ.extend hxt r ≤ ψ.val := by
  classical
  have hximp : φ.toForm ≤ α.form x := (Finset.mem_filter.mp hx).2.2.1
  have hxψ : x ∈ ψ.val.tests := by
    by_contra hxnot
    have hr : α.ReachableWith ψ.val x := by
      refine ⟨ψ.val, le_refl _, ?_⟩; exact (PathCond.toForm_antitone hφψ).trans hximp
    apply ψ.property.2.2 hxnot hxt
    · intro hstuck; obtain ⟨v, hψv, hlit⟩ := hsat
      exact ψ.property.2.1 v hψv (hstuck v ((PathCond.toForm_antitone hφψ).trans hximp v hψv))
    · exact hr
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases hz with rfl | hz
    · exact hxψ
    · exact hφψ.1 hz
  · intro z; rcases z with ⟨z, rfl | hz⟩
    · obtain ⟨v, hψv, hlit⟩ := hsat
      simp only [PathCond.extend, dif_pos]
      apply Bool.eq_iff_iff.mpr; rw [ψ.val.truth_iff_mem hψv]
      cases r
      · simp only [Bool.false_eq_true]
        constructor
        · exact False.elim
        · intro hzv
          have : z ∉ v := by
            simpa only [cond_false, Form.not, Form.literal, Set.mem_compl_iff,
              Set.mem_singleton_iff] using hlit
          exact this hzv
      · constructor
        · intro _; simpa only [cond_true, Form.literal, Set.mem_singleton_iff] using hlit
        · intro _; trivial
    · have hne : z ≠ x := fun h ↦ hx_nt (h ▸ hz)
      simp only [PathCond.extend, dif_neg hne]; exact hφψ.2 ⟨z, hz⟩

/-- Filtering after observing a ready test distributes over the `α` part and the copies,
with the active branches updated by extending the path condition. -/
lemma seq_filter_by_outcome_nodes
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    {x : Node} (hx : x ∈ α.next u φ.toForm) (hxt : α.isTest x)
    (hx_nt : x ∉ φ.tests) (r : Bool) :
    (α.seq β f).filter_by_outcome (α.seq_nodes β f u φ) x r =
      α.seq_nodes β f (α.filter_by_outcome u x r) (φ.extend hxt r) := by
  classical
  ext z
  simp only [filter_by_outcome, seq_nodes, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_union, Finset.mem_biUnion, mem_active]
  constructor
  · rintro ⟨⟨hzx, hzu | ⟨ψ, hφψ, hzψ⟩⟩, hsat⟩
    · left;refine ⟨⟨hzx, hzu⟩, ?_⟩
      rw [seq_form_alpha α β f (hu hzu)] at hsat; exact hsat
    · right; refine ⟨ψ, ?_, ?_⟩
      · apply extend_le_branch_of_outcome_sat α φ hx hxt hx_nt r ψ hφψ
        obtain ⟨v, hseq, hlit⟩ := hsat
        rw [seq_form_copy α β f ψ ((f ψ).property.mem_toFinset.mp hzψ)] at hseq
        exact ⟨v, hseq.2, hlit⟩
      · exact hzψ
  · rintro (⟨⟨hzx, hzu⟩, hsat⟩ | ⟨ψ, hφeψ, hzψ⟩)
    · refine ⟨⟨hzx, Or.inl hzu⟩, ?_⟩
      rw [seq_form_alpha α β f (hu hzu)]; exact hsat
    · have hznode : z ∈ (f ψ).nodes := (f ψ).property.mem_toFinset.mp hzψ
      have hzne : z ≠ x := by
        rintro rfl
        exact Set.disjoint_left.mp (f.property ψ).2.1 (hu (Finset.mem_filter.mp hx).2.1) hznode
      refine ⟨⟨hzne, Or.inr ⟨ψ, ?_, hzψ⟩⟩, ?_⟩
      · exact (φ.extend_le hx_nt hxt r).trans hφeψ
      · rw [seq_form_copy α β f ψ hznode]
        have hcopydep : ((f ψ).form z).DependsOn (f ψ).nodes :=
          copy_form_dependsOn α β f ψ hznode
        have hψdep : ψ.val.toForm.DependsOn α.nodes := by
          refine ψ.val.dependsOn.monotone _ ?_
          exact ψ.val.tests_valid.trans tests_sub_nodes
        have hboth : Form.sat (((f ψ).form z).and ψ.val.toForm) :=
          (Form.sat_and_indep hcopydep hψdep (f.property ψ).2.1.symm ψ.val.sat).2
            (((f ψ).val.property.form_dom z).mpr hznode)
        obtain ⟨v, hcopy, hψ⟩ := hboth
        have hφe := PathCond.toForm_antitone hφeψ v hψ
        rw [PathCond.extend_toForm φ hxt r hx_nt] at hφe
        refine ⟨v, ⟨⟨hcopy, hψ⟩, ?_⟩⟩
        simpa only [Bool.cond_eq_ite] using hφe.2

/-- The full node set of a sequence is its `seq_nodes` set at the empty path condition. -/
lemma seq_nodes_finset_eq (α β : Lpofin (Label act test)) (f : CopyFn α β) :
    (α.seq β f).nodes_finset = α.seq_nodes β f α.nodes_finset ⊥ := by
  classical ext x
  simp only [Lpofin.nodes_finset, Lpo.nodes, seq, seq_base, Set.Finite.mem_toFinset,
    seq_nodes, Finset.mem_union, mem_active, bot_le, Finset.mem_biUnion, true_and]
  constructor
  · rintro (hx | ⟨_, ⟨⟨ψ, rfl⟩, hxψ⟩⟩)
    · exact Or.inl hx
    · right; exact ⟨ψ, hxψ⟩
  · rintro (hx | ⟨ψ, hxψ⟩)
    · exact Or.inl hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨ψ, hxψ⟩)

lemma lin_node_seq
    (u : Finset Node) (φ : PathCond α) (hu : ↑u ⊆ α.nodes)
    (hdisj : Disjoint (↑u : Set Node) φ.tests)
    {x : Node} {σ : s} (hx : x ∈ u)
    (ih_plain :
      ¬ α.isTest x → ¬ α.lab x = ⊥ →
      (α.seq β f).lin_rec ((α.seq_nodes β f u φ).erase x) φ.toForm =
      fun τ ↦ α.lin_rec (u.erase x) φ.toForm τ >>= (β.lin : s → t s))
    (ih_test : ∀ (ht : α.isTest x) {r : Bool},
      (α.seq β f).lin_rec ((α.seq β f).filter_by_outcome (α.seq_nodes β f u φ) x r)
        (φ.extend ht r).toForm =
      fun τ ↦ α.lin_rec (α.filter_by_outcome u x r) (φ.extend ht r).toForm τ >>=
        (β.lin : s → t s)) :
    (α.seq β f).lin_node (α.seq_nodes β f u φ) φ.toForm x (Finset.mem_union_left _ hx) σ =
    α.lin_node u φ.toForm x hx σ >>= (β.lin : s → t s) := by
  unfold lin_node
  rw [seq_lab_alpha α β f (hu hx)]
  cases hl : α.lab x with
  | bot => symm; exact ContinuousMonad.bind_strict
  | fork =>
    refine congrFun (ih_plain ?_ ?_) σ
    · intro ht; have ⟨b, hlab⟩ := (Label.isTest_iff _).mp ht
      rw [hlab] at hl; contradiction
    · intro hlab; rw [hlab] at hl; contradiction
  | act a =>
    simp only; rw [bind_assoc]; refine congrArg₂ Bind.bind rfl ?_
    refine ih_plain ?_ ?_
    · intro ht; have ⟨b, hlab⟩ := (Label.isTest_iff _).mp ht
      rw [hlab] at hl; contradiction
    · intro hlab; rw [hlab] at hl; contradiction
  | test b =>
    classical
    simp only; rw [bind_assoc]; refine congrArg₂ Bind.bind rfl ?_
    ext r; have hxt := (Label.isTest_iff _).mpr ⟨_, hl⟩
    have hx_nt : x ∉ φ.tests := Set.disjoint_left.mp hdisj hx
    rw [← PathCond.extend_toForm _ hxt _ hx_nt]
    exact congrFun (ih_test _) _

lemma lin_rec_seq
    (u : Finset Node)
    (φ : PathCond α)
    (hu : ↑u ⊆ α.nodes)
    -- Completeness: all tests below `u` must be accounted for in the
    -- path condition `φ`
    (hcomp : ∀ z ∈ α.tests, ∀ y ∈ u, α.rel z y → z ∉ u → z ∈ φ.tests)
    -- Reachability: all tests in the path condition are reachable via
    -- the path condition
    (hreach : ∀ z ∈ φ.tests, φ.toForm ≤ α.form z)
    -- The path condition is disjoint from `u`
    (hdisj : Disjoint (↑u : Set Node) φ.tests)
    -- All reachable `⊥` nodes have not yet been processed
    (hbots : ∀ x ∈ α.val.bots, α.ReachableWith φ x → x ∈ u)
    -- Maximality: all reachable tests that are compatible with the
    -- path condition are still in `u`
    (hmax : ∀ {x}, x ∉ φ.tests → α.isTest x → α.ReachableWith φ x → x ∈ u) :
    (lin_rec (seq α β f) (seq_nodes α β f u φ) φ.toForm : s → t s) =
    fun σ ↦ lin_rec α u φ.toForm σ >>= lin β := by
  classical
  induction u using Finset.strongInduction generalizing φ with
  | H u ih =>
    ext σ; nth_rw 2 [lin_rec]; by_cases hemp : α.next u φ.toForm = ∅
    · simp only [↓reduceIte, hemp, pure_bind]
      exact congrFun (α.seq_lin_rec_after_alpha β f u φ hu hcomp hreach hbots hmax hemp) σ
    · unfold lin_rec
      have hnext := seq_next_alpha α β f u φ hu (Finset.nonempty_of_ne_empty hemp)
      conv => lhs; arg 1; lhs; exact hnext
      simp only [hemp, ↓reduceIte]; rw [Linearizable.bind_additive]
      refine Nondet.finset_congr hnext ?_
      ext ⟨x, hx⟩; simp only [Function.comp_apply]
      rw [hnext] at hx; have hxu := (Finset.mem_filter.mp hx).2.1
      apply α.lin_node_seq β f u φ hu hdisj hxu
      · intro hnt hnbot; rw [seq_erase_alpha _ _ _ _ _ (hu hxu)]
        refine ih _ ?_ _ ?_ ?_ hreach ?_ ?_ ?_
        · exact Finset.erase_ssubset hxu
        · intro y hy; exact hu <| Finset.erase_subset _ _ hy
        · intro z hz y hy hzy hz'
          refine hcomp z hz y ?_ hzy ?_
          · exact Finset.erase_subset _ _ hy
          · intro hzu; refine Finset.mem_erase.mpr ⟨?_, hzu⟩ |> hz'
            rintro rfl; exact hnt hz
        · refine Disjoint.mono ?_ (le_refl φ.tests) hdisj
          exact Finset.erase_subset x u
        · intro z hz hr; refine Finset.mem_erase.mpr ⟨?_, hbots z hz hr⟩
          rintro rfl; apply hnbot; exact hz.2
        · intro z hz hzt hr; refine Finset.mem_erase.mpr ⟨?_, hmax hz hzt hr⟩
          rintro rfl; exact hnt hzt
      · intro hxt r; have hx_nt := Set.disjoint_left.mp hdisj hxu
        rw [α.seq_filter_by_outcome_nodes β f u φ hu hx hxt hx_nt r]
        refine ih _ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
        · exact ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase <| Finset.erase_ssubset hxu
        · intro y hy; exact hu <| Finset.erase_subset _ _ <| filter_by_outcome_sub_erase hy
        · intro z hz y hy hzy hz'; by_cases heq : z = x
          · subst heq; exact Set.mem_insert _ _
          · refine Set.mem_insert_of_mem _ ?_
            have ⟨hy, ⟨v, hyf, hv⟩⟩ := Finset.mem_filter.mp hy
            have ⟨hne, hy⟩ := Finset.mem_erase.mp hy
            refine hcomp _ hz _ hy hzy ?_; intro hzu
            apply (Finset.mem_filter.mpr.mt hz' |> not_and.mp) <| Finset.mem_erase.mpr ⟨heq, hzu⟩
            refine ⟨v, ?_, hv⟩; exact (α.val.property.form _ (hu hzu)).2 _ hzy _ hyf
        · rintro z hz; refine (PathCond.toForm_antitone <| φ.extend_le hx_nt _ _).trans ?_
          rcases hz with rfl | hz
          · exact (Finset.mem_filter.mp hx).2.2.1
          · exact hreach _ hz
        · apply Set.disjoint_left.mpr
          intro y hy hytests
          have hyf := (Finset.mem_filter.mp hy).1
          have ⟨hyne, hyu⟩ := Finset.mem_erase.mp hyf
          rcases hytests with rfl | hytests
          · exact hyne rfl
          · exact Set.disjoint_left.mp hdisj hyu hytests
        · intro z hz ⟨ψ, hext, himp⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
          · rintro rfl; have ⟨b, hlab⟩ := (Label.isTest_iff _).mp hxt
            have := hz.2.symm.trans hlab; contradiction
          · refine hbots z hz ⟨ψ, ?_, himp⟩
            exact (φ.extend_le hx_nt _ _).trans hext
          · have ⟨v, hψ⟩ := ψ.sat
            refine ⟨v, himp _ hψ, ?_⟩
            have hform := PathCond.toForm_antitone hext _ hψ ⟨x, Set.mem_insert _ _⟩
            conv at hform => simp only; arg 1; lhs; exact dif_pos rfl
            rwa [Bool.cond_eq_ite]
        · intro z hz hzt hr
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
          · rintro rfl; apply hz; exact Set.mem_insert _ _
          · refine hmax ?_ hzt ?_
            · intro h; apply hz
              exact Set.mem_insert_of_mem _ h
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
  rw [seq_nodes_finset_eq α β f]; nth_rw 1 2 [← PathCond.empty_toForm]
  apply α.lin_rec_seq β f _ ⊥
  · intro x hx; exact α.property.mem_toFinset.mp hx
  · intro z hz _ _ _ hz'; exfalso; apply hz'
    exact α.property.mem_toFinset.mpr <| tests_sub_nodes hz
  · intro z hz; exfalso; exact Set.notMem_empty _ hz
  · exact Set.disjoint_empty _
  · intro z ⟨hz, _⟩ _; exact α.property.mem_toFinset.mpr hz
  · intro z _ hz _; exact α.property.mem_toFinset.mpr <| tests_sub_nodes hz

end Lpofin
