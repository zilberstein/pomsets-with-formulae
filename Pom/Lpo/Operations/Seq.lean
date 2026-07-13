import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Order

namespace Lpofin
open Classical

variable {l : Type} [PartialOrder l] [OrderBot l]

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin l) : Form Node := Form.sOr fun x : ↑α.val.bots ↦ α.form x.val

lemma stuck_antitone : @Antitone (Lpofin l) _ _ _ stuck := by
  intro α β hle v ⟨⟨x, hx, hlab⟩, hform⟩
  rcases hle.succ _ hx with hx' | ⟨y, ⟨hy, hlab'⟩, hyx⟩
  · refine ⟨⟨x, hx', ?_⟩, ?_⟩
    · refine le_antisymm ?_ bot_le
      rw [← hlab]; exact hle.lab x
    · refine (congrFun (hle.form x hx') v).mpr ?_
      exact hform
  · refine ⟨⟨y, hy, hlab'⟩, ?_⟩
    refine (congrFun (hle.form _ hy) _).mpr ?_
    refine (β.val.property.form _ (hle.nodes hy)).2 _ hyx _ ?_
    exact hform

-- A node is in the exntensible set if it is possible for it not be stuck
noncomputable def extens (α : Lpofin l) : Finset Node :=
  α.nodes_finset.filter fun x ↦ ¬ α.form x ≤ α.stuck

lemma extens_not_bot {α : Lpofin l} {x : Node} : x ∈ α.extens → α.lab x ≠ ⊥ := by
  intro h; simp [extens] at h; intro heq; apply h.2; intro v hform
  refine ⟨⟨x, ?_, heq⟩, hform⟩
  exact (α.val.property.form_dom x).mp ⟨v, hform⟩

lemma extens_subset_nodes {α : Lpofin l} : ∀ x ∈ α.extens, x ∈ α.nodes := by
  intro x hx; exact (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hx).1

lemma extens_monotone : @Monotone (Lpofin l) _ _ _ extens := by
  intro α β hle x; simp [extens]; intro hx hstuck
  have hx' := (Set.Finite.mem_toFinset _).mp hx
  refine ⟨(Set.Finite.mem_toFinset _).mpr (hle.nodes hx'), fun hc ↦ ?_⟩
  refine hstuck (fun v hform ↦ stuck_antitone hle v (hc v ?_))
  simp [Lpofin.form]; rw [← hle.form x hx']; exact hform

lemma le_extens {α β : Lpofin l} (hle : α ≤ β) :
    α.extens = β.extens.filter fun x ↦ ¬ (β.form x ≤ α.stuck) := by
  ext x; constructor
  · intro hx; refine Finset.mem_filter.mpr ⟨extens_monotone hle hx, ?_⟩
    intro c; refine (Finset.mem_filter.mp hx).2 (le_trans ?_ c)
    exact le_form hle
  · intro hx; obtain ⟨hx, hstk⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx', _⟩ := Finset.mem_filter.mp hx
    apply (Set.Finite.mem_toFinset _).mp at hx'
    rcases hle.succ _  hx' with hxα | ⟨y, ⟨hy, hbot⟩, hyx⟩
    · refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hxα, ?_⟩
      intro c; refine hstk (le_of_eq_of_le (Eq.symm ?_) c)
      exact hle.form _ hxα
    · exfalso; refine hstk (((β.val.property.form y (hle.nodes hy)).2 _ hyx).trans ?_)
      refine le_of_eq_of_le (Eq.symm (hle.form _ hy)) ?_
      intro v hform; exact ⟨⟨y, hy, hbot⟩, hform⟩

def conj (α : Lpofin l) (S : Finset Node) : Form Node :=
  Form.sAnd fun x : ↑S ↦ α.form x.val

def branches_set (α : Lpofin l) : Set (Form Node) :=
  α.conj ''
  { S : Finset Node
  | S.Nonempty ∧
    S ⊆ α.extens ∧
    (α.conj S).sat ∧
    α.conj S ≤ α.stuck.not ∧
    ∀ T, S ⊂ T → T ⊆ α.extens → ¬ Form.sat (fun v ↦ ∀ x ∈ T, α.form x v)
  }

lemma branches_finite (α : Lpofin l) : α.branches_set.Finite := by
  refine Set.Finite.image _ ?_
  refine Set.Finite.subset α.extens.powerset.finite_toSet ?_
  intro s ⟨_, hsub, _⟩; simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, hsub]

noncomputable def branches (α : Lpofin l) : Finset (Form Node) := α.branches_finite.toFinset

lemma branches_set_monotone : @Monotone (Lpofin l) _ _ _ branches_set := by
  rintro α β hle φ ⟨S, ⟨hne, hsub, hsat, hstuck, hmax⟩, hφ⟩; subst hφ
  refine ⟨S, ⟨hne, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hsub (extens_monotone hle)
  · rcases hsat with ⟨v, hv⟩; use v; intro x
    refine (congrFun (hle.form x ?_) _).mp (hv x)
    have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
    exact (Set.Finite.mem_toFinset _).mp hx'
  · intro v hform hstuck'; refine hstuck v ?_ ?_
    · intro x; refine (congr_fun (hle.form x ?_) v).mpr (hform x)
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'
    · exact stuck_antitone hle v hstuck'
  · intro T hST hT ⟨v, hc⟩; obtain ⟨x, hxT, hxS⟩ := Finset.exists_of_ssubset hST
    have hform : α.conj S v := by
      intro y; refine (congrFun (hle.form _ ?_) _).mpr (hc _ ?_)
      · exact extens_subset_nodes _ (hsub y.property)
      · exact (Finset.ssubset_def.mp hST).1 y.property
    rcases hle.succ _ (extens_subset_nodes _ (hT hxT))
      with hx | ⟨y, hy, hyx⟩
    · refine hmax (insert x S) (Finset.ssubset_insert hxS) ?_ ?_
      · refine Finset.insert_subset (Finset.mem_filter.mpr ⟨?_, ?_⟩) hsub
        · exact (Set.Finite.mem_toFinset _).mpr hx
        · intro c; refine hstuck v hform ?_
          exact c v ((congrFun (hle.form _ hx) _).mpr (hc _ hxT))
      · use v; intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact (congrFun (hle.form y hx) _).mpr (hc y hxT)
        · refine (congrFun (hle.form y ?_) _).mpr (hc y ?_)
          · exact extens_subset_nodes _ (hsub hy')
          · exact Finset.mem_of_subset (Finset.ssubset_def.mp hST).1 hy'
    · refine hstuck v hform ⟨⟨y, hy⟩, ?_⟩
      refine (congrFun (hle.form _ hy.1) _).mpr ?_
      exact (β.val.property.form _ (hle.nodes hy.1)).2 _ hyx v (hc _ hxT)
  · ext1 v; refine forall_congr fun x ↦ ?_; ext; constructor
    · intro h; refine (congr_fun (hle.form x ?_) v).mpr h
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'
    · intro h; refine (congr_fun (hle.form x ?_) v).mp h
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'

lemma le_branches_set {α β : Lpofin l} (hle : α ≤ β) :
    α.branches_set = { φ ∈ β.branches_set | φ ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; constructor
    · exact branches_set_monotone hle h
    · rcases h with ⟨_, ⟨_, _, _, hstuck, _⟩, rfl⟩
      exact hstuck
  · rintro ⟨⟨S, ⟨hne, hsub, ⟨v, hsat⟩, _, hmax⟩, rfl⟩, hstuck⟩
    have hS x (hx : x ∈ S) : x ∈ α.nodes := by
      have hx' := extens_subset_nodes _ (hsub hx)
      rcases hle.succ _ hx' with hxα | ⟨y, hbot, hyx⟩
      · exact hxα
      · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
        refine (congrFun (hle.form y hbot.1) _).mpr ?_
        refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
        exact hsat ⟨_, hx⟩
    refine ⟨S, ⟨hne, ?_, ⟨v, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro x hx; rw [le_extens hle]; refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact hsub hx
      · intro c; exact hstuck v hsat (c v (hsat ⟨x, hx⟩))
    · intro x; exact (congrFun (hle.form x (hS _ x.property)) _).mpr (hsat x)
    · refine le_trans ?_ hstuck; intro u hu x
      exact (congrFun (hle.form _ (hS _ x.property)) _).mp (hu x)
    · intro T hST hT ⟨u, hu⟩; refine hmax T hST ?_ ?_
      · exact le_trans hT (extens_monotone hle)
      · use u; intro x hx; refine (congrFun (hle.form _ ?_) _).mp (hu _ hx)
        exact extens_subset_nodes _ (hT hx)
    · ext1 u; refine forall_congr fun x ↦ ?_
      exact congrFun (hle.form x (hS _ x.property)) _

lemma branches_monotone : @Monotone (Lpofin l) _ _ _ branches := by
  unfold branches; intro α β hle; simp; exact branches_set_monotone hle

lemma branches_not_mutually_sat {α : Lpofin l} {φ ψ : Form Node}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ v ∧ ψ v) := by
  intro v ⟨h₁, h₂⟩
  rcases (Set.Finite.mem_toFinset _).mp hφ with ⟨S, ⟨_, hsub, _, _, hmax⟩, rfl⟩
  rcases (Set.Finite.mem_toFinset _).mp hψ with ⟨T, ⟨_, hsub', _, _, hmax'⟩, rfl⟩
  refine hmax (S ∪ T) ⟨Finset.subset_union_left, ?_⟩ ?_ ?_
  · intro h; apply hneq; refine congrArg _ ?_; ext x; constructor
    · intro hx; by_contra ht; refine hmax' (insert x T) ?_ ?_ ?_
      · exact Finset.ssubset_insert ht
      · intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hsub hx
        · exact hsub' hy
      · use v; intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
        · exact h₁ ⟨y, hx⟩
        · exact h₂ ⟨y, hy⟩
    · intro hx; exact h (Finset.subset_union_right hx)
  · intro x hx; rcases Finset.mem_union.mp hx with hx | hx
    · exact hsub hx
    · exact hsub' hx
  · use v; intro x hx; rcases Finset.mem_union.mp hx with hx | hx
    · exact h₁ ⟨x, hx⟩
    · exact h₂ ⟨x, hx⟩

def CopyFn (α β : Lpofin l) : Type :=
  { f : ↑α.branches → Lpofin l //
    ∀ φ : ↑α.branches,
      f φ ≈ β ∧
      Disjoint α.nodes (f φ).nodes ∧
      ∀ ψ, φ ≠ ψ → Disjoint (f φ).nodes (f ψ).nodes
  }
instance {α β : Lpofin l} : FunLike (CopyFn α β) ↑α.branches (Lpofin l) where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.ext h

def CopyFn_extends {α α' β β' : Lpofin l}
    (hle : α ≤ α') (f : CopyFn α β) (g : CopyFn α' β') :=
  ∀ φ : ↑α.branches, f φ ≤ g ⟨φ.val, branches_monotone hle φ.property⟩

noncomputable def seq_base [DCPO l] (α β : Lpofin l) (f : CopyFn α β) : Lpo_base l := {
  nodes := α.nodes ∪ ⋃ φ : ↑α.branches, (f φ).nodes
  rel x y :=
    α.rel x y ∨
    ∃ φ : ↑α.branches,
      (f φ).rel x y ∨
      (φ ≤ α.form x ∧ y ∈ (f φ).nodes)
  lab x :=
    if hx : ∃ φ : ↑α.branches, x ∈ (f φ).nodes then
      (f hx.choose).lab x
    else
      α.lab x
  form x := if x ∈ α.nodes then α.form x else Form.sOr fun φ : ↑α.branches ↦ ((f φ).form x).and φ.val
}

lemma branch_implies_node {α : Lpofin l} {x : Node} :
    ∀ φ : ↑α.branches, φ ≤ α.form x → x ∈ α.val.nodes := by
  intro φ hle
  rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨hne, hsub, hsat, hstk, hmax⟩, heq⟩
  refine (α.val.property.form_dom x).mp ?_
  rcases hsat with ⟨v, hv⟩; use v; exact hle v ((congrFun heq _).mp hv)

lemma seq_nodes_finite [DCPO l] {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).nodes.Finite := by
  refine Set.finite_union.mpr ⟨α.property, ?_⟩
  refine Set.finite_iUnion ?_; intro φ; exact (f φ).property

lemma seq_rel_valid [DCPO l] {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).rel.IsCausalityRel (seq_base α β f).nodes := by
  have h₁ := α.val.property
  have h₂ φ := (f φ).val.property
  rcases f with ⟨f, hf⟩
  have hd₁ φ := (hf φ).2.1
  have hd₂ φ ψ := (hf φ).2.2 ψ
  have contra {P : Prop} {s t : Set Node} {x : Node} (hd : Disjoint s t)
      (hs : x ∈ s) (ht : x ∈ t) : P :=
    False.elim (Set.disjoint_left.mp hd hs ht)
  constructor
  -- Transitivity
  · rintro x y z (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyz | ⟨ψ, hyz | ⟨hy', hz⟩⟩)
    · left; exact h₁.rel.trans hxy hyz
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2
        ((f ψ).val.property.rel_dom hyz).1
    · right; use ψ; right; refine ⟨?_, hz⟩
      refine hy'.trans ?_; exact (h₁.form x (h₁.rel_dom hxy).1).2 y hxy
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 ((f φ).val.property.rel_dom hxy).2
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; left; exact (f φ).val.property.rel.trans hxy hyz
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyz).1
    · have hy := branch_implies_node ψ hy'
      exact contra (hd₁ φ) hy ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 hy
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; right; refine ⟨hx, ?_⟩
        exact ((f φ).val.property.rel_dom hyz).2
      · exact contra (hd₂ φ ψ heq) hy ((f ψ).val.property.rel_dom hyz).1
    · have hy'' := branch_implies_node ψ hy'
      exact contra (hd₁ φ) hy'' hy
  -- Antisymmetry
  · rintro x y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyx | ⟨ψ, hyx | ⟨hy', hx'⟩⟩)
    · exact h₁.rel.antisymm hxy hyx
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2 ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).1 hx'
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).2 ((f φ).val.property.rel_dom hxy).1
    · by_cases heq : φ = ψ
      · subst heq; exact (f φ).val.property.rel.antisymm hxy hyx
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ φ)
        (branch_implies_node ψ hy')
        ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).1 hy
    · exact contra (hd₁ ψ) (branch_implies_node φ hx)
        ((f ψ).val.property.rel_dom hyx).2
    · exact contra (hd₁ ψ) (branch_implies_node φ hx) hx'
  -- Irreflexivity
  · rintro x (hxx | ⟨φ, hxx | ⟨hx, hx'⟩⟩)
    · exact h₁.rel.irrefl x hxx
    · exact (f φ).val.property.rel.irrefl x hxx
    · exact contra (hd₁ φ) (branch_implies_node φ hx) hx'
  -- Finitely Preceded
  · intro x; refine (seq_nodes_finite (α := α) (β := β) (f := ⟨f, hf⟩)).subset ?_
    rintro y (hyx | ⟨φ, hyx | ⟨hy, hx⟩⟩)
    · left; exact (h₁.rel_dom hyx).1
    · right; simp only [nodes, ne_eq, Set.mem_iUnion]
      use φ; exact ((h₂ φ).rel_dom hyx).1
    · left; exact branch_implies_node φ hy
  -- Finite Levels
  · intro n; refine (seq_nodes_finite (α := α) (β := β) (f := ⟨f, hf⟩)).subset ?_
    intro x ⟨hx, _⟩; exact hx
  -- Single-Rooted
  · obtain ⟨x, hx, hroot⟩ := h₁.rel.single_rooted; refine ⟨x, Or.inl hx, ?_⟩
    rintro y (hy | hy) hneq
    · left; exact hroot _ hy hneq
    · apply Set.mem_iUnion.mp at hy; rcases hy with ⟨φ, hy⟩
      right; use φ; right; refine ⟨?_, hy⟩
      intro v hform
      have ⟨S, ⟨⟨y, hy⟩, hext, ⟨v', hsat⟩, _⟩, hconj⟩ := (Set.Finite.mem_toFinset _).mp φ.property
      rw [← hconj] at hform; have := hform ⟨_, hy⟩
      by_cases heq : x = y
      · subst heq; exact this
      · have hy := extens_subset_nodes _ (hext hy)
        exact (α.val.property.form _ hx).2 _ (hroot _ hy heq) _ this

lemma seq_valid [DCPO l] (α β : Lpofin l) (f : CopyFn α β) :
    is_valid_lpo (seq_base α β f) := by
  constructor
  -- Rel Domain
  · intro x y hrel; cases hrel with
    | inl hrel =>
        refine ⟨Or.inl ?_, Or.inl ?_⟩
        · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).1
        · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).2
    | inr hrel =>
        rcases hrel with ⟨φ, (hrel | ⟨hx, hy⟩)⟩
        · constructor <;> refine Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).1
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).2
        · refine ⟨Or.inl ?_, Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)⟩
          · exact branch_implies_node φ hx
          · exact hy
  -- Label Domain
  · intro x hx; apply (Set.mem_union _ _ _).mpr.mt at hx
    simp only [Set.mem_iUnion, Subtype.exists, not_or, not_exists] at hx
    rcases hx with ⟨hx, hx'⟩
    simp only [seq_base, Subtype.exists]
    refine (dif_neg ?_).trans (α.val.property.lab_dom _ hx)
    intro ⟨φ, hφ, hx⟩; exact hx' _ hφ hx
  -- Rel Properties
  · exact seq_rel_valid
  -- Bot Successors
  · rintro x hlab y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩)
    · have hx := (α.val.property.rel_dom hxy).1
      refine (α.val.property.bot x).mt ?_ ?_
      · intro hc; exact hc _ hxy
      · rw [← hlab]; refine Eq.trans ?_ (dif_neg ?_).symm
        · rfl
        · intro ⟨φ, hc⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hx hc
    · have hx := ((f φ).val.property.rel_dom hxy).1
      refine ((f φ).val.property.bot x).mt ?_ ?_
      · intro hc; exact hc _ hxy
      · rw [← hlab]; refine ((dif_pos ⟨φ, hx⟩).trans ?_).symm
        refine congrArg₂ Lpo.lab (congrArg _ (congrArg _ ?_)) rfl
        refine (not_not.mp (((f.property φ).2.2 _).mt ?_)).symm
        refine Set.not_disjoint_iff.mpr ⟨x, hx, ?_⟩
        exact Exists.choose_spec (p := fun ψ ↦ x ∈ (f ψ).nodes) _
    · have hx' := branch_implies_node φ hx
      simp only [seq_base, nodes] at hlab
      rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨_, _, ⟨v, hv⟩, hstk, _⟩, heq⟩
      rw [← heq] at hx; have hform := hx v hv
      have : ¬ (∃ φ, x ∈ (f φ).nodes) := by
        intro ⟨ψ, hx⟩; exact Set.disjoint_left.mp (f.property ψ).2.1 hx' hx
      have := (dif_neg this).symm.trans hlab
      exact hstk v hv ⟨⟨x, hx', this⟩, hform⟩
  -- Formula Domain
  · intro x; constructor
    · rintro ⟨v, hv⟩; by_cases hx : x ∈ α.nodes <;>
      simp only [seq_base, Subtype.exists, hx, ↓reduceIte] at hv
      · left; exact (α.val.property.form_dom x).mp ⟨v, hv⟩
      · rcases hv with ⟨φ, hφ, _⟩; right
        simp only [Set.mem_iUnion]
        use φ; exact ((f φ).val.property.form_dom x).mp ⟨v, hφ⟩
    · simp only [seq_base, nodes, Subtype.exists, Set.mem_union, Set.mem_iUnion]
      rintro (hx | ⟨φ, hφ, hx⟩)
      · simp only [hx, ↓reduceIte]
        exact (α.val.property.form_dom x).mpr hx
      · have hx' : x ∉ α.val.nodes :=
          Set.disjoint_right.mp (f.2 ⟨φ, hφ⟩).2.1 hx
        simp only [hx', ↓reduceIte]
        obtain ⟨v, hv⟩ := ((f ⟨φ, hφ⟩).val.property.form_dom x).mpr hx
        have ⟨s, ⟨_, hs, ⟨v', hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp hφ
        refine ⟨(v ∩ (f ⟨φ, hφ⟩).nodes) ∪ (v' ∩ α.nodes), ⟨φ, hφ⟩, ?_, ?_⟩
        · refine (((f ⟨φ, hφ⟩).val.property.form _ hx).1 _ _ ?_).mp hv
          refine Set.disjoint_left.mpr ?_; intro y hy hrel
          rcases Set.mem_symmDiff.mp hy with ⟨hy, hy'⟩ | ⟨⟨hy, _⟩ | ⟨hy, ha⟩, hy'⟩
          · simp only [Set.mem_union, Set.mem_inter_iff, not_or, not_and] at hy'
            refine hy'.1 hy ?_
            exact ((f _).val.property.rel_dom hrel).1
          · exact hy' hy
          · exact Set.disjoint_right.mp (f.property _).2.1 ((f _).val.property.rel_dom hrel).1 ha
        · subst heq; simp only; intro y
          have hy' := extens_subset_nodes _ (hs y.property)
          refine ((α.val.property.form _ hy').1 _ _ ?_).mp (hsat y)
          refine Set.disjoint_left.mpr ?_; intro z hz hrel
          rcases Set.mem_symmDiff.mp hz with ⟨hzv', hz⟩ | ⟨⟨hzv, hz⟩ | h, hzv'⟩
          · simp only [Set.mem_union, Set.mem_inter_iff, not_or, not_and] at hz
            exact hz.2 hzv' (α.val.property.rel_dom hrel).1
          · refine Set.disjoint_left.mp (f.property _).2.1 ?_ hz
            exact (α.val.property.rel_dom hrel).1
          · exact hzv' h.1
  -- Formula Properties
  · rintro x (hx | hx) <;> refine ⟨?_, fun y hrel ↦ ?_⟩
    · simp only [seq_base, if_pos hx]
      refine Form.DependsOn.monotone _ ?_ (α.val.property.form _ hx).1
      intro y hrel; left; exact hrel
    · rcases hrel with hrel | ⟨φ, hrel | ⟨hform, hy⟩⟩
      · have hy : y ∈ α.nodes := (α.val.property.rel_dom hrel).2
        simp only [seq_base, if_pos hx, if_pos hy]
        exact (α.val.property.form _ hx).2 _ hrel
      · exfalso; refine Set.disjoint_left.mp (f.property φ).2.1 hx ?_
        exact ((f φ).val.property.rel_dom hrel).1
      · have hy' : y ∉ α.nodes :=
          Set.disjoint_right.mp (f.property φ).2.1 hy
        simp only [seq_base, if_pos hx, if_neg hy']
        refine le_trans ?_ hform; intro v ⟨ψ, hsat, hψ⟩
        have hy'' := ((f ψ).val.property.form_dom _).mp ⟨_, hsat⟩
        have := not_not.mp (((f.property φ).2.2 ψ).mt (Set.not_disjoint_iff.mpr ⟨_, hy, hy''⟩))
        subst this; exact hψ
    · simp only [Set.mem_iUnion] at hx; have ⟨φ, hx⟩ := hx
      have hx' : x ∉ α.nodes :=
        Set.disjoint_right.mp (f.property φ).2.1 hx
      simp only [seq_base, if_neg hx']
      have :
          (Form.sOr fun φ ↦ ((f φ).form x).and φ.val) =
          ((f φ).form x).and φ.val := by
        ext v; constructor
        · intro ⟨ψ, hform⟩; by_cases heq : φ = ψ
          · subst heq; exact hform
          · exfalso; have := Set.disjoint_left.mp ((f.property φ).2.2 _ heq) hx
            exact this (((f ψ).val.property.form_dom _).mp ⟨_, hform.1⟩)
        · intro hform; exact ⟨φ, hform⟩
      rw [this]
      refine Form.DependsOn.monotone _
        (?_ : ({ y | (f φ).rel y x } ∪ { y | φ.val ≤ α.form y }) ⊆ _)
        ?_
      · rintro y (hrel | hform)
        · right; use φ; left; exact hrel
        · right; use φ; right; exact ⟨hform, hx⟩
      · refine Form.DependsOn.and ?_ ?_
        · exact ((f φ).val.property.form  _ hx).1
        · have ⟨s, ⟨_, hs, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
          rw [← heq]
          refine Form.DependsOn.monotone _
            (?_ : (⋃ z : ↑s, { y | α.form z ≤ α.form y }) ⊆ _)
            ?_
          · intro y; simp only [Set.mem_iUnion]; intro ⟨z, hform⟩ v h; exact hform v (h z)
          · refine Form.DependsOn.sAnd fun z ↦ ?_
            have hz := extens_subset_nodes _ (hs z.property)
            refine (α.val.property.form _ hz).1.monotone _ ?_
            intro y hrel; have hy := (α.val.property.rel_dom hrel).1
            exact (α.val.property.form _ hy).2 _ hrel
    · rcases hrel with (hrel | ⟨φ, hrel | ⟨hform, hy⟩⟩)
      · have ⟨hx, hy⟩ := α.val.property.rel_dom hrel
        refine le_of_eq_of_le (if_pos hy) ?_
        refine le_of_le_of_eq ?_ (if_pos hx).symm
        exact (α.val.property.form _ hx).2 _ hrel
      · have ⟨hx, hy⟩ := (f φ).val.property.rel_dom hrel
        have hx' := Set.disjoint_right.mp (f.property φ).2.1 hx
        have hy' := Set.disjoint_right.mp (f.property φ).2.1 hy
        refine le_of_eq_of_le (if_neg hy') ?_
        refine le_of_le_of_eq ?_ (if_neg hx').symm
        intro v ⟨ψ, hform, hφ⟩
        have hy'' := ((f ψ).val.property.form_dom _).mp ⟨_, hform⟩
        have := not_not.mp (((f.property φ).2.2 ψ).mt (Set.not_disjoint_iff.mpr ⟨_, hy, hy''⟩))
        subst this; refine ⟨φ, ?_, hφ⟩
        exact ((f φ).val.property.form _ hx).2 _ hrel _ hform
      · exfalso; simp only [Set.mem_iUnion] at hx
        have ⟨ψ, hx⟩ := hx; refine Set.disjoint_right.mp (f.property ψ).2.1 hx ?_
        have ⟨s, ⟨_, _, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
        rw [← heq] at hform; exact (α.val.property.form_dom _).mp ⟨_, hform _ hsat⟩

noncomputable def seq [DCPO l] (α β : Lpofin l) (f : CopyFn α β) : Lpofin l := {
  val := {
    val := seq_base α β f
    property := seq_valid α β f
  }
  property := seq_nodes_finite
}

lemma seq_monotone [DCPO l] {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hle₁ : α ≤ α') (hext : CopyFn_extends hle₁ f g) :
    seq α β f ≤ seq α' β' g := by
  constructor
  · simp only [Lpo.nodes, seq, seq_base, nodes,
      Subtype.exists, Set.union_subset_iff, Set.iUnion_subset_iff, Subtype.forall]
    constructor
    · intro x hx; left; exact hle₁.nodes hx
    · intro φ hφ x hx; right
      have hφ' := branches_monotone hle₁ hφ
      simp only [Set.mem_iUnion, Subtype.exists]
      exact ⟨φ, hφ', (hext ⟨φ, hφ⟩).nodes hx⟩
  · rintro x (hx | hx) y hyx
    · rcases hyx with (hyx | ⟨ψ, hyx | ⟨hx', hy⟩⟩)
      · left; exact hle₁.downcl x hx y hyx
      · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle₁.nodes hx)
          ((g ψ).val.property.rel_dom hyx).2
      · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle₁.nodes hx) hy
    · rcases Set.mem_iUnion.mp hx with ⟨φ, hx⟩
      rcases hyx with (hyx | ⟨ψ, hyx⟩)
      · exfalso; have hx' := (hext φ).nodes hx
        exact Set.disjoint_left.mp (g.property _).2.1
          (α'.val.property.rel_dom hyx).2
          hx'
      · by_cases heq : ψ = ⟨φ.val, branches_monotone hle₁ φ.property⟩
        · subst heq; rcases hyx with hyx | ⟨hy, hx'⟩
          · right; refine Set.mem_iUnion.mpr ⟨φ, ?_⟩;
            exact (hext φ).downcl x hx y hyx
          · left
            have ⟨s, ⟨_, _, ⟨v, hsat⟩, hstk, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
            have hy' : y ∈ α'.nodes := by
              refine (α'.val.property.form_dom _).mp ?_
              rw [← heq] at hy; exact ⟨v, hy _ hsat⟩
            refine or_iff_not_imp_right.mp (hle₁.succ _ hy') ?_
            intro ⟨z, hz, hrel⟩
            refine not_exists.mp (hstk _ hsat) ⟨_, hz⟩ ?_
            refine (congrFun (hle₁.form _ hz.1) _).mpr ?_
            refine (α'.val.property.form _ (hle₁.nodes hz.1)).2 _ hrel _ ?_
            rw [← heq] at hy; exact hy _ hsat
        · exfalso
          refine Set.disjoint_left.mp ((g.property ψ).2.2 _ heq)
              ?_
              ((hext φ).nodes hx)
          rcases hyx with hyx | ⟨_, hx'⟩
          · exact ((g ψ).val.property.rel_dom hyx).2
          · exact hx'
  · intro x hx y hy; ext; constructor
    · rintro (hrel | ⟨φ, h⟩)
      · left; exact le_rel hle₁ hrel
      · right; refine ⟨⟨φ.val, branches_monotone hle₁ φ.property⟩, ?_⟩
        rcases h with (hrel | ⟨hform, hy'⟩)
        · left; exact le_rel (hext _) hrel
        · right; refine ⟨?_, (hext _).nodes hy'⟩
          refine le_of_le_of_eq hform (hle₁.form _ ?_)
          refine (α.val.property.form_dom _).mp ?_
          have ⟨s, ⟨_, _, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
          rw [← heq] at hform; exact ⟨v, hform _ hsat⟩
    · simp only [Lpo.nodes, seq, seq_base, nodes, Set.mem_union, Set.mem_iUnion, Lpo.rel] at *
      obtain (hx | ⟨φ, hx⟩) := hx <;>
      obtain (hy | ⟨ψ, hy⟩) := hy <;>
      rintro (hrel | ⟨φ', hrel | ⟨hform, hy'⟩⟩)
      · left; exact (hle₁.rel _ hx _ hy).mpr hrel
      · exfalso; have hx' := ((g _).val.property.rel_dom hrel).1
        exact Set.disjoint_left.mp (g.property _).2.1 (hle₁.nodes hx) hx'
      · exfalso; exact Set.disjoint_left.mp (g.property _).2.1 (hle₁.nodes hy) hy'
      · exfalso; have hy' := (α'.val.property.rel_dom hrel).2
        exact Set.disjoint_left.mp (g.property _).2.1 hy' ((hext _).nodes hy)
      · exfalso; have hx' := ((g _).val.property.rel_dom hrel).1
        exact Set.disjoint_left.mp (g.property _).2.1 (hle₁.nodes hx) hx'
      · refine Or.inr ⟨ψ, Or.inr ⟨?_, hy⟩⟩
        refine le_of_eq_of_le ?_ (le_of_le_of_eq hform ?_)
        · refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2 ⟨ψ.val, ?_⟩).mt ?_)).symm
          · exact branches_monotone hle₁ ψ.property
          · exact Set.not_disjoint_iff.mpr ⟨y, hy', (hext _).nodes hy⟩
        · symm; exact hle₁.form _ hx
      · exfalso; have hx' := (α'.val.property.rel_dom hrel).1
        exact Set.disjoint_left.mp (g.property _).2.1 hx' ((hext _).nodes hx)
      · exfalso; have hy' := ((g _).val.property.rel_dom hrel).2
        exact Set.disjoint_left.mp (g.property _).2.1 (hle₁.nodes hy) hy'
      · exfalso; exact Set.disjoint_left.mp (g.property _).2.1 (hle₁.nodes hy) hy'
      · exfalso; have hx' := (α'.val.property.rel_dom hrel).1
        exact Set.disjoint_left.mp (g.property _).2.1 hx' ((hext _).nodes hx)
      · refine Or.inr ⟨φ, Or.inl ?_⟩
        have ⟨hx', hy'⟩ := (g _).val.property.rel_dom hrel
        have heq : φ.val = φ'.val := by
          refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2 ⟨φ.val, ?_⟩).mt ?_)).symm
          · exact branches_monotone hle₁ φ.property
          · exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes hx⟩
        have : φ = ψ := by
          ext1; rw [heq]
          refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2 ⟨ψ.val, ?_⟩).mt ?_))
          · exact branches_monotone hle₁ ψ.property
          · exact Set.not_disjoint_iff.mpr ⟨y, hy', (hext _).nodes hy⟩
        subst this; refine ((hext φ).rel _ hx _ hy).mpr ?_
        · have {h} : ⟨φ.val, h⟩ = φ' := by ext1; exact heq
          rw [this]; exact hrel
      · exfalso; refine Set.disjoint_left.mp (g.property _).2.1 ?_ ((hext _).nodes hx)
        refine (α'.val.property.form_dom _).mp ?_
        have ⟨s, ⟨_, _, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ'.property
        rw [← heq] at hform; exact ⟨v, hform _ hsat⟩
  · intro x; by_cases hx : x ∈ (α.seq β f).nodes
    · rcases hx with hx | hx
      · have hx' : x ∈ α'.nodes := hle₁.nodes hx
        have hf : ¬ ∃ φ, x ∈ (f φ).nodes := by
          intro ⟨φ, hφ⟩; exact Set.disjoint_right.mp (f.property φ).2.1 hφ hx
        have hg : ¬ ∃ φ, x ∈ (g φ).nodes := by
          intro ⟨φ, hφ⟩; exact Set.disjoint_right.mp (g.property φ).2.1 hφ hx'
        simp only [Lpo.lab, seq, seq_base, dif_neg hf, dif_neg hg]
        exact hle₁.lab x
      · simp only [Set.mem_iUnion] at hx
        have ⟨φ, hf⟩ := hx; have hg := (hext φ).nodes hf
        have hx' : ∃ φ, x ∈ (g φ).nodes := ⟨⟨φ.val, _⟩, hg⟩
        simp only [Lpo.lab, seq, seq_base, dif_pos hx, dif_pos hx']
        refine le_of_le_of_eq ((hext _).lab x) ?_
        refine congrArg₂ Lpofin.lab (congrArg _ ?_) rfl
        refine not_not.mp (((g.property _).2.2 _).mt (Set.not_disjoint_iff.mpr ?_))
        refine ⟨x, ?_, Exists.choose_spec hx'⟩
        exact (hext _).nodes (Exists.choose_spec hx)
    · exact le_of_eq_of_le ((α.seq β f).val.property.lab_dom _ hx) bot_le
  · rintro x (hx | hx)
    · have hx' := hle₁.nodes hx
      simp only [Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
      simp only [hx, hx', ↓reduceIte]; exact hle₁.form x hx
    · rcases Set.mem_iUnion.mp hx with ⟨φ, h⟩
      simp only [Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
      have hx₁ := Set.disjoint_right.mp (f.property φ).2.1 h
      have hx₂ := Set.disjoint_right.mp (g.property _).2.1 ((hext φ).nodes h)
      simp only [Lpofin.nodes, Lpo.nodes] at hx₁
      simp only [Lpofin.nodes, Lpo.nodes] at hx₂
      simp only [hx₁, ↓reduceIte, hx₂]
      ext v; constructor
      · intro ⟨ψ, hψ, hφ⟩
        have heq : φ = ψ := by
          by_contra hc
          have hd := (f.property φ).2.2 ψ hc
          have hx := Set.disjoint_left.mp hd h
          exact ((f ψ).val.property.form_dom x).mp.mt hx ⟨v, hψ⟩
        subst heq; exact ⟨_, (congrFun ((hext _).form _ h) _).mp hψ, hφ⟩
      · intro ⟨ψ, hform, hψ⟩
        have heq : ψ.val = φ.val := by
          have hx' := ((g ψ).val.property.form_dom _).mp ⟨_, hform⟩
          refine congrArg Subtype.val (not_not.mp (((g.property ψ).2.2 ⟨φ, ?_⟩).mt ?_))
          · exact branches_monotone hle₁ φ.property
          · exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes h⟩
        refine ⟨φ, ?_, ?_⟩
        · refine (congrFun ?_ _).mpr hform
          refine ((hext φ).form _ h).trans ?_
          have {h} : ⟨φ.val, h⟩ = ψ := by ext1; exact heq.symm
          rw [this]; rfl
        · rw [← heq]; exact hψ
  · simp only [Lpo.nodes, seq, seq_base, Set.mem_union, Set.mem_iUnion, Lpo.bots, Lpo.rel, Lpo.lab]
    rintro x (hx | ⟨φ, hx⟩)
    · rcases hle₁.succ _ hx with (hx' | ⟨z, hz, hrel⟩)
      · left; left; exact hx'
      · right; refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inl hrel⟩
        refine (dif_neg ?_).trans hz.2
        intro ⟨φ, hz'⟩
        exact Set.disjoint_left.mp (f.property φ).2.1 hz.1 hz'
    · by_cases hφ : φ.val ∈ α.branches
      · rcases (hext ⟨_, hφ⟩).succ _ hx with (hx' | ⟨z, hz, hrel⟩)
        · left; right; exact ⟨_, hx'⟩
        · right; refine ⟨z, ⟨Or.inr ⟨_, hz.1⟩, ?_⟩, Or.inr ⟨φ, Or.inl hrel⟩⟩
          refine (dif_pos ⟨_, hz.1⟩).trans ?_
          have {ψ} : (f ψ).lab z = ⊥ := by
            by_cases heq : ψ = ⟨φ.val, hφ⟩
            · subst heq; exact hz.2
            · refine (f ψ).val.property.lab_dom _ ?_
              exact Set.disjoint_right.mp ((f.property _).2.2 _ heq) hz.1
          exact this
      · right
        have ⟨s, ⟨hne, hs, ⟨v, hsat⟩, hstk, hmax⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
        have hφ' := (Set.Finite.mem_toFinset _).mpr.mt hφ
        rw [le_branches_set hle₁] at hφ'
        have h := (Set.Finite.mem_toFinset _).mp φ.property
        have ⟨v', hform⟩ := not_forall.mp ((Set.mem_inter h).mt hφ')
        have ⟨hv, hform⟩ := Classical.not_imp.mp hform
        have ⟨⟨z, hz⟩, hform⟩ := not_not.mp hform
        by_cases hz' : z ∈ s
        · refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inr ⟨φ, Or.inr ⟨?_, hx⟩⟩⟩
          · refine (dif_neg ?_).trans hz.2
            intro ⟨φ, hz'⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hz.1 hz'
          · rw [← heq]; intro v hv; exact hv ⟨_, hz'⟩
        · exfalso; rw [← heq] at hv; refine hstk _ hv ?_
          have : z ∉ α'.extens := by
            intro hc
            refine hmax (insert z s) (Finset.ssubset_insert hz') ?_ ?_
            · intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hc
              · exact hs hy
            · use v'; intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
              · exact (congrFun (hle₁.form _ hz.1) _).mp hform
              · exact hv ⟨_, hy⟩
          have := Finset.mem_filter.mpr.mt this; simp only [not_and, Decidable.not_not] at this
          have := this ((Set.Finite.mem_toFinset _).mpr (hle₁.nodes hz.1))
          exact this _ ((congrFun (hle₁.form _ hz.1) _).mp hform)


namespace Equiv

noncomputable def union {α : Type} {X X' Y Y' : Set α} (e₁ : X ≃ Y) (e₂ : X' ≃ Y')
    (h₁ : Disjoint X X') (h₂ : Disjoint Y Y') :
    ↑(X ∪ X') ≃ ↑(Y ∪ Y') :=
  (Equiv.Set.union h₁).trans
    ((e₁.sumCongr e₂).trans (Equiv.Set.union h₂).symm)

lemma union_symm {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} :
    (union e₁ e₂ h₁ h₂).symm = union e₁.symm e₂.symm h₂ h₁ := by
  unfold union; ext1 x
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm,
    Equiv.sumCongr_apply, Equiv.trans_apply]

lemma union_apply_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x : α} (hx : x ∈ X) :
    (union e₁ e₂ h₁ h₂ ⟨x, Set.subset_union_left hx⟩).val = (e₁ ⟨x, hx⟩).val := by
  simp only [union, Equiv.trans_apply, Equiv.sumCongr_apply]
  conv => arg 1; arg 1; arg 2; arg 3; exact Equiv.Set.union_apply_left _ hx
  simp only [Sum.map_inl, Equiv.Set.union_symm_apply_left, Set.subset_union_left, Set.coe_inclusion]

lemma union_apply_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x : α} (hx : x ∈ X') :
    (union e₁ e₂ h₁ h₂ ⟨x, Set.subset_union_right hx⟩).val = (e₂ ⟨x, hx⟩).val := by
  simp only [union, Equiv.trans_apply, Equiv.sumCongr_apply]
  conv => arg 1; arg 1; arg 2; arg 3; exact Equiv.Set.union_apply_right _ hx
  simp only [Sum.map_inr, Equiv.Set.union_symm_apply_right, Set.subset_union_right,
    Set.coe_inclusion]

lemma union_symm_apply_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y : α} (hy : y ∈ Y) :
    ((union e₁ e₂ h₁ h₂).symm ⟨y, Set.subset_union_left hy⟩).val = (e₁.symm ⟨y, hy⟩).val := by
  rw [union_symm, union_apply_left]

lemma union_symm_apply_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y : α} (hy : y ∈ Y') :
    ((union e₁ e₂ h₁ h₂).symm ⟨y, Set.subset_union_right hy⟩).val = (e₂.symm ⟨y, hy⟩).val := by
  rw [union_symm, union_apply_right]

lemma mem_union_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x}
    (hx : (union e₁ e₂ h₁ h₂ x).val ∈ Y) : x.val ∈ X := by
  have := @union_symm_apply_left _ _ _ _ _ e₁ e₂ h₁ h₂ _ hx
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {x}
    (hx : (union e₁ e₂ h₁ h₂ x).val ∈ Y') : x.val ∈ X' := by
  have := @union_symm_apply_right _ _ _ _ _ e₁ e₂ h₁ h₂ _ hx
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_symm_left {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y}
    (hy : ((union e₁ e₂ h₁ h₂).symm y).val ∈ X) : y.val ∈ Y := by
  have := @union_apply_left _ _ _ _ _ e₁ e₂ h₁ h₂ _ hy
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this; rw [this]; exact Subtype.coe_prop _

lemma mem_union_symm_right {α : Type} {X X' Y Y' : Set α} {e₁ : X ≃ Y} {e₂ : X' ≃ Y'}
    {h₁ : Disjoint X X'} {h₂ : Disjoint Y Y'} {y}
    (hy : ((union e₁ e₂ h₁ h₂).symm y).val ∈ X') : y.val ∈ Y' := by
  have := @union_apply_right _ _ _ _ _ e₁ e₂ h₁ h₂ _ hy
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this; rw [this]; exact Subtype.coe_prop _

noncomputable def sigma_iUnion {α β : Type} {f : α → Set β}
    (h : ∀ x y, x ≠ y → Disjoint (f x) (f y)) :
    Sigma (fun x ↦ ↑(f x)) ≃ ↑(Set.iUnion f) := {
  toFun x := ⟨x.snd.val, Set.mem_iUnion.mpr ⟨x.fst, x.snd.property⟩⟩
  invFun x := by
    have := Set.mem_iUnion.mp x.property
    exact Sigma.mk this.choose ⟨x.val, this.choose_spec⟩
  left_inv x := by
    ext <;> simp only
    by_contra hc
    let p i := x.snd.val ∈ f i
    exact Set.disjoint_left.mp (h _ _ hc) (Exists.choose_spec (p := p) _) x.snd.property
  right_inv x := by simp only [Subtype.coe_eta]
}

noncomputable def iUnion {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    (h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y))
    (h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y))
    (e : ι ≃ κ) (e' : (i : ι) → f i ≃ g (e i)) :
    ↑(Set.iUnion f) ≃ ↑(Set.iUnion g) :=
  (Equiv.sigma_iUnion h₁).symm.trans
    ((Equiv.sigmaCongr e e').trans (Equiv.sigma_iUnion h₂))

lemma iUnion_apply {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {x : α} {i : ι} (hx : x ∈ f i) :
    (iUnion h₁ h₂ e e' ⟨x, Set.subset_iUnion _ _ hx⟩).val = (e' i ⟨x, hx⟩).val := by
  simp only [iUnion, sigma_iUnion, Equiv.sigmaCongr, Equiv.trans_apply, Equiv.coe_fn_symm_mk,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply, Equiv.coe_fn_mk]
  have h := Set.mem_iUnion.mp (Set.subset_iUnion _ _ hx)
  have : h.choose = i := by
    refine not_not.mp ((h₁ _ _).mt ?_)
    exact Set.not_disjoint_iff.mpr ⟨x, h.choose_spec, hx⟩
  subst this; rfl

def swap_fun {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    (e : ι ≃ κ) (e' : (i : ι) → f i ≃ g (e i)) :
    (k : κ) → g k ≃ f (e.symm k) :=
  fun k ↦
    (Equiv.setCongr (by simp only [Equiv.apply_symm_apply])).trans (e' (e.symm k)).symm

lemma iUnion_symm {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)} :
    (iUnion h₁ h₂ e e').symm =
    iUnion h₂ h₁ e.symm (swap_fun e e') := by
  ext1 x; unfold swap_fun
  simp only [iUnion, sigma_iUnion, Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk,
    Equiv.trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply, Subtype.mk.injEq]
  refine congrArg _ (congrArg _ ?_)
  ext; grind only

lemma iUnion_symm_apply {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : α} {k : κ} (hy : y ∈ g k) :
    ((iUnion h₁ h₂ e e').symm ⟨y, Set.subset_iUnion _ _ hy⟩).val =
    ((e' (e.symm k)).symm ⟨y, by simpa only [Equiv.apply_symm_apply]⟩).val := by
  rw [iUnion_symm]; refine (iUnion_apply hy).trans ?_
  simp only [swap_fun, Equiv.trans_apply, Equiv.setCongr_apply]

lemma iUnion_symm_apply' {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : α} {i : ι} (hy : y ∈ g (e i)) :
    ((iUnion h₁ h₂ e e').symm ⟨y, Set.subset_iUnion _ _ hy⟩).val =
    ((e' i).symm ⟨y, by simpa only [Equiv.apply_symm_apply]⟩).val := by
  rw [iUnion_symm]; refine (iUnion_apply hy).trans ?_
  simp [swap_fun]; sorry

lemma mem_iUnion {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {x : ↑(⋃ i, f i)} {k : κ} (h : (iUnion h₁ h₂ e e' x).val ∈ g k) :
    x.val ∈ f (e.symm k) := by
  have := @iUnion_symm_apply _ _ _ _ _ h₁ h₂ e e' _ _ h
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this
  rw [this]; exact Subtype.coe_prop _

lemma mem_iUnion_symm {ι κ α : Type} {f : ι → Set α} {g : κ → Set α}
    {h₁ : ∀ x y, x ≠ y → Disjoint (f x) (f y)}
    {h₂ : ∀ x y, x ≠ y → Disjoint (g x) (g y)}
    {e : ι ≃ κ} {e' : (i : ι) → f i ≃ g (e i)}
    {y : ↑(⋃ k, g k)} {i : ι} (h : ((iUnion h₁ h₂ e e').symm y).val ∈ f i) :
    y.val ∈ g (e i) := by
  have := @iUnion_apply _ _ _ _ _ h₁ h₂ e e' _ _ h
  simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at this
  rw [this]; exact Subtype.coe_prop _

end Equiv

lemma branches_permute {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    ∀ φ ∈ α.branches, φ.permute e ∈ α'.branches := by
  intro φ hφ
  obtain ⟨s, ⟨hne, hsub, ⟨v, hsat⟩, hstk, hmax⟩, rfl⟩ := (Set.Finite.mem_toFinset _).mp hφ
  let t := s.attach.image
    (fun x : ↑s ↦ (e ⟨x.val, extens_subset_nodes _ (hsub x.property)⟩).val)
  refine (Set.Finite.mem_toFinset _).mpr ⟨t, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> subst t
  · refine Finset.Nonempty.image (Finset.univ_nonempty_iff.mpr ?_) _
    exact hne.coe_sort
  · conv => rhs; rw [← h]
    intro x hx; obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [extens, Finset.mem_filter]; constructor
    · refine (Set.Finite.mem_toFinset _).mpr ?_; exact Subtype.coe_prop _
    · intro hc
      have := hsub hy; simp [extens] at this; have ⟨hy', h'⟩ := this; apply h'
      have hy' := (Set.Finite.mem_toFinset _).mp hy'; intro v hform
      have ⟨⟨z, hz, hbot⟩, _, hform'⟩ := hc (Form.image v e) ((Lpo.permute_form_sat_iff hy').mp hform)
      refine ⟨⟨(e.symm ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · refine Eq.trans ?_ hbot; exact (if_pos hz).symm
      · refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 2; arg 1; exact e.apply_symm_apply _
        exact ⟨hz, hform'⟩
  · use Form.image v e; intro ⟨x, hx⟩; obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hx
    conv => simp only; arg 1; exact h.symm
    refine (Lpo.permute_form_sat_iff _).mp (hsat ⟨_, hy⟩)
  · intro v hv ⟨⟨z, hz, hbot⟩, hform⟩
    refine hstk (Form.image v e.symm) ?_ ?_
    · intro ⟨x, hx⟩; refine ((Lpo.permute_form_sat_iff ?_ (e := e)).mpr ?_)
      · exact extens_subset_nodes _ (hsub hx)
      · conv => arg 3; arg 2; exact e.symm_symm.symm
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv at hv => arg 1; exact h.symm
        refine hv ⟨(e ⟨x, _⟩).val, ?_⟩
        exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    · refine ⟨⟨(e.symm ⟨z, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
      · rw [← h] at hbot; simp only [Lpo.lab, permute, Lpo.permute, dite_eq_right_iff] at hbot
        exact hbot hz
      · simp only
        refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
        conv => arg 3; exact Form.image_inv v e.symm
        refine Lpo.form_inter_nodes_sat_iff.mp ?_
        conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
        conv at hform => simp only; arg 1; exact h.symm
        exact hform
  · intro t ⟨hst, hnts⟩ hex ⟨v, hform⟩
    refine hmax (t.attach.image fun y ↦ (e.symm ⟨y.val, ?_⟩).val) ?_ ?_ ?_
    · exact extens_subset_nodes _ (hex y.property)
    · constructor
      · intro x hx; refine Finset.mem_image.mpr ⟨⟨e ⟨x, ?_⟩, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · exact extens_subset_nodes _ (hsub hx)
        · exact hst (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
        · simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      · intro hc; apply hnts; intro x hx
        refine Finset.mem_image.mpr ⟨⟨(e.symm ⟨x, ?_⟩).val, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · exact extens_subset_nodes _ (hex hx)
        · exact hc (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
        · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · intro x hx; simp only [extens, Finset.mem_image, Finset.mem_attach, true_and, Finset.mem_filter] at *
      obtain ⟨y, rfl⟩ := hx; constructor
      · exact (Set.Finite.mem_toFinset _).mpr (Subtype.coe_prop _)
      · intro hc; have := hex y.property
        simp only [extens, nodes_finset, Finset.mem_filter, Set.Finite.mem_toFinset] at this
        apply this.2; intro v hform
        rw [← h] at hform; simp only [Lpofin.permute, form, Lpo.permute, Lpo.form] at hform
        have ⟨hy, hform⟩ := hform
        have ⟨⟨z, hz, hbot⟩, hform⟩ := hc _ hform
        refine ⟨⟨(e ⟨_, hz⟩).val, Subtype.coe_prop _, ?_⟩, ?_⟩
        · conv => arg 1; arg 1; arg 1; exact h.symm
          simp only [Lpofin.permute, Lpo.permute, Lpo.lab]
          refine (dif_pos (Subtype.coe_prop _)).trans ?_
          conv => lhs; arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.symm_apply_apply _
          exact hbot
        · simp only [← h]
          refine Lpo.form_inter_nodes_sat_iff.mpr ?_
          conv => arg 3; exact (Form.image_inv _ e.symm).symm
          conv => arg 3; arg 2; exact e.symm_symm
          exact (Lpo.permute_form_sat_iff _).mp hform
    · refine ⟨Form.image v e.symm, ?_⟩; intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      refine (Lpo.permute_form_sat_iff (Subtype.coe_prop _) (e := e)).mpr ?_
      conv => arg 2; simp only [Subtype.coe_eta]; arg 1; exact e.apply_symm_apply _
      conv => arg 3; exact Form.image_inv _ _
      refine Lpo.form_inter_nodes_sat_iff.mp ?_
      have := hform _ y.property; rw [← h] at this; exact this
  · conv => lhs; arg 1; rw [← h]
    simp only [conj]; unfold Form.permute; ext v; constructor
    · intro hform x
      have :=
        hform
          ⟨(e ⟨x.val, extens_subset_nodes _ (hsub x.property)⟩).val,
            Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩⟩
      simp only [form, Lpo.form, permute, Lpo.permute, Form.permute, Subtype.coe_eta,
        Subtype.coe_prop, exists_const] at this
      conv at this => arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact this
    · intro hform x
      have ⟨y, _, heq⟩ := Finset.mem_image.mp x.property; rw [← heq]
      have := hform y
      simp only [form, Lpo.form, permute, Lpo.permute, Form.permute, Subtype.coe_eta,
        Subtype.coe_prop, exists_const]
      conv => arg 2; arg 1; exact Equiv.symm_apply_apply _ _
      exact this

def branches_equiv [PartialOrder l] [OrderBot l] {α α' : Lpofin l} {e : α.nodes ≃ α'.nodes}
    (h : α.permute e = α') :
    α.branches ≃ α'.branches := {
  toFun φ := ⟨φ.val.permute e, branches_permute h _ φ.property⟩
  invFun φ := ⟨φ.val.permute e.symm, by {
    refine branches_permute ?_ _ φ.property
    refine Subtype.ext ?_; symm; refine (Lpo.permute_symm ?_)
    conv => rhs; arg 1; exact h.symm
    rfl
  }⟩
  left_inv := by
    intro ⟨φ, hφ⟩
    unfold Form.permute; ext1; ext1 v; simp only [Equiv.symm_symm, Form.image]
    obtain ⟨s, ⟨_, hsub, _⟩, rfl⟩:= (Set.Finite.mem_toFinset _).mp hφ
    have h (x : ↑s) := (α.val.property.form _ (extens_subset_nodes _ (hsub x.property))).1
    refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨z, rfl, w, heq, hw⟩, hv⟩ | ⟨hv, h⟩
    · apply hv; rw [← Subtype.val_injective heq]; simpa only [Equiv.symm_apply_apply]
    · have hx := (α.val.property.rel_dom hrel).1
      refine h ⟨e ⟨x, hx⟩, ?_, ⟨x, hx⟩, rfl, hv⟩
      simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro ⟨φ, hφ⟩
    unfold Form.permute; ext1; ext1 v; simp only [Form.image, Equiv.symm_symm, Subtype.exists,
      exists_and_right, Set.mem_setOf_eq, ↓existsAndEq, Subtype.coe_eta, Equiv.apply_symm_apply,
      Subtype.coe_prop, exists_const, true_and, exists_prop]
    obtain ⟨s, ⟨_, hsub, _⟩, rfl⟩:= (Set.Finite.mem_toFinset _).mp hφ
    have h (x : ↑s) := (α'.val.property.form _ (extens_subset_nodes _ (hsub x.property))).1
    refine Form.DependsOn.sAnd h _ _ ?_
    refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨y, hrel⟩ := Set.mem_iUnion.mp hx'
    rcases Set.mem_symmDiff.mp hx with ⟨⟨_, h⟩, h'⟩ | ⟨hv, h⟩
    · exact h' h
    · refine h ⟨⟨?_, True.intro⟩, hv⟩; exact (α'.val.property.rel_dom hrel).1
}

lemma seq_isomorphic [DCPO l] [OrderBot l] {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hα : α ≈ α') (hβ : β ≈ β') : seq α β f ≈ seq α' β' g := by
  have ⟨e, he⟩ := hα
  have eb := branches_equiv (Subtype.ext he)
  have (φ : ↑α.branches) :
      ∃ e : ((f φ).nodes ≃ (g (eb φ)).nodes), (f φ).permute e = (g (eb φ)) := by
    have ⟨ef, hf⟩ := (f.property φ).1
    have ⟨eg, hg⟩ := (g.property (eb φ)).1
    have ⟨eβ, h⟩ := hβ
    refine ⟨ef.trans (eβ.trans eg.symm), ?_⟩
    unfold Lpofin.permute; refine Subtype.ext ?_; simp only
    refine Lpo.permute_trans.symm.trans ?_
    refine Lpo.permute_trans.symm.trans ?_
    symm; refine Lpo.permute_symm (hg.trans (h.symm.trans ?_))
    refine Lpo.permute_congr _ _ hf.symm ?_
    intro x; rfl
  choose eφ h using this
  let e' := Equiv.iUnion
    (fun φ ↦ (f.property φ).2.2)
    (fun φ ↦ (g.property φ).2.2)
    eb eφ
  refine ⟨Equiv.union e e' ?_ ?_ , ?_⟩
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (f.property φ).2.1 hx hx'
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    have ⟨φ, hx'⟩ := Set.mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (g.property φ).2.1 hx hx'
  · ext1
    · rfl
    · ext x y
      by_cases hx : x ∈ (α'.seq β' g).nodes
      · by_cases hy : y ∈ (α'.seq β' g).nodes
        · simp only [seq, seq_base, Lpo.permute, Lpo.nodes, Lpo.rel]
          unfold Rel.permute
          refine Iff.trans ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx, hy, h⟩⟩ ?_
          refine or_congr ?_ ?_
          · unfold Lpofin.rel; rw [← he]
            simp only [Lpo.permute, Lpo.rel, Rel.permute]
            constructor
            · intro hrel; have ⟨hx', hy'⟩ := (α.val.property.rel_dom hrel)
              have hx := Equiv.mem_union_symm_left hx'
              have hy := Equiv.mem_union_symm_left hy'
              refine ⟨hx, hy, ?_⟩
              rw [Equiv.union_symm_apply_left hx, Equiv.union_symm_apply_left hy] at hrel
              exact hrel
            · intro ⟨hx', hy', hrel⟩
              refine (congrArg₂ α.rel ?_ ?_).mpr hrel
              · exact Equiv.union_symm_apply_left hx'
              · exact Equiv.union_symm_apply_left hy'
          · refine eb.exists_congr ?_; intro φ
            rw [← h φ]
            simp only [Lpofin.permute, Lpo.permute, rel, Lpo.rel, nodes, Lpo.nodes, Rel.permute]
            refine or_congr ?_ ?_
            · constructor
              · intro hrel
                have ⟨hx', hy'⟩ := (f φ).val.property.rel_dom hrel
                have hx'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hx'⟩)
                have hy'' := Equiv.mem_union_symm_right (Set.mem_iUnion.mpr ⟨_, hy'⟩)
                conv at hx' => arg 2; exact Equiv.union_symm_apply_right hx''
                conv at hy' => arg 2; exact Equiv.union_symm_apply_right hy''
                unfold e' at hx'
                have hx := Equiv.mem_iUnion_symm (e := eb) hx'
                have hy := Equiv.mem_iUnion_symm (e := eb) hy'
                refine ⟨hx, hy, (congrArg₂ _ ?_ ?_).mp hrel⟩; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
              · intro ⟨hx', hy', hrel⟩
                refine (congrArg₂ _ ?_ ?_).mpr hrel; all_goals {
                  refine (Equiv.union_symm_apply_right ?_).trans ?_
                  · refine Set.mem_iUnion.mpr ⟨eb φ, ?_⟩; assumption
                  · exact Equiv.iUnion_symm_apply' _
                }
            · refine and_congr ?_ ?_
              · sorry
              · sorry
        · constructor
          · intro ⟨_, hy', _⟩; exfalso; exact hy hy'
          · intro hrel; exfalso; exact hy ((seq _ _ _).val.property.rel_dom hrel).2
      · constructor
        · intro ⟨hx', _⟩; exfalso; exact hx hx'
        · intro hrel; exfalso; exact hx ((seq _ _ _).val.property.rel_dom hrel).1



      constructor
      · rintro ⟨hx, hy, hrel | ⟨φ, hrel | ⟨hform, hj⟩⟩⟩
        · left; unfold Lpofin.rel; rw [← he]; simp only [Lpo.permute, Lpo.rel, Rel.permute]
          have ⟨hx', hy'⟩ := (α.val.property.rel_dom hrel)
          have hx := Equiv.mem_union_symm_left hx'
          have hy := Equiv.mem_union_symm_left hy'
          refine ⟨hx, hy, ?_⟩
          rw [Equiv.union_symm_apply_left hx, Equiv.union_symm_apply_left hy] at hrel
          exact hrel
        · right; use eb φ; left
          have ⟨hx', hy'⟩ := (f φ).val.property.rel_dom hrel
          rw [← h φ]; simp only [Lpofin.permute, rel, Lpo.permute, Lpo.rel, Rel.permute]
          sorry
        · sorry
      · intro h; sorry
    · simp only [seq, seq_base, Lpo.permute, Lpo.lab, Lpo.nodes]
      ext x; by_cases hx : x ∈ α'.nodes ∪ ⋃ φ, (g φ).nodes
      · conv => lhs; exact dif_pos hx
        by_cases hx' : ∃ φ, x ∈ (g φ).nodes
        · conv => rhs; exact dif_pos hx'
          have ⟨φ, hx'⟩ := hx'
          refine (dif_pos ?_).trans ?_
          · use eb.symm φ; sorry
          · conv => rhs; arg 1; arg 2; exact (eb.apply_symm_apply _).symm
            conv => rhs; arg 1; exact (h _).symm
            simp only [permute, lab, Lpo.permute, Lpo.lab]
            sorry
      · conv => lhs; exact dif_neg hx
        symm; refine (dif_neg ?_).trans ?_
        · intro ⟨φ, hφ⟩; apply hx; right; exact Set.mem_iUnion.mpr ⟨_, hφ⟩
        · refine α'.val.property.lab_dom _ ?_
          intro hx'; apply hx; left; exact hx'
    · simp only [seq, seq_base, Lpo.permute, Lpo.form, Lpo.nodes]
      ext x v; constructor
      · intro ⟨hx, hform⟩
        rcases hx with hx | hx
        · rw [if_pos hx, Lpofin.form, ← he]
          use hx

          --conv => congrFun (if_pos hx) _


end Lpofin
