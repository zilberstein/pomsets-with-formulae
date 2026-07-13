import Pom.Lpo.Operations.Seq.Branches
import Pom.Lpo.Operations.Seq.Equiv

namespace Lpofin

variable {l : Type} [PartialOrder l] [OrderBot l]

def CopyFn (α β : Lpofin l) : Type :=
  { f : ↑α.branches → Lpofin l //
    ∀ φ : ↑α.branches,
      f φ ≈ β ∧
      Disjoint α.nodes (f φ).nodes ∧
      ∀ ψ, φ ≠ ψ → Disjoint (f φ).nodes (f ψ).nodes
  }
instance {α β : Lpofin l} : FunLike (CopyFn α β) ↑α.branches (Lpofin l) where
  coe := Subtype.val
  coe_injective _ _ h := Subtype.ext h

def CopyFn_extends {α α' β β' : Lpofin l}
    (hle : α ≤ α') (f : CopyFn α β) (g : CopyFn α' β') :=
  ∀ φ : ↑α.branches, f φ ≤ g ⟨φ.val, branches_monotone hle φ.property⟩

open Classical in
noncomputable def seq_base (α β : Lpofin l) (f : CopyFn α β) : Lpo_base l := {
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
  form x :=
    if x ∈ α.nodes then α.form x else Form.sOr fun φ : ↑α.branches ↦ ((f φ).form x).and φ.val
}

lemma branch_implies_node {α : Lpofin l} {x : Node} :
    ∀ φ : ↑α.branches, φ ≤ α.form x → x ∈ α.val.nodes := by
  intro φ hle
  rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨hne, hsub, hsat, hstk, hmax⟩, heq⟩
  refine (α.val.property.form_dom x).mp ?_
  rcases hsat with ⟨v, hv⟩; use v; exact hle v ((congrFun heq _).mp hv)

lemma seq_nodes_finite {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).nodes.Finite := by
  refine Set.finite_union.mpr ⟨α.property, ?_⟩
  refine Set.finite_iUnion ?_; intro φ; exact (f φ).property

lemma seq_rel_valid {α β : Lpofin l} {f : CopyFn α β} :
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

lemma seq_valid(α β : Lpofin l) (f : CopyFn α β) :
    IsValidLpo (seq_base α β f) := by
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
    intro ⟨⟨φ, hφ⟩, hx⟩; exact hx' _ hφ hx
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

noncomputable def seq (α β : Lpofin l) (f : CopyFn α β) : Lpofin l := {
  val := {
    val := seq_base α β f
    property := seq_valid α β f
  }
  property := seq_nodes_finite
}

open Classical in
lemma seq_monotone {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
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


end Lpofin
