import Pom.Lpo.Operations.Seq

namespace Lpofin

variable {act test : Type} [PartialOrder act] [PartialOrder test]
  {α α' β β' : Lpofin (Label act test)}

namespace CopyFn

def extends_to (f : CopyFn α β) (g : CopyFn α' β') (hle : α ≤ α') :=
  ∀ φ : ↑α.branches, f φ ≤ g ⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩

end CopyFn

variable {f : CopyFn α β} {g : CopyFn α' β'}

lemma seq_monotone_nodes (hle : α ≤ α') (hext : f.extends_to g hle) :
    (seq α β f).nodes ⊆ (seq α' β' g).nodes := by
  rintro x (hx | ⟨_, ⟨⟨φ, hφ⟩, rfl⟩, hx⟩)
  · left; exact hle.nodes hx
  · right; have hφ' := branches_monotone hle hφ
    apply Set.mem_iUnion.mpr ?_
    exact ⟨⟨_, hφ'⟩, (hext ⟨φ, hφ⟩).nodes hx⟩

lemma seq_monotone_downcl (hle : α ≤ α') (hext : f.extends_to g hle) :
    (α'.seq β' g).rel.IsDownClosed (α.seq β f).nodes := by
  rintro x (hx | hx) y hyx
  · rcases hyx with (hyx | ⟨ψ, hyx | ⟨hx', hy⟩⟩)
    · left; exact hle.downcl x hx y hyx
    · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle.nodes hx)
        ((g ψ).val.property.rel_dom hyx).2
    · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle.nodes hx) hy
  · rcases Set.mem_iUnion.mp hx with ⟨φ, hx⟩
    rcases hyx with (hyx | ⟨ψ, hyx⟩)
    · exfalso; have hx' := (hext φ).nodes hx
      exact Set.disjoint_left.mp (g.property _).2.1
        (α'.val.property.rel_dom hyx).2
        hx'
    · by_cases heq : ψ = ⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩
      · subst heq; rcases hyx with hyx | ⟨hy, hx'⟩
        · right; refine Set.mem_iUnion.mpr ⟨φ, ?_⟩;
          exact (hext φ).downcl x hx y hyx
        · left
          have ⟨_, hstk, _⟩ := φ.property
          have ⟨v, hsat⟩ := φ.val.sat
          have hy' : y ∈ α'.nodes := by
            refine (α'.val.property.form_dom _).mp ?_
            exact ⟨v, hy _ hsat⟩
          refine or_iff_not_imp_right.mp (hle.succ _ hy') ?_
          intro ⟨z, hz, hrel⟩
          refine not_exists.mp (hstk _ hsat) ⟨z, hz.1, hz.2, ?_⟩ ?_
          · sorry
          · refine (congrFun (hle.form _ hz.1) _).mpr ?_
            refine (α'.val.property.form _ (hle.nodes hz.1)).2 _ hrel _ ?_
            exact hy _ hsat
      · exfalso
        refine Set.disjoint_left.mp ((g.property ψ).2.2 _ heq)
            ?_
            ((hext φ).nodes hx)
        rcases hyx with hyx | ⟨_, hx'⟩
        · exact ((g ψ).val.property.rel_dom hyx).2
        · exact hx'

lemma seq_monotone_rel (hle : α ≤ α') (hext : f.extends_to g hle)
    (x : Node) (hx : x ∈ (α.seq β f).nodes) (y : Node) (hy : y ∈ (α.seq β f).nodes) :
    (α.seq β f).rel x y = (α'.seq β' g).rel x y := by
  ext; constructor
  · rintro (hrel | ⟨φ, h⟩)
    · left; exact le_rel hle hrel
    · right; refine ⟨⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩, ?_⟩
      rcases h with (hrel | ⟨hform, hy'⟩)
      · left; exact le_rel (hext _) hrel
      · right; refine ⟨?_, (hext _).nodes hy'⟩
        refine le_of_le_of_eq hform (hle.form _ ?_)
        refine (α.val.property.form_dom _).mp ?_
        have ⟨v, hsat⟩ := φ.val.sat
        exact ⟨v, hform _ hsat⟩
  · simp only [Lpo.nodes, seq, seq_base, nodes, Set.mem_union, Set.mem_iUnion, Lpo.rel] at *
    obtain (hx | ⟨φ, hx⟩) := hx <;>
    obtain (hy | ⟨ψ, hy⟩) := hy <;>
    rintro (hrel | ⟨φ', hrel | ⟨hform, hy'⟩⟩)
    · left; exact (hle.rel _ hx _ hy).mpr hrel
    · exfalso; have hx' := ((g _).val.property.rel_dom hrel).1
      exact Set.disjoint_left.mp (g.property _).2.1 (hle.nodes hx) hx'
    · exfalso; exact Set.disjoint_left.mp (g.property _).2.1 (hle.nodes hy) hy'
    · exfalso; have hy' := (α'.val.property.rel_dom hrel).2
      exact Set.disjoint_left.mp (g.property _).2.1 hy' ((hext _).nodes hy)
    · exfalso; have hx' := ((g _).val.property.rel_dom hrel).1
      exact Set.disjoint_left.mp (g.property _).2.1 (hle.nodes hx) hx'
    · refine Or.inr ⟨ψ, Or.inr ⟨?_, hy⟩⟩
      refine le_of_eq_of_le ?_ (le_of_le_of_eq hform ?_)
      · conv => lhs; exact (PathCond.cast_toForm (hle := hle)).symm
        refine congrArg _ ?_
        refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2 ⟨ψ.val.up_cast hle, ?_⟩).mt ?_)).symm
        · exact branches_monotone hle ψ.property
        · exact Set.not_disjoint_iff.mpr ⟨y, hy', (hext _).nodes hy⟩
      · symm; exact hle.form _ hx
    · exfalso; have hx' := (α'.val.property.rel_dom hrel).1
      exact Set.disjoint_left.mp (g.property _).2.1 hx' ((hext _).nodes hx)
    · exfalso; have hy' := ((g _).val.property.rel_dom hrel).2
      exact Set.disjoint_left.mp (g.property _).2.1 (hle.nodes hy) hy'
    · exfalso; exact Set.disjoint_left.mp (g.property _).2.1 (hle.nodes hy) hy'
    · exfalso; have hx' := (α'.val.property.rel_dom hrel).1
      exact Set.disjoint_left.mp (g.property _).2.1 hx' ((hext _).nodes hx)
    · refine Or.inr ⟨φ, Or.inl ?_⟩
      have ⟨hx', hy'⟩ := (g _).val.property.rel_dom hrel
      have heq : φ.val.up_cast hle = φ'.val := by
        refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2 ⟨φ.val.up_cast hle, ?_⟩).mt ?_)).symm
        · exact branches_monotone hle φ.property
        · exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes hx⟩
      have : φ = ψ := by
        rcases φ' with ⟨φ', _⟩; subst heq; sorry
        -- refine not_not.mp (((g.property _).2.2 ⟨ψ.val.up_cast hle₁, ?_⟩).mt ?_)
        -- · exact branches_monotone hle₁ ψ.property
        -- · exact Set.not_disjoint_iff.mpr ⟨y, hy', (hext _).nodes hy⟩
      subst this; refine ((hext φ).rel _ hx _ hy).mpr ?_
      · have {h} : ⟨φ.val.up_cast hle, h⟩ = φ' := by ext1; exact heq
        rw [this]; exact hrel
    · exfalso; refine Set.disjoint_left.mp (g.property _).2.1 ?_ ((hext _).nodes hx)
      refine (α'.val.property.form_dom _).mp ?_
      have ⟨v, hsat⟩ := φ'.val.sat
      exact ⟨v, hform _ hsat⟩

lemma seq_monotone_lab (hle : α ≤ α') (hext : f.extends_to g hle) (x : Node) :
    (α.seq β f).lab x ≤ (α'.seq β' g).lab x := by
  by_cases hx : x ∈ (α.seq β f).nodes
  · rcases hx with hx | hx
    · have hx' : x ∈ α'.nodes := hle.nodes hx
      have hf : ¬ ∃ φ, x ∈ (f φ).nodes := by
        intro ⟨φ, hφ⟩; exact Set.disjoint_right.mp (f.property φ).2.1 hφ hx
      have hg : ¬ ∃ φ, x ∈ (g φ).nodes := by
        intro ⟨φ, hφ⟩; exact Set.disjoint_right.mp (g.property φ).2.1 hφ hx'
      simp only [Lpo.lab, Lpofin.lab, seq, seq_base, dif_neg hf, dif_neg hg]
      exact hle.lab x
    · simp only [Set.mem_iUnion] at hx
      have ⟨φ, hf⟩ := hx; have hg := (hext φ).nodes hf
      have hx' : ∃ φ, x ∈ (g φ).nodes := ⟨⟨φ.val.up_cast hle, _⟩, hg⟩
      simp only [Lpo.lab, Lpofin.lab, seq, seq_base, dif_pos hx, dif_pos hx']
      refine le_of_le_of_eq ((hext _).lab x) ?_
      refine congrArg₂ Lpofin.lab (congrArg _ ?_) rfl
      refine not_not.mp (((g.property _).2.2 _).mt (Set.not_disjoint_iff.mpr ?_))
      refine ⟨x, ?_, Exists.choose_spec hx'⟩
      exact (hext _).nodes (Exists.choose_spec hx)
  · exact le_of_eq_of_le ((α.seq β f).val.property.lab_dom _ hx) bot_le

lemma seq_monotone_form (hle : α ≤ α') (hext : f.extends_to g hle)
    (x : Node) (hx : x ∈ (α.seq β f).nodes) :
    (α.seq β f).form x = (α'.seq β' g).form x := by
  rcases hx with (hx | hx)
  · have hx' := hle.nodes hx
    ext v; refine or_congr ?_ ?_
    · apply iff_iff_eq.mpr; exact congrFun (hle.form _ hx) _
    · sorry
  · rcases Set.mem_iUnion.mp hx with ⟨φ, h⟩
    sorry
    -- simp only [Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
    -- have hx₁ := Set.disjoint_right.mp (f.property φ).2.1 h
    -- have hx₂ := Set.disjoint_right.mp (g.property _).2.1 ((hext φ).nodes h)
    -- simp only [Lpofin.nodes, Lpo.nodes] at hx₁
    -- simp only [Lpofin.nodes, Lpo.nodes] at hx₂
    -- simp only [hx₁, ↓reduceIte, hx₂]
    -- ext v; constructor
    -- · intro ⟨ψ, hψ, hφ⟩
    --   have heq : φ = ψ := by
    --     by_contra hc
    --     have hd := (f.property φ).2.2 ψ hc
    --     have hx := Set.disjoint_left.mp hd h
    --     exact ((f ψ).val.property.form_dom x).mp.mt hx ⟨v, hψ⟩
    --   subst heq; exact ⟨_, (congrFun ((hext _).form _ h) _).mp hψ, hφ⟩
    -- · intro ⟨ψ, hform, hψ⟩
    --   have heq : ψ.val = φ.val := by
    --     have hx' := ((g ψ).val.property.form_dom _).mp ⟨_, hform⟩
    --     refine congrArg Subtype.val (not_not.mp (((g.property ψ).2.2 ⟨φ, ?_⟩).mt ?_))
    --     · exact branches_monotone hle₁ φ.property
    --     · exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes h⟩
    --   refine ⟨φ, ?_, ?_⟩
    --   · refine (congrFun ?_ _).mpr hform
    --     refine ((hext φ).form _ h).trans ?_
    --     have {h} : ⟨φ.val, h⟩ = ψ := by ext1; exact heq.symm
    --     rw [this]; rfl
    --   · rw [← heq]; exact hψ

lemma seq_monotone_succ (hle : α ≤ α') (hext : f.extends_to g hle)
    (x : Node) (hx : x ∈ (α'.seq β' g).nodes) :
    x ∈ (α.seq β f).nodes ∨ ∃ z ∈ (α.seq β f).val.bots, (α'.seq β' g).rel z x := by
  simp only [Lpo.nodes, seq, seq_base, Set.mem_union, Set.mem_iUnion, Lpo.bots, Lpo.rel, Lpo.lab]
  rcases hx with (hx | ⟨φ, hx⟩)
  · rcases hle.succ _ hx with (hx' | ⟨z, hz, hrel⟩)
    · left; left; exact hx'
    · right; refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inl hrel⟩
      refine (dif_neg ?_).trans hz.2
      intro ⟨φ, hz'⟩
      exact Set.disjoint_left.mp (f.property φ).2.1 hz.1 hz'
  · sorry
    -- by_cases hφ : φ.val ∈ α.branches
    -- · rcases (hext ⟨_, hφ⟩).succ _ hx with (hx' | ⟨z, hz, hrel⟩)
    --   · left; right; exact ⟨_, hx'⟩
    --   · right; refine ⟨z, ⟨Or.inr ⟨_, hz.1⟩, ?_⟩, Or.inr ⟨φ, Or.inl hrel⟩⟩
    --     refine (dif_pos ⟨_, hz.1⟩).trans ?_
    --     have {ψ} : (f ψ).lab z = ⊥ := by
    --       by_cases heq : ψ = ⟨φ.val, hφ⟩
    --       · subst heq; exact hz.2
    --       · refine (f ψ).val.property.lab_dom _ ?_
    --         exact Set.disjoint_right.mp ((f.property _).2.2 _ heq) hz.1
    --     exact this
    -- · right
    --   have ⟨t, _, g, heq, ⟨himp, hstk⟩, hmax⟩ := φ.property
    --   rw [le_branches hle₁] at hφ
    --   have h := φ.property
    --   have ⟨v', hform⟩ := not_forall.mp ((Set.mem_inter h).mt hφ)
    --   have ⟨hv, hform⟩ := Classical.not_imp.mp hform
    --   have ⟨⟨z, hz⟩, hform⟩ := not_not.mp hform
    --   by_cases hz' : z ∈ t
    --   · refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inr ⟨φ, Or.inr ⟨?_, hx⟩⟩⟩
    --     · refine (dif_neg ?_).trans hz.2
    --       intro ⟨φ, hz'⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hz.1 hz'
    --     · rw [heq]; intro v hv; exact himp _ hv ⟨_, hz'⟩
    --   · exfalso; sorry
        --  rw [heq] at hv; refine hstk _ hv ?_
        -- have : z ∉ α'.tests := by
        --   intro hc; refine hmax hz' hc ⟨?_, ?_, ?_⟩ (b := true)
        --   · refine ⟨v' ∪ {z}, ?_⟩; intro y; by_cases heq : y = z
        --     · simp only [node_lit, heq, ↓reduceDIte, ↓reduceIte, Set.union_singleton]
        --       exact Set.mem_insert _ _
        --     · have hy := Set.mem_of_mem_insert_of_ne y.property heq
        --       have hform := hv ⟨y.val, hy⟩
        --       simp only [node_lit, heq, ↓reduceDIte, Set.union_singleton]
        --       by_cases h : g ⟨↑y, hy⟩ = true
        --       · conv => exact congrFun (if_pos h) _
        --         conv at hform => exact congrFun (if_pos h) _
        --         exact Set.mem_insert_of_mem _ hform
        --       · conv => exact congrFun (if_neg h) _
        --         conv at hform => exact congrFun (if_neg h) _
        --         intro hc; apply hform; exact Set.mem_of_mem_insert_of_ne hc heq
        --   · sorry
        --   · sorry
        -- have := (hmax hz').mt
        -- have := not_and.mp this; rw [Decidable.not_not] at this
        -- have := this (hle₁.nodes hz.1)
        -- exact this _ ((congrFun (hle₁.form _ hz.1) _).mp hform)

open Classical in
lemma seq_monotone (hle : α ≤ α') (hext : f.extends_to g hle) :
    seq α β f ≤ seq α' β' g := by
  constructor
  · exact seq_monotone_nodes hle hext
  · exact seq_monotone_downcl hle hext
  · exact seq_monotone_rel hle hext
  · exact seq_monotone_lab hle hext
  · exact seq_monotone_form hle hext
  · exact seq_monotone_succ hle hext

end Lpofin
