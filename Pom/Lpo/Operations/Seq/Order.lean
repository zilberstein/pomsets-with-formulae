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
        (α'.val.property.rel_dom hyx).2 hx'
    · have heq : ψ = ⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩ := by
        by_contra hne;
        refine Set.disjoint_left.mp ((g.property ψ).2.2 _ hne)
          ?_
          ((hext φ).nodes hx)
        rcases hyx with hyx | ⟨_, hx'⟩
        · exact ((g ψ).val.property.rel_dom hyx).2
        · exact hx'
      subst heq; rcases hyx with hyx | ⟨hy, hx'⟩
      · right; refine Set.mem_iUnion.mpr ⟨φ, ?_⟩;
        exact (hext φ).downcl x hx y hyx
      · left; have ⟨v, hsat⟩ := φ.val.sat
        have hy' : y ∈ α'.nodes := by
          refine (α'.val.property.form_dom _).mp ?_
          exact ⟨v, hy _ hsat⟩
        refine or_iff_not_imp_right.mp (hle.succ _ hy') ?_
        intro ⟨z, hz, hrel⟩
        have ⟨_, hstk, _⟩ := φ.property
        refine not_exists.mp (hstk _ hsat) ⟨z, hz.1, hz.2, ?_⟩ ?_
        · refine ⟨φ, le_refl _, hy.trans ?_⟩
          conv => rhs; exact hle.form z hz.1
          exact (α'.val.property.form z (hle.nodes hz.1)).2 _ hrel
        · refine (congrFun (hle.form _ hz.1) _).mpr ?_
          refine (α'.val.property.form _ (hle.nodes hz.1)).2 _ hrel _ ?_
          exact hy _ hsat

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
  · simp only [Lpo.nodes, seq, seq_base, nodes, Set.mem_union, Set.mem_iUnion] at *
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
        refine congrArg Subtype.val
          (not_not.mp (((g.property φ').2.2 ⟨ψ.val.up_cast hle, ?_⟩).mt ?_)).symm
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
        refine congrArg Subtype.val
          (not_not.mp (((g.property φ').2.2 ⟨φ.val.up_cast hle, ?_⟩).mt ?_)).symm
        · exact branches_monotone hle φ.property
        · exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes hx⟩
      have heq' : ψ.val.up_cast hle = φ'.val := by
        refine congrArg Subtype.val (not_not.mp (((g.property φ').2.2
          ⟨ψ.val.up_cast hle, branches_monotone hle ψ.property⟩).mt ?_)).symm
        exact Set.not_disjoint_iff.mpr ⟨y, hy', (hext _).nodes hy⟩
      have : φ = ψ := by
        apply Subtype.ext
        exact PathCond.up_cast_injective hle (heq.trans heq'.symm)
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
    · constructor
      · rintro ⟨φ, hform, -⟩
        have hxcopy := ((f φ).val.property.form_dom x).mp ⟨v, hform⟩
        exact False.elim (Set.disjoint_right.mp (f.property φ).2.1 hxcopy hx)
      · rintro ⟨φ, hform, -⟩
        have hxcopy := ((g φ).val.property.form_dom x).mp ⟨v, hform⟩
        exact False.elim (Set.disjoint_right.mp (g.property φ).2.1 hxcopy hx')
  · rcases Set.mem_iUnion.mp hx with ⟨φ, h⟩
    simp only [Lpofin.form, Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
    have hx₁ := Set.disjoint_right.mp (f.property φ).2.1 h
    have hx₂ := Set.disjoint_right.mp (g.property _).2.1 ((hext φ).nodes h)
    simp only [Lpofin.nodes, Lpo.nodes] at hx₁
    simp only [Lpofin.nodes, Lpo.nodes] at hx₂
    ext v
    change (α.form x v ∨ Form.sOr (fun ψ ↦ ((f ψ).form x).and ψ.val.toForm) v) ↔
      (α'.form x v ∨ Form.sOr (fun ψ ↦ ((g ψ).form x).and ψ.val.toForm) v)
    constructor
    · rintro (hα | ⟨ψ, hψ, hφ⟩)
      · exact False.elim (hx₁ ((α.val.property.form_dom x).mp ⟨v, hα⟩))
      · right
        have heq : φ = ψ := by
          by_contra hc
          have hd := (f.property φ).2.2 ψ hc
          have hx := Set.disjoint_left.mp hd h
          exact ((f ψ).val.property.form_dom x).mp.mt hx ⟨v, hψ⟩
        subst heq
        exact ⟨⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩,
          (congrFun ((hext _).form _ h) _).mp hψ,
          (congrFun (PathCond.cast_toForm (φ := φ.val) (hle := hle)) v).mpr hφ⟩
    · rintro (hα | ⟨ψ, hform, hψ⟩)
      · exact False.elim (hx₂ ((α'.val.property.form_dom x).mp ⟨v, hα⟩))
      · right
        have heq : ψ.val = φ.val.up_cast hle := by
          have hx' := ((g ψ).val.property.form_dom _).mp ⟨_, hform⟩
          refine congrArg Subtype.val (not_not.mp (((g.property ψ).2.2
            ⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩).mt ?_))
          exact Set.not_disjoint_iff.mpr ⟨x, hx', (hext _).nodes h⟩
        refine ⟨φ, ?_, ?_⟩
        · refine (congrFun ((hext φ).form _ h) _).mpr ?_
          have hsub : ⟨φ.val.up_cast hle, branches_monotone hle φ.property⟩ = ψ := by
            ext1
            exact heq.symm
          rw [hsub]
          exact hform
        · rw [← PathCond.cast_toForm (hle := hle), ← heq]
          exact hψ

lemma branch_missing_test_bot_predecessor (hle : α ≤ α') (φ : ↑α'.branches)
    (hmissing : ¬ φ.val.tests ⊆ α.tests) :
    ∃ z ∈ α.val.bots, φ.val.toForm ≤ α'.form z := by
  rw [Set.not_subset] at hmissing
  obtain ⟨x, hxtests, hxnot⟩ := hmissing
  have hform := φ.property.1 x hxtests
  have hxnode : x ∈ α'.nodes := tests_sub_nodes (φ.val.tests_valid hxtests)
  rcases hle.succ x hxnode with hx | ⟨z, hz, hrel⟩
  · refine ⟨x, ⟨hx, ?_⟩, hform⟩
    rcases isTest_of_le_or_bot hle (φ.val.tests_valid hxtests) with htest | hbot
    · exact False.elim (hxnot htest)
    · exact hbot
  · refine ⟨z, hz, hform.trans ?_⟩
    exact (α'.val.property.form z (hle.nodes hz.1)).2 x hrel

lemma branch_old_tests_bot_predecessor (hle : α ≤ α') (φ : PathCond α)
    (hφ : φ.up_cast hle ∈ α'.branches) (hnot : ¬ φ.toForm ≤ (α.stuck φ).not) :
    ∃ z ∈ α.val.bots, φ.toForm ≤ α'.form z := by
  have ⟨_, himp⟩ := not_forall.mp hnot
  have ⟨_, hnn⟩ := Classical.not_imp.mp himp
  have ⟨⟨z, hz, hbot, hr⟩, hform⟩ := not_not.mp hnn
  refine ⟨z, ⟨hz, hbot⟩, ?_⟩
  -- Construct `ψ'` to be a minimal reachability witness
  have ⟨ψ, hext, himp, hmin⟩ := hr.minimal hz
  by_cases heq : φ.tests = ψ.tests
  · have ⟨v, hsat⟩ := ψ.sat
    have heq :=
      pathCond_eq_of_tests_eq_of_common_sat heq (PathCond.toForm_antitone hext _ hsat) hsat
    rw [heq]; conv => rhs; exact (hle.form _ hz).symm
    exact himp
  · exfalso; have ⟨_, hstk, hmax⟩ := hφ
    have ⟨_, y, hy, hy'⟩ := ssubset_of_ne_of_subset heq hext.1 |> Set.ssubset_iff_exists.mp
    have hyz : α.rel y z := Or.resolve_left (hmin _ hy) hy'
    have hzy := (α.val.property.form _ (tests_sub_nodes <| ψ.tests_valid hy)).2 z hyz
    refine hmax hy' ?_ ?_ ?_
    · exact (ψ.up_cast hle).tests_valid hy
    · intro h; have ⟨v, hv⟩ := ψ.sat
      apply hstk v <| PathCond.toForm_antitone hext _ hv
      refine h v ?_
      exact himp _ hv |> hzy _ |> le_form hle _
    · refine ⟨ψ.up_cast hle, hext, ?_⟩
      exact himp.trans <| hzy.trans <| le_form hle

lemma branch_lift_or_bot_predecessor (hle : α ≤ α') (φ : ↑α'.branches) :
    (∃ ψ : ↑α.branches, ψ.val.up_cast hle = φ.val) ∨
      ∃ z ∈ α.val.bots, φ.val.toForm ≤ α'.form z := by
  by_cases htests : φ.val.tests ⊆ α.tests
  · let ψ : PathCond α := {
      tests := φ.val.tests
      truth := φ.val.truth
      tests_valid := htests
    }
    by_cases hψ : ψ ∈ α.branches
    · left; refine ⟨⟨ψ, hψ⟩, ?_⟩; rfl
    · right; apply branch_old_tests_bot_predecessor hle ψ φ.property
      intro hstuck; apply hψ
      rw [le_branches hle]
      exact ⟨φ.property, hstuck⟩
  · exact Or.inr (branch_missing_test_bot_predecessor hle φ htests)

lemma seq_monotone_succ (hle : α ≤ α') (hext : f.extends_to g hle)
    (x : Node) (hx : x ∈ (α'.seq β' g).nodes) :
    x ∈ (α.seq β f).nodes ∨ ∃ z ∈ (α.seq β f).val.bots, (α'.seq β' g).rel z x := by
  rcases hx with (hx | ⟨_, ⟨φ, rfl⟩, hx⟩)
  · rcases hle.succ _ hx with (hx' | ⟨z, hz, hrel⟩)
    · left; left; exact hx'
    · right; refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inl hrel⟩
      refine (dif_neg ?_).trans hz.2
      intro ⟨φ, hz'⟩
      exact Set.disjoint_left.mp (f.property φ).2.1 hz.1 hz'
  · rcases branch_lift_or_bot_predecessor hle φ with ⟨ψ, heq⟩ | ⟨z, hz, hform⟩
    · have hsub : ⟨ψ.val.up_cast hle, branches_monotone hle ψ.property⟩ = φ := by
        ext1
        exact heq
      subst hsub
      rcases (hext ψ).succ _ hx with hx' | ⟨z, hz, hrel⟩
      · left; right; exact ⟨(f ψ).nodes, ⟨ψ, rfl⟩, hx'⟩
      · right
        refine ⟨z, ⟨?_, ?_⟩, ?_⟩
        · right; exact Set.mem_iUnion.mpr ⟨ψ, hz.1⟩
        · refine (dif_pos ⟨ψ, hz.1⟩).trans ?_
          have {η} : (f η).lab z = ⊥ := by
            by_cases heq : η = ψ
            · subst heq; exact hz.2
            · refine (f η).val.property.lab_dom _ ?_
              exact Set.disjoint_right.mp ((f.property _).2.2 _ heq) hz.1
          exact this
        · right; exact ⟨⟨ψ.val.up_cast hle, branches_monotone hle ψ.property⟩, Or.inl hrel⟩
    · right; refine ⟨z, ⟨Or.inl hz.1, ?_⟩, Or.inr ⟨φ, Or.inr ⟨hform, hx⟩⟩⟩
      refine (dif_neg ?_).trans hz.2
      intro ⟨ψ, hz'⟩
      exact Set.disjoint_left.mp (f.property ψ).2.1 hz.1 hz'

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
