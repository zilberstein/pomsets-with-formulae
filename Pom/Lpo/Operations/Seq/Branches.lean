import Pom.Lpo.Order.FinApprox

namespace Lpofin

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
def extens (α : Lpofin l) : Set Node :=
  { x ∈ α.nodes | ¬ α.form x ≤ α.stuck }

lemma extens_finite (α : Lpofin l) : α.extens.Finite := by
  apply α.property.subset; intro x hx; exact hx.1

lemma extens_not_bot {α : Lpofin l} {x : Node} : x ∈ α.extens → α.lab x ≠ ⊥ := by
  intro h heq; apply h.2; intro v hform
  refine ⟨⟨x, ?_, heq⟩, hform⟩
  exact (α.val.property.form_dom x).mp ⟨v, hform⟩

lemma extens_monotone : @Monotone (Lpofin l) _ _ _ extens := by
  intro α β hle x ⟨hx, hstuck⟩
  refine ⟨hle.nodes hx, ?_⟩; intro hc
  refine hstuck (fun v hform ↦ stuck_antitone hle v (hc v ?_))
  simp only [form]; rw [← hle.form x hx]; exact hform

lemma le_extens {α β : Lpofin l} (hle : α ≤ β) :
    α.extens = { x ∈ β.extens | ¬ (β.form x ≤ α.stuck) } := by
  ext x; constructor
  · intro hx; refine ⟨extens_monotone hle hx, ?_⟩
    intro c; refine hx.2 (le_trans ?_ c)
    exact le_form hle
  · intro ⟨⟨hx, _⟩, hstk⟩
    rcases hle.succ _  hx with hxα | ⟨y, ⟨hy, hbot⟩, hyx⟩
    · refine ⟨hxα, ?_⟩
      intro c; refine hstk (le_of_eq_of_le (Eq.symm ?_) c)
      exact hle.form _ hxα
    · exfalso; refine hstk (((β.val.property.form y (hle.nodes hy)).2 _ hyx).trans ?_)
      refine le_of_eq_of_le (Eq.symm (hle.form _ hy)) ?_
      intro v hform; exact ⟨⟨y, hy, hbot⟩, hform⟩

def conj (α : Lpofin l) (S : Set Node) : Form Node :=
  Form.sAnd fun x : ↑S ↦ α.form x.val

def branches (α : Lpofin l) : Set (Form Node) :=
  α.conj ''
  { S : Set Node
  | S.Nonempty ∧
    S ⊆ α.extens ∧
    (α.conj S).sat ∧
    α.conj S ≤ α.stuck.not ∧
    ∀ T, S ⊂ T → T ⊆ α.extens → ¬ Form.sat (fun v ↦ ∀ x ∈ T, α.form x v)
  }

lemma branches_finite (α : Lpofin l) : α.branches.Finite := by
  refine Set.Finite.image _ ?_
  refine α.extens_finite.powerset.subset ?_
  intro s ⟨_, hsub, _⟩; exact hsub

lemma branches_monotone : @Monotone (Lpofin l) _ _ _ branches := by
  classical
  rintro α β hle φ ⟨S, ⟨hne, hsub, hsat, hstuck, hmax⟩, hφ⟩; subst hφ
  refine ⟨S, ⟨hne, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hsub (extens_monotone hle)
  · rcases hsat with ⟨v, hv⟩; use v; intro x
    refine (congrFun (hle.form x ?_) _).mp (hv x)
    exact hsub x.property |>.1
  · intro v hform hstuck'; refine hstuck v ?_ ?_
    · intro x; refine (congr_fun (hle.form x ?_) v).mpr (hform x)
      exact hsub x.property |>.1
    · exact stuck_antitone hle v hstuck'
  · intro T hST hT ⟨v, hc⟩; obtain ⟨x, hxT, hxS⟩ := Set.exists_of_ssubset hST
    have hform : α.conj S v := by
      intro y; refine (congrFun (hle.form _ ?_) _).mpr (hc _ ?_)
      · exact (hsub y.property).1
      · exact hST.subset y.property
    rcases hle.succ _ (hT hxT).1
      with hx | ⟨y, hy, hyx⟩
    · refine hmax (insert x S) (Set.ssubset_insert hxS) ?_ ?_
      · refine Set.insert_subset ⟨hx, ?_⟩ hsub
        · intro c; refine hstuck v hform ?_
          exact c v ((congrFun (hle.form _ hx) _).mpr (hc _ hxT))
      · use v; intro y hy; rcases Set.mem_insert_iff.mp hy with rfl | hy'
        · exact (congrFun (hle.form y hx) _).mpr (hc y hxT)
        · refine (congrFun (hle.form y ?_) _).mpr (hc y ?_)
          · exact (hsub hy').1
          · exact hST.subset hy'
    · refine hstuck v hform ⟨⟨y, hy⟩, ?_⟩
      refine (congrFun (hle.form _ hy.1) _).mpr ?_
      exact (β.val.property.form _ (hle.nodes hy.1)).2 _ hyx v (hc _ hxT)
  · ext1 v; refine forall_congr fun x ↦ ?_; ext; constructor
    · intro h; refine (congr_fun (hle.form x ?_) v).mpr h
      exact (hsub x.property).1
    · intro h; refine (congr_fun (hle.form x ?_) v).mp h
      exact (hsub x.property).1

lemma le_branches {α β : Lpofin l} (hle : α ≤ β) :
    α.branches = { φ ∈ β.branches | φ ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; constructor
    · exact branches_monotone hle h
    · rcases h with ⟨_, ⟨_, _, _, hstuck, _⟩, rfl⟩
      exact hstuck
  · rintro ⟨⟨S, ⟨hne, hsub, ⟨v, hsat⟩, _, hmax⟩, rfl⟩, hstuck⟩
    have hS x (hx : x ∈ S) : x ∈ α.nodes := by
      rcases hle.succ _ (hsub hx).1 with hxα | ⟨y, hbot, hyx⟩
      · exact hxα
      · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
        refine (congrFun (hle.form y hbot.1) _).mpr ?_
        refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
        exact hsat ⟨_, hx⟩
    refine ⟨S, ⟨hne, ?_, ⟨v, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro x hx; rw [le_extens hle]
      refine ⟨hsub hx, ?_⟩
      intro c; exact hstuck v hsat (c v (hsat ⟨x, hx⟩))
    · intro x; exact (congrFun (hle.form x (hS _ x.property)) _).mpr (hsat x)
    · refine le_trans ?_ hstuck; intro u hu x
      exact (congrFun (hle.form _ (hS _ x.property)) _).mp (hu x)
    · intro T hST hT ⟨u, hu⟩; refine hmax T hST ?_ ?_
      · exact le_trans hT (extens_monotone hle)
      · use u; intro x hx; refine (congrFun (hle.form _ ?_) _).mp (hu _ hx)
        exact (hT hx).1
    · ext1 u; refine forall_congr fun x ↦ ?_
      exact congrFun (hle.form x (hS _ x.property)) _

lemma branches_not_mutually_sat {α : Lpofin l} {φ ψ : Form Node}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ v ∧ ψ v) := by
  intro v ⟨h₁, h₂⟩
  obtain ⟨S, ⟨_, hsub, _, _, hmax⟩, rfl⟩ := hφ
  obtain ⟨T, ⟨_, hsub', _, _, hmax'⟩, rfl⟩ := hψ
  refine hmax (S ∪ T) ⟨Set.subset_union_left, ?_⟩ ?_ ?_
  · intro h; apply hneq; refine congrArg _ ?_; ext x; constructor
    · intro hx; by_contra ht; refine hmax' (insert x T) ?_ ?_ ?_
      · exact Set.ssubset_insert ht
      · intro y hy; rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact hsub hx
        · exact hsub' hy
      · use v; intro y hy; rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact h₁ ⟨y, hx⟩
        · exact h₂ ⟨y, hy⟩
    · intro hx; exact h (Set.subset_union_right hx)
  · rintro x (hx | hx)
    · exact hsub hx
    · exact hsub' hx
  · use v; rintro x (hx | hx)
    · exact h₁ ⟨x, hx⟩
    · exact h₂ ⟨x, hx⟩

end Lpofin
