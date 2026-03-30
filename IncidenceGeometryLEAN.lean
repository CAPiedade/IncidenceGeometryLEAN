import Mathlib
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
universe u v w

/-structure IncidenceSystem (X : Type u) (I : Type v) where
  points : Set X
  types : Set I
  type_func : X → I
  incidence : X → X → Prop
  incidence_reflexive : Reflexive incidence
  incidence_symmetric : Symmetric incidence
  incidence_type_condition : ∀ {x y : X}, x ∈ points → y ∈ points→ incidence x y ↔ type_func x ≠ type_func y ∨ x=y

 /--Create a coloring  -/
def IncidenceSystemGraph (S : IncidenceSystem X I) : SimpleGraph X where
  Adj a b := a ≠ b ∧ (S.incidence a b ∨ S.incidence b a)


def FlagOfIncidenceSystem {X I} (F : Set X) (S : IncidenceSystem X I) :=  {x | x ∈ F ∧ x ∈ S.points}



def ResidueOfIncidenceSystem (S : IncidenceSystem X I) (Fl : FlagOfIncidenceSystem F S) : IncidenceSystem X I where
  points := {x | x ∈ S.points ∧ ∀ y ∈ F, S.incidence x y ∧ x ≠ y}
  types := {S.type_func x | x ∈ F}
  type_func := S.type_func
  incidence := S.incidence
  incidence_reflexive := S.incidence_reflexive
  incidence_symmetric := S.incidence_symmetric
  incidence_type_condition := S.incidence_type_condition
-/

structure IncidenceSystem (X : Type u) (I : Type v) where
  points : Set X
  types : Set I
  type_func : X → I
  incidence : X → X → Prop
  incidence_reflexive : Reflexive incidence
  incidence_symmetric : Symmetric incidence
  incidence_type_condition :
    ∀ x y : X, x ∈ points → y ∈ points → (incidence x y ↔ (type_func x ≠ type_func y ∨ x = y))

variable {X : Type u} {I : Type v}

@[ext] theorem IncidenceSystem.ext {S T : IncidenceSystem X I}
    (hpoints : S.points = T.points)
    (htypes : S.types = T.types)
    (htype_func : S.type_func = T.type_func)
    (hincidence : S.incidence = T.incidence) : S = T := by
  cases S
  cases T
  cases hpoints
  cases htypes
  cases htype_func
  cases hincidence
  simp

-- elements of X \ points are singletons in this graph
def IncidenceGraph (S : IncidenceSystem X I) : SimpleGraph X where
  Adj a b := a ≠ b ∧ a ∈ S.points ∧ b ∈ S.points ∧ S.incidence a b
  symm a b := by                      -- so symmetry requires a proof
    intro h
    rcases h with ⟨hne, ha, hb, hab⟩
    exact ⟨Ne.symm hne, hb, ha, S.incidence_symmetric hab⟩

def IncidenceGraphColoring {S : IncidenceSystem X I} :
    (IncidenceGraph S).Coloring I :=
  SimpleGraph.Coloring.mk S.type_func <| by
    intro a b hab
    rcases hab with ⟨hne, ha, hb, hab⟩
    have hcond : S.type_func a ≠ S.type_func b ∨ a = b :=
      (S.incidence_type_condition a b ha hb).1 hab
    rcases hcond with hneType | heq
    · exact hneType
    · exact (hne heq).elim

structure ColoredGraph (X : Type u) (I : Type v) where
  graph : SimpleGraph X
  coloring : graph.Coloring I

instance : Coe (IncidenceSystem X I) (ColoredGraph X I) where
  coe := fun S => ⟨IncidenceGraph S, IncidenceGraphColoring ⟩


/- A flag is a set of pairwise incident elements -/
def IsFlag (F : Set X) (S : IncidenceSystem X I) : Prop :=
  F ⊆ S.points ∧ ∀ x ∈ F, ∀ y ∈ F, S.incidence x y

theorem IsFlag_iff (S : IncidenceSystem X I) (F : Set X) (hF : F ⊆ S.points) :
    IsFlag F S ↔ (IncidenceGraph S).IsClique F := by
  constructor
  · intro hflag a ha b hb hne
    exact ⟨hne, hF ha, hF hb, hflag.2 a ha b hb⟩
  · intro h
    refine ⟨hF, ?_⟩
    intro x hx y hy
    match Classical.em <| x = y with
    | Or.inl heq =>
        subst heq
        exact S.incidence_reflexive x
    | Or.inr hne => exact (h hx hy hne).2.2.2

def IncidenceSystemOfColoredGraph (G : SimpleGraph X) (c : G.Coloring I)
    (hcomplete : ∀ x y : X, c x ≠ c y → x = y ∨ G.Adj x y) : -- CHANGE CONDITION!
    IncidenceSystem X I where
  points := Set.univ
  types := Set.univ
  type_func := c
  incidence x y := x = y ∨ G.Adj x y
  incidence_reflexive := by
    intro x
    exact Or.inl rfl
  incidence_symmetric := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.symm
    · exact Or.inr (G.symm hxy)
  incidence_type_condition := by
    intro x y _ _
    constructor
    · intro hxy
      rcases hxy with hxy | hxy
      · exact Or.inr hxy
      · exact Or.inl (c.valid hxy)
    · intro hxy
      rcases hxy with hxy | hxy
      · exact hcomplete x y hxy
      · exact Or.inl hxy


def ResidueOfIncidenceSystem (F : Set X) (S : IncidenceSystem X I) (hF : IsFlag F S) :
    IncidenceSystem X I where
  points := {x | x ∈ S.points \ F ∧ ∀ y ∈ F, S.incidence x y}
  types := Set.image S.type_func {x | x ∈ S.points \ F ∧ ∀ y ∈ F, S.incidence x y}
  type_func := S.type_func
  incidence := S.incidence
  incidence_reflexive := S.incidence_reflexive
  incidence_symmetric := S.incidence_symmetric
  incidence_type_condition := by
    intro x y
    match Classical.em <| x = y with
    | Or.inl h =>
        subst h
        simp [S.incidence_reflexive x]
    | Or.inr h =>
        simp only [Set.mem_diff, Set.mem_setOf_eq, ne_eq, h, or_false, and_imp]
        intro hx _ _ hy _ _
        simp [h, S.incidence_type_condition x y hx hy]


theorem ResidueOfIncidenceSystem_points (F : Set X) (S : IncidenceSystem X I) (hF : IsFlag F S) :
    (ResidueOfIncidenceSystem F S hF).points ⊆ S.points := by
  simp only [ResidueOfIncidenceSystem, Set.mem_setOf_eq, Set.mem_diff, true_and, and_imp]
  intro x hx
  simp only [Set.mem_setOf_eq,] at hx
  exact hx.1.1

theorem FlagOfResidue_FlagOfOriginal (F G: Set X) (S : IncidenceSystem X I) (hF : IsFlag F S):
    IsFlag G (ResidueOfIncidenceSystem F S hF) → IsFlag G S := by
  simp only [IsFlag, ResidueOfIncidenceSystem, and_imp]
  intro hG_points hG_incidence
  exact ⟨Set.Subset.trans hG_points (ResidueOfIncidenceSystem_points F S hF),
  fun x hx y hy => hG_incidence x hx y hy⟩

theorem FlagOfResidue_iff_BigFlagOfIncidenceSystem (S : IncidenceSystem X I) (F G: Set X)
(hF : IsFlag F S) (hG : G ⊆ (ResidueOfIncidenceSystem F S hF).points):
  IsFlag G (ResidueOfIncidenceSystem F S hF) ↔ IsFlag (F ∪ G) S := by
  simp only [IsFlag, ResidueOfIncidenceSystem, Set.mem_diff, Set.union_subset_iff]
  apply Iff.intro
  · intro direct_imp
    obtain ⟨left, right⟩ := direct_imp
    apply And.intro
    · constructor
      · intro x hx
        exact hF.1 hx
      · intro y hy
        let k := left hy
        simp only [Set.mem_setOf_eq, Set.mem_diff] at k
        exact k.1.1
    · intro x hx y hy
      simp only [Set.mem_union] at hx hy
      match hx,hy with
      | Or.inl hx', Or.inl hy' => exact hF.2 x hx' y hy'
      | Or.inl hx', Or.inr hy' =>
        let k := left hy'
        simp only [Set.mem_setOf_eq, Set.mem_diff] at k
        exact S.incidence_symmetric (k.2 x hx')
      | Or.inr hx', Or.inl hy' =>
        let k := left hx'
        simp only [Set.mem_setOf_eq, Set.mem_diff] at k
        exact k.2 y hy'
      | Or.inr hx', Or.inr hy' => exact right x hx' y hy'
  · intro reverse_imp
    obtain ⟨left, right⟩ := reverse_imp
    apply And.intro
    · intro x hx
      let k := hG hx
      simp only [ResidueOfIncidenceSystem, Set.mem_setOf_eq, Set.mem_diff] at k
      exact k
    · intro x hx y hy
      exact right x (Or.inr hx) y (Or.inr hy)

theorem Residue_Of_Flag_G_Of_Residue_Over_F_is_Residue_F_cup_G (S : IncidenceSystem X I) (F G: Set X)
(hF : IsFlag F S) (hG : IsFlag G (ResidueOfIncidenceSystem F S hF)):
  ResidueOfIncidenceSystem G (ResidueOfIncidenceSystem F S hF) hG =
    ResidueOfIncidenceSystem (F ∪ G) S
      ((FlagOfResidue_iff_BigFlagOfIncidenceSystem S F G hF hG.1).1 hG) := by
  have hpoints :
      (ResidueOfIncidenceSystem G (ResidueOfIncidenceSystem F S hF) hG).points =
        (ResidueOfIncidenceSystem (F ∪ G) S
          ((FlagOfResidue_iff_BigFlagOfIncidenceSystem S F G hF hG.1).1 hG)).points := by
    ext x
    simp only [ResidueOfIncidenceSystem, Set.mem_setOf_eq, Set.mem_diff, Set.mem_union,
      and_assoc, and_left_comm, and_comm]
    constructor
    · intro hx
      rcases hx with ⟨hxF, hxG, hxP, hincF, hincG⟩
      refine ⟨?_, hxP, ?_⟩
      · intro hxFG
        rcases hxFG with hxF' | hxG'
        · exact hxF hxF'
        · exact hxG hxG'
      · intro y hy
        rcases hy with hy | hy
        · exact hincF y hy
        · exact hincG y hy
    · intro hx
      rcases hx with ⟨hxFG, hxP, hincFG⟩
      refine ⟨?_, ?_, hxP, ?_, ?_⟩
      · intro hxF
        exact hxFG (Or.inl hxF)
      · intro hxG
        exact hxFG (Or.inr hxG)
      · intro y hy
        exact hincFG y (Or.inl hy)
      · intro y hy
        exact hincFG y (Or.inr hy)
  refine IncidenceSystem.ext hpoints ?_ rfl rfl
  simpa only [ResidueOfIncidenceSystem] using congrArg (Set.image S.type_func) hpoints



def IncSys_IsConnected (S : IncidenceSystem X I) : Prop :=
  SimpleGraph.Connected (IncidenceGraph S)

def TypeOfFlag (F : Set X) (S : IncidenceSystem X I) : Set I :=
  Set.image S.type_func F

def IsChamber (F : Set X) (S : IncidenceSystem X I) : Prop :=
  IsFlag F S ∧ (TypeOfFlag F S) = Set.image S.type_func S.points


def IncSys_IsResiduallyConnected (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) →
  IncSys_IsConnected (ResidueOfIncidenceSystem F S hF)
  ∧ Set.ncard (ResidueOfIncidenceSystem F S hF).types ≥ 2


def IsGeometry (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → ∃ C : Set X, C ⊆ S.points ∧ IsChamber C S ∧ F ⊆ C


theorem If_Gamma_Geometry_Then_Gamma_F_Geometry_Over_I_minus_tF (S : IncidenceSystem X I) (F : Set X)
(hF : IsFlag F S) :
  IsGeometry S  → IsGeometry (ResidueOfIncidenceSystem F S hF) ∧
    (ResidueOfIncidenceSystem F S hF).types =
      Set.image S.type_func S.points \ {S.type_func x | x ∈ F} := by
  intro hGeom
  let R := ResidueOfIncidenceSystem F S hF
  constructor
  · intro G hGsub hG
    have hFGflag : IsFlag (F ∪ G) S :=
      (FlagOfResidue_iff_BigFlagOfIncidenceSystem S F G hF hGsub).1 hG
    obtain ⟨C, hCsub, hCch, hFGsub⟩ := hGeom (F ∪ G) (by
      intro x hx
      rcases hx with hx | hx
      · exact hF.1 hx
      · exact (hGsub hx).1.1) hFGflag
    let D : Set X := C \ F
    have hDsubR : D ⊆ R.points := by
      intro x hxD
      rcases hxD with ⟨hxC, hxnotF⟩
      refine ⟨⟨hCsub hxC, hxnotF⟩, ?_⟩
      intro y hyF
      exact hCch.1.2 x hxC y (hFGsub (Or.inl hyF))
    have hDflagR : IsFlag D R := by
      constructor
      · exact hDsubR
      · intro x hxD y hyD
        exact hCch.1.2 x hxD.1 y hyD.1
    have hDchamberR : IsChamber D R := by
      refine ⟨hDflagR, ?_⟩
      ext i
      constructor
      · intro hi
        rcases hi with ⟨x, hxD, hxi⟩
        refine ⟨x, hDsubR hxD, hxi⟩
      · intro hi
        rcases hi with ⟨x, hxR, hxi⟩
        have hixS : i ∈ Set.image S.type_func S.points := ⟨x, hxR.1.1, hxi⟩
        have hixC : i ∈ TypeOfFlag C S := by
          rw [hCch.2]
          exact hixS
        rcases hixC with ⟨z, hzC, hzi⟩
        have hznotF : z ∉ F := by
          intro hzF
          have hxincz : S.incidence x z := hxR.2 z hzF
          have hzP : z ∈ S.points := hF.1 hzF
          have hxyOr : S.type_func x ≠ S.type_func z ∨ x = z :=
            (S.incidence_type_condition x z hxR.1.1 hzP).1 hxincz
          have hxz : x = z := by
            rcases hxyOr with hneq | hxz
            · exfalso
              exact hneq (by simpa [hxi, hzi])
            · exact hxz
          exact hxR.1.2 (hxz ▸ hzF)
        exact ⟨z, ⟨hzC, hznotF⟩, hzi⟩
    refine ⟨D, hDsubR, hDchamberR, ?_⟩
    intro x hxGx
    have hxR : x ∈ R.points := hGsub hxGx
    have hxC : x ∈ C := hFGsub (Or.inr hxGx)
    exact ⟨hxC, hxR.1.2⟩
  · ext i
    constructor
    · intro hi
      rcases hi with ⟨x, hxR, hxi⟩
      refine ⟨⟨x, hxR.1.1, hxi⟩, ?_⟩
      intro hiF
      rcases hiF with ⟨y, hyF, hyi⟩
      have hxyInc : S.incidence x y := hxR.2 y hyF
      have hyP : y ∈ S.points := hF.1 hyF
      have hxyOr : S.type_func x ≠ S.type_func y ∨ x = y :=
        (S.incidence_type_condition x y hxR.1.1 hyP).1 hxyInc
      have hxy : x = y := by
        rcases hxyOr with hneq | hxy
        · exfalso
          exact hneq (by simp [hxi, hyi])
        · exact hxy
      exact hxR.1.2 (hxy ▸ hyF)
    · intro hi
      rcases hi with ⟨hiS, hiNotF⟩
      obtain ⟨C, hCsub, hCch, hFsubC⟩ := hGeom F hF.1 hF
      have hiC : i ∈ TypeOfFlag C S := by
        rw [hCch.2]
        exact hiS
      rcases hiC with ⟨z, hzC, hzi⟩
      have hznotF : z ∉ F := by
        intro hzF
        exact hiNotF ⟨z, hzF, hzi⟩
      have hzR : z ∈ R.points := by
        refine ⟨⟨hCsub hzC, hznotF⟩, ?_⟩
        intro y hyF
        exact hCch.1.2 z hzC y (hFsubC hyF)
      exact ⟨z, hzR, hzi⟩

def IsFirm (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points ≥ 2

def IsThin (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points = 2

def IsThick (S : IncidenceSystem X I) : Prop :=
  ∀ F : Set X, F ⊆ S.points → (hF : IsFlag F S) → IsGeometry S →
  Set.ncard (ResidueOfIncidenceSystem F S hF).types = 1 →
  Set.ncard (ResidueOfIncidenceSystem F S hF).points > 2

def IsHypertope (S : IncidenceSystem X I) : Prop :=
IsGeometry S ∧  IsThin S ∧ IncSys_IsResiduallyConnected S



def IsWeakHomomorphism (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  ∀ x ∈ S.points, α x ∈ T.points ∧
  ∀ x ∈ S.points, ∀ y ∈ S.points, ((S.incidence x y → T.incidence (α x) (α y)) ∧
  (S.type_func x = S.type_func y ↔ T.type_func (α x) = T.type_func (α y)))

def IsHomomorphism (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsWeakHomomorphism S T α ∧ S.types = T.types ∧
  ∀ x ∈ S.points, S.type_func x = T.type_func (α x)

def IsCorrelation [Nonempty X] (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsWeakHomomorphism S T α ∧ Function.Bijective α ∧ IsWeakHomomorphism T S (Function.invFun α)

def IsIsomorphism [Nonempty X] (S T : IncidenceSystem X I) (α : X → X) : Prop :=
  IsHomomorphism S T α ∧ IsCorrelation S T α

def IsAutomorphism [Nonempty X] (S : IncidenceSystem X I) (α : X → X) : Prop :=
  IsIsomorphism S S α

def IsAutoCorrelation [Nonempty X] (S : IncidenceSystem X I) (α : X → X) : Prop :=
  IsCorrelation S S α

structure WeakHomomorphism [Nonempty X] (S T : IncidenceSystem X I) where
  Fun : X → X
  isWeakHom : IsWeakHomomorphism S T Fun

structure Homomorphism [Nonempty X] (S T : IncidenceSystem X I) extends WeakHomomorphism S T where
  isHom : IsHomomorphism S T Fun
  isWeakHom := by exact isHom.1

structure Correlation [Nonempty X] (S T : IncidenceSystem X I) extends WeakHomomorphism S T where
  isCorr : IsCorrelation S T Fun
  isWeakHom := by exact isCorr.1

structure Isomorphism [Nonempty X] (S T : IncidenceSystem X I) extends Homomorphism S T where
  isIso : IsIsomorphism S T Fun
  isHom:= by exact isIso.1

structure Automorphism [Nonempty X] (S : IncidenceSystem X I) extends Isomorphism S S where
  isAuto : IsAutomorphism S Fun := isIso

structure AutoCorrelation [Nonempty X] (S : IncidenceSystem X I) extends Correlation S S where
  isAutoCorr : IsAutoCorrelation S Fun := isCorr

def composeWeakHomomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : WeakHomomorphism S T) (β : WeakHomomorphism T U) :
    WeakHomomorphism S U :=
{ Fun := β.Fun ∘ α.Fun
  isWeakHom := by
    intro x hx
    have hαx : α.Fun x ∈ T.points := (α.isWeakHom x hx).1
    have hβx : β.Fun (α.Fun x) ∈ U.points := (β.isWeakHom (α.Fun x) hαx).1
    constructor
    · exact hβx
    · intro x hx y hy
      have hαx : α.Fun x ∈ T.points := (α.isWeakHom x hx).1
      have hαy : α.Fun y ∈ T.points := (α.isWeakHom y hy).1
      have hαxy :
          (S.incidence x y → T.incidence (α.Fun x) (α.Fun y)) ∧
          (S.type_func x = S.type_func y ↔
            T.type_func (α.Fun x) = T.type_func (α.Fun y)) :=
        (α.isWeakHom x hx).2 x hx y hy
      have hβxy :
          (T.incidence (α.Fun x) (α.Fun y) →
            U.incidence (β.Fun (α.Fun x)) (β.Fun (α.Fun y))) ∧
          (T.type_func (α.Fun x) = T.type_func (α.Fun y) ↔
            U.type_func (β.Fun (α.Fun x)) = U.type_func (β.Fun (α.Fun y))) :=
        (β.isWeakHom (α.Fun x) hαx).2 (α.Fun x) hαx (α.Fun y) hαy
      refine ⟨?_, ?_⟩
      · intro hS
        exact hβxy.1 (hαxy.1 hS)
      · exact Iff.trans hαxy.2 hβxy.2
}

def composeHomomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Homomorphism S T) (β : Homomorphism T U) :
    Homomorphism S U :=
{ toWeakHomomorphism := composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism
  isHom := by
    constructor
    · exact (composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism).isWeakHom
    · constructor
      · calc S.types = T.types := α.isHom.2.1
          _ = U.types := β.isHom.2.1
      · intro x hx
        calc S.type_func x = T.type_func (α.Fun x) := α.isHom.2.2 x hx
          _ = U.type_func (β.Fun (α.Fun x)) := β.isHom.2.2 (α.Fun x) ((α.isWeakHom x hx).1)
}

def composeCorrelation [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Correlation S T) (β : Correlation T U) :
    Correlation S U :=
{ toWeakHomomorphism := composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism
  isCorr := by
    constructor
    · exact (composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism).isWeakHom
    · constructor
      · simpa [composeWeakHomomorphism, Function.comp] using
          (Function.Bijective.comp β.isCorr.2.1 α.isCorr.2.1)
      · let αinv : WeakHomomorphism T S :=
          { Fun := Function.invFun α.Fun
            isWeakHom := α.isCorr.2.2 }
        let βinv : WeakHomomorphism U T :=
          { Fun := Function.invFun β.Fun
            isWeakHom := β.isCorr.2.2 }
        have hinvEq :
            Function.invFun (β.Fun ∘ α.Fun) =
              Function.invFun α.Fun ∘ Function.invFun β.Fun := by
          apply Function.invFun_eq_of_injective_of_rightInverse
          · exact (Function.Bijective.comp β.isCorr.2.1 α.isCorr.2.1).1
          · intro x
            dsimp [Function.comp]
            rw [Function.rightInverse_invFun α.isCorr.2.1.2,
              Function.rightInverse_invFun β.isCorr.2.1.2]
        have hinvEq' :
            Function.invFun
                (composeWeakHomomorphism α.toWeakHomomorphism β.toWeakHomomorphism).Fun =
              Function.invFun α.Fun ∘ Function.invFun β.Fun := by
          simpa [composeWeakHomomorphism] using hinvEq
        simpa [hinvEq'] using
          (composeWeakHomomorphism βinv αinv).isWeakHom
}

def composeIsomorphism [Nonempty X]
    {S T U : IncidenceSystem X I}
    (α : Isomorphism S T) (β : Isomorphism T U) :
    Isomorphism S U :=
{ toHomomorphism := composeHomomorphism α.toHomomorphism β.toHomomorphism
  isIso := by
    let αcorr : Correlation S T :=
      { toWeakHomomorphism := α.toWeakHomomorphism
        isCorr := α.isIso.2 }
    let βcorr : Correlation T U :=
      { toWeakHomomorphism := β.toWeakHomomorphism
        isCorr := β.isIso.2 }
    constructor
    · exact (composeHomomorphism α.toHomomorphism β.toHomomorphism).isHom
    · simpa [composeHomomorphism, composeWeakHomomorphism, Function.comp] using
        (composeCorrelation αcorr βcorr).isCorr
}

def composeAutomorphism [Nonempty X]
    {S : IncidenceSystem X I}
    (α β : Automorphism S) :
    Automorphism S :=
{ toIsomorphism := composeIsomorphism α.toIsomorphism β.toIsomorphism
  isAuto := (composeIsomorphism α.toIsomorphism β.toIsomorphism).isIso
}

def composeAutoCorrelation [Nonempty X]
    {S : IncidenceSystem X I}
    (α β : AutoCorrelation S) :
    AutoCorrelation S :=
{ toCorrelation := composeCorrelation α.toCorrelation β.toCorrelation
  isAutoCorr := (composeCorrelation α.toCorrelation β.toCorrelation).isCorr
}

@[ext] theorem WeakHomomorphism.ext [Nonempty X] {S T : IncidenceSystem X I}
    {α β : WeakHomomorphism S T} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aFun aWeak =>
    cases β with
    | mk bFun bWeak =>
      dsimp at hFun
      cases hFun
      simp

@[ext] theorem Homomorphism.ext [Nonempty X] {S T : IncidenceSystem X I}
    {α β : Homomorphism S T} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aWeak aHom =>
    cases β with
    | mk bWeak bHom =>
      have hWeak : aWeak = bWeak := WeakHomomorphism.ext hFun
      cases hWeak
      simp

@[ext] theorem Isomorphism.ext [Nonempty X] {S T : IncidenceSystem X I}
    {α β : Isomorphism S T} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aHom aIso =>
    cases β with
    | mk bHom bIso =>
      have hHom : aHom = bHom := Homomorphism.ext hFun
      cases hHom
      simp

@[ext] theorem Correlation.ext [Nonempty X] {S T : IncidenceSystem X I}
    {α β : Correlation S T} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aWeak aCorr =>
    cases β with
    | mk bWeak bCorr =>
      have hWeak : aWeak = bWeak := WeakHomomorphism.ext hFun
      cases hWeak
      simp

@[ext] theorem Automorphism.ext [Nonempty X] {S : IncidenceSystem X I}
    {α β : Automorphism S} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aIso aAuto =>
    cases β with
    | mk bIso bAuto =>
      have hIso : aIso = bIso := Isomorphism.ext hFun
      cases hIso
      simp

@[ext] theorem AutoCorrelation.ext [Nonempty X] {S : IncidenceSystem X I}
    {α β : AutoCorrelation S} (hFun : α.Fun = β.Fun) : α = β := by
  cases α with
  | mk aCorr aAutoCorr =>
    cases β with
    | mk bCorr bAutoCorr =>
      have hCorr : aCorr = bCorr := Correlation.ext hFun
      cases hCorr
      simp

def idIsomorphism [Nonempty X] (S : IncidenceSystem X I) : Isomorphism S S := by
  have hWeakId : IsWeakHomomorphism S S id := by
    intro x hx
    constructor
    · simpa using hx
    · intro x hx y hy
      refine ⟨?_, ?_⟩
      · intro hxy
        simpa using hxy
      · simp
  have hHomId : IsHomomorphism S S id := by
    constructor
    · exact hWeakId
    · constructor
      · rfl
      · intro x hx
        rfl
  have hInvId : Function.invFun (id : X → X) = id := by
    apply Function.invFun_eq_of_injective_of_rightInverse
    · intro a b h
      exact h
    · intro x
      rfl
  have hCorrId : IsCorrelation S S id := by
    constructor
    · exact hWeakId
    · constructor
      · exact Function.bijective_id
      · simpa [hInvId] using hWeakId
  exact
    { toHomomorphism :=
        { toWeakHomomorphism :=
            { Fun := id
              isWeakHom := hWeakId }
          isHom := hHomId }
      isIso := ⟨hHomId, hCorrId⟩ }

noncomputable def invIsomorphism [Nonempty X] {S : IncidenceSystem X I}
    (α : Automorphism S) : Isomorphism S S := by
  let f := α.Fun
  have hHom : IsHomomorphism S S f := α.isAuto.1
  have hCorr : IsCorrelation S S f := α.isAuto.2
  have hWeak : IsWeakHomomorphism S S f := hCorr.1
  have hBij : Function.Bijective f := hCorr.2.1
  have hInvWeak : IsWeakHomomorphism S S (Function.invFun f) := hCorr.2.2
  have hInvHom : IsHomomorphism S S (Function.invFun f) := by
    constructor
    · exact hInvWeak
    · constructor
      · rfl
      · intro x hx
        have hx' : Function.invFun f x ∈ S.points := (hInvWeak x hx).1
        have htype : S.type_func (Function.invFun f x) = S.type_func (f (Function.invFun f x)) :=
          hHom.2.2 (Function.invFun f x) hx'
        simpa [Function.rightInverse_invFun hBij.2 x] using htype.symm
  have hInvBij : Function.Bijective (Function.invFun f) := by
    refine ⟨?_, ?_⟩
    · exact (Function.rightInverse_invFun hBij.2).injective
    · exact Function.invFun_surjective hBij.1
  have hInvInvEq : Function.invFun (Function.invFun f) = f := by
    apply Function.invFun_eq_of_injective_of_rightInverse
    · exact hInvBij.1
    · exact Function.leftInverse_invFun hBij.1
  have hInvCorr : IsCorrelation S S (Function.invFun f) := by
    constructor
    · exact hInvWeak
    · constructor
      · exact hInvBij
      · simpa [hInvInvEq] using hWeak
  exact
    { toHomomorphism :=
        { toWeakHomomorphism :=
            { Fun := Function.invFun f
              isWeakHom := hInvWeak }
          isHom := hInvHom }
      isIso := ⟨hInvHom, hInvCorr⟩ }

def idCorrelation [Nonempty X] (S : IncidenceSystem X I) : Correlation S S := by
  have hWeakId : IsWeakHomomorphism S S id := by
    intro x hx
    constructor
    · simpa using hx
    · intro x hx y hy
      refine ⟨?_, ?_⟩
      · intro hxy
        simpa using hxy
      · simp
  have hInvId : Function.invFun (id : X → X) = id := by
    apply Function.invFun_eq_of_injective_of_rightInverse
    · intro a b h
      exact h
    · intro x
      rfl
  have hCorrId : IsCorrelation S S id := by
    refine ⟨hWeakId, ?_⟩
    refine ⟨Function.bijective_id, ?_⟩
    simpa [hInvId] using hWeakId
  exact
    { toWeakHomomorphism :=
        { Fun := id
          isWeakHom := hWeakId }
      isCorr := hCorrId }

noncomputable def invCorrelation [Nonempty X] {S : IncidenceSystem X I}
    (α : AutoCorrelation S) : Correlation S S := by
  let f := α.Fun
  have hCorr : IsCorrelation S S f := α.isAutoCorr
  have hWeak : IsWeakHomomorphism S S f := hCorr.1
  have hBij : Function.Bijective f := hCorr.2.1
  have hInvWeak : IsWeakHomomorphism S S (Function.invFun f) := hCorr.2.2
  have hInvBij : Function.Bijective (Function.invFun f) := by
    refine ⟨?_, ?_⟩
    · exact (Function.rightInverse_invFun hBij.2).injective
    · exact Function.invFun_surjective hBij.1
  have hInvInvEq : Function.invFun (Function.invFun f) = f := by
    apply Function.invFun_eq_of_injective_of_rightInverse
    · exact hInvBij.1
    · exact Function.leftInverse_invFun hBij.1
  have hInvCorr : IsCorrelation S S (Function.invFun f) := by
    refine ⟨hInvWeak, ?_⟩
    refine ⟨hInvBij, ?_⟩
    simpa [hInvInvEq] using hWeak
  exact
    { toWeakHomomorphism :=
        { Fun := Function.invFun f
          isWeakHom := hInvWeak }
      isCorr := hInvCorr }

-- Automorphism Group of Type-Presserving
noncomputable instance IncSys_AutomorphismGroup [Nonempty X]
  (S : IncidenceSystem X I) : Group (Automorphism S) :=
  { mul := composeAutomorphism
    one := { toIsomorphism := idIsomorphism S }
    inv := fun α => { toIsomorphism := invIsomorphism α }
    mul_assoc := by
      intros α β γ
      ext x
      rfl
    one_mul := by
      intro α
      ext x
      rfl
    mul_one := by
      intro α
      ext x
      rfl
    inv_mul_cancel := by
      intro α
      ext x
      exact Function.rightInverse_invFun α.isAuto.2.2.1.2 x }

-- Autocorrelation Group (includes non-type-preserving automorphisms)
noncomputable instance IncSys_AutoCorrelationGroup [Nonempty X]
  (S : IncidenceSystem X I) : Group (AutoCorrelation S) :=
  { mul := composeAutoCorrelation
    one := { toCorrelation := idCorrelation S }
    inv := fun α => { toCorrelation := invCorrelation α }
    mul_assoc := by
      intros α β γ
      ext x
      rfl
    one_mul := by
      intro α
      ext x
      rfl
    mul_one := by
      intro α
      ext x
      rfl
    inv_mul_cancel := by
      intro α
      ext x
      exact Function.rightInverse_invFun α.isAutoCorr.2.1.2 x }


theorem typeOfFlag_image_automorphism [Nonempty X] (S : IncidenceSystem X I)
    (α : Automorphism S) (F : Set X) (hF : IsFlag F S) :
    TypeOfFlag (Set.image α.Fun F) S = TypeOfFlag F S := by
  ext i
  constructor
  · intro hi
    rcases hi with ⟨y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact α.isAuto.1.2.2 x (hF.1 hx)
  · intro hi
    rcases hi with ⟨x, hx, rfl⟩
    refine ⟨α.Fun x, ⟨x, hx, rfl⟩, ?_⟩
    exact (α.isAuto.1.2.2 x (hF.1 hx)).symm

theorem eq_of_subset_chamber_of_typeEq (S : IncidenceSystem X I)
    {C A B : Set X} (hC : IsChamber C S)
    (hA : A ⊆ C) (hB : B ⊆ C)
    (hType : TypeOfFlag A S = TypeOfFlag B S) :
    A = B := by
  ext x
  constructor
  · intro hxA
    have hxC : x ∈ C := hA hxA
    have htxA : S.type_func x ∈ TypeOfFlag A S := ⟨x, hxA, rfl⟩
    have htxB : S.type_func x ∈ TypeOfFlag B S := by simpa [hType] using htxA
    rcases htxB with ⟨y, hyB, htyx⟩
    have hyC : y ∈ C := hB hyB
    have hxyInc : S.incidence x y := hC.1.2 x hxC y hyC
    have hxP : x ∈ S.points := hC.1.1 hxC
    have hyP : y ∈ S.points := hC.1.1 hyC
    have hxyOr : S.type_func x ≠ S.type_func y ∨ x = y :=
      (S.incidence_type_condition x y hxP hyP).1 hxyInc
    have hxy : x = y := by
      rcases hxyOr with hne | hEq
      · exfalso
        exact hne (by simp [htyx])
      · exact hEq
    simpa [hxy] using hyB
  · intro hxB
    have hxC : x ∈ C := hB hxB
    have htxB : S.type_func x ∈ TypeOfFlag B S := ⟨x, hxB, rfl⟩
    have htxA : S.type_func x ∈ TypeOfFlag A S := by simpa [hType] using htxB
    rcases htxA with ⟨y, hyA, htyx⟩
    have hyC : y ∈ C := hA hyA
    have hxyInc : S.incidence x y := hC.1.2 x hxC y hyC
    have hxP : x ∈ S.points := hC.1.1 hxC
    have hyP : y ∈ S.points := hC.1.1 hyC
    have hxyOr : S.type_func x ≠ S.type_func y ∨ x = y :=
      (S.incidence_type_condition x y hxP hyP).1 hxyInc
    have hxy : x = y := by
      rcases hxyOr with hne | hEq
      · exfalso
        exact hne (by simp [htyx])
      · exact hEq
    simpa [hxy] using hyA

def IsFlagTransitive [Nonempty X] (S : IncidenceSystem X I) : Prop :=
  ∀ F G : Set X, IsFlag F S → IsFlag G S →
    TypeOfFlag F S = TypeOfFlag G S →
    ∃ α : Automorphism S, Set.image α.Fun F = G

def IsChamberTransitive [Nonempty X] (S : IncidenceSystem X I) : Prop :=
  ∀ C D : Set X, IsChamber C S → IsChamber D S →
    ∃ α : Automorphism S, Set.image α.Fun C = D

set_option linter.style.whitespace false in
theorem ChamberTransitive_iff_FlagTransitive [Nonempty X]
    (S : IncidenceSystem X I) (IsGeom : IsGeometry S) :
    IsChamberTransitive S ↔ IsFlagTransitive S := by
  constructor
  · intro hChamberTrans F G hF hG hType
    obtain ⟨CF, hCF, hChamberF, hFsubCF⟩ := IsGeom F hF.1 hF
    obtain ⟨CG, hCG, hChamberG, hGsubCG⟩ := IsGeom G hG.1 hG
    obtain ⟨α, hα⟩ := hChamberTrans CF CG hChamberF hChamberG
    refine ⟨α, ?_⟩
    have hImgSubCG : Set.image α.Fun F ⊆ CG := by
      intro y hy
      rcases hy with ⟨x, hxF, rfl⟩
      have hxCF : x ∈ CF := hFsubCF hxF
      have hax : α.Fun x ∈ Set.image α.Fun CF := ⟨x, hxCF, rfl⟩
      simpa [hα] using hax
    have hTypeImg : TypeOfFlag (Set.image α.Fun F) S = TypeOfFlag F S :=
      typeOfFlag_image_automorphism S α F hF
    have hTypeImgG : TypeOfFlag (Set.image α.Fun F) S = TypeOfFlag G S :=
      hTypeImg.trans hType
    exact eq_of_subset_chamber_of_typeEq S hChamberG hImgSubCG hGsubCG hTypeImgG
  · intro hFlagTrans C D hC hD
    rcases hC with ⟨hCFlag, hCType⟩
    rcases hD with ⟨hDFlag, hDType⟩
    have hTypeCD : TypeOfFlag C S = TypeOfFlag D S := by
      rw [hCType, hDType]
    exact hFlagTrans C D hCFlag hDFlag hTypeCD


theorem FlagTransitive_and_ExistsChamber_implies_Geometry [Nonempty X]
    (S : IncidenceSystem X I) (C : Set X) (hC : IsChamber C S) :
    IsFlagTransitive S → IsGeometry S := by
  intro hTrans F hFsub hFflag
  let G := {x | x ∈ C ∧ S.type_func x ∈ TypeOfFlag F S}
  have hG_sub : G ⊆ S.points := by
    intro x hx
    rcases hx with ⟨hxC, _⟩
    exact hC.1.1 hxC
  have hG_flag : IsFlag G S := by
    constructor
    · exact hG_sub
    · intro x hx y hy
      rcases hx with ⟨hxC, _⟩
      rcases hy with ⟨hyC, _⟩
      exact hC.1.2 x hxC y hyC
  have hType_eq : TypeOfFlag G S = TypeOfFlag F S := by
    ext i
    constructor
    · intro hi
      rcases hi with ⟨x, ⟨hxC, htype⟩, rfl⟩
      exact htype
    · intro hi
      rcases hi with ⟨z, hzF, rfl⟩
      have hzP : z ∈ S.points := hFsub hzF
      have : S.type_func z ∈ Set.image S.type_func S.points := ⟨z, hzP, rfl⟩
      have htC : S.type_func z ∈ TypeOfFlag C S := by
        have tmp := this
        rw [← hC.2] at tmp
        exact tmp
      rcases htC with ⟨y, hyC, hytz⟩
      have hy_type_in_F : S.type_func y ∈ TypeOfFlag F S := by
        have htz := Set.mem_image_of_mem S.type_func hzF
        rw [hytz.symm] at htz
        exact htz
      exact ⟨y, ⟨hyC, hy_type_in_F⟩, hytz⟩
  obtain ⟨α, hαimg⟩ := hTrans F G hFflag hG_flag hType_eq.symm
  let β : Automorphism S := { toIsomorphism := invIsomorphism α }
  -- image of a chamber under an automorphism is a chamber
  have hFlag_βC : IsFlag (Set.image β.Fun C) S := by
    constructor
    · intro x hx
      rcases hx with ⟨y, hyC, rfl⟩
      have hyP : y ∈ S.points := hC.1.1 hyC
      have hweak := β.toIsomorphism.toHomomorphism.toWeakHomomorphism.isWeakHom y hyP
      exact hweak.1
    · intro x hx y hy
      rcases hx with ⟨u, huC, rfl⟩
      rcases hy with ⟨v, hvC, rfl⟩
      have huP : u ∈ S.points := hC.1.1 huC
      have hvP : v ∈ S.points := hC.1.1 hvC
      have hweaku := β.toIsomorphism.toHomomorphism.toWeakHomomorphism.isWeakHom u huP
      have hpres := (hweaku.2 u huP v hvP).1
      exact hpres (hC.1.2 u huC v hvC)
  have hType_βC : TypeOfFlag (Set.image β.Fun C) S = TypeOfFlag C S :=
    typeOfFlag_image_automorphism S β C hC.1
  -- C' := image of C under inverse automorphism is a chamber containing F
  use Set.image β.Fun C
  constructor
  · exact hFlag_βC.1
  constructor
  · exact ⟨hFlag_βC, hType_βC.trans hC.2⟩
  · intro x hx
    have hmem : α.Fun x ∈ Set.image α.Fun F := Set.mem_image_of_mem _ hx
    have hmemG : α.Fun x ∈ G := by rwa [hαimg] at hmem
    rcases hmemG with ⟨hyC, _⟩
    have hCorr := α.isAuto.2
    have hBij := hCorr.2.1
    have beta_eq : β.Fun (α.Fun x) = Function.invFun α.Fun (α.Fun x) := by
      dsimp [β]
      rfl
    have inv_eq := Function.leftInverse_invFun hBij.1 x
    have final_eq := Eq.trans beta_eq inv_eq
    refine ⟨α.Fun x, hyC, final_eq⟩
