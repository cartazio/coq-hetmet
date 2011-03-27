(*********************************************************************************************************************************)
(* SemiCategory:                                                                                                                 *)
(*                                                                                                                               *)
(*   Same as a category, but without identity maps.   See                                                                        *)
(*                                                                                                                               *)
(*       http://ncatlab.org/nlab/show/semicategory                                                                               *)
(*                                                                                                                               *)
(*********************************************************************************************************************************)

Generalizable All Variables.
Require Import Preamble.
Require Import General.

Class SemiCategory (Ob:Type)(Hom:Ob->Ob->Type) :=
{ semi_hom              := Hom
; semi_ob               := Ob
; semi_comp             :  forall  {a}{b}{c}, Hom a b -> Hom b c -> Hom a c
; semi_eqv              :  forall  a b,   (Hom a b) -> (Hom a b) -> Prop
; semi_eqv_equivalence  :  forall  a b,   Equivalence (semi_eqv a b)
; semi_comp_respects    :  forall  a b c, Proper (semi_eqv a b ==> semi_eqv b c ==> semi_eqv a c) (@semi_comp _ _ _)
; semi_associativity    :
       forall `(f:Hom a b)`(g:Hom b c)`(h:Hom c d), semi_eqv _ _ (semi_comp (semi_comp f g) h) (semi_comp f (semi_comp g h))
}.
Coercion semi_ob : SemiCategory >-> Sortclass.

Notation "a ~->   b" := (@semi_hom  _ _ _       a b) (at level 70).
Notation "f ~-~   g" := (@semi_eqv  _ _ _ _ _   f g) (at level 54).
Notation "f >>->> g" := (@semi_comp _ _ _ _ _ _ f g) (at level 45).

Add Parametric Relation (Ob:Type)(Hom:Ob->Ob->Type)(C:SemiCategory Ob Hom)(a b:Ob) : (semi_hom a b) (semi_eqv a b)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (semi_eqv_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (semi_eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (semi_eqv_equivalence a b))
  as parametric_relation_semi_eqv.
  Add Parametric Morphism `(c:SemiCategory Ob Hom)(a b c:Ob) : (@semi_comp _ _ _ a b c)
  with signature (semi_eqv _ _ ==> semi_eqv _ _ ==> semi_eqv _ _) as parametric_morphism_semi_comp.
    intros.
    apply semi_comp_respects; auto.
  Defined.

Class SemiFunctor
`( c1                 : SemiCategory                           )
`( c2                 : SemiCategory                           )
( fobj                : c1 -> c2                               ) :=
{ semifunctor_fobj         := fobj
; semi_fmor                : forall {a b}, (a~->b) -> (fobj a)~->(fobj b)
; semi_fmor_respects       : forall a b (f f':a~->b),   (f ~-~ f') ->        (semi_fmor f ~-~ semi_fmor f')
; semi_fmor_preserves_comp : forall `(f:a~->b)`(g:b~->c), (semi_fmor f) >>->> (semi_fmor g) ~-~ semi_fmor (f >>->> g)
}.
Implicit Arguments semi_fmor [[Ob][Hom][c1][Ob0][Hom0][c2][fobj][a][b]].

  (* register "fmor" so we can rewrite through it *)
  Implicit Arguments semi_fmor                [ Ob Hom Ob0 Hom0 c1 c2 fobj a b ].
  Implicit Arguments semi_fmor_respects       [ Ob Hom Ob0 Hom0 c1 c2 fobj a b ].
  Implicit Arguments semi_fmor_preserves_comp [ Ob Hom Ob0 Hom0 c1 c2 fobj a b c ].
  Notation "F \- f" := (semi_fmor F f) (at level 20)  : category_scope.
  Add Parametric Morphism `(C1:SemiCategory)`(C2:SemiCategory)
    (Fobj:C1->C2)
    (F:SemiFunctor C1 C2 Fobj)
    (a b:C1)
  : (@semi_fmor _ _ C1 _ _ C2 Fobj F a b)
  with signature ((@semi_eqv C1 _ C1 a b) ==> (@semi_eqv C2 _ C2 (Fobj a) (Fobj b))) as parametric_morphism_semi_fmor'.
  intros; apply (@semi_fmor_respects _ _ C1 _ _ C2 Fobj F a b x y); auto.
  Defined.
  Coercion semifunctor_fobj : SemiFunctor >-> Funclass.

Definition semifunctor_comp
  `(C1:SemiCategory)
  `(C2:SemiCategory)
  `(C3:SemiCategory)
  `(F:@SemiFunctor _ _ C1 _ _ C2 Fobj)`(G:@SemiFunctor _ _ C2 _ _ C3 Gobj) : SemiFunctor C1 C3 (Gobj ○ Fobj).
  intros. apply (Build_SemiFunctor _ _ _ _ _ _ _ (fun a b m => semi_fmor G (semi_fmor F m))).
  intros.
  setoid_rewrite H.
  reflexivity.
  intros.
  setoid_rewrite semi_fmor_preserves_comp; auto.
  setoid_rewrite semi_fmor_preserves_comp; auto.
  reflexivity.
  Defined.
Notation "f >>>–>>> g" := (@semifunctor_comp _ _ _ _ _ _ _ _ _ _ f _ g) (at level 20)  : category_scope.

Class IsomorphicSemiCategories `(C:SemiCategory)`(D:SemiCategory) :=
{ isc_f_obj    : C -> D
; isc_g_obj    : D -> C
; isc_f        : SemiFunctor C D isc_f_obj
; isc_g        : SemiFunctor D C isc_g_obj
; isc_forward  : forall a b (f:a~->b), semi_fmor isc_f  (semi_fmor isc_g  f) ~-~ f
}.
; isc_backward : isc_g >>>> isc_f ~~~~ functor_id D
}.


