Section main.

  (** This program compiles with COQ 8.9 and introduces combinatory logic.
      Combinatory logic is an alternative to lambda calculus which does NOT features bound 
      variables (and yet is Turing complete) which means the meta theory is considerably easier
      (in other words we aren't required to solve the "poplmark challenge" before proving 
      meaningful results). The results in this text can be found in the book 
      Lambda-Calculus and Combinators: An Introduction by R. Hindley and J. Seldin.
      What is to be found here:
      -Confluence theorems
      -Strong normalizability of typable terms
      -implementation of elementary arithmetic functions
      -Rice theorem
   *)
  
  Section definition_of_combinators.

    Variable context:Type.

    Inductive SK_Term:Type:=
    |skt_letter: context ->  SK_Term
    |skt_s: SK_Term
    |skt_k: SK_Term
    |skt_app: SK_Term -> SK_Term -> SK_Term.

    Notation s:= skt_s.
    Notation k:= skt_k.
    Notation var:= skt_letter.
    Notation "a ° b" := (skt_app a b) (left associativity, at level 51).

    Inductive direct_reduction: SK_Term -> SK_Term -> Type:=
    |dr_k: forall a b:SK_Term, direct_reduction (k ° a ° b) a
    |dr_s: forall a b c:SK_Term, direct_reduction (s ° a ° b ° c) (a ° c ° (b ° c))
    |dr_left: forall a a' b:SK_Term,
        direct_reduction a a' -> direct_reduction (a ° b) (a' ° b)
    |dr_right: forall a b b':SK_Term,
        direct_reduction b b' -> direct_reduction (a ° b) (a ° b').

    Inductive beta_reduction: SK_Term -> SK_Term -> Type:=
    |br_refl: forall x:SK_Term, beta_reduction x x
    |br_step: forall x y z:SK_Term,
        beta_reduction x y -> direct_reduction y z -> beta_reduction x z.

    Section Strong_normalizability.

      (** this will be used later in the text*)

      Inductive strongly_normalizable: SK_Term -> Type :=
      |sn_intro: forall x:SK_Term,
          (forall y:SK_Term, direct_reduction x y -> strongly_normalizable y)
          -> strongly_normalizable x.

      (** No infinite chain of reductions can start with a strongly normalizable term,
        in fact this is the definition in the litterature but we deal with the concept with
        COQ tools here. We show this result below *)

      Fixpoint SN_stability (x y:SK_Term) (p:strongly_normalizable x){struct p}:
        direct_reduction x y -> strongly_normalizable y.
      Proof.
        intro d.
        destruct p as (n,q).
        apply q; assumption.
      Defined.
      
      Definition no_infinite_reduction_sequence_if_strongly_normalizable_with_types:
        forall (Error:Type) (u: nat -> SK_Term),          
          strongly_normalizable (u 0) ->
          (forall n:nat, direct_reduction (u n) (u (S n))) ->
          Error.

        (*forall x:SK_Term,
          strongly_normalizable x
                         ->
                         forall (T:Type) (f:nat -> SK_Term),
                           (f 0 = x) ->
                            (forall n:nat, (direct_reduction (f n) (f (S n)))) ->
                           T.*)
      Proof.
        assert (let aux := fun (u:SK_Term) =>
                             forall (T:Type) (f:nat -> SK_Term),
                           (f 0 = u) ->
                            (forall n:nat, (direct_reduction (f n) (f (S n)))) ->
                           T 
                in
                forall x:SK_Term, strongly_normalizable x -> aux x
               ) as L.
        apply strongly_normalizable_rect.
        intros.
        apply X with (f:= fun k:nat => f (S k)) (y:= f 1).
        rewrite <- H.
        apply X0.
        reflexivity.
        intros; apply X0.
        simpl in L. intros Error u snu0.
        apply L with (x:= u 0). assumption. reflexivity.
      Defined.

      Theorem no_infinite_reduction_sequence_if_strongly_normalizable:
        forall u: nat -> SK_Term,
          strongly_normalizable (u 0) ->
          (forall n:nat, direct_reduction (u n) (u (S n))) ->
          False.
(*        forall x:SK_Term,
          strongly_normalizable x
                         ->
                         inhabited
                           {f:nat -> SK_Term &
                                     prod (f 0 = x) 
                                          (forall n:nat,
                                              (direct_reduction (f n) (f (S n))))} -> False.*)
      Proof.
        intros.
        apply no_infinite_reduction_sequence_if_strongly_normalizable_with_types
          with (u:=u). assumption. assumption.
      Defined.
        
       (*
        destruct H.
        destruct X as (t,r).
        destruct X0 as (f,e).
        apply no_infinite_reduction_sequence_if_strongly_normalizable_with_types
          with (x:=t) (f:=f).
        apply sn_intro.
        assumption.
        apply e.
        apply e.
      Defined.*)
      
    End Strong_normalizability.

    Definition br_transitivity: forall x y z:SK_Term,
        beta_reduction x y -> beta_reduction y z -> beta_reduction x z.
    Proof.
      assert (let aux:= fun p q:SK_Term => forall r:SK_Term,
                            beta_reduction r p -> beta_reduction r q
              in
          forall (m n:SK_Term),
                 beta_reduction m n -> aux m n) as L.
      apply beta_reduction_rect.
      intros; assumption.
      intros.
      apply br_step with (y:=y).
      apply X.
      assumption.
      assumption.
      simpl in L.
      intros.
      apply L with (m:=y).
      assumption.
      assumption.
    Defined.

    Definition br_right: forall x y y':SK_Term,
        beta_reduction y y' -> beta_reduction  (x ° y) (x ° y').
    Proof.
      assert (let aux:= fun p q:SK_Term => forall r:SK_Term,
                            beta_reduction (r ° p) (r ° q)
              in
          forall (m n:SK_Term),
                 beta_reduction m n -> aux m n) as L.
      apply beta_reduction_rect.
      intros; apply br_refl.
      intros.
      apply br_step with (y:= r ° y).
      apply X.
      apply dr_right; assumption.
      simpl in L.
      intros; apply L.
      assumption.
    Defined.

    Definition br_left: forall x x' y:SK_Term,
        beta_reduction x x' -> beta_reduction (x ° y) (x' ° y).
    Proof.
      assert (let aux:= fun p q:SK_Term => forall r:SK_Term,
                            beta_reduction (p ° r) (q ° r)
              in
          forall (m n:SK_Term),
                 beta_reduction m n -> aux m n) as L.
      apply beta_reduction_rect.
      intros; apply br_refl.
      intros.
      apply br_step with (y:= y ° r).
      apply X.
      apply dr_left; assumption.
      simpl in L.
      intros; apply L.
      assumption.
    Defined.
        
    Definition br_leftright: forall x x' y y':SK_Term,
        beta_reduction x x' ->
        beta_reduction y y' ->
        beta_reduction (x ° y) (x' ° y').
    Proof.
      intros.
      apply br_transitivity with (y:= x' ° y).
      apply br_left.
      assumption.
      apply br_right.
      assumption.
    Defined.

    Definition skt_i:= s ° k ° k.

    Definition br_k: forall a b:SK_Term, beta_reduction (k ° a ° b) a.
    Proof.
      intros.
      apply br_step with (y:= k ° a ° b).
      apply br_refl.
      apply dr_k.
    Defined.

    Definition br_s: forall a b c:SK_Term, beta_reduction (s ° a ° b ° c) (a ° c ° (b ° c)).
    Proof.
      intros.
      apply br_step with (y:= s ° a ° b ° c).
      apply br_refl.
      apply dr_s.
    Defined.
    
    Definition br_i: forall x:SK_Term, beta_reduction (skt_i ° x) x.
    Proof.
      intros.
      unfold skt_i.
      apply br_step with (y:= k ° x ° (k ° x)).
      apply br_s.
      apply dr_k.
    Defined.

    Section Confluence.
      (** In this section we prove that the beta reduction relationship on combinators is 
       confluent. This is done with the help of a new reduction relationship for which
       the result is esaier to prove, then we prove both relationships are equivalent. *)
      
      Inductive direct_parallel_reduction: SK_Term -> SK_Term -> Type :=
      |dpr_refl: forall x:SK_Term, direct_parallel_reduction x x
      |dpr_k: forall a b:SK_Term, direct_parallel_reduction (k ° a ° b) a
      |dpr_s: forall a b c:SK_Term, direct_parallel_reduction (s ° a ° b ° c) (a ° c ° (b ° c))
      |dpr_leftright: forall x x' y y':SK_Term,
          direct_parallel_reduction x x' ->
          direct_parallel_reduction y y' ->
          direct_parallel_reduction (x ° y) (x' ° y').
      
      Inductive parallel_reduction: SK_Term -> SK_Term -> Type:=
      |pr_refl: forall x:SK_Term, parallel_reduction x x
      |pr_step: forall x y z:SK_Term,
          parallel_reduction x y -> direct_parallel_reduction y z -> parallel_reduction x z.

      Definition direct_beta_to_direct_parallel: forall x y:SK_Term,
          direct_reduction x y -> direct_parallel_reduction x y.
      Proof.
        apply direct_reduction_rect.
        apply dpr_k.
        apply dpr_s.
        intros.
        apply dpr_leftright.
        assumption.
        apply dpr_refl.
        intros.
        apply dpr_leftright.
        apply dpr_refl.
        assumption.
      Defined.

      Definition beta_to_parallel: forall x y:SK_Term,
          beta_reduction x y -> parallel_reduction x y.
      Proof.
        apply beta_reduction_rect.
        apply pr_refl.
        intros.
        apply pr_step with (y:=y).
        assumption.
        apply direct_beta_to_direct_parallel.
        assumption.
      Defined.

      Definition direct_parallel_to_beta: 
        forall x y:SK_Term,
          direct_parallel_reduction x y -> beta_reduction x y.
      Proof.
        apply direct_parallel_reduction_rect.
        apply br_refl.
        apply br_k.
        apply br_s.
        intros.
        apply br_leftright.
        assumption.
        assumption.
      Defined.

      Definition parallel_to_beta: 
        forall x y:SK_Term,
          parallel_reduction x y -> beta_reduction x y.
      Proof.
        apply parallel_reduction_rect.
        apply br_refl.
        intros.
        apply br_transitivity with (y:=y).
        assumption.
        apply direct_parallel_to_beta.
        assumption.
      Defined.
        
      Definition diamond_k_case: forall a b t:SK_Term,
          direct_parallel_reduction (k ° a ° b) t ->
          sum (t=a)
              ({a':SK_Term & {b':SK_Term & prod (t = k ° a' ° b')
                                                (prod
                                                   (direct_parallel_reduction a a')
                                                   (direct_parallel_reduction b b')
              )}}).
      Proof.
        intros.
        inversion X.
        right.
        exists a.
        exists b.
        split.
        reflexivity.
        split.
        apply dpr_refl.
        apply dpr_refl.
        left; reflexivity.
        inversion X0.
        right.
        exists a.
        exists y'.
        split.
        reflexivity.
        split.
        apply dpr_refl.
        assumption.
        inversion X2.
        right.
        exists y'0.
        exists y'.
        split.
        reflexivity.
        split.
        assumption.
        assumption.
      Defined.

      Definition diamond_s_case: forall a b c t:SK_Term,
          direct_parallel_reduction (s ° a ° b ° c) t ->
          sum (t= a ° c ° (b ° c))
              ({a':SK_Term &
                   {b':SK_Term &
                       {c':SK_Term & prod (t = s ° a' ° b' ° c')
                                                (prod
                                                   (direct_parallel_reduction a a')
                                                   (prod
                                                      (direct_parallel_reduction b b')
                                                      (direct_parallel_reduction c c')
                                                   )
              )}}}).
      Proof.
        intros.
        inversion X.
        right.
        exists a.
        exists b.
        exists c.
        split.
        reflexivity.
        split.
        apply dpr_refl.
        split.
        apply dpr_refl.
        apply dpr_refl.
        left; reflexivity.
        inversion X0.
        right.
        exists a. exists b. exists y'.
        split. reflexivity. split. apply dpr_refl. split. apply dpr_refl. assumption.
        inversion X2. right.        
        exists a. exists y'0. exists y'.
        split. reflexivity. split. apply dpr_refl. split. assumption. assumption.
        inversion X4. right.
        exists y'1. exists y'0. exists y'.
        split. reflexivity. split. assumption. split. assumption. assumption.
      Defined.

      Definition diamond_lemma: forall a b:SK_Term,
          direct_parallel_reduction a b ->
          forall c:SK_Term, direct_parallel_reduction a c ->
          {d:SK_Term & prod (direct_parallel_reduction b d) (direct_parallel_reduction c d)}.
      Proof.
        assert (let aux := fun (a b:SK_Term) =>
                             forall c:SK_Term,
                               direct_parallel_reduction a c ->
                               {d:SK_Term &
                                  prod (direct_parallel_reduction b d)
                                       (direct_parallel_reduction c d)}
                in
                forall m n:SK_Term, direct_parallel_reduction m n -> aux m n                
          ) as L.
        apply direct_parallel_reduction_rect.
        intros; exists c.
        split. assumption. apply dpr_refl.
        intros. apply diamond_k_case in X.
        destruct X as [e|T].
        exists a. rewrite e. split. apply dpr_refl. apply dpr_refl.
        destruct T as (a',T2).
        destruct T2 as (b',T3).
        exists a'. destruct T3 as (T3e,T3p). rewrite T3e. split. apply T3p. apply dpr_k.
        intros a b c f X. apply diamond_s_case in X.
        destruct X as [e|T].
        exists f. rewrite e. split. apply dpr_refl. apply dpr_refl.
        destruct T as (a',T2). destruct T2 as (b',T3). destruct T3 as (c',T4).
        exists (a' ° c' ° (b' ° c')). destruct T4 as (T4e,T4p). rewrite T4e. split.
        apply dpr_leftright. apply dpr_leftright. apply T4p. apply T4p.
        apply dpr_leftright. apply T4p. apply T4p. apply dpr_s.
        intros.
        inversion X1.
        exists (x' ° y').
        split. apply dpr_refl. apply dpr_leftright. assumption. assumption.
        rewrite <- H0 in X1.
        destruct diamond_k_case with (a:=a)(b:=y) (t:= x' ° y') as [e|T].
        rewrite H0.
        apply dpr_leftright. assumption. assumption.
        exists (x' ° y'). split. apply dpr_refl. rewrite <- H2. rewrite <- e. apply dpr_refl.
        destruct T as (a',T2). destruct T2 as (b',T3). destruct T3 as (T3e,T3p).
        exists a'. rewrite T3e. rewrite <- H2. split. apply dpr_k. apply T3p.
        destruct diamond_s_case with (a:=a)(b:=b)(c:=y)(t:= x' ° y') as [e|T].
        rewrite H0. apply dpr_leftright. assumption. assumption. exists (a ° y ° (b ° y)).
        rewrite e. split. apply dpr_refl. apply dpr_refl. 
        destruct T as (a',T2). destruct T2 as (b',T3). destruct T3 as (c',T4).
        destruct T4 as (T4e,T4p). rewrite T4e. exists (a' ° c' ° (b' ° c')). split.
        apply dpr_s. 
        apply dpr_leftright. apply dpr_leftright. apply T4p. apply T4p.
        apply dpr_leftright. apply T4p. apply T4p.
        destruct X with (c:=x'0) as (xd,Tx). assumption.
        destruct X0 with (c:=y'0) as (yd,Ty). assumption.
        exists (xd ° yd). split.
        apply dpr_leftright. apply Tx. apply Ty.
        apply dpr_leftright. apply Tx. apply Ty.
        simpl in L.
        assumption.
      Defined.
        
      Definition parallel_Church_Rosser: forall a b c:SK_Term,
          parallel_reduction a b -> 
          parallel_reduction a c ->
          {d:SK_Term & prod (parallel_reduction b d) (parallel_reduction c d)}.
      Proof.
        assert (let aux := fun (a b:SK_Term) =>
                             forall c:SK_Term,
                               direct_parallel_reduction a c ->
                               {d:SK_Term &
                                  prod (direct_parallel_reduction b d)
                                       (parallel_reduction c d)}
                in
                forall m n:SK_Term, parallel_reduction m n -> aux m n                
          ) as L.
        apply parallel_reduction_rect.
        intros.
        exists c.
        split. assumption. apply pr_refl.
        intros. destruct X with (c:=c) as (f,P). assumption.
        destruct diamond_lemma with (a:=y) (b:=z) (c:=f) as (g,Q). assumption.
        apply P. exists g. split. apply Q. apply pr_step with (y:=f). apply P. apply Q.
        assert (let aux := fun (a b:SK_Term) =>
                             forall c:SK_Term,
                               parallel_reduction a c ->
                               {d:SK_Term &
                                  prod (parallel_reduction b d)
                                       (parallel_reduction c d)}
                in
                forall m n:SK_Term, parallel_reduction m n -> aux m n                
               ) as M.
        apply parallel_reduction_rect.
        intros.
        exists c.
        split. assumption. apply pr_refl.
        intros. destruct X with (c:=c) as (f,P). assumption.
        destruct L with (m:=y)(n:=f)(c:=z) as (g,Q). apply P. assumption. exists g. split.
        apply Q. apply pr_step with (y:=f). apply P. apply Q. simpl in L. simpl in M.
        intros. apply M with (m:=a). assumption. assumption.
      Defined.
        
      Definition Church_Rosser: forall a b c:SK_Term,
          beta_reduction a b -> 
          beta_reduction a c ->
          {d:SK_Term & prod (beta_reduction b d) (beta_reduction c d)}.
      Proof.
        intros.
        destruct parallel_Church_Rosser with (a:=a) (b:=b) (c:=c) as (f,P).
        apply beta_to_parallel; assumption.
        apply beta_to_parallel; assumption.
        exists f. split.
        apply parallel_to_beta; apply P.
        apply parallel_to_beta; apply P.
      Defined.         
        
    End Confluence.

    Section Sorts.

      Variable V:Type.

      Inductive SK_sort:Type:=
      |sks_letter: V -> SK_sort
      |sks_arrow: SK_sort -> SK_sort -> SK_sort.
      
    End Sorts.

    Section Typing_judgements.

      (** In this section we define a simple type system for combinators and prove
       that all typable terms are strongly normalizable (Tait theorem), which yields the
       fact that no infinite sequence of non trivial reductions can start by a typable term.
       *)
      
      Variable V:Type.
      Variable sort_assignment: context -> (SK_sort V).

      Notation T:= (SK_sort V).
      Notation "a --> b":= (sks_arrow V a b) (right associativity, at level 61).

      Notation k_sort:= (fun (a b:T) => a --> b --> a).
      Notation s_sort := (fun (a b c:T) => (a --> b --> c) --> (a --> b) --> a --> c). 

      Inductive Typing_Judgement: T -> SK_Term -> Type :=
      |tj_letter: forall x:context, Typing_Judgement (sort_assignment x) (var x)
      |tj_k: forall a b:T, Typing_Judgement (k_sort a b) k
      |tj_s: forall a b c:T, Typing_Judgement (s_sort a b c) s
      |tj_arrow: forall (a b:T) (f x:SK_Term),
          Typing_Judgement (a --> b) f ->
          Typing_Judgement a x ->
          Typing_Judgement b (f ° x).

      Notation "|- p ; q":= (Typing_Judgement q p) (at level 62).

      Definition Curry_Typed_SK_Term (t:T):=
        {x:SK_Term & |- x; t}.

      Definition ctskt_app
                 (a b:T) (f:Curry_Typed_SK_Term (a --> b))
                 (x:Curry_Typed_SK_Term a):Curry_Typed_SK_Term b:=
        existT (Typing_Judgement b) ((projT1 f) ° (projT1 x))
               (tj_arrow a b (projT1 f) (projT1 x) (projT2 f) (projT2 x)).

      Definition ctskt_letter (x:context):Curry_Typed_SK_Term (sort_assignment x):=
        existT (Typing_Judgement (sort_assignment x)) (var x) (tj_letter x).

      Definition ctskt_k (a b:T):Curry_Typed_SK_Term (k_sort a b):=
        existT (Typing_Judgement (k_sort a b)) k (tj_k a b).

      Definition ctskt_s (a b c:T):Curry_Typed_SK_Term (s_sort a b c):=
        existT (Typing_Judgement (s_sort a b c)) s (tj_s a b c).
      
      Definition ctskt_k_prod := (fun (a b:T)(x:Curry_Typed_SK_Term a)
                                      (y:Curry_Typed_SK_Term b) =>
                                    ctskt_app b a (ctskt_app a (b --> a) (ctskt_k a b) x) y).
      Definition ctskt_s_prod :=
        (fun (a b c:T)
             (x:Curry_Typed_SK_Term (a --> b --> c))
             (y:Curry_Typed_SK_Term (a --> b))
             (z:Curry_Typed_SK_Term a) =>
           ctskt_app a c
                     (ctskt_app
                        (a --> b) (a --> c)
                        (ctskt_app
                           (a--> b --> c) ((a --> b) --> a --> c)
                           (ctskt_s a b c) x)
                        y)
                     z
        ).

      Definition ctskt_s_expr :=
        (fun (a b c:T)
             (x:Curry_Typed_SK_Term (a --> b --> c))
             (y:Curry_Typed_SK_Term (a --> b))
             (z:Curry_Typed_SK_Term a) =>
           ctskt_app
             b c
             (ctskt_app
                a (b --> c)
                x z
             )        
             (ctskt_app
                a b
                y z
        )).

      Inductive CT_direct_reduction: forall a:T,
          Curry_Typed_SK_Term a -> Curry_Typed_SK_Term a -> Type :=
      |ctdr_k: forall (a b:T) (x:Curry_Typed_SK_Term a) (y: Curry_Typed_SK_Term b),
          CT_direct_reduction a (ctskt_k_prod a b x y) x
      |ctdr_s: forall (a b c:T)
                      (x:Curry_Typed_SK_Term (a --> b --> c))
                      (y:Curry_Typed_SK_Term (a --> b))
                      (z:Curry_Typed_SK_Term a),
          CT_direct_reduction c (ctskt_s_prod a b c x y z) (ctskt_s_expr a b c x y z)
      |ctdr_left: forall (a b:T)
                         (f f':Curry_Typed_SK_Term (a --> b))
                         (x:Curry_Typed_SK_Term a),
          CT_direct_reduction (a --> b) f f' ->
          CT_direct_reduction b (ctskt_app a b f x) (ctskt_app a b f' x)
       |ctdr_right: forall (a b:T)
                         (f:Curry_Typed_SK_Term (a --> b))
                         (x x':Curry_Typed_SK_Term a),
          CT_direct_reduction a x x' ->
          CT_direct_reduction b (ctskt_app a b f x) (ctskt_app a b f x').          

      Fixpoint direct_subject_reduction
               (x y:SK_Term) (a:T)
               (r:direct_reduction x y)
               (j: |- x ; a)
               {struct r}:
        (|- y ; a).
      Proof.
        destruct r.
        inversion j.
        inversion X.
        inversion X1.
        rewrite <- H8.
        assumption.
        inversion j.
        inversion X.
        inversion X1.
        inversion X3.
        apply tj_arrow with (a:= b3).
        apply tj_arrow with (a:= a4).
        rewrite <- H12; rewrite H9; assumption.
        rewrite H11; assumption.
        apply tj_arrow with (a:=a4).
        rewrite H10; assumption.
        rewrite H11; assumption.
        inversion j.
        apply tj_arrow with (a:=a1).
        apply direct_subject_reduction with (x:=a0); assumption. assumption.
        inversion j.
        apply tj_arrow with (a:=a1).
        assumption. apply direct_subject_reduction with (x:=b); assumption.
      Defined.      
        
      Definition subject_reduction: forall (x y:SK_Term) (a:T),
          beta_reduction x y -> (|- x ; a) -> (|- y ; a).
      Proof.
        assert (let aux := fun (m n:SK_Term) =>
                             forall a:T, (|- m ; a) -> (|- n ; a)
                in
                forall x y:SK_Term, beta_reduction x y -> aux x y            
               ) as L.
        apply beta_reduction_rect.
        intros; assumption.
        intros.
        apply direct_subject_reduction with (x:=y).
        assumption. apply X. assumption.
        simpl in L. intros. apply L with (x:=x). assumption. assumption.
      Defined.

      Definition tj_i: forall a:T, |- skt_i ; (a --> a).
      Proof.
        intros. unfold skt_i.
        apply tj_arrow with (a:= k_sort a a).
        apply tj_arrow with (a:= k_sort a (a --> a)).
        apply tj_s.
        apply tj_k.
        apply tj_k.
      Defined.

      Section a_simple_interpreter_for_sk.

        Variable sort_letter_interpretation: V -> Type.

        Fixpoint sk_sort_interpretation (a:T){struct a}:Type:=
          match a with
          |sks_letter _ v => sort_letter_interpretation v
          |sks_arrow _ b c => (sk_sort_interpretation b) -> (sk_sort_interpretation c)
          end.

        Definition coq_map_k (P Q:Type) (x: P) (y:Q):P:= x.
        Definition coq_map_s
                   (P Q R:Type) (x: P -> Q -> R) (y:P -> Q) (z:P):R:= x z (y z).

        Variable environment: forall x:context, sk_sort_interpretation (sort_assignment x).
        
        Fixpoint TJ_interpretation
                 (t:SK_Term)
                 (p:T)
                 (j: |- t; p)
                 {struct j}:sk_sort_interpretation p:=
          match j with
          |tj_letter l => environment l
          |tj_k a b => coq_map_k (sk_sort_interpretation a) (sk_sort_interpretation b)
          |tj_s a b c => coq_map_s (sk_sort_interpretation a)
                                   (sk_sort_interpretation b)
                                   (sk_sort_interpretation c)
          |tj_arrow a b f z jf jz =>
           (TJ_interpretation f (a --> b) jf)
             (TJ_interpretation z a jz)
          end.

        Definition CTSKT_interpretation (t:T) (x:Curry_Typed_SK_Term t):=
          TJ_interpretation (projT1 x) t (projT2 x).

        Definition ctskti_morphism:
          forall (a b:T)
                 (f:Curry_Typed_SK_Term (a --> b))(x:Curry_Typed_SK_Term a),
            (CTSKT_interpretation b (ctskt_app a b f x)) =
            (CTSKT_interpretation (a --> b) f) (CTSKT_interpretation a x).
        Proof.
          intros; simpl; reflexivity.
        Defined.
        
        Fixpoint CT_soundness
                 (a:T)
                 (p q:Curry_Typed_SK_Term a)
                 (r:CT_direct_reduction a p q)
                 {struct r}:
          (CTSKT_interpretation a p) =
          (CTSKT_interpretation a q).     
        Proof.
          destruct r.
          unfold ctskt_k.
          simpl. reflexivity.
          unfold ctskt_s.
          simpl. reflexivity.
          rewrite ctskti_morphism.
          rewrite ctskti_morphism.
          rewrite CT_soundness with (p:=f)(q:=f'). reflexivity.
          assumption.
          rewrite ctskti_morphism.
          rewrite ctskti_morphism.
          rewrite CT_soundness with (p:=x)(q:=x'). reflexivity.
          assumption.
        Defined.

        Fixpoint CT_projection
                 (a:T)(x y:Curry_Typed_SK_Term a) (r: CT_direct_reduction a x y)
                 {struct r}:direct_reduction (projT1 x) (projT1 y).
        Proof.
          destruct r.
          simpl; apply dr_k.
          simpl; apply dr_s.
          simpl; apply dr_left; apply CT_projection; assumption.
          simpl; apply dr_right; apply CT_projection; assumption.
        Defined.

      End a_simple_interpreter_for_sk.     
      
    End Typing_judgements.
    
  End definition_of_combinators.

  Section Tait.

    Variables Ctxt SL:Type.
    Variable sort_assignment: Ctxt -> SK_sort SL. 

    Definition Auxiliary_context:= sum Ctxt (SK_sort SL).

    Definition aux_sort_assignment (x:Auxiliary_context):SK_sort SL:=
      match x with
      |inl y => sort_assignment y 
      |inr z => z
      end.

    Section strong_computability.

      Notation C:= (SK_Term Auxiliary_context).
      Notation s:= (skt_s Auxiliary_context).
      Notation k:= (skt_k Auxiliary_context).
      Notation var:= (skt_letter Auxiliary_context).
      Notation "a ° b" := (skt_app Auxiliary_context a b) (left associativity, at level 51).
      Notation T:= (SK_sort SL).
      Notation "a --> b":= (sks_arrow SL a b) (right associativity, at level 61).
      Notation "|- p ; q":=
        (Typing_Judgement Auxiliary_context SL aux_sort_assignment q p) (at level 62).
      Notation A:= Auxiliary_context.
      Notation "m >d n":= (direct_reduction A m n) (at level 63).
      Notation "m >b n":= (beta_reduction A m n) (at level 63).
      Notation SN:= (fun x:C => strongly_normalizable A x).

      Fixpoint strongly_computable (a:T)(x:C)(j:|- x;a){struct a}:Type.
      Proof.
        destruct a.
        apply (SN x).
        apply (forall (y:C) (jy: |- y; a1),
                  strongly_computable a1 y jy ->
                  strongly_computable a2 (x ° y) (tj_arrow
                                                    A SL
                                                    aux_sort_assignment a1 a2 x y j jy)
              ).
      Defined.

      Notation tj_arr := (fun (a1 a2:T) (x y:C) (jx: |- x; a1 --> a2) (jy: |- y; a1) =>
                       tj_arrow
                         A SL
                         aux_sort_assignment a1 a2 x y jx jy).
      
      Definition sc_morphism: forall (x y:C)(a b:T) (jx: |- x; a--> b) (jy: |- y;a),
          strongly_computable (a --> b) x jx -> strongly_computable a y jy ->
          strongly_computable b (x ° y) (tj_arr a b x y jx jy).
      Proof.
        intros.
        unfold strongly_computable in X.
        apply X.
        assumption.
      Defined.

      Definition sub_term_sn: forall x y:C, SN (x ° y) -> prod (SN x) (SN y).
      Proof.
        assert (let aux:= fun (p:C) => forall q r:C, (q ° r = p) -> prod (SN q) (SN r)
                              in
                          forall n:C, SN n -> aux n
               ) as L.
        apply strongly_normalizable_rect.
        intros.
        split.
        apply sn_intro.
        intros.
        destruct X with (y:= y ° r)(q:=y) (r:=r).
        rewrite <- H.
        apply dr_left.
        assumption.
        reflexivity.
        assumption.
        apply sn_intro.
        intros.
        destruct X with (y:= q ° y)(q:=q) (r:=y).
        rewrite <- H.
        apply dr_right.
        assumption.
        reflexivity.
        assumption.
        simpl in L.
        intros.
        apply L with (n:= x ° y).
        assumption.
        reflexivity.
      Defined.

      Inductive letter_headed_sn_tail: C -> Type:=
      |lh_atom: forall l:A, letter_headed_sn_tail (var l)
      |lh_prod: forall x y:C, letter_headed_sn_tail x -> SN y -> letter_headed_sn_tail (x ° y).

      Definition lhsnt_left (x y:C):letter_headed_sn_tail (x ° y) ->
                                            letter_headed_sn_tail x.
      Proof.
        intros.
        inversion X.
        assumption.
      Defined.

      Fixpoint letter_headed_sn_tail_stability (x y:C) (l:letter_headed_sn_tail x)
               {struct l}: x >d y -> letter_headed_sn_tail y.
      Proof.
        destruct l.
        intros.
        inversion X.
        intros.
        inversion X.
        rewrite <- H0 in l.
        inversion l.
        inversion X0.
        rewrite <- H0 in l.
        inversion l.
        inversion X0.
        inversion X2.
        apply lh_prod.
        apply letter_headed_sn_tail_stability with (x:=x).
        assumption.
        assumption.
        assumption.
        apply lh_prod.
        assumption.
        apply SN_stability with (x:=y0).
        assumption.
        assumption.
      Defined.

      Definition lhsnt_cases:
        forall x y z:C, letter_headed_sn_tail x -> SN y ->
                        x ° y >d z ->
                        sum ({a:C & prod (z = a ° y) (prod (x >d a)(letter_headed_sn_tail a))})
                            ({b:C & prod (z = x ° b) (prod (y >d b)(SN b))}).
      Proof.
        intros x y z l2.
        intros.          
        inversion X0.
        rewrite <- H0 in l2.
        inversion l2.
        inversion X1.
        rewrite <- H0 in l2.
        inversion l2.
        inversion X1.
        inversion X3.
        left.
        exists a'.
        split.
        reflexivity.
        split.
        assumption.
        apply letter_headed_sn_tail_stability with (x:=x).
        assumption.
        assumption.
        right.
        exists b'.
        split.
        reflexivity.
        split.
        assumption.
        apply SN_stability with (x:=y).
        assumption.
        assumption.
      Defined.

      Inductive double_red: C ->C -> C -> C -> Type:=
      |double_left: forall x x' y:C, x >d x' -> double_red x y x' y
      |double_right: forall x y y':C, y >d y' -> double_red x y x y'.

      Inductive double_sn: C -> C -> Type:=
      |double_sn_intro: forall x y:C,
          (forall x' y':C, double_red x y x' y' -> double_sn x' y') ->
          double_sn x y.

      Definition double_halt:
        forall (x y:C), SN x -> SN y -> double_sn x y.
      Proof.
        assert (let aux := fun u:C => forall v:C, SN v -> double_sn u v
                in
               forall x:C, SN x -> aux x) as L.
        apply strongly_normalizable_rect.
        intros x P Q z sz.
        assert (forall w:C, SN w -> double_sn x w) as R.
        apply strongly_normalizable_rect.
        intros w Pw Rw.
        apply double_sn_intro.
        intros.
        destruct X.
        apply Q.
        assumption.
        apply sn_intro; assumption.
        apply Rw.
        assumption.
        apply R.
        assumption.
        simpl in L.
        intros.
        apply L.
        assumption.
        assumption.
      Defined.
      
      Definition lhsnt_sn: forall (x:C), letter_headed_sn_tail x -> SN x.
      Proof.
         assert (let aux := fun (p q:C) =>
                             letter_headed_sn_tail p -> SN q -> SN (p ° q)
                in
                forall (m n:C), double_sn m n -> aux m n
               ) as L.
        apply double_sn_rect.
        intros x0 y0 P Q lx0 sy0.
        apply sn_intro.
        intros y1 R.
        destruct lhsnt_cases with (x:=x0) (y:=y0) (z:=y1) as [M1|M2].
        assumption.
        assumption.
        assumption.
        destruct M1 as (a,Pa).
        destruct Pa as (ea,Qa).
        rewrite ea.
        apply Q.
        apply double_left.
        apply Qa.
        apply Qa.
        assumption.
        destruct M2 as (b,Pb).
        destruct Pb as (eb,Qb).
        rewrite eb.
        apply Q.
        apply double_right.
        apply Qb.
        assumption.
        apply Qb.
        simpl in L.
        apply letter_headed_sn_tail_rect.
        intros.
        apply sn_intro.
        intros.
        inversion X.
        intros.
        apply L.
        apply double_halt.
        assumption.
        assumption.
        assumption.
        assumption.
      Defined.              
      
      Fixpoint lh_sc (a:T)(x:C) (j: |- x;a) {struct a}:
        prod (letter_headed_sn_tail x -> strongly_computable a x j)
             (strongly_computable a x j -> SN x).
      Proof.
        destruct a.
        simpl.
        split.
        apply lhsnt_sn.
        intros; assumption.
        split.
        intro.
        intro.
        intros.
        apply lh_sc.
        apply lh_prod.
        assumption.
        apply lh_sc with (a:=a1) (x:=y) (j:=jy).
        assumption.
        intros.
        apply sub_term_sn with (x:=x) (y:= var (inr a1)).
        apply lh_sc with
            (a:=a2) (x:= x ° (var (inr a1)))
            (j:= tj_arr a1 a2 x (var (inr a1)) j
                        (tj_letter A SL aux_sort_assignment (inr a1))).
        apply X.
        apply lh_sc.
        apply lh_atom.
      Defined.

      Section S_and_K_are_strongly_computable.

        Definition tj_k_prod
                   (a b:T)(x y:C) (jax: |- x;a)
                   (jby: |- y;b): (|- k ° x ° y ; a):=
          projT2
            (ctskt_k_prod
               A SL aux_sort_assignment a b
               (existT (Typing_Judgement A SL aux_sort_assignment a) x jax)
               (existT (Typing_Judgement A SL aux_sort_assignment b) y jby)
            ).

        Definition tj_s_prod
                   (a b c:T)(x y z:C) (jabcx: |- x;a --> b --> c)
                   (jaby: |- y;a --> b)
                   (jaz: |- z; a): (|- s ° x ° y °z; c):=
          projT2
            (ctskt_s_prod
               A SL aux_sort_assignment a b c
               (existT (Typing_Judgement A SL aux_sort_assignment (a --> b --> c)) x jabcx)
               (existT (Typing_Judgement A SL aux_sort_assignment (a --> b)) y jaby)
               (existT (Typing_Judgement A SL aux_sort_assignment a) z jaz)
            ).

        Definition tj_s_expr
                   (a b c:T)(x y z:C) (jabcx: |- x;a --> b --> c)
                   (jaby: |- y;a --> b)
                   (jaz: |- z; a): (|- x ° z ° (y ° z); c):=
          projT2
            (ctskt_s_expr
               A SL aux_sort_assignment a b c
               (existT (Typing_Judgement A SL aux_sort_assignment (a --> b --> c)) x jabcx)
               (existT (Typing_Judgement A SL aux_sort_assignment (a --> b)) y jaby)
               (existT (Typing_Judgement A SL aux_sort_assignment a) z jaz)
            ).

        Inductive k_sc_prod:forall (t:T)(u:C),(|- u;t) -> Type:=
        |kp_init: forall (a b:T)(x y:C) (jax: |- x; a) (jby: |- y;b),
            strongly_computable a x jax ->
            strongly_computable b y jby ->
            k_sc_prod a (k ° x ° y) (tj_k_prod a b x y jax jby)
        |kp_app: forall (a b:T) (f x:C) (jabf: |- f; a-->b) (jax: |- x; a),
            strongly_computable a x jax ->
            k_sc_prod (a-->b) f jabf ->
            k_sc_prod b (f ° x) (tj_arr a b f x jabf jax).           

        Inductive s_sc_prod:forall (t:T)(u:C),(|- u;t) -> Type:=
        |sp_init: forall (a b c:T)(x y z:C)
                         (jabcx: |- x; a --> b --> c)
                         (jaby: |- y; a --> b)
                         (jaz: |- z; a),
            strongly_computable (a --> b --> c) x jabcx ->
            strongly_computable (a --> b) y jaby ->
            strongly_computable a z jaz ->
            s_sc_prod c (s ° x ° y ° z) (tj_s_prod a b c x y z jabcx jaby jaz)
        |sp_app: forall (a b:T) (f x:C) (jabf: |- f; a-->b) (jax: |- x; a),
            strongly_computable a x jax ->
            s_sc_prod (a-->b) f jabf ->
            s_sc_prod b (f ° x) (tj_arr a b f x jabf jax).

        Fixpoint SC_stability
                 (x:C)(a:T)(jx:|- x;a)(y:C)(jy:|- y;a)(r:x>dy){struct a}:
          strongly_computable a x jx ->
          strongly_computable a y jy.
        Proof.
          destruct a.
          simpl.
          intros.
          apply SN_stability with (x:=x); assumption.
          intros.
          assert (forall (z:C) (h: |- z;a1),
                     strongly_computable a1 z h ->
                     strongly_computable a2 (y ° z) (tj_arr a1 a2 y z jy h)) as E.
          intros.
          apply SC_stability with
              (x:=x ° z)
              (jx:= tj_arr a1 a2 x z jx h).
          apply dr_left; assumption.
          apply sc_morphism.
          assumption.
          assumption.
          intro.
          intros.
          apply E.
          assumption.
        Defined.
        
        Definition sc_double_halt:
          forall (a b:T)(x y:C)(jax: |- x; a)(jby: |- y;b),
            strongly_computable a x jax ->
            strongly_computable b y jby ->
            double_sn x y.
        Proof.
          intros.
          apply double_halt.
          apply lh_sc with (a:=a)(j:=jax)(x:=x); assumption.          
          apply lh_sc with (a:=b)(j:=jby)(x:=y); assumption.
        Defined.

        Definition rp_destructor (P:C -> C -> C -> Type):
          (forall (x y:C), P (k ° x) y x) ->
          (forall (x y z:C), P (s ° x ° y)  z (x ° z ° (y ° z))) ->
          (forall (x x' y:C), x>d x' -> P x y (x' ° y)) ->
          (forall (x y y':C), y>d y' -> P x y (x ° y')) ->
          forall x y z:C, x ° y >d z -> P x y z.
        Proof.
          intros.
          inversion X3.
          apply X.
          apply X0.
          apply X1; assumption.
          apply X2; assumption.
        Defined.

        Notation j_forward :=
          (fun (x y:C) (a:T) (r: x>d y) (j: |- x;a) =>
             (direct_subject_reduction A SL aux_sort_assignment x y a r j)).       

        
        Definition rk_destructor
                   (P:C -> C -> C -> Type):
          (forall (x y:C), P x y x) ->
          (forall (x x' y:C), x >d x' ->  P x y (k ° x' ° y)) ->
          (forall (x y y':C), y>d y' -> P x y (k ° x ° y')) ->
          forall (x y z:C), k ° x ° y >d z -> P x y z.
        Proof.
          intros.
          inversion X2.
          apply X.
          inversion X3.
          inversion X4.
          apply X0.          
          assumption.
          apply X1.
          assumption.
        Defined.
        
        Definition dcutk1: let aux :=
                             fun
                               (p q r:C) =>
                               forall (a b:T)
                                      (jp: |- p; (a --> b))(jq: |- q;a),
                                 (k_sc_prod (a --> b) p jp) ->
                                 (strongly_computable a q jq) ->
                                 sum
                                   ({p':C & prod ((prod (r = p' ° q)(p >d p')))
                                                 (|- p'; (a --> b))})
                                   ({q':C & prod (prod (r = p ° q')(q >d q'))
                                                 ({jq': (|- q';a)
                                                        & strongly_computable a q' jq'})})
                         in
                         forall x y z:C, 
                             (x ° y) >d z -> aux x y z. 
        Proof.
          apply rp_destructor.
          intros.
          inversion X.
          inversion X2.
          intros.
          inversion X.
          inversion X2.
          inversion X4.
          intros.
          left.
          exists x'.
          split.
          split.
          reflexivity.
          assumption.
          apply direct_subject_reduction with (x:=x).
          assumption.          
          assumption.
          intros.
          right.
          exists y'.
          split.
          split.
          reflexivity.
          assumption.
          exists (
              direct_subject_reduction
                A SL aux_sort_assignment
                y y' a X jq                          
            ).
          apply SC_stability with (x:= y) (jx:=jq).
          assumption.
          assumption.
        Defined.       
        
        Definition k_sc_ps_zero:
          let aux := fun (x y z:C)=>
        forall (a b:T)(jax: |- x; a) (jby: |- y;b),
            strongly_computable a x jax ->
            strongly_computable b y jby ->
            sum
              ({jz: (|- z; a) & k_sc_prod a z jz})
              ({jz: (|- z; a) & strongly_computable a z jz})
          in
          forall (x y z:C), k ° x ° y >d z -> aux x y z. 
        Proof.
          apply rk_destructor.
          intros.
          right; exists jax.
          assumption.
          intros.
          left.
          exists (tj_k_prod a b x' y (j_forward x x' a X jax) jby).
          apply kp_init.
          apply SC_stability with (x:=x) (jx:=jax).
          assumption.
          assumption.
          assumption.
          intros.
          left.
          exists (tj_k_prod a b x y' jax (j_forward y y' b X jby)).
          apply kp_init.
          assumption.
          apply SC_stability with (x:=y) (jx:=jby).
          assumption.
          assumption.
        Defined.                    

        Fixpoint k_sc_prod_pseudo_stability
                 (a:T)(x z:C)(j:|- x;a)(l:k_sc_prod a x j)
                 (r:x >d z){struct l}: 
          sum
            ({jz: (|- z; a) & k_sc_prod a z jz})
            ({jz: (|- z; a) & strongly_computable a z jz}).                        
        Proof.
          destruct l.
          intros.
          destruct k_sc_ps_zero with
              (a:=a) (b:=b) (x:=x) (y:=y) (z:=z) (jax := jax) (jby := jby).
          assumption.
          assumption.
          assumption.
          left; assumption.
          right; assumption.
          destruct dcutk1 with
              (x:=f) (y:=x) (z:=z) (a:=a) (b:=b) (jp := jabf) (jq:=jax).
          assumption.
          assumption.
          assumption.
          destruct s0 as (p',Pp').
          destruct Pp' as (Qp',Rp').
          destruct Qp' as (ep', Sp').
          rewrite ep'.
          destruct k_sc_prod_pseudo_stability with
              (a:= (a --> b)) (x:=f)(z:=p') (j:=jabf).
          assumption.
          assumption.
          destruct s0 as (jp',Mp').
          left.
          exists (tj_arr a b p' x jp' jax).
          apply kp_app.
          assumption.
          assumption.
          right.
          destruct s0 as (jp',Mp').
          exists (tj_arr a b p' x jp' jax).
          apply sc_morphism.
          assumption.
          assumption.
          destruct s0 as (p',Pp').
          destruct Pp' as (Qp',Rp').
          destruct Qp' as (ep', Sp').
          rewrite ep'.
          left.
          destruct Rp' as (jp',Tp').
          exists (tj_arr a b f p' jabf jp').
          apply kp_app.
          assumption.
          assumption.
        Defined.
        
        Fixpoint k_sc_prod_sn (a:T)(x:C)(j:|- x;a)(l:k_sc_prod a x j) {struct l}:
          SN x.
        Proof.
          destruct l.
          assert (
              let aux := fun (p q:C) =>
                           SN p -> SN q -> SN (k ° p ° q)
              in
              forall p q:C, double_sn p q -> aux p q
            ) as D.
          apply double_sn_rect.
          intros.
          apply sn_intro.
          intros.
          inversion X2.
          rewrite <- H2.
          assumption.
          inversion X3.
          inversion X4.
          apply X.
          apply double_left.
          assumption.
          apply SN_stability with (x:=x0).
          assumption.
          assumption.
          assumption.
          apply X.
          apply double_right.
          assumption.
          assumption.
          apply SN_stability with (x:=y0).
          assumption.
          assumption.
          simpl in D.
          apply D.
          apply double_halt.
          apply lh_sc with (a:=a)(x:=x)(j:=jax).
          assumption.
          apply lh_sc with (a:=b)(x:=y)(j:=jby).
          assumption.
          apply lh_sc with (a:=a)(x:=x)(j:=jax).
          assumption.
          apply lh_sc with (a:=b)(x:=y)(j:=jby).
          assumption.
          assert (
              let aux := fun (p q:C) =>
                           forall b:T,
                           SN p ->
                           SN q ->
                           forall (jp: |- p; a--> b) (jq: |- q;a),
                             (k_sc_prod (a --> b) p jp) ->
                             (strongly_computable a q jq) ->
                           SN (p ° q)
              in
              forall p q:C, double_sn p q -> aux p q
            ) as D.
          apply double_sn_rect.
          intros.
          apply sn_intro.          
          intros.
          destruct dcutk1 with (x:=x0) (y:=y) (z:=y0) (jp:=jp) (jq:=jq) as [Q1|Q2].
          assumption.
          assumption.
          assumption.
          destruct Q1 as (q1,Pq1).
          destruct Pq1 as (Fq1,jq1).
          destruct Fq1 as (eq1,Rq1).
          rewrite eq1.
          destruct k_sc_prod_pseudo_stability with (a:=a --> b0) (x:=x0) (j:=jp)
                                                   (z:=q1).
          assumption.
          assumption.
          destruct s0 as (jps,Eps).
          apply X with (x':=q1) (b:=b0) (jp:=jps) (jq:=jq).
          apply double_left.
          assumption.
          apply SN_stability with (x:=x0).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          destruct s0 as (jps,Eps).          
          apply lh_sc with (a:= b0) (j:= tj_arr a b0 q1 y jps jq).
          apply sc_morphism.
          assumption.
          assumption.
          destruct Q2 as (q2,Pq2).
          destruct Pq2 as (Fq2,Gq2).
          destruct Fq2 as (eq2,Rq2).
          destruct Gq2 as (jq2,Mq2).
          rewrite eq2.
          apply X with (b:=b0) (jp:=jp) (jq:=jq2).
          apply double_right.
          assumption.
          assumption.
          apply lh_sc with (a:=a) (j:=jq2).
          assumption.
          assumption.
          assumption.
          simpl in D.
          assert (SN f) as snf.
          apply k_sc_prod_sn with (a:=a --> b) (j:= jabf).
          assumption.
          assert (SN x) as snx.
          apply lh_sc with (a:= a) (j:= jax).
          assumption.
          apply D with (b:=b) (jp:= jabf) (jq:=jax).
          apply double_halt.
          assumption.
          assumption.
          assumption.
          assumption.         
          assumption.
          assumption.
        Defined.

        Definition rs_destructor
                   (P:C -> C -> C -> C -> Type):
          (forall (x y z:C), P x y z (x ° z ° (y ° z))) ->
          (forall (x x' y z:C), x >d x' ->  P x y z (s ° x' ° y ° z)) ->
          (forall (x y y' z:C), y>d y' -> P x y z (s ° x ° y' ° z)) ->
          (forall (x y z z':C), z>d z' -> P x y z (s ° x ° y ° z')) ->
          forall (x y z t:C), s ° x ° y ° z >d t -> P x y z t.
        Proof.
          intros.
          inversion X3.
          apply X.
          inversion X4.
          inversion X5.
          inversion X6.
          apply X0.          
          assumption.
          apply X1.
          assumption.
          apply X2.
          assumption.
        Defined.
        
        Definition dcuts1: let aux :=
                             fun
                               (p q r:C) =>
                               forall (a b:T)
                                      (jp: |- p; (a --> b))(jq: |- q;a),
                                 (s_sc_prod (a --> b) p jp) ->
                                 (strongly_computable a q jq) ->
                                 sum
                                   ({p':C & prod ((prod (r = p' ° q)(p >d p')))
                                                 (|- p'; (a --> b))})
                                   ({q':C & prod (prod (r = p ° q')(q >d q'))
                                                 ({jq': (|- q';a)
                                                        & strongly_computable a q' jq'})})
                         in
                         forall x y z:C, 
                             (x ° y) >d z -> aux x y z. 
        Proof.
          apply rp_destructor.
          intros.
          inversion X.
          inversion X2.
          intros.
          inversion X.
          inversion X2.
          inversion X4.
          intros.
          left.
          exists x'.
          split.
          split.
          reflexivity.
          assumption.
          apply direct_subject_reduction with (x:=x).
          assumption.          
          assumption.
          intros.
          right.
          exists y'.
          split.
          split.
          reflexivity.
          assumption.
          exists (
              direct_subject_reduction
                A SL aux_sort_assignment
                y y' a X jq                          
            ).
          apply SC_stability with (x:= y) (jx:=jq).
          assumption.
          assumption.
        Defined.       
        
        Definition s_sc_ps_zero:
          let aux :=
              fun (x y z t:C) =>
                forall (a b c:T)
                       (jabcx: |- x; (a --> b --> c))
                       (jaby: |- y; (a --> b))
                       (jaz: |- z;a),
                  strongly_computable (a --> b --> c) x jabcx ->
                  strongly_computable (a --> b) y jaby ->
                  strongly_computable a z jaz ->
                  sum
                    ({jt: (|- t; c) & s_sc_prod c t jt})
                    ({jt: (|- t; c) & strongly_computable c t jt})
          in
          forall (x y z t:C), s ° x ° y ° z >d t -> aux x y z t. 
        Proof.
          apply rs_destructor.
          intros.
          right.
          exists (tj_s_expr a b c x y z jabcx jaby jaz).
          apply sc_morphism.
          apply sc_morphism.
          simpl; assumption.
          simpl; assumption.
          apply sc_morphism.
          simpl; assumption.
          simpl; assumption.                          
          intros.
          left.          
          exists (tj_s_prod a b c x' y z (j_forward x x' (a --> b --> c) X jabcx) jaby jaz).
          apply sp_init.
          apply SC_stability with (x:=x) (jx:=jabcx).
          assumption.
          assumption.
          assumption.
          assumption.
          intros.
          left.
          exists (tj_s_prod a b c x y' z jabcx (j_forward y y' (a --> b) X jaby) jaz).
          apply sp_init.
          assumption.
          apply SC_stability with (x:=y) (jx:=jaby).
          assumption.
          assumption.
          assumption.
          intros.
          left.
          exists (tj_s_prod a b c x y z' jabcx jaby (j_forward z z' a X jaz)).
          apply sp_init.
          assumption.
          assumption.
          apply SC_stability with (x:=z) (jx:=jaz).
          assumption.
          assumption.
        Defined.                    

        Fixpoint s_sc_prod_pseudo_stability
                 (a:T)(x z:C)(j:|- x;a)(l:s_sc_prod a x j)
                 (r:x >d z){struct l}: 
          sum
            ({jz: (|- z; a) & s_sc_prod a z jz})
            ({jz: (|- z; a) & strongly_computable a z jz}).                        
        Proof.
          destruct l.
          intros.
          destruct s_sc_ps_zero with
              (a:=a) (b:=b) (x:=x) (y:=y) (z:=z0) (t:=z)
              (jabcx := jabcx) (jaby := jaby) (jaz:=jaz).
          assumption.
          assumption.
          assumption.
          assumption.
          left; assumption.
          right; assumption.
          destruct dcuts1 with
              (x:=f) (y:=x) (z:=z) (a:=a) (b:=b) (jp := jabf) (jq:=jax).
          assumption.
          assumption.
          assumption.
          destruct s0 as (p',Pp').
          destruct Pp' as (Qp',Rp').
          destruct Qp' as (ep', Sp').
          rewrite ep'.
          destruct s_sc_prod_pseudo_stability with
              (a:= (a --> b)) (x:=f)(z:=p') (j:=jabf).
          assumption.
          assumption.
          destruct s0 as (jp',Mp').
          left.
          exists (tj_arr a b p' x jp' jax).
          apply sp_app.
          assumption.
          assumption.
          right.
          destruct s0 as (jp',Mp').
          exists (tj_arr a b p' x jp' jax).
          apply sc_morphism.
          assumption.
          assumption.
          destruct s0 as (p',Pp').
          destruct Pp' as (Qp',Rp').
          destruct Qp' as (ep', Sp').
          rewrite ep'.
          left.
          destruct Rp' as (jp',Tp').
          exists (tj_arr a b f p' jabf jp').
          apply sp_app.
          assumption.
          assumption.
        Defined.

        Definition sp_init_sn:
          forall (a b c:T) (x y z:C)
                 (jabcx: |- x;(a --> b --> c))
                 (jaby: |- y; (a --> b))
                 (jaz: |- z; a),
            strongly_computable (a --> b --> c) x jabcx ->
            strongly_computable (a --> b) y jaby ->
            strongly_computable a z jaz ->
            SN (s ° x ° y ° z).
        Proof.
          assert (let aux :=
                      fun (x y:C) => SN x -> SN y -> SN (s ° x ° y)
                  in
                  forall x y:C, double_sn x y -> aux x y
                 ) as D1.
          apply double_sn_rect.
          intros.
          apply sn_intro.
          intros.
          inversion X2.
          inversion X3.
          inversion X4.
          apply X.
          apply double_left.
          assumption.
          apply SN_stability with (x:=x); assumption.
          assumption.
          apply X.
          apply double_right.
          assumption.
          assumption.
          apply SN_stability with (x:=y); assumption.
          simpl in D1.
          assert (forall x y:C, SN x -> SN y -> SN (s ° x ° y)) as D2.
          intros.
          apply D1.
          apply double_halt.
          assumption.
          assumption.
          assumption.
          assumption.
          assert (let aux :=
                      fun (p z:C) =>
                        forall x y:C,SN x -> SN y -> SN z -> SN p ->
                                   SN (x ° z ° (y ° z)) ->
                                   (p = s° x ° y) ->
                                   SN (s ° x ° y ° z)
                  in
                  forall p z:C, double_sn p z -> aux p z
                 ) as E1.
          apply double_sn_rect.
          intros.
          apply sn_intro.          
          intros.
          inversion X5.
          assumption.
          inversion X6.
          inversion X7.
          inversion X8.
          apply X with (x' := s ° b' ° y0).
          apply double_left.
          rewrite H.
          apply dr_left; apply dr_right; assumption.
          apply SN_stability with (x:=x0); assumption.
          assumption.
          assumption.
          apply D2.
          apply SN_stability with (x:=x0); assumption.
          assumption.
          apply SN_stability with (x:=x0 ° y ° (y0 ° y)).
          assumption.
          apply dr_left; apply dr_left; assumption.
          reflexivity.
          apply X with (x' := s ° x0 ° b').
          apply double_left.
          rewrite H.
          apply dr_right; assumption.
          assumption.
          apply SN_stability with (x:=y0); assumption.
          assumption.
          apply D2.
          assumption.
          apply SN_stability with (x:=y0); assumption.
          apply SN_stability with (x:=x0 ° y ° (y0 ° y)).
          assumption.
          apply dr_right; apply dr_left; assumption.
          reflexivity.
          apply X with (x' := s ° x0 ° y0).
          rewrite <- H.
          apply double_right.
          assumption.
          assumption.
          assumption.
          apply SN_stability with (x:=y); assumption.
          apply D2.
          assumption.
          assumption.
          apply SN_stability with (x:=x0 ° y ° (y0 ° b')).
          apply SN_stability with (x:=x0 ° y ° (y0 ° y)).
          assumption.
          apply dr_right; apply dr_right; assumption.
          apply dr_left; apply dr_right; assumption.
          reflexivity.
          simpl in E1.
          assert (forall x y z:C,
                     SN x -> SN y -> SN z -> SN (x ° z ° (y ° z)) -> SN (s ° x ° y ° z)
                 ) as E2.
          intros.
          apply E1 with (p:= s ° x ° y).
          apply double_halt.
          apply D2.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          apply D2.
          assumption.
          assumption.
          assumption.
          reflexivity.
          intros.
          apply E2.
          apply lh_sc with (a:=a --> b --> c) (j:= jabcx); assumption.
          apply lh_sc with (a:=a --> b) (j:= jaby); assumption.
          apply lh_sc with (a:=a) (j:= jaz); assumption.
          apply lh_sc with
              (a:=c)
              (j:= tj_s_expr a b c x y z jabcx jaby jaz).
          apply sc_morphism.
          apply sc_morphism.
          assumption.
          assumption.
          apply sc_morphism.
          assumption.
          assumption.
        Defined.
            
        Fixpoint s_sc_prod_sn (a:T)(x:C)(j:|- x;a)(l:s_sc_prod a x j) {struct l}:
          SN x.
        Proof.
          destruct l.
          apply sp_init_sn with
              (a:=a) (b:=b) (c:=c) (jabcx:=jabcx) (jaby:=jaby) (jaz:=jaz).
          assumption.
          assumption.
          assumption.          
          assert (
              let aux := fun (p q:C) =>
                           forall b:T,
                           SN p ->
                           SN q ->
                           forall (jp: |- p; a--> b) (jq: |- q;a),
                             (s_sc_prod (a --> b) p jp) ->
                             (strongly_computable a q jq) ->
                           SN (p ° q)
              in
              forall p q:C, double_sn p q -> aux p q
            ) as D.
          apply double_sn_rect.
          intros.
          apply sn_intro.          
          intros.
          destruct dcuts1 with (x:=x0) (y:=y) (z:=y0) (jp:=jp) (jq:=jq) as [Q1|Q2].
          assumption.
          assumption.
          assumption.
          destruct Q1 as (q1,Pq1).
          destruct Pq1 as (Fq1,jq1).
          destruct Fq1 as (eq1,Rq1).
          rewrite eq1.
          destruct s_sc_prod_pseudo_stability with (a:=a --> b0) (x:=x0) (j:=jp)
                                                   (z:=q1).
          assumption.
          assumption.
          destruct s0 as (jps,Eps).
          apply X with (x':=q1) (b:=b0) (jp:=jps) (jq:=jq).
          apply double_left.
          assumption.
          apply SN_stability with (x:=x0).
          assumption.
          assumption.
          assumption.
          assumption.
          assumption.
          destruct s0 as (jps,Eps).          
          apply lh_sc with (a:= b0) (j:= tj_arr a b0 q1 y jps jq).
          apply sc_morphism.
          assumption.
          assumption.
          destruct Q2 as (q2,Pq2).
          destruct Pq2 as (Fq2,Gq2).
          destruct Fq2 as (eq2,Rq2).
          destruct Gq2 as (jq2,Mq2).
          rewrite eq2.
          apply X with (b:=b0) (jp:=jp) (jq:=jq2).
          apply double_right.
          assumption.
          assumption.
          apply lh_sc with (a:=a) (j:=jq2).
          assumption.
          assumption.
          assumption.
          simpl in D.
          assert (SN f) as snf.
          apply s_sc_prod_sn with (a:=a --> b) (j:= jabf).
          assumption.
          assert (SN x) as snx.
          apply lh_sc with (a:= a) (j:= jax).
          assumption.
          apply D with (b:=b) (jp:= jabf) (jq:=jax).
          apply double_halt.
          assumption.
          assumption.
          assumption.
          assumption.         
          assumption.
          assumption.
        Defined.

        Definition k_sc_prod_sc:
          let aux := fun (a:T) => forall (x:C) (j: |- x;a),
                         k_sc_prod a x j -> strongly_computable a x j
          in
        forall (t:T), aux t.
        Proof.
          apply SK_sort_rect.
          intros.
          simpl.
          apply k_sc_prod_sn in X; assumption.
          intros u E v F x G kp.
          intro.
          intros.
          apply F.
          apply kp_app.
          assumption.
          assumption.
        Defined.

        Definition s_sc_prod_sc:
          let aux := fun (a:T) => forall (x:C) (j: |- x;a),
                         s_sc_prod a x j -> strongly_computable a x j
          in
        forall (t:T), aux t.
        Proof.
          apply SK_sort_rect.
          intros.
          simpl.
          apply s_sc_prod_sn in X; assumption.
          intros u E v F x G sp.
          intro.
          intros.
          apply F.
          apply sp_app.
          assumption.
          assumption.
        Defined.

        Definition K_is_strongly_computable: forall a b:T,
            strongly_computable (a --> b --> a) k (tj_k A SL aux_sort_assignment a b).
        Proof.
          intros.
          intro.
          intros.
          intro.
          intros.
          apply k_sc_prod_sc.
          apply kp_init.
          assumption.
          assumption.
        Defined.

        Definition S_is_strongly_computable: forall a b c:T,
            strongly_computable
              ((a --> b --> c) --> (a --> b) --> a --> c)
              s
              (tj_s A SL aux_sort_assignment a b c).
        Proof.
          intros.
          intro.
          intros.
          intro.
          intros.
          intro.
          intros.
          apply s_sc_prod_sc.
          apply sp_init.
          assumption.
          assumption.
          assumption.
        Defined.
       
      End S_and_K_are_strongly_computable.

      Definition every_typed_term_is_strongly_computable:
        let aux := fun (t:T) (x:C) (j: |-x;t) =>
                     strongly_computable t x j
        in
        forall (t:T) (x:C)(j: |-x;t), aux t x j. 
      Proof.
        apply Typing_Judgement_rect.
        intros.
        apply lh_sc.
        apply lh_atom.
        apply K_is_strongly_computable.
        apply S_is_strongly_computable.
        intros; apply sc_morphism.
        assumption.
        assumption.
      Defined.

      Definition Tait_normalization_theorem_for_the_auxiliary_context:
        forall (x:C) (t:T)(j:|- x;t), strongly_normalizable A x.
      Proof.
        intros.
        apply lh_sc with (a:=t) (j:=j).
        apply every_typed_term_is_strongly_computable.
      Defined.
      
    End strong_computability.
    
    Fixpoint auxiliary_context_term_embedding
             (x: SK_Term Ctxt){struct x}: (SK_Term Auxiliary_context):=
      match x with
      |skt_letter _ l => skt_letter Auxiliary_context (inl l)
      |skt_s _ => skt_s Auxiliary_context 
      |skt_k _ => skt_k Auxiliary_context
      |skt_app _ y z => skt_app Auxiliary_context
                                (auxiliary_context_term_embedding y)
                                (auxiliary_context_term_embedding z)
      end.

    Definition ac_dr_morphism:
      forall (x y:SK_Term Ctxt),
        direct_reduction Ctxt x y ->
        direct_reduction Auxiliary_context
                         (auxiliary_context_term_embedding x)
                         (auxiliary_context_term_embedding y).
    Proof.
      apply direct_reduction_rect.
      intros; apply dr_k.
      intros; apply dr_s.
      intros; apply dr_left.
      assumption.
      intros; apply dr_right.
      assumption.
    Defined.
    
    Definition auxiliary_sn_pullback: forall x:SK_Term Ctxt,
        strongly_normalizable Auxiliary_context (auxiliary_context_term_embedding x) ->
        strongly_normalizable Ctxt x.
    Proof.
      assert (let aux :=
                  fun u: SK_Term Auxiliary_context =>
                    forall x:SK_Term Ctxt,
                      direct_reduction
                        Auxiliary_context
                        u (auxiliary_context_term_embedding x) ->
                      strongly_normalizable Ctxt x
              in
              forall v:SK_Term Auxiliary_context,
                strongly_normalizable Auxiliary_context v -> aux v

             ) as L.
      apply strongly_normalizable_rect.
      intros.
      apply sn_intro.
      intros.
      apply X with (x:=y) (y:= auxiliary_context_term_embedding x0).
      assumption.
      apply ac_dr_morphism.
      assumption.
      simpl in L.
      intros.
      apply sn_intro.
      intros.
      apply L with (v:= auxiliary_context_term_embedding x).
      assumption.
      apply ac_dr_morphism.
      assumption.
    Defined.   
      
    Fixpoint auxiliary_context_tj_embedding
             (t:SK_sort SL)
             (x:SK_Term Ctxt)(j: Typing_Judgement Ctxt SL sort_assignment t x){struct j}:
      Typing_Judgement Auxiliary_context SL aux_sort_assignment t
                       (auxiliary_context_term_embedding x).
    Proof.
      destruct j.
      simpl. apply tj_letter with (x:=inl x).
      apply tj_k.
      apply tj_s.
      apply tj_arrow with (a:=a).
      apply auxiliary_context_tj_embedding; apply j1.
      apply auxiliary_context_tj_embedding; apply j2.
    Defined.

    Definition Tait_strong_normalization_theorem:
      forall (x:SK_Term Ctxt) (t: SK_sort SL),
        Typing_Judgement Ctxt SL sort_assignment t x ->
        strongly_normalizable Ctxt x.
    Proof.
      intros.
      apply auxiliary_sn_pullback.
      apply Tait_normalization_theorem_for_the_auxiliary_context with (t:=t).
      apply auxiliary_context_tj_embedding.
      assumption.
    Defined.

    Definition no_infinite_reduction_sequence_if_typable_with_types:
        forall (Error:Type) (u: nat -> SK_Term Ctxt) (t: SK_sort SL),          
          Typing_Judgement Ctxt SL sort_assignment t (u 0) ->
          (forall n:nat, direct_reduction Ctxt (u n) (u (S n))) ->
          Error.
    Proof.
      intros Error u t j.
      apply no_infinite_reduction_sequence_if_strongly_normalizable_with_types.
      apply Tait_strong_normalization_theorem with (t:=t). assumption.
    Defined.

    Theorem no_infinite_reduction_sequence_if_typable:
        forall (u: nat -> SK_Term Ctxt) (t: SK_sort SL),          
          Typing_Judgement Ctxt SL sort_assignment t (u 0) ->
          (forall n:nat, direct_reduction Ctxt (u n) (u (S n))) ->
          False.
    Proof.
      intros u t j.
      apply no_infinite_reduction_sequence_if_strongly_normalizable.
      apply Tait_strong_normalization_theorem with (t:=t). assumption.
    Defined.
    
  End Tait.

  Section An_elementary_abstraction_operator.

    Variable Ctxt SL:Type.
    Variable sort_assignment: Ctxt -> SK_sort SL.
    
    Notation C:= (SK_Term Ctxt).
    Notation s:= (skt_s Ctxt).
    Notation k:= (skt_k Ctxt).
    Notation var:= (skt_letter Ctxt).
    Notation "a ° b" := (skt_app Ctxt a b) (left associativity, at level 51).
    Notation T:= (SK_sort SL).
    Notation "a --> b":= (sks_arrow SL a b) (right associativity, at level 61).
    Notation "|- p ; q":=
      (Typing_Judgement Ctxt SL sort_assignment q p) (at level 62).
    Notation A:= Ctxt.
    Notation "m >d n":= (direct_reduction A m n) (at level 63).
    Notation "m >b n":= (beta_reduction A m n) (at level 63).

    (** this is a crude and *highly* unoptimized example of abstraction operator we 
     include for its simplicity, its purpose is often to prove that SK is Turing complete
     among other results
     A new variable (to be bound by "simple_lambda") is added to the current context with 
     the coq "option" constructor, below we prove its basic properties with respect to 
     substitution and typing.
     *)
    
    Fixpoint simple_lambda (t:SK_Term (option Ctxt)){struct t}:=
      match t with
      |skt_letter _ l => match l with
                         |Some v => k ° (var v)
                         |None => skt_i Ctxt
                         end 
      |skt_k _ => k ° k
      |skt_s _ => k ° s
      |skt_app _ x y => s ° (simple_lambda x) ° (simple_lambda y)
      end.

    Fixpoint sk_specialize (t:C) (f:SK_Term (option Ctxt)){struct f}:=
      match f with
      |skt_letter _ l => match l with
                         |Some v => var v
                         |None => t
                         end 
      |skt_k _ => k 
      |skt_s _ => s
      |skt_app _ x y => (sk_specialize t x) ° (sk_specialize t y)
      end.

    Definition simple_lambda_specialization_property:
      forall (t:C)(f:SK_Term (option Ctxt)),
        (simple_lambda f)° t >b (sk_specialize t f).
    Proof.
      intro.
      apply SK_Term_rect.
      intros.
      destruct c.
      simpl.
      apply br_k.
      simpl.
      apply br_i.
      simpl.
      apply br_k.
      simpl.
      apply br_k.
      intros x E y F.
      simpl.
      apply br_transitivity with (y:= ((simple_lambda x) ° t) ° ((simple_lambda y) ° t)).
      apply br_s.
      apply br_leftright.
      assumption.
      assumption.
    Defined.

    (** We assign a sort to the new variable*)

    Variable domain:T.
    
    Definition add_sort (u:option Ctxt):T:=
               match u with
               |Some v => sort_assignment v
               |None => domain
               end.

    Fixpoint simple_lambda_tj
             (f: SK_Term (option Ctxt)) (range:T)
             (j:Typing_Judgement (option Ctxt) SL add_sort range f){struct j}:
    |- (simple_lambda f); (domain --> range).
    Proof.
      destruct j.
      simpl.
      destruct x.
      apply tj_arrow with (a:= (add_sort (Some c))).
      apply tj_k.
      apply tj_letter.
      simpl.
      apply tj_i.
      simpl.
      apply tj_arrow with (a:= (a --> b --> a)).
      apply tj_k.
      apply tj_k.
      apply tj_arrow with (a:= (a --> b --> c) --> (a --> b) --> a --> c).
      apply tj_k.
      apply tj_s.
      simpl.
      apply tj_arrow with (a:= domain --> a).
      apply tj_arrow with (a:= domain --> a --> b).
      apply tj_s.
      apply simple_lambda_tj.
      assumption.
      apply simple_lambda_tj.
      assumption.
    Defined.      
      
  End An_elementary_abstraction_operator.

  Section Basic_arithmetics_and_a_fixed_point_combinator.

    Variable Ctxt SL:Type.

    Notation C:= (SK_Term Ctxt).
    Notation s:= (skt_s Ctxt).
    Notation k:= (skt_k Ctxt).
    Notation var:= (skt_letter Ctxt).
    Notation "a ° b" := (skt_app Ctxt a b) (left associativity, at level 51).
    Notation "m >d n":= (direct_reduction Ctxt m n) (at level 63).
    Notation "m >b n":= (beta_reduction Ctxt m n) (at level 63).
    Notation i:= (skt_i Ctxt).

    Ltac bt h:= apply br_transitivity with (y:=h).
    Ltac bk:= apply br_k.
    Ltac bs:= apply br_s.
    Ltac bl:= apply br_left.
    Ltac br:= apply br_right.
    Ltac bi:= apply br_i.
    Ltac blr:= apply br_leftright.
    
    Definition skt_u:C:= s ° (k ° (s ° i)) ° (s ° i ° i).   
    
    Definition br_u: forall x y:C,
        skt_u ° x ° y >b y ° (x ° x ° y).
    Proof.
      intros.
      unfold skt_u.
      bt ((k ° (s ° i) ° x) ° (s ° i ° i ° x) ° y).
      bl; bs.
      bt (s ° i ° (x ° x) ° y).
      bl.
      blr.
      bk.
      bt (i ° x ° (i ° x)).
      bs.
      blr; bi; bi.
      bt (i ° y ° (x ° x ° y)).
      bs.
      bl; bi.
    Defined.

    Definition Turing_fixed_point_combinator:C:= skt_u ° skt_u.

    Definition Turing_fixed_point_combinator_identity:
      forall f:C, Turing_fixed_point_combinator ° f >b f ° (Turing_fixed_point_combinator ° f).
    Proof.
      intros.
      unfold Turing_fixed_point_combinator.
      apply br_u.
    Defined.

    Definition skt_b: C:= s ° (k ° s) ° k.

    Definition br_b: forall x y z:C,
        skt_b ° x ° y ° z >b x ° (y ° z).
    Proof.
      intros.
      unfold skt_b.
      bt (k ° s ° x ° (k ° x) ° y ° z).
      bl; bl; bs.
      bt (s ° (k ° x) ° y ° z).
      bl; bl; bl; bk.
      bt (k ° x ° z ° (y ° z)).
      bs.
      bl.
      bk.
    Defined.

    Ltac bb:= apply br_b.
    
    Definition skt_w:C:= s ° s° (s ° k).

    Definition br_w: forall x y:C, skt_w ° x ° y >b x ° y ° y.
    Proof.
      intros; unfold skt_w. bt (s ° x ° (s ° k ° x) ° y). bl. bs.
      bt (x ° y ° (s ° k ° x ° y)). bs. br. bt (k ° y ° (x ° y)). bs. bk.
    Defined.      
      
    Ltac bw := apply br_w.     

    Definition skt_t:C:= s° (k ° (s ° i)) ° k.

    Definition br_t: forall x y:C,
        skt_t ° x ° y >b y ° x.
    Proof.
      intros.
      unfold skt_t.
      bt (s ° i ° (k ° x) ° y).
      bl.
      bt (k ° (s ° i) ° x ° (k ° x)).
      bs.
      bl; bk.
      bt (i ° y ° (k ° x ° y)).
      bs.
      blr.
      bi.
      bk.
    Defined.
      
    Ltac bT:= apply br_t.
    
    Definition skt_c:C:= s° (s ° (k ° s) ° (s ° (k ° k) ° s)) ° (k ° k).

    Definition br_c: forall x y z:C,
        skt_c ° x ° y ° z >b x ° z ° y.
    Proof.
      intros; unfold skt_c.      
      bt (s ° (k ° (s ° x)) ° k ° y ° z).
      bl; bl. bt (s ° (k ° s) ° (s ° (k ° k) ° s) ° x ° (k ° k ° x)).
      bs. blr. bt (k ° s ° x ° (s ° (k ° k) ° s ° x)).
      bs. blr. bk. bt (k ° k ° x ° (s ° x)). bs. bl. bk. bk.
      bt (s ° x ° (k ° y) ° z). bl. bt (k ° (s ° x) ° y ° (k ° y)). bs. bl; bk.
      bt (x ° z ° (k ° y ° z)). bs. br. bk.
    Defined.

    Ltac bc := apply br_c.

    Definition skt_v:C := s ° (k ° skt_c) ° skt_t.

    Definition br_v: forall x y z:C,
        skt_v ° x ° y ° z >b z ° x ° y.
    Proof.
      intros.
      unfold skt_v. bt (skt_c ° (skt_t ° x) ° y ° z). bl; bl.
      bt (k ° skt_c ° x ° (skt_t ° x)). bs. bl; bk. bt (skt_t ° x ° z ° y). bc. bl. bT.
    Defined.

    Ltac bv := apply br_v.
    
    Definition skt_succ:C:= s ° skt_b.

    Definition skt_zero:C := s ° k.

    Definition br_succ: forall n f x:C,
        skt_succ ° n ° f ° x >b f ° (n ° f ° x).
    Proof.
      intros.
      unfold skt_succ.
      bt (skt_b ° f ° (n ° f) ° x).
      bl; bs.
      bb.
    Defined.

    Ltac bsucc := apply br_succ.
    
    Definition br_zero: forall f x:C,
        skt_zero ° f ° x >b x.
    Proof.
      intros.
      unfold skt_zero.
      bt (k ° x ° (f ° x)). bs. bk.
    Defined.

    Ltac b0:= apply br_zero.

    Fixpoint Church_integer (n:nat) {struct n}:C:=
      match n with
      |0 => skt_zero
      |S m => skt_succ ° (Church_integer m)
      end.

    Definition skt_plus := skt_t ° skt_succ.

    Definition sk_integer_sum_identity:
      forall p q:nat,
        (Church_integer q) ° skt_succ ° (Church_integer p) >b Church_integer (q + p).
    Proof.
      intro p; induction q.
      simpl.
      b0.
      simpl.
      bt (skt_succ ° (Church_integer q ° skt_succ ° Church_integer p)).
      bsucc.
      br; apply IHq.
    Defined.
                                                             
    Definition br_plus: forall (m n:nat),
        skt_plus ° (Church_integer n) ° (Church_integer m)
        >b
        Church_integer (n + m).                                                      
    Proof.
      intros.
      unfold skt_plus.
      bt (Church_integer n ° skt_succ ° Church_integer m).
      bl; bT.
      apply sk_integer_sum_identity.
    Defined.

    Ltac bplus := apply br_plus.

    Definition sk_integer_product_identity: forall n m:nat,
        (Church_integer m) ° (skt_plus ° Church_integer n) ° skt_zero
        >b Church_integer (m * n).
    Proof.
      intro n; induction m.
      simpl; b0.
      simpl.
      bt (skt_plus ° (Church_integer n) °
                   (Church_integer m  ° (skt_plus ° (Church_integer n)) ° skt_zero)).
      bsucc. bt (skt_plus ° (Church_integer n) ° (Church_integer (m * n))).
      br; apply IHm.
      simpl; bplus.
    Defined.

    Definition operator_iter (op init:C):C:=
      skt_c ° (skt_b ° (skt_c ° skt_v ° init) ° op). 

    Definition operator_iter_identity: forall (op init x y:C),
        (operator_iter op init) ° x ° y
        >b x ° (op ° y) ° init.
    Proof.
      intros; unfold operator_iter.
      bt (skt_b ° (skt_c ° skt_v ° init) ° op ° y ° x).
      bc.
      bt (skt_c ° skt_v ° init ° (op ° y) ° x). bl; bb.
      bt (skt_v ° (op ° y) ° init ° x). bl; bc. bv.
    Defined.      
    
    Definition skt_product:C := operator_iter skt_plus skt_zero.

    Definition br_product: forall m n:nat,
        skt_product ° (Church_integer m) ° (Church_integer n)
        >b
           Church_integer (m * n).
    Proof.
      intros.
      unfold skt_product.
      bt (Church_integer m ° (skt_plus ° (Church_integer n)) ° skt_zero).
      apply operator_iter_identity.
      apply sk_integer_product_identity.
    Defined.

    Ltac bproduct := apply br_product.
    
    Definition skt_power:C:= skt_c ° (operator_iter skt_product (Church_integer 1)).
    
    Definition sk_integer_power_identity: forall n m:nat,
        (Church_integer m) ° (skt_product ° Church_integer n) ° (Church_integer 1)
        >b Church_integer (Nat.pow n m).
    Proof.
      intro n; induction m.
      simpl.
      b0.
      simpl.
      bt (skt_product ° (Church_integer n) °
                      (Church_integer m  ° (skt_product ° (Church_integer n)) °
                                      (Church_integer 1))).
      bsucc. bt (skt_product ° (Church_integer n) ° (Church_integer (Nat.pow n m))).
      br; apply IHm.
      simpl. bproduct.      
    Defined.

    Definition br_power: forall m n:nat,
        skt_power ° (Church_integer m) ° (Church_integer n)
        >b Church_integer (Nat.pow m n).
    Proof.                   
      intros.
      unfold skt_power.
      bt (operator_iter skt_product (Church_integer 1) °
                        (Church_integer n) ° (Church_integer m)). bc.
      bt ((Church_integer n) ° (skt_product ° Church_integer m) ° (Church_integer 1)).
      apply operator_iter_identity.
      apply sk_integer_power_identity.
    Defined.
    
    (** substractions are trickier to implement; we need additional tools.*)

    Definition skt_proj1:= skt_t ° k.
    Definition skt_proj2:= skt_t ° skt_zero.

    Definition br_proj1: forall x y:C, skt_proj1 ° (skt_v ° x ° y) >b x.
    Proof.
      intros.
      bt (skt_v ° x ° y ° k). bT. bt (k ° x ° y). bv. bk.
    Defined.

    Ltac bp1 := apply br_proj1.

    Definition br_proj2: forall x y:C, skt_proj2 ° (skt_v ° x ° y) >b y.
    Proof.
      intros.
      bt (skt_v ° x ° y ° skt_zero). bT. bt (skt_zero ° x ° y). bv. b0.
    Defined.

    Ltac bp2 := apply br_proj2.

    Definition parametric_iterator_aux (f:C):C:=
      s ° (skt_b ° skt_v ° (skt_b ° skt_succ ° skt_proj1)) °
        (s ° (skt_b ° f ° skt_proj1) ° skt_proj2).

    Definition parametric_iterator_aux_identity: forall f p:C,
        parametric_iterator_aux f ° p
        >b
           skt_v ° (skt_succ ° (skt_proj1 ° p)) ° (f ° (skt_proj1 ° p) ° (skt_proj2 ° p)).
    Proof.
      intros.
      bt (skt_b ° skt_v ° (skt_b ° skt_succ ° skt_proj1) ° p °
                (s ° (skt_b ° f ° skt_proj1) ° skt_proj2 ° p)).
      bs. blr. bt (skt_v ° (skt_b ° skt_succ ° skt_proj1 ° p)). bb.
      br. bb.
      bt (skt_b ° f ° skt_proj1 ° p ° (skt_proj2 ° p)). bs.
      bl. bb. 
    Defined.

    Definition skt_pia:C:=
      skt_b ° (s ° (skt_b ° skt_v ° (skt_b ° skt_succ ° skt_proj1))) °
            (skt_c ° (skt_b ° s ° (skt_c ° skt_b ° skt_proj1)) ° skt_proj2).

    Definition br_pia: forall (f p:C),
        skt_pia ° f ° p
        >b
           skt_v ° (skt_succ ° (skt_proj1 ° p)) ° (f ° (skt_proj1 ° p) ° (skt_proj2 ° p)).
    Proof.
      intros.
      bt ((parametric_iterator_aux f) ° p). bl.
      bt (s ° (skt_b ° skt_v ° (skt_b ° skt_succ ° skt_proj1)) °
            (skt_c ° (skt_b ° s ° (skt_c ° skt_b ° skt_proj1)) ° skt_proj2 ° f)).
      unfold skt_pia. bb. br. bt (skt_b ° s ° (skt_c ° skt_b ° skt_proj1) ° f ° skt_proj2).
      bc. bl. bt (s ° (skt_c ° skt_b ° skt_proj1 ° f)). bb. br. bc.
      apply parametric_iterator_aux_identity.
    Defined.

    Ltac bpia := apply br_pia.
      
    Definition parametric_iterator (f init n:C):C:=
      skt_proj2
        ° (n ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)).

    Definition parametric_iterator_init_identity: forall (f init:C),
        parametric_iterator f init skt_zero
        >b
           init.
    Proof.
      intros. bt (skt_proj2 ° (skt_v ° skt_zero ° init)). br; b0. bp2. 
    Defined.

    Definition parametric_iterator_first_coordinate: forall (f init:C) (n:nat),
      skt_proj1
        ° ((Church_integer n) ° (skt_pia ° f) ° (skt_v ° skt_zero ° init))
      >b Church_integer n.
    Proof.
      intros f init. induction n.
      simpl. bt (skt_proj1 ° (skt_v ° skt_zero ° init)). br; b0. bp1.
      simpl.
      bt (skt_proj1 ° (skt_pia ° f
                               ° ((Church_integer n) ° (skt_pia ° f) °
                                                     (skt_v ° skt_zero ° init)))).
      br. bsucc.
      bt (skt_proj1
            ° (skt_v 
                 ° (skt_succ
                      ° (skt_proj1
                           °((Church_integer n)
                               ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))) °
                 (f ° (skt_proj1
                         ° ((Church_integer n)
                              ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))
                    ° (skt_proj2
                         ° ((Church_integer n)
                              ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))))).
      br.
      bpia.
      bt (skt_succ
            ° (skt_proj1
                 °((Church_integer n)
                     ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))). bp1.
      br; apply IHn.      
    Defined.    
    
    Definition parametric_iterator_succ_identity: forall (f init:C) (n:nat),
        parametric_iterator f init (Church_integer (S n))
        >b
        f ° (Church_integer n) ° (parametric_iterator f init (Church_integer n)).  
    Proof.
      intros.
      unfold parametric_iterator. simpl.
      bt (skt_proj2 ° ((skt_pia ° f)
                         ° ((Church_integer n) ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))).
      br. bsucc.         
      bt (skt_proj2
            ° (skt_v 
                 ° (skt_succ
                      ° (skt_proj1
                           °((Church_integer n)
                               ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))) °
                 (f ° (skt_proj1
                         ° ((Church_integer n)
                              ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))
                    ° (skt_proj2
                         ° ((Church_integer n)
                              ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))))).
      br.
      bpia.
      bt (f ° (skt_proj1 ° (Church_integer n ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))
            ° (skt_proj2 ° (Church_integer n ° (skt_pia ° f) ° (skt_v ° skt_zero ° init)))).
      bp2.
      bl. br. apply parametric_iterator_first_coordinate.     
    Defined.      

    Definition skt_pred:C:=
      skt_b ° skt_proj2 ° (skt_v ° (skt_pia ° k) ° (skt_v ° skt_zero ° skt_zero)).    

    Definition pred_pi_identity: forall n:C,
        skt_pred ° n >b parametric_iterator k skt_zero n.
    Proof.
      intros.
      bt (skt_proj2 ° (skt_v ° (skt_pia ° k) ° (skt_v ° skt_zero ° skt_zero) ° n)).
      bb. br; bv.
    Defined.

    Definition pred_zero_identity:
      skt_pred ° skt_zero >b skt_zero.
    Proof.
      intros.
      bt (parametric_iterator k skt_zero skt_zero).
      apply pred_pi_identity. simpl. apply parametric_iterator_init_identity.
    Defined.
    
    Definition pred_succ_identity:
      forall n:nat, skt_pred ° (Church_integer (S n)) >b Church_integer n.
    Proof.
      intros.
      bt (parametric_iterator k skt_zero (Church_integer (S n))).
      apply pred_pi_identity.
      bt (k ° (Church_integer n) ° (parametric_iterator k skt_zero (Church_integer n))).
      apply parametric_iterator_succ_identity. bk.
    Defined.

    Definition br_pred: forall n:nat,
        skt_pred ° (Church_integer n) >b Church_integer (Nat.pred n).
    Proof.
      destruct n.
      simpl. apply pred_zero_identity.
      apply pred_succ_identity.
    Defined.

    Fixpoint nat_custom_minus (p q:nat){struct q}:=
      match q with
      | 0 => p
      | S r => Nat.pred (nat_custom_minus p r)
      end.

    Fixpoint cm_sub_eq (p q:nat) {struct p}: Nat.sub p q = nat_custom_minus p q. 
    Proof.
      assert (forall x y:nat, x - y = Nat.pred (S x - y)) as E.
      induction x.
      intros. destruct y. simpl; reflexivity. simpl; reflexivity.
      intros. destruct y. simpl; reflexivity. simpl. apply IHx.             
      destruct p. induction q. simpl; reflexivity. simpl. simpl in IHq. rewrite <- IHq. simpl.
      simpl; reflexivity.
      induction q. simpl; reflexivity. simpl. rewrite <- IHq. apply E.
    Defined.

    Definition skt_minus:= skt_c ° (skt_t ° skt_pred).

    Definition skt_minus_identity: forall m n:nat,
        (Church_integer n) ° skt_pred ° (Church_integer m) 
        >b
           Church_integer (nat_custom_minus m n).
    Proof.
      intro m. induction n. simpl. b0.
      simpl. bt (skt_pred ° ((Church_integer n) ° skt_pred ° (Church_integer m))).
      bsucc. bt (skt_pred ° (Church_integer (nat_custom_minus m n))). br. assumption.
      apply br_pred.
    Defined.

    Definition br_minus: forall m n:nat,
        skt_minus ° (Church_integer m) ° (Church_integer n) 
        >b
           Church_integer (m - n).
    Proof.
      intros. rewrite cm_sub_eq.
      bt ((Church_integer n) ° skt_pred ° (Church_integer m)).
      bt (skt_t ° skt_pred ° (Church_integer n) ° (Church_integer m)). bc. bl. bT.
      apply skt_minus_identity.
    Defined.

    Section basic_undecidability.

      (** In the following, "Error" can be anything, including the empty set or False. 
        The message is that no combinator can reduce to both k and k ° i, and 
       no non trivial characteristic function on combinators can be represented by a 
       combinator: a characteristic map takes its value in the set of booleans which are 
       k and k ° i in combinatory logic; such a map is a boolean test. The Rice theorem
       prevents the existence of such a test unless it is constant: otherwise the program 
       below builds a term on which the test returns a result which is neither 
       true (k) or false (k ° i).*)
      
      Definition skt_boolean_soundness: forall (Error:Type) (u:C),
        (u >b k) -> (u >b k ° i) -> Error.
      Proof.
        intros.
        destruct Church_Rosser with (context := Ctxt) (a:= u) (b:= k) (c:= k ° i).
        assumption. assumption.
        assert (let aux := fun (a b:C) => k = a -> k = b in
                forall a b:C, a >b b -> aux a b) as RK.
        apply beta_reduction_ind. intros; assumption.
        intros. apply H in H0. rewrite <- H0 in d. inversion d. simpl in RK.
        assert (let aux := fun (a b:C) => k ° i = a -> k ° i = b in
                forall a b:C, a >b b -> aux a b) as RKI.
        apply beta_reduction_ind. intros; assumption.
        intros. apply H in H0. rewrite <- H0 in d. inversion d. inversion X1. apply f_equal.
        inversion X1. inversion X2. inversion X3. inversion X3. inversion X2. simpl in RKI.
        destruct p as (r1,r2). apply RK in r1. apply RKI in r2. rewrite <- r1 in r2.
        absurd (k ° i = k). discriminate. assumption. reflexivity. reflexivity.
      Defined.

      Definition Rice: forall (a b test:C) (Error:Type),
          test ° a >b k ->
          test ° b >b k ° i -> 
          {n:C & prod (test ° n >b k -> Error) (test ° n >b k ° i -> Error)}.
      Proof.
        intros.
        assert ({m:C & m >b test ° m ° b ° a}) as M.
        exists (skt_u ° skt_u ° (skt_b ° (skt_v ° b ° a) ° test)).
        bt (skt_b ° (skt_v ° b ° a) ° test
                  ° (skt_u ° skt_u ° (skt_b ° (skt_v ° b ° a) ° test))).
        apply Turing_fixed_point_combinator_identity.
        bt (skt_v ° b ° a ° 
                  (test ° (skt_u ° skt_u ° (skt_b ° (skt_v ° b ° a) ° test)))).
        bb. bv.
        destruct M as (m,rm).
        exists m.
        split.
        intro.
        apply skt_boolean_soundness with (u:= test ° m). assumption.
        bt (test ° b). br. bt (test ° m ° b ° a). assumption. bt (k ° b ° a).
        bl; bl; assumption. bk. assumption.
        intro.
        apply skt_boolean_soundness with (u:= test ° m).
        bt (test ° a). br. bt (test ° m ° b ° a). assumption. bt (k ° i ° b ° a).
        bl; bl; assumption. bt (i ° a). bl; bk. bi. assumption. assumption.
      Defined.
          
    End basic_undecidability.
    
  End Basic_arithmetics_and_a_fixed_point_combinator.
  
End main.
