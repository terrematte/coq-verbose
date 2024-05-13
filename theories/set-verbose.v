Notation "++ A" := (True -> A) (at level 100).
Notation "-- A" := (not A) (at level 99).

Variable U : Type.

Definition Ensemble := U -> Prop.

Definition In (A:Ensemble) (x:U) : Prop := A x.

Definition Included (B C:Ensemble) : Prop := forall x:U, (++ In B x) -> (++ In C x).

Inductive Empty_set : Ensemble :=.

Inductive Union (B C:Ensemble) : Ensemble :=
| Union_introl : forall x:U, (++ In B x) -> (++ In (Union B C) x)
| Union_intror : forall x:U, (++ In C x) -> (++ In (Union B C) x).

Inductive Intersection (B C:Ensemble) : Ensemble :=
Intersection_intro :
forall x:U, (++ In B x) -> (++ In C x) -> In (Intersection B C) x.

Definition Difference (B C:Ensemble) : Ensemble :=
fun x:U => (++ In B x) /\ (-- In C x).

Inductive Symmetric_difference (B C:Ensemble) : Ensemble :=
| Symm_diff_introl : forall x:U, (++ In (Difference B C) x)
  -> (++ In (Symmetric_difference B C) x)
| Symm_diff_intror :  forall x:U, (++ In (Difference C B) x)
  -> (++ In (Symmetric_difference B C) x).

Definition Exclusion (B C:Ensemble) : Prop := forall x:U,
((++ In B x) -> (-- In C x)) \/ ((++ In C x) -> (-- In B x)).

Notation "x ∈ A" := (In A x) (at level 50).
Notation "A ⊆ B" := (Included A B) (at level 51).
Notation "A ⋎ B" := (Exclusion A B) (at level 51).
Notation "A ∩ B" := (Intersection A B) (at level 49).
Notation "A ∪ B" := (Union A B) (at level 46).
Notation "A \ B" := (Difference A B) (at level 48).
Notation "A △ B" := (Symmetric_difference A B) (at level 47).
                                                         
Axiom ax_pbc : forall (P : Prop), (~P -> False) -> P.

Axiom denial_involutive : forall (P : Prop), (-- (-- P)) = ++ P.

Axiom denial_of_assertion : forall (P : Prop), (-- (++ P)) = -- P.
 
Ltac ass X := exact X.

Ltac pps Q :=
  lazymatch goal with
  | |- False =>
  let H := fresh "H" in
  let H0 := fresh "H0" in
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in  
  assert (H : ((++ Q) /\ (-- Q)) -> False);
  [ intro H0; elim H0; intros H1 H2; unfold "--" in H2;
    apply H2 in H1; auto
  | apply H; split; clear H]
  | _ => fail "(not a contradiction)"
  end.


Ltac alvo_def_rel_l x i s :=
  lazymatch goal with
  | |- ++ ?P =>
    match P with
    | ?L ⊆ ?R =>
      match L with
      | s =>
        let H := fresh "H" in
        unfold "⊆";
        intro H; clear H;
         intros x i
      | _ => fail "Incorrect argument " s
      end
    | ?L ⋎ ?R =>
      match L with
      | s =>
        let H := fresh "H" in
        unfold "⋎";
        intro H; clear H;
        intro x;
        left; intro i
      | _ => fail "Incorrect argument " s
      end
    | ?L ⋎ ?R =>
      match R with
      | s =>
        let H := fresh "H" in
        unfold "⋎";
        intro H; clear H;
        intro x;
        right; intro i
      | _ => fail "Incorrect argument " s
      end
    | _ => fail "(neither an inclusion nor an exclusion)"
    end
  | _ => fail "(not an assertion)"
  end.
  
Tactic Notation "Seja" simple_intropattern(J) ":" "("
"++" simple_intropattern(I) "∈ "constr(H) ")" :=
alvo_def_rel_l I J H.

 
Ltac alvo_def_rel_l2 x i s :=
  lazymatch goal with
  | |- ++ ?P =>
    lazymatch P with
    | ?L ⊆ ?R =>
      lazymatch R with
      | s =>
        let H := fresh "H" in
        let j := fresh "j" in
        unfold "⊆";
        intro H; clear H;
        intro x;
        intro j;
        apply ax_pbc;
        intro i;
        rewrite denial_of_assertion in i;
        pps (++ x ∈ L); auto;
        rewrite denial_of_assertion;
        clear j
      | _ => fail "Incorrect argument " s
      end
    | _ => fail "(neither an inclusion nor an exclusion)"
    end
  | _ => fail "(not an assertion)"
  end.

Tactic Notation "Por" "contrapositividade" ","
"seja" simple_intropattern(J) ":" "("
"--" simple_intropattern(I) "∈ "constr(H) ")" :=
alvo_def_rel_l2 I J H.

Ltac pbc i :=
  lazymatch goal with
  | |- -- ?P =>
  	lazymatch P with
   	| ?y ∈ ?L ∪ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_involutive P) in i
   	| ?y ∈ ?L ∩ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_involutive P) in i
   	| ?y ∈ ?L \ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_involutive P) in i
   	| ?y ∈ ?L △ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_involutive P) in i
    | _ => fail "The goal is not a denial involving a set-theoretical operation"
    end
  | |- ++ ?P =>
  	lazymatch P with
   	| ?y ∈ ?L ∪ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_of_assertion P) in i
   	| ?y ∈ ?L ∩ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_of_assertion P) in i
   	| ?y ∈ ?L \ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_of_assertion P) in i
   	| ?y ∈ ?L △ ?R =>  
      apply ax_pbc; intro i;
      rewrite (denial_of_assertion P) in i
    | _ => fail "The goal is not an assertion involving a set-theoretical operation"
    end
  | _ => fail "The goal is neither a set-theoretical assertion nor denial"
  end.
  
Tactic Notation "Por" "contradição" "," "assuma" simple_intropattern(H) :=
pbc H.
 
Ltac proof_by_cases i :=
  lazymatch type of i with
    | ++ ?y ∈ ?L △ ?R =>
      let H := fresh "H" in
      destruct i as [y i | y i]; auto;
      repeat (match goal with
      | [H : True |- _ ] => clear H
      end);
      [ generalize dependent i
      | generalize dependent i ]
    | ++ ?y ∈ ?L ∪ ?R =>
      let H := fresh "H" in
      destruct i as [y i | y i]; auto;
      repeat (match goal with
      | [H : True |- _ ] => clear H
      end);
      [ generalize dependent i
      | generalize dependent i ]
    | -- ?y ∈ ?L ∩ ?R =>
      let H := fresh "H" in
      let H2 := fresh "H2" in
      assert (H : (-- y ∈ L) \/ (-- y ∈ R));
      [ unfold "--" in i; apply ax_pbc;
     intro H; apply i; split; apply ax_pbc;
     intro H2;
     [ pps ((-- y ∈ L) \/ (-- y ∈ R));
     [ left; auto
     | auto ]
     | pps ((-- y ∈ L) \/ (-- y ∈ R));
     [ right; auto
     | auto ]]
      | clear i; destruct H as [i | i];
      [ generalize dependent i
      | generalize dependent i ] ]
    | -- ?y ∈ ?L \ ?R =>
      let H := fresh "H" in
      let H2 := fresh "H2" in
      assert (H : (-- y ∈ L) \/ (++ y ∈ R));
      [ unfold "--" in i; apply ax_pbc;
     intro H; apply i; split; apply ax_pbc;
     intro H2;
     [ pps ((-- y ∈ L) \/ (++ y ∈ R));
     [ left; auto
     | auto ]
     | pps ((-- y ∈ L) \/ (++ y ∈ R));
     [ right; rewrite denial_involutive in H2; auto
     | auto ]]
      | clear i; destruct H as [i | i];
      [ generalize dependent i
      | generalize dependent i ] ]
    | _ => fail "(the hypothesis is not a disjunctive definition)"
    end.


Tactic Notation "Divisão" "por" "casos" "em"
simple_intropattern(I) :=
proof_by_cases I.

Ltac case_ltac i H :=
  intro i;
  lazymatch type of i  with
  | H => idtac
  | _ => fail i "is incorrect"
  end.

Tactic Notation "Caso" simple_intropattern(I) ":" constr(H) := 
case_ltac I H.


Ltac p_union_r label i H :=
  lazymatch type of label with
  | ++ ?y ∈ ?S =>
    lazymatch H with
    | ++ ?z ∈ ?L ∪ ?R =>
      assert (i : H);
      [ try (left; [apply label; auto | auto]);
        try (right; [apply label; auto | auto])
      | auto ]; auto
    | _ => fail "The conclusion" i "is not an assertion of an union"
    end
  | _ => fail "Hypothesis" label "can't be applied to this definition"
  end.

Tactic Notation "Pela" "definição" "de" "união" "em" simple_intropattern(I) ","
"temos" "que" simple_intropattern(J) ":" constr(H) :=
p_union_r I J H.

Ltac m_union_l label1 label2 i H :=
  lazymatch H with
  | -- ?y ∈ ?L ∪ ?R =>
    match type of label1 with
    | -- y ∈ L =>
      match type of label2 with
      | -- y ∈ R =>
        let Hyp1 := fresh "Hyp1" in
        assert (i : H);
        [ intro Hyp1; destruct Hyp1;
          [ unfold "--" in label1; apply label1; auto
          | unfold "--" in label2; apply label2; auto ]
        | auto ]
      end
    | -- y ∈ R =>
      match type of label2 with
      | -- y ∈ L =>
        let Hyp1 := fresh "Hyp1" in
        assert (i : H);
        [ intro Hyp1; destruct Hyp1;
          [ unfold "--" in label2; apply label2; auto
          | unfold "--" in label1; apply label1; auto ]
        | auto ]
      end
    | _ => fail "At least" label1 "or" label2 "can't be applied to this definition"
    end
  | _ => fail "Conclusion" i "is not a denial of an union"
  end.
 
Tactic Notation "Pela" "definição" "de" "união" "em" simple_intropattern(I)
"e" simple_intropattern(J)","  "temos" "que" simple_intropattern(K)
":" constr(H) :=
m_union_l I J K H.

Ltac m_union_r label i j H1 H2 :=
  lazymatch type of label with
  | -- ?y ∈ ?L ∪ ?R =>
    match H1 with
    | -- y ∈ L =>
      match H2 with
      | -- y ∈ R =>
        let Hyp1 := fresh "Hyp1" in
        let Hyp2 := fresh "Hyp2" in
        assert (Hyp1 : (H1) /\ (H2));
        [ split; unfold "--" in label;
          unfold "--"; intro Hyp2; apply label;
          [ left; auto
          | right; auto ]
        | elim Hyp1; intros i j; clear Hyp1 ]; auto
       end
    | -- y ∈ R =>
      match H2 with
      | -- y ∈ L =>
        let Hyp1 := fresh "Hyp1" in
        let Hyp2 := fresh "Hyp2" in
        assert (Hyp1 : (H2) /\ (H1));
        [ split; unfold "--" in label;
          unfold "--"; intro Hyp2; apply label;
          [ left; auto
          | right; auto ]
        | elim Hyp1; intros i j; clear Hyp1 ]; auto
       end
     | _ => fail "At least" i "or" j "is incorrect"
     end
  | _ => fail "Hypothesis" label "is not a denial of a union"
  end.
 
Tactic Notation "Pela" "definição" "de" "união" "em" simple_intropattern(I) ","
"temos" "que" simple_intropattern(J) ":" constr(H1)
"e" simple_intropattern(K) ":" constr(H2)
:=
m_union_r I J K H1 H2.
 
Ltac p_inter_r label1 label2 i H :=
  lazymatch H with
  | ++ ?y ∈ ?L ∩ ?R =>
    match type of label1 with
    | ++ y ∈ L =>
      match type of label2 with
      | ++ y ∈ R =>
      assert (i : H);
      [ split; auto |  ]; auto
      end
    | ++ y ∈ R =>
      match type of label2 with
      | ++ y ∈ L =>
      assert (i : H);
      [ split; auto |  ]; auto
      end
    | _ => fail "At least" label1 "or" label2 "can't be applied to this definition"
    end
  | _ => fail "The conclusion" H "is not an assertion of an intersection"
  end.
  

Tactic Notation "Pela" "definição" "de" "interseção" "em" simple_intropattern(I)
"e" simple_intropattern(J)","  "temos" "que" simple_intropattern(K)
":" constr(H) :=
p_inter_r I J K H.

Ltac p_inter_l label i j H1 H2 :=
  lazymatch type of label with
  | ++ ?y ∈ ?L ∩ ?R =>
    match H1 with
    | ++ y ∈ L =>
      match H2 with
      | ++ y ∈ R =>
      assert (i : (H1) /\ (H2));
      [ elim label; auto
      | elim i; clear i; intros i j ]; auto
      end
    | ++ y ∈ R =>
      match H2 with
      | ++ y ∈ L =>
      assert (i : (H1) /\ (H2));
      [ elim label; auto
      | elim i; clear i; intros i j ]; auto
      end
    | _ => fail "At least" i "or" j "is incorrect"
    end
  | _ => fail "Hypothesis" label "is not an assertion of an intersection"
  end.
 
Tactic Notation "Pela" "definição" "de" "interseção" "em" simple_intropattern(I) ","
"temos" "que" simple_intropattern(J) ":" constr(H1)
"e" simple_intropattern(K) ":" constr(H2)
:=
p_inter_l I J K H1 H2.

Ltac m_inter_r label i H :=
  lazymatch H with
  | -- ?y ∈ ?L ∩ ?R =>
    match type of label with
    | -- y ∈ L =>
      let Hyp1 := fresh "Hyp1" in
      assert (i : H);
      [ unfold "--"; intro Hyp1; unfold "--" in label;
        apply label; elim Hyp1; auto
      | auto ]; auto
    | -- y ∈ R =>
      let Hyp1 := fresh "Hyp1" in
      assert (i : H);
      [ unfold "--"; intro Hyp1; unfold "--" in label;
        apply label; elim Hyp1; auto
      | auto ]; auto
    | _ => fail "Hypothesis" label "can't be applied to this definition"
    end
  | _ => fail "The conclusion" i "is not a denial of an intersection"
  end.

Tactic Notation "Pela" "definição" "de" "interseção" "em" simple_intropattern(I) ","
"temos" "que" simple_intropattern(J) ":" constr(H) :=
m_inter_r I J H.

Ltac p_diff_r label1 label2 i H :=
  lazymatch H with
  | ++ ?y ∈ ?L \ ?R =>
    match type of label1 with
    | ++ y ∈ L =>
      match type of label2 with
      | -- y ∈ R =>
        assert (i : H);
        [ split; auto |  ]; auto
      end
    | -- y ∈ R =>
      match type of label2 with
      | ++ y ∈ L =>
        assert (i : H);
        [ split; auto |  ]; auto
      end
    | _ => fail "At least" label1 "or" label2 "can't be applied to this definition"
    end
  | _ => fail "The conclusion" i "is not an assertion of a set difference"
  end.
 
Tactic Notation "Pela" "definição" "de" "complemento" "relativo" "em"
simple_intropattern(I) "e" simple_intropattern(J)","  "temos" "que"
simple_intropattern(K) ":" constr(H) :=
p_diff_r I J K H.

Ltac p_diff_l label i j H1 H2 :=
  lazymatch type of label with
  | ++ ?y ∈ ?L \ ?R =>
    match H1 with
    | ++ y ∈ L =>
      match H2 with
      | -- y ∈ R =>
      assert (i : (H1) /\ (H2));
      [ elim label; auto
      | elim i; clear i; intros i j ]; auto
      end
    | -- y ∈ R =>
      match H2 with
      | ++ y ∈ L =>
      assert (i : (H1) /\ (H2));
      [ elim label; auto
      | elim i; clear i; intros i j ]; auto
      end
    | _ => fail "At least" i "or" j "is incorrect"
    end
  | _ => fail "Hypothesis" label "is not an assertion of a set difference"
  end.
 
Tactic Notation "Pela" "definição" "de" "complemento" "relativo" "em"
simple_intropattern(I) "," "temos" "que" simple_intropattern(J) ":"
constr(H1) "e" simple_intropattern(K) ":" constr(H2)
:=
p_diff_l I J K H1 H2.

Ltac m_dif_r label i H :=
  match H with
  | -- ?y ∈ ?L \ ?R =>
    lazymatch type of label with
    | -- y ∈ L =>
      let Hyp1 := fresh "Hyp1" in
      assert (i : H);
      [ unfold "--"; intro Hyp1; unfold "--" in label;
        apply label; elim Hyp1; auto
      | auto ]; auto
    | ++ y ∈ R =>
      let Hyp1 := fresh "Hyp1" in
      assert (i : H);
      [ unfold "--"; intro Hyp1; pps (++ y ∈ R); auto;
        elim Hyp1; auto
      | auto ]; auto
    | _ => fail "Hypothesis" label "can't be applied to this definition"
    end
  | _ => fail "The conclusion" i "is incorrect"
  end.

Tactic Notation "Pela" "definição" "de" "complemento" "relativo" "em"
simple_intropattern(I) "," "temos" "que" simple_intropattern(J) ":"
constr(H) :=
m_dif_r I J H.

Ltac p_symm_r label i H :=
  lazymatch type of label with
  | ++ ?y ∈ ?S =>
    lazymatch H with
    | ++ ?z ∈ ?L △ ?R =>
      assert (i : H);
      [ try (left; [apply label; auto | auto]);
        try (right; [apply label; auto | auto])
      | auto ]; auto
    | _ => fail "The conclusion" i "is not an assertion of a symmetric difference"
    end
  | _ => fail "Hypothesis" label "can't be applied to this definition"
  end.
  
Tactic Notation "Pela" "definição" "de" "diferença" "simétrica"
"em" simple_intropattern(I) "," "temos" "que" simple_intropattern(J)
":" constr(H) :=
p_symm_r I J H.

Ltac m_symm_l label1 label2 i H :=
  lazymatch H with
  | -- ?y ∈ ?L △ ?R =>
    match type of label1 with
    | -- y ∈ L \ R =>
      match type of label2 with
      | -- y ∈ R \ L =>
        let Hyp1 := fresh "Hyp1" in
        assert (i : H);
        [ intro Hyp1; destruct Hyp1;
          [ unfold "--" in label1; apply label1; auto
          | unfold "--" in label2; apply label2; auto ]
        | auto ]
      end
    | -- y ∈ R \ L =>
      match type of label2 with
      | -- y ∈ L \ R =>
        let Hyp1 := fresh "Hyp1" in
        assert (i : H);
        [ intro Hyp1; destruct Hyp1;
          [ unfold "--" in label2; apply label2; auto
          | unfold "--" in label1; apply label1; auto ]
        | auto ]
      end
    | _ => fail "At least" label1 "or" label2 "can't be applied to this definition"
    end
    | _ => fail "Conclusion" i "is not a denial of an union"
  end.
 
Tactic Notation "Pela" "definição" "de" "diferença" "simétrica"
"em" simple_intropattern(I) "e" simple_intropattern(J)","
"temos" "que" simple_intropattern(K) ":" constr(H) :=
m_symm_l I J K H.

Ltac m_symm_r label i j H1 H2 :=
  lazymatch type of label with
  | -- ?y ∈ ?L △ ?R =>
    match H1 with
    | -- y ∈ L \ R =>
      match H2 with
      | -- y ∈ R \ L =>
        let Hyp1 := fresh "Hyp1" in
        let Hyp2 := fresh "Hyp2" in
        assert (Hyp1 : (H1) /\ (H2));
        [ split; unfold "--" in label;
          unfold "--"; intro Hyp2; apply label;
          [ left; auto
          | right; auto ]
        | elim Hyp1; intros i j; clear Hyp1 ]; auto
       end
    | -- y ∈ R \ L =>
      match H2 with
      | -- y ∈ L \ R =>
        let Hyp1 := fresh "Hyp1" in
        let Hyp2 := fresh "Hyp2" in
        assert (Hyp1 : (H2) /\ (H1));
        [ split; unfold "--" in label;
          unfold "--"; intro Hyp2; apply label;
          [ left; auto
          | right; auto ]
        | elim Hyp1; intros i j; clear Hyp1 ]; auto
       end
     | _ => fail "At least" i "or" j "is incorrect"
     end
  | _ => fail "Hypothesis" label "is not a defion of a symmetric difference"
  end.
 
Tactic Notation "Pela" "definição" "de" "diferença" "simétrica"
"em" simple_intropattern(I) "," "temos" "que" simple_intropattern(J)
":" constr(H1) "e" simple_intropattern(K) ":" constr(H2) :=
m_symm_r I J K H1 H2.

Parameter x : U.
Parameter A B C : Ensemble.

Theorem test1 : ++ (A ∪ (B ∩ C)) ⊆ ((A ∪ B) ∩ (A ∪ C)).
Proof.
Seja H : (++ x ∈ (A ∪ (B ∩ C))).
Divisão por casos em H.
- Caso H : (++ x ∈ A).
  Pela definição de união em H, temos que Hab : (++ x ∈ (A ∪ B)).
  Pela definição de união em H, temos que Hac : (++ x ∈ (A ∪ C)).
  Pela definição de interseção em Hab e Hac, temos que
  Habac : (++ x ∈ ((A ∪ B) ∩ (A ∪ C))).
- Caso H : (++ x ∈ (B ∩ C)).
  Pela definição de interseção em H,
  temos que Hb : (++ x ∈ B) e Hc : (++ x ∈ C).
  Pela definição de união em Hb, temos que Hab : (++ x ∈ (A ∪ B)).
  Pela definição de união em Hc, temos que Hac : (++ x ∈ (A ∪ C)).
  Pela definição de interseção em Hab e Hac, temos que
  Habac : (++ x ∈ ((A ∪ B) ∩ (A ∪ C))).
Qed.

Theorem test2 : ++ (A ∪ (B ∩ C)) ⊆ ((A ∪ B) ∩ (A ∪ C)).
Proof.
Por contrapositividade, seja H : (-- x ∈ ((A ∪ B) ∩ (A ∪ C))).
Divisão por casos em H.
- Caso H : (-- x ∈ (A ∪ B)).
  Pela definição de união em H, temos que Ha : (-- x ∈ A)
  e Hb : (-- x ∈ B).
  Pela definição de interseção em Hb, temos que Hbc : (-- x ∈ B ∩ C).
  Pela definição de união em Ha e Hbc, temos que
  Habc : (-- x ∈ (A ∪ (B ∩ C))).
- Caso H : (-- x ∈ A ∪ C).
  Pela definição de união em H, temos que Ha : (-- x ∈ A)
  e Hc : (-- x ∈ C).
  Pela definição de interseção em Hc, temos que Hbc : (-- x ∈ B ∩ C).
  Pela definição de união em Ha e Hbc, temos que
  Habc : (-- x ∈ (A ∪ (B ∩ C))).
Qed.

Theorem test3 : ++ (A ∩ B) ⋎ (A △ B).
Proof.
Seja H : (++ x ∈ (A ∩ B)).
Pela definição de interseção em H, temos que
Ha : (++ x ∈ A) e Hb : (++ x ∈ B).
Pela definição de complemento relativo em Ha,
temos que Hba : (-- x ∈ (B \ A)).
Pela definição de complemento relativo em Hb,
temos que Hab : (-- x ∈ (A \ B)).
Pela definição de diferença simétrica em Hba e Hab,
temos que Hsym : (-- x ∈ (A △ B)).
Qed.

Theorem test4 : ++ (A △ B) ⋎ (A ∩ B).
Proof.
Seja H : (++ x ∈ (A ∩ B)).
Pela definição de interseção em H, temos que
Ha : (++ x ∈ A) e Hb : (++ x ∈ B).
Por contradição, assuma H1.
Divisão por casos em H1.
- Caso H1 : (++ x ∈ (A \ B)).
	Pela definição de complemento relativo em H1,
	temos que H2 : (++ x ∈ A) e H3 : (-- x ∈ B).
- Caso H1 : (++ x ∈ (B \ A)).
	Pela definição de complemento relativo em H1,
	temos que H2 : (++ x ∈ B) e H3 : (-- x ∈ A).
Qed.

