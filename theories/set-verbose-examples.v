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
