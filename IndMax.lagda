
% !TEX root =  main.tex



\subsection{Recursive Maximum}


\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
  module IndMax {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ )
    (default : (c : ℂ) → El c) where
    open import RawTree ℂ El Cℕ CℕIso
\end{code}

\begin{code}
    private
        data IndMaxView : Tree → Tree → Set ℓ where
          IndMaxZ-L : ∀ {t} → IndMaxView Z t
          IndMaxZ-R : ∀ {t} → IndMaxView t Z
          IndMaxLim-L : ∀ {t} {c : ℂ} {f : El c → Tree}
            → IndMaxView (Lim c f) t
          IndMaxLim-R : ∀ {t} {c : ℂ} {f : El c → Tree}
            → (∀   {c' : ℂ} {f' : El c' → Tree} → ¬ (t ≡ Lim  c' f'))
            → IndMaxView t (Lim c f)
          IndMaxLim-Suc : ∀  {t1 t2 } → IndMaxView (↑ t1) (↑ t2)
    opaque

        indMaxView : ∀ t1 t2 → IndMaxView t1 t2
        indMaxView Z t2 = IndMaxZ-L
        indMaxView (Lim c f) t2 = IndMaxLim-L
        indMaxView (↑ t1) Z = IndMaxZ-R
        indMaxView (↑ t1) (Lim c f) = IndMaxLim-R λ ()
        indMaxView (↑ t1) (↑ t2) = IndMaxLim-Suc


        indMax : Tree → Tree → Tree
        indMax' : ∀ {t1 t2} → IndMaxView t1 t2 → Tree

        indMax t1 t2 = indMax' (indMaxView t1 t2)

        indMax' {.Z} {t2} IndMaxZ-L = t2
        indMax' {t1} {.Z} IndMaxZ-R = t1
        indMax' {(Lim c f)} {t2} IndMaxLim-L
            = Lim c λ x → indMax (f x) t2
        indMax' {t1} {(Lim c f)} (IndMaxLim-R _)
            = Lim c (λ x → indMax t1 (f x))
        indMax' {(↑ t1)} {(↑ t2)} IndMaxLim-Suc = ↑ (indMax t1 t2)


  \end{code}

  \begin{code}


    underLim : ∀   {c : ℂ}  {t} →  {f : El c → Tree} → (∀ k → t ≤ f k) → t ≤ Lim c f
    underLim {c = c}  {t} {f} all = ≤-trans (≤-cocone (λ _ → t) (default c) (≤-refl t)) (≤-limiting (λ _ → t) (λ k → ≤-cocone f k (all k)))

    opaque
        unfolding indMax indMax'

        indMax-≤L : ∀ {t1 t2} → t1 ≤ indMax t1 t2
        indMax-≤L {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-L = ≤-Z
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-L {f = f} = extLim f (λ x → indMax (f x) t2) (λ k → indMax-≤L)
        ... | IndMaxLim-R {f = f} _ = underLim  λ k → indMax-≤L {t2 = f k}
        ... | IndMaxLim-Suc = ≤-sucMono indMax-≤L


        indMax-≤R : ∀ {t1 t2} → t2 ≤ indMax t1 t2
        indMax-≤R {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-R = ≤-Z
        ... | IndMaxZ-L = ≤-refl _
        ... | IndMaxLim-R {f = f} _ = extLim f (λ x → indMax t1 (f x)) (λ k → indMax-≤R {t1 = t1} {f k})
        ... | IndMaxLim-L {f = f} = underLim  λ k → indMax-≤R
        ... | IndMaxLim-Suc {t1} {t2} = ≤-sucMono (indMax-≤R {t1 = t1} {t2 = t2})




        indMax-monoR : ∀ {t1 t2 t2'} → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1 t2'
        indMax-monoR' : ∀ {t1 t2 t2'} → t2 < t2' → indMax t1 t2 < indMax (↑ t1) t2'

        indMax-monoR {t1} {t2} {t2'} lt with indMaxView t1 t2 in eq1 | indMaxView t1 t2' in eq2
        ... | IndMaxZ-L  | v2  = ≤-trans lt (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R  | v2  = ≤-trans indMax-≤L (≤-reflEq (cong indMax' eq2))
        ... | IndMaxLim-L {f = f1} |  IndMaxLim-L  = extLim _ _ λ k → indMax-monoR {t1 = f1 k} lt
        indMax-monoR {t1} {(Lim _ f')} {.(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-R neq  | IndMaxLim-R neq'
            = ≤-limiting (λ x → indMax t1 (f' x)) (λ y → ≤-cocone (λ x → indMax t1 (f x)) k (indMax-monoR {t1 = t1} {t2 = f' y} (≤-trans (≤-cocone _ y (≤-refl _)) lt)))
        indMax-monoR {t1} {.(Lim _ _)} {t2'} (≤-limiting f x₁) | IndMaxLim-R x  | v2  =
            ≤-trans (≤-limiting (λ x₂ → indMax t1 (f x₂)) λ k → indMax-monoR {t1 = t1} (x₁ k)) (≤-reflEq (cong indMax' eq2))
        indMax-monoR {(↑ t1)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc  = ≤-sucMono (indMax-monoR {t1 = t1} lt)
        indMax-monoR {(↑ t1)} {(↑ t2)} {(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-R x
            = ≤-trans (indMax-monoR' {t1 = t1} {t2 = t2} {t2' = f k} lt) (≤-cocone (λ x₁ → indMax (↑ t1) (f x₁)) k (≤-refl _)) --indMax-monoR' {!lt!}

        indMax-monoR' {t1} {t2} {t2'}  (≤-sucMono lt) = ≤-sucMono ( (indMax-monoR {t1 = t1} lt))
        indMax-monoR' {t1} {t2} {.(Lim _ f)} (≤-cocone f k lt)
            = ≤-cocone _ k (indMax-monoR' {t1 = t1} lt)


        indMax-monoL : ∀ {t1 t1' t2} → t1 ≤ t1' → indMax t1 t2 ≤ indMax t1' t2
        indMax-monoL' : ∀ {t1 t1' t2} → t1 < t1' → indMax t1 t2 < indMax t1' (↑ t2)
        indMax-monoL {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        ... | IndMaxZ-L | v2 = ≤-trans (indMax-≤R {t1 = t1'}) (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R | v2 = ≤-trans lt (≤-trans (indMax-≤L {t1 = t1'}) (≤-reflEq (cong indMax' eq2)))
        indMax-monoL {.(Lim _ _)} {.(Lim _ f)} {t2} (≤-cocone f k lt) | IndMaxLim-L  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) t2) k (indMax-monoL lt)
        indMax-monoL {.(Lim _ _)} {t1'} {t2} (≤-limiting f lt) | IndMaxLim-L |  v2
            = ≤-limiting (λ x₁ → indMax (f x₁) t2) λ k → ≤-trans (indMax-monoL (lt k)) (≤-reflEq (cong indMax' eq2))
        indMax-monoL {.Z} {.Z} {.(Lim _ _)} ≤-Z | IndMaxLim-R neq  | IndMaxZ-L  = ≤-refl _
        indMax-monoL  {.(Lim _ f)} {.Z} {.(Lim _ _)} (≤-limiting f x) | IndMaxLim-R neq | IndMaxZ-L
            with () ← neq refl
        indMax-monoL {t1} {.(Lim _ _)} {.(Lim _ _)} (≤-cocone _ k lt) | IndMaxLim-R {f = f} neq | IndMaxLim-L {f = f'}
            = ≤-limiting (λ x → indMax t1 (f x)) (λ y → ≤-cocone (λ x → indMax (f' x) (Lim _ _)) k
            (≤-trans (indMax-monoL lt) (indMax-monoR {t1 = f' k} (≤-cocone f y (≤-refl _)))))
        ... | IndMaxLim-R neq | IndMaxLim-R {f = f} neq' = extLim (λ x → indMax t1 (f x)) (λ x → indMax t1' (f x)) (λ k → indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc
            = ≤-sucMono (indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(Lim _ f)} {.(↑ _)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) (↑ _)) k (indMax-monoL' lt)

        indMax-monoL' {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        indMax-monoL' {t1} {.(↑ _)} {t2} (≤-sucMono lt) | v1 | v2 = ≤-sucMono (≤-trans (≤-reflEq (cong indMax' (sym eq1))) (indMax-monoL lt))
        indMax-monoL' {t1} {.(Lim _ f)} {t2} (≤-cocone f k lt) | v1 | v2
            = ≤-cocone _ k (≤-trans (≤-sucMono (≤-reflEq (cong indMax' (sym eq1)))) (indMax-monoL' lt))
\end{code}


\subsubsection{Limitation: Idempotence}




\begin{code}

        indMax-mono : ∀ {t1 t2 t1' t2'} → t1 ≤ t1' → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1' t2'
        indMax-mono {t1' = t1'} lt1 lt2 = ≤-trans (indMax-monoL lt1) (indMax-monoR {t1 = t1'} lt2)

        indMax-strictMono : ∀ {t1 t2 t1' t2'} → t1 < t1' → t2 < t2' → indMax t1 t2 < indMax t1' t2'
        indMax-strictMono lt1 lt2 = indMax-mono lt1 lt2


        indMax-sucMono : ∀ {t1 t2 t1' t2'} → indMax t1 t2 ≤ indMax t1' t2' → indMax t1 t2 < indMax (↑ t1') (↑ t2')
        indMax-sucMono lt = ≤-sucMono lt


        indMax-Z : ∀ t → indMax t Z ≤ t
        indMax-Z Z = ≤-Z
        indMax-Z (↑ t) = ≤-refl (indMax (↑ t) Z)
        indMax-Z (Lim c f) = extLim (λ x → indMax (f x) Z) f (λ k → indMax-Z (f k))

        indMax-↑ : ∀ {t1 t2} → indMax (↑ t1) (↑ t2) ≡ ↑ (indMax t1 t2)
        indMax-↑ = refl

        indMax-≤Z : ∀ t → indMax t Z ≤ t
        indMax-≤Z Z = ≤-refl _
        indMax-≤Z (↑ t) = ≤-refl _
        indMax-≤Z (Lim c f) = extLim _ _ (λ k → indMax-≤Z (f k))



        indMax-limR : ∀   {c : ℂ} (f : El  c  → Tree) t → indMax t (Lim c f) ≤ Lim c (λ k → indMax t (f k))
        indMax-limR f Z = ≤-refl _
        indMax-limR f (↑ t) = extLim _ _ λ k → ≤-refl _
        indMax-limR f (Lim c f₁) = ≤-limiting _ λ k → ≤-trans (indMax-limR f (f₁ k)) (extLim _ _ (λ k2 → indMax-monoL {t1 = f₁ k} {t1' = Lim c f₁} {t2 = f k2}  (≤-cocone _ k (≤-refl _))))


        indMax-commut : ∀ t1 t2 → indMax t1 t2 ≤ indMax t2 t1
        indMax-commut t1 t2 with indMaxView t1 t2
        ... | IndMaxZ-L = indMax-≤L
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-R {f = f} x = extLim _ _ (λ k → indMax-commut t1 (f k))
        ... | IndMaxLim-Suc {t1 = t1} {t2 = t2} = ≤-sucMono (indMax-commut t1 t2)
        ... | IndMaxLim-L {c = c} {f = f} with indMaxView t2 t1
        ... | IndMaxZ-L = extLim _ _ λ k → indMax-Z (f k)
        ... | IndMaxLim-R x = extLim _ _ (λ k → indMax-commut (f k) t2)
        ... | IndMaxLim-L {c = c2} {f = f2} =
            ≤-trans (extLim _ _ λ k → indMax-limR f2 (f k))
            (≤-trans (≤-limiting _ (λ k → ≤-limiting _ λ k2 → ≤-cocone _ k2 (≤-cocone _ k (≤-refl _))))
            (≤-trans (≤-refl (Lim c2 λ k2 → Lim c λ k → indMax (f k) (f2 k2)))
            (extLim _ _ (λ k2 → ≤-limiting _ λ k1 → ≤-trans (indMax-commut (f k1) (f2 k2)) (indMax-monoR {t1 = f2 k2} {t2 = f k1} {t2' = Lim c f} (≤-cocone _ k1 (≤-refl _)))))))


        indMax-assocL : ∀ t1 t2 t3 → indMax t1 (indMax t2 t3) ≤ indMax (indMax t1 t2) t3
        indMax-assocL t1 t2 t3 with indMaxView t2 t3 in eq23
        ... | IndMaxZ-L = indMax-monoL {t1 = t1} {t1' = indMax t1 Z} {t2 = t3} indMax-≤L
        ... | IndMaxZ-R = indMax-≤L
        ... | m with indMaxView t1 t2
        ... | IndMaxZ-L rewrite sym eq23 = ≤-refl _
        ... | IndMaxZ-R rewrite sym eq23 = ≤-refl _
        ... | IndMaxLim-R {f = f} x rewrite sym eq23 = ≤-trans (indMax-limR (λ x → indMax (f x) t3) t1) (extLim _ _ λ k → indMax-assocL t1 (f k) t3) -- f,indMax-limR f t1
        indMax-assocL .(↑ _) .(↑ _) .Z | IndMaxZ-R  | IndMaxLim-Suc = ≤-refl _
        indMax-assocL t1 t2 .(Lim _ _) | IndMaxLim-R {f = f} x   | IndMaxLim-Suc = extLim _ _ λ k → indMax-assocL t1 t2 (f k)
        indMax-assocL (↑ t1) (↑ t2) (↑ t3) | IndMaxLim-Suc  | IndMaxLim-Suc = ≤-sucMono (indMax-assocL t1 t2 t3)
        ... | IndMaxLim-L {f = f} rewrite sym eq23 = extLim _ _ λ k → indMax-assocL (f k) t2 t3



        indMax-assocR : ∀ t1 t2 t3 →  indMax (indMax t1 t2) t3 ≤ indMax t1 (indMax t2 t3)
        indMax-assocR t1 t2 t3 = ≤-trans (indMax-commut (indMax t1 t2) t3) (≤-trans (indMax-monoR {t1 = t3} (indMax-commut t1 t2))
            (≤-trans (indMax-assocL t3 t2 t1) (≤-trans (indMax-commut (indMax t3 t2) t1) (indMax-monoR {t1 = t1} (indMax-commut t3 t2)))))


        indMax-swap4 : ∀ {t1 t1' t2 t2'} → indMax (indMax t1 t1') (indMax t2 t2') ≤ indMax (indMax t1 t2) (indMax t1' t2')
        indMax-swap4 {t1}{t1'}{t2 }{t2'} =
            indMax-assocL (indMax t1 t1') t2 t2'
            ≤⨟ indMax-monoL {t1 = indMax (indMax t1 t1') t2} {t2 = t2'}
            (indMax-assocR t1 t1' t2 ≤⨟ indMax-monoR {t1 = t1} (indMax-commut t1' t2) ≤⨟ indMax-assocL t1 t2 t1')
            ≤⨟ indMax-assocR (indMax t1 t2) t1' t2'

        indMax-swap6 : ∀ {t1 t2 t3 t1' t2' t3'} → indMax (indMax t1 t1') (indMax (indMax t2 t2') (indMax t3 t3')) ≤ indMax (indMax t1 (indMax t2 t3)) (indMax t1' (indMax t2' t3'))
        indMax-swap6 {t1} {t2} {t3} {t1'} {t2'} {t3'} =
            indMax-monoR {t1 = indMax t1 t1'} (indMax-swap4 {t1 = t2} {t1' = t2'} {t2 = t3} {t2' = t3'})
            ≤⨟ indMax-swap4 {t1 = t1} {t1' = t1'}

        indMax-lim2L :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            → Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2))) ≤ indMax (Lim  c1 f1) (Lim  c2 f2)
        indMax-lim2L f1 f2 = ≤-limiting  _ (λ k1 → ≤-limiting  _ λ k2 → indMax-mono (≤-cocone  f1 k1 (≤-refl _)) (≤-cocone  f2 k2 (≤-refl _)))

        indMax-lim2R :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            →  indMax (Lim  c1 f1) (Lim  c2 f2) ≤ Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2)))
        indMax-lim2R f1 f2 = extLim  _ _ (λ k1 → indMax-limR  _ (f1 k1))



\end{code}

