module Red where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; Extensionality; sym)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; _∷_; []; lookup; _[_]=_; here; there)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

postulate extensionality : ∀{a b} → Extensionality a b

data type : Set where
  ty-arr : type → type → type
  ty-unit : type

tyEq : (t u : type) → t ≡ u ⊎ t ≢ u
tyEq (ty-arr t t₁) (ty-arr u u₁) with tyEq t u
tyEq (ty-arr t t₁) (ty-arr .t u₁) | inj₁ refl with tyEq t₁ u₁
tyEq (ty-arr t t₁) (ty-arr .t .t₁) | inj₁ refl | inj₁ refl = inj₁ refl
tyEq (ty-arr t t₁) (ty-arr .t u₁) | inj₁ refl | inj₂ y = inj₂ λ{ refl → y refl }
tyEq (ty-arr t t₁) (ty-arr u u₁) | inj₂ y = inj₂ λ{ refl → y refl }
tyEq (ty-arr t t₁) ty-unit = inj₂ (λ ())
tyEq ty-unit (ty-arr u u₁) = inj₂ (λ ())
tyEq ty-unit ty-unit = inj₁ refl

data term (n : ℕ) : Set where
  tm-var : Fin n → term n
  tm-lam : type → term (suc n) → term n
  tm-app : term n → term n → term n
  tm-unit : term n

ρ : ∀{m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
ρ f zero = zero
ρ f (suc n) = suc (f n)

rename : ∀{m n} → (Fin m → Fin n) → term m → term n
rename f (tm-var ix) = tm-var (f ix)
rename f (tm-lam A a) = tm-lam A (rename (ρ f) a)
rename f (tm-app a b) = tm-app (rename f a) (rename f b)
rename f tm-unit = tm-unit

σ : ∀{m n} → (Fin m → term n) → Fin (suc m) → term (suc n)
σ f zero = tm-var zero
σ f (suc n) = rename suc (f n)

subst : ∀{m n} → (Fin m → term n) → term m → term n
subst f (tm-var ix) = f ix
subst f (tm-lam A a) = tm-lam A (subst (σ f) a)
subst f (tm-app a b) = tm-app (subst f a) (subst f b)
subst f tm-unit = tm-unit

σ-⊥ : (f : Fin 0 → term 0) → (x : Fin 1) → σ f x ≡ tm-var x
σ-⊥ f zero = refl
σ-⊥ f (suc ())

σ-var : ∀{n} → (x : Fin (suc n)) → σ tm-var x ≡ tm-var x
σ-var zero = refl
σ-var (suc x) = refl

subst-var : ∀{n} → (x : term n) → subst tm-var x ≡ x
subst-var (tm-var x) = refl
subst-var {n} (tm-lam A e)
  rewrite
    extensionality (σ-var {n}) | subst-var e = refl
subst-var (tm-app a b) rewrite subst-var a | subst-var b = refl
subst-var tm-unit = refl

subst-⊥ : (f : Fin 0 → term 0) → (x : term zero) → subst f x ≡ x
subst-⊥ f (tm-var ())
subst-⊥ f (tm-lam A e) rewrite extensionality (σ-⊥ f) | subst-var e = refl
subst-⊥ f (tm-app a b) rewrite subst-⊥ f a | subst-⊥ f b = refl
subst-⊥ f tm-unit = refl

replace : ∀{n} → term n → Fin (suc n) → term n
replace x = λ{ zero → x ; (suc n) → tm-var n }

infixl 20 _[_]
_[_] : ∀{n} → term (suc n) → term n → term n
_[_] a b = subst (replace b) a

data _⊢_⇒_ {n} (Γ : Vec type n) : term n → type → Set where
  ⇒-var :
    ∀{ix : Fin n} {A} →
    Γ [ ix ]= A →
    Γ ⊢ tm-var ix ⇒ A
  ⇒-app :
    ∀{A B} {f x} →
    Γ ⊢ f ⇒ ty-arr A B →
    Γ ⊢ x ⇒ A →
    Γ ⊢ tm-app f x ⇒ B
  ⇒-lam :
    ∀{e} {B} →
    (A : type) →
    (A ∷ Γ) ⊢ e ⇒ B →
    Γ ⊢ tm-lam A e ⇒ ty-arr A B
  ⇒-unit : Γ ⊢ tm-unit ⇒ ty-unit

data value {n} : term n → Set where
  value-lam : ∀{A e} → value (tm-lam A e)
  value-unit : value tm-unit

infix 10 _↓_
data _↓_ {n} : term n → term n → Set where
  ↓-app₁ : ∀{f f' x} → f ↓ f' → tm-app f x ↓ tm-app f' x
  ↓-app₂ : ∀{f x x'} → value f → x ↓ x' → tm-app f x ↓ tm-app f x'
  ↓-β : ∀{x A e} → value x → tm-app (tm-lam A e) x ↓ e [ x ]

progress : ∀{x T} → [] ⊢ x ⇒ T → value x ⊎ ∃[ x' ](x ↓ x')
progress (⇒-var ())
progress (⇒-app f x) with progress f
progress (⇒-app f x) | inj₁ vf with progress x
progress (⇒-app f x) | inj₁ value-lam | inj₁ vx = inj₂ (_ , ↓-β vx)
progress (⇒-app () x) | inj₁ value-unit | inj₁ vx
progress (⇒-app f x) | inj₁ vf | inj₂ (x' , x↓x') = inj₂ (_ , ↓-app₂ vf x↓x')
progress (⇒-app f x) | inj₂ (f' , f↓f') = inj₂ (_ , ↓-app₁ f↓f')
progress (⇒-lam A e) = inj₁ value-lam
progress ⇒-unit = inj₁ value-unit

rename-preservation :
  ∀{m n} {Γ : Vec type m} {Δ : Vec type n} {x T} →
  (f : Fin m → Fin n) →
  (∀{ix : Fin m} {S} → Γ [ ix ]= S → Δ [ f ix ]= S) →
  Γ ⊢ x ⇒ T →
  Δ ⊢ rename f x ⇒ T
rename-preservation f ff (⇒-var x) = ⇒-var (ff x)
rename-preservation f ff (⇒-app a b) =
  ⇒-app (rename-preservation f ff a) (rename-preservation f ff b)
rename-preservation f ff (⇒-lam A e) =
  ⇒-lam A (rename-preservation (ρ f) (λ{ here → here; (there prf) → there (ff prf) }) e)
rename-preservation f ff ⇒-unit = ⇒-unit

subst-preservation :
  ∀{m n} {Γ : Vec type m} {Δ : Vec type n} {x T} →
  (f : Fin m → term n) →
  (∀{ix : Fin m} {S} → Γ [ ix ]= S → Δ ⊢ f ix ⇒ S) →
  Γ ⊢ x ⇒ T →
  Δ ⊢ subst f x ⇒ T
subst-preservation f ff (⇒-var x) = ff x
subst-preservation f ff (⇒-app a b) =
  ⇒-app (subst-preservation f ff a) (subst-preservation f ff b)
subst-preservation f ff (⇒-lam A e) with
  subst-preservation
    (σ f)
    (λ{
      here → ⇒-var here;
      (there prf) → rename-preservation suc (λ x → there x) (ff prf)
     })
    e
... | ee = ⇒-lam A ee
subst-preservation f ff ⇒-unit = ⇒-unit

preservation : ∀{x x' T} → [] ⊢ x ⇒ T → x ↓ x' → [] ⊢ x' ⇒ T
preservation (⇒-var ())
preservation (⇒-app ht ht₁) (↓-app₁ step) = ⇒-app (preservation ht step) ht₁
preservation (⇒-app ht ht₁) (↓-app₂ x₁ step) = ⇒-app ht (preservation ht₁ step)
preservation (⇒-app (⇒-lam A f) x) (↓-β _) =
  subst-preservation _ (λ{ here → x; (there prf) → ⇒-var prf}) f
preservation (⇒-lam A ht) ()
preservation ⇒-unit ()

data _⇓_ {n} : term n → term n → Set where
  ⇓-refl : ∀{a} → a ⇓ a
  ⇓-trans : ∀{a a' a''} → a ↓ a' → a' ⇓ a'' → a ⇓ a''

⇓-app₂ : ∀{n} {a b b' : term n} → value a → b ⇓ b' → tm-app a b ⇓ tm-app a b'
⇓-app₂ va ⇓-refl = ⇓-refl
⇓-app₂ va (⇓-trans x bb) = ⇓-trans (↓-app₂ va x) (⇓-app₂ va bb)

preservation-⇓ : ∀{x x' T} → [] ⊢ x ⇒ T → x ⇓ x' → [] ⊢ x' ⇒ T
preservation-⇓ h ⇓-refl = h
preservation-⇓ h (⇓-trans x↓x' rest) with preservation h x↓x'
... | h' = preservation-⇓ h' rest

SN : ∀{n} → term n → Set
SN x = ∃[ x' ]((x ⇓ x') × value x')

Red : type → term zero → Set
Red ty-unit tm = ([] ⊢ tm ⇒ ty-unit) × SN tm
Red (ty-arr A B) tm =
  ([] ⊢ tm ⇒ ty-arr A B) ×
  SN tm ×
  ({x : term zero} → Red A x → Red B (tm-app tm x))

Red-sn : ∀{T x} → Red T x → SN x
Red-sn {ty-arr A B} red = proj₁ (proj₂ red)
Red-sn {ty-unit} red = proj₂ red

Red-wt : ∀{T x} → Red T x → [] ⊢ x ⇒ T
Red-wt {ty-arr A B} red = proj₁ red
Red-wt {ty-unit} red = proj₁ red

σ-ρ :
  ∀{m n o} →
  (f : Fin n → term o) →
  (g : Fin m → Fin n) →
  (x : Fin (suc m)) →
  σ f (ρ g x) ≡ σ (λ y → f (g y)) x
σ-ρ f g zero = refl
σ-ρ f g (suc x) = refl

subst-rename :
  ∀{m n o} →
  (f : Fin n → term o) →
  (g : Fin m → Fin n) →
  (x : term m) →
  subst f (rename g x) ≡
  subst (λ y → f (g y)) x
subst-rename f g (tm-var x) = refl
subst-rename f g (tm-lam A e)
  rewrite
    subst-rename (σ f) (ρ g) e |
    extensionality (σ-ρ f g) = refl
subst-rename f g (tm-app a b)
  rewrite
    subst-rename f g a |
    subst-rename f g b = refl
subst-rename f g tm-unit = refl

_⊨_ : ∀{n} → (f : Fin n → term zero) → Vec type n → Set
_⊨_ {n} f Γ = ∀{ix : Fin n} {T} → Γ [ ix ]= T → Red T (f ix)

σ-⊨ :
  ∀{n} {Γ : Vec type n} {A} →
  (f : Fin n → term zero) →
  f ⊨ Γ →
  (x : term zero) →
  Red A x →
  (λ y → subst (replace x) (σ f y)) ⊨ (A ∷ Γ)
σ-⊨ f f⊨Γ x red here = red
σ-⊨ f f⊨Γ x red (there {_} {i} prf)
  rewrite
    subst-rename (replace x) suc (f i) | subst-var (f i) = f⊨Γ prf

↓-det : ∀{x x' x'' : term 0} → x ↓ x' → x ↓ x'' → x' ≡ x''
↓-det (↓-app₁ step1) (↓-app₁ step2) rewrite ↓-det step1 step2 = refl
↓-det (↓-app₁ ()) (↓-app₂ value-lam step2)
↓-det (↓-app₁ ()) (↓-app₂ value-unit step2)
↓-det (↓-app₁ ()) (↓-β value-lam)
↓-det (↓-app₁ ()) (↓-β value-unit)
↓-det (↓-app₂ () step1) (↓-app₁ (↓-app₁ step2))
↓-det (↓-app₂ () step1) (↓-app₁ (↓-app₂ x₃ step2))
↓-det (↓-app₂ () step1) (↓-app₁ (↓-β x₃))
↓-det (↓-app₂ x1 step1) (↓-app₂ x2 step2) rewrite ↓-det step1 step2 = refl
↓-det (↓-app₂ x1 ()) (↓-β value-lam)
↓-det (↓-app₂ x1 ()) (↓-β value-unit)
↓-det (↓-β x₁) (↓-app₁ ())
↓-det (↓-β value-lam) (↓-app₂ x2 ())
↓-det (↓-β value-unit) (↓-app₂ x2 ())
↓-det (↓-β x1) (↓-β x2) = refl

SN-↓-fw : ∀{x x' : term zero} → (x ↓ x') → SN x → SN x'
SN-↓-fw () (.(tm-lam _ _) , ⇓-refl , value-lam)
SN-↓-fw () (.tm-unit , ⇓-refl , value-unit)
SN-↓-fw step (x'' , ⇓-trans step' rest , vx'')
  rewrite
    ↓-det step step' = x'' , rest , vx''

SN-↓-bw : ∀{x x' T} → [] ⊢ x' ⇒ T → (x ↓ x') → SN x' → SN x
SN-↓-bw (⇒-var ()) step sn
SN-↓-bw (⇒-app a b) step (x' , tm-app⇓x' , vx') = x' , ⇓-trans step tm-app⇓x' , vx'
SN-↓-bw (⇒-lam A e) step (x' , tm-lam⇓x' , vx') = x' , ⇓-trans step tm-lam⇓x' , vx'
SN-↓-bw ⇒-unit step (x' , tm-unit⇓x' , vx') = x' , ⇓-trans step tm-unit⇓x' , vx'

Red-↓-bw : ∀{T x x'} → [] ⊢ x ⇒ T → (x ↓ x') → Red T x' → Red T x
Red-↓-bw {ty-arr A B} ht step (x'⇒T , SNx' , pres) =
  ht , SN-↓-bw x'⇒T step SNx' , λ red → Red-↓-bw (⇒-app ht (Red-wt red)) (↓-app₁ step) (pres red)
Red-↓-bw {ty-unit} ht step (_ , x'' , x'⇓x'' , vx'') =
  ht , x'' , ⇓-trans step x'⇓x'' , vx''

Red-↓-fw : ∀{T x x'} → (x ↓ x') → Red T x → Red T x'
Red-↓-fw {ty-arr A B} step (ht , SNx , pres) =
  preservation ht step , SN-↓-fw step SNx , λ red → Red-↓-fw (↓-app₁ step) (pres red)
Red-↓-fw {ty-unit} step (ht , SNx) =
  preservation ht step , SN-↓-fw step SNx

Red-⇓-fw : ∀{T x x'} → (x ⇓ x') → Red T x → Red T x'
Red-⇓-fw ⇓-refl red = red
Red-⇓-fw (⇓-trans step steps) red = Red-⇓-fw steps (Red-↓-fw step red)

Red-⇓-bw : ∀{T x x'} → [] ⊢ x ⇒ T → (x ⇓ x') → Red T x' → Red T x
Red-⇓-bw ht ⇓-refl red = red
Red-⇓-bw ht (⇓-trans step steps) red =
  Red-↓-bw ht step (Red-⇓-bw (preservation ht step) steps red)

ρ-∘ :
  ∀{m n o} →
  (f : Fin n → Fin o) →
  (g : Fin m → Fin n) →
  (x : Fin (suc m)) →
  ρ f (ρ g x) ≡
  ρ (λ y → f (g y)) x
ρ-∘ f g zero = refl
ρ-∘ f g (suc x) = refl

rename-∘ :
  ∀{m n o} →
  (f : Fin n → Fin o) →
  (g : Fin m → Fin n) →
  (x : term m) →
  rename f (rename g x) ≡
  rename (λ y -> f (g y)) x
rename-∘ f g (tm-var x) = refl
rename-∘ f g (tm-lam A e)
  rewrite
    rename-∘ (ρ f) (ρ g) e |
    extensionality (ρ-∘ f g) = refl
rename-∘ f g (tm-app a b)
  rewrite
    rename-∘ f g a |
    rename-∘ f g b = refl
rename-∘ f g tm-unit = refl

rename-ρ-σ :
  ∀{m n o} →
  (f : Fin n → Fin o) →
  (g : Fin m → term n) →
  (x : Fin (suc m)) →
  rename (ρ f) (σ g x) ≡
  σ (λ y → rename f (g y)) x
rename-ρ-σ f g zero = refl
rename-ρ-σ f g (suc x)
  rewrite
    rename-∘ (ρ f) suc (g x) |
    rename-∘ suc f (g x) = refl

rename-subst :
  ∀{m n o} →
  (f : Fin n → Fin o) →
  (g : Fin m → term n) →
  (x : term m) →
  rename f (subst g x) ≡
  subst (λ y → rename f (g y)) x
rename-subst f g (tm-var x) = refl
rename-subst f g (tm-lam A e)
  rewrite
    rename-subst (ρ f) (σ g) e |
    extensionality (rename-ρ-σ f g) = refl
rename-subst f g (tm-app a b)
  rewrite
    rename-subst f g a |
    rename-subst f g b = refl
rename-subst f g tm-unit = refl

σ-subst :
  ∀{m n o} →
  (f : Fin n → term o) →
  (g : Fin m → term n) →
  (x : Fin (suc m)) →
  subst (σ f) (σ g x) ≡
  σ (λ y → subst f (g y)) x
σ-subst f g zero = refl
σ-subst f g (suc x)
  rewrite
    subst-rename (σ f) suc (g x) |
    rename-subst suc f (g x) = refl

subst-∘ :
  ∀{m n o} →
  (f : Fin n → term o) →
  (g : Fin m → term n) →
  (x : term m) →
  subst f (subst g x) ≡ subst (λ y → subst f (g y)) x
subst-∘ f g (tm-var x) = refl
subst-∘ f g (tm-lam A e)
  rewrite
    subst-∘ (σ f) (σ g) e |
    extensionality (σ-subst f g) = refl
subst-∘ f g (tm-app a b)
  rewrite
    subst-∘ f g a |
    subst-∘ f g b = refl
subst-∘ f g tm-unit = refl

thing1 :
  ∀{n} {B} →
  (f : Fin n → term 0) →
  (x : term 0) →
  (ex : term (suc n)) →
  Red B (subst (λ z → subst (replace x) (σ f z)) ex) →
  Red B (subst (replace x) (subst (σ f) ex))
thing1 f x ex red rewrite sym (extensionality (subst-∘ (replace x) (σ f))) = red

wt-Red :
  ∀{n} {Γ : Vec type n} {x T} →
  (f : Fin n → term zero) →
  f ⊨ Γ →
  Γ ⊢ x ⇒ T →
  Red T (subst f x)
wt-Red f ff (⇒-var x) = ff x
wt-Red f ff (⇒-app a b) with wt-Red f ff a
wt-Red f ff (⇒-app a b) | _ , _ , pres = pres (wt-Red f ff b)
wt-Red f ff (⇒-lam {e} A htAB) =
  let
    htABsubst = subst-preservation f (λ a → Red-wt (ff a)) (⇒-lam A htAB)
  in
  htABsubst ,
  (_ , ⇓-refl , value-lam) ,
  λ redA →
  let
    x' , x⇓x' , vx' = Red-sn redA
    redA' = Red-⇓-fw x⇓x' redA
    res = wt-Red (subst (replace x') ∘ σ f) (σ-⊨ f ff x' redA') htAB
  in
    Red-⇓-bw
      (⇒-app htABsubst (Red-wt redA))
      (⇓-app₂ value-lam x⇓x')
      (Red-↓-bw
         (⇒-app htABsubst (Red-wt redA'))
         (↓-β vx')
         (thing1 f x' e res))
wt-Red f ff ⇒-unit = ⇒-unit , tm-unit , ⇓-refl , value-unit

sn : ∀{x T} → [] ⊢ x ⇒ T → SN x
sn {x} ht rewrite sym (subst-⊥ (λ ()) x) = Red-sn (wt-Red (λ ()) (λ ()) ht)
