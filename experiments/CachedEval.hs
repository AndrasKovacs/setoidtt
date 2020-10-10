{-# language Strict, LambdaCase, UnicodeSyntax, PatternSynonyms #-}
{-# options_ghc -Wincomplete-patterns #-}

type Lvl = Int
type Ix  = Int
type Env = [Val]
type Con = Lvl
type Ren = [Lvl]

infixl 8 $$
($$) = App

pattern Let t u = App (Lam u) t

instance Num Tm where
  fromInteger = Var . fromIntegral
  (+) = undefined; (*) = undefined; abs = undefined
  signum = undefined; negate = undefined

data Tm = Var Ix | Lam Tm | App Tm Tm deriving Show
data Val = VVar Lvl | VApp Val ~Val | VLam Con Env Tm ~Val deriving Show

-- VVar : Var Γ A → Val Γ A
-- VApp : Val Γ (Π A B) → (u : Val Γ A) → Val Γ (B[id,u])
-- VLam : (Γ' : Con){wk : Γ ≥ Γ'}{Δ : Con}(σ : Env Γ' Δ)(t : Tm (Δ, A) B)
--        → Val (Γ', A[σ]) B[σ⁺]
--        → Val Γ (Π A[σ∘wk] B[(σ∘wk)⁺])

-- weakening for Env/Val is still implicit, because {wk : Γ ≥ Γ'} is computationally irrelevant
-- hence σ∘wk = σ

-- eval : (Γ : Con)(σ : Env Γ Δ) → Tm Δ A → Val Γ A[σ]
eval ∷ Con → Env → Tm → Val
eval gamma σ = \case
  Var x   → σ !! x
  App t u → case (eval gamma σ t, eval gamma σ u) of

               (VLam gamma' σ' t _ , u) →
                 -- wk  : Γ ≥ Γ'
                 -- σ'  : Env Γ' Δ
                 -- t   : Tm (Δ, A) B
                 -- u   : Val Γ A[σ]
                 --     : Val Γ A[σ']

                 -- we know that A[σ] = A[σ'] and B[σ⁺] = B[σ'⁺]
                 -- goal : Val Γ (B[σ, u])

                 -- σ'∘wk    : Env Γ Δ
                 -- σ'∘wk, u : Env Γ (Δ, A)
                 -- eval Γ (σ'∘wk, u) : Tm (Δ, A) B → Val Γ B[σ'∘wk, u]
                 -- eval Γ (σ'∘wk, u) t : Val Γ B[σ'∘wk, u]
                 --                     : Val Γ B[σ', u]
                 --                     : Val Γ B[σ'⁺][id, u]
                 --                     : Val Γ B[σ⁺][id, u]
                 --                     : Val Γ B[σ, u]         OK
                 eval gamma (u:σ') t

               (t, u) → VApp t u

  -- t         : Tm (Δ, A) B
  -- σ         : Env Γ Δ
  -- σ⁺        : Env (Γ,A[σ]) (Δ, A)
  -- eval σ⁺ t : Val (Γ,A[σ]) B[σ⁺]
  Lam t   → VLam gamma {- id -} σ t (eval (gamma + 1) (VVar gamma:σ) t)

-- rename : (Δ : Con)(σ : Ren Γ Δ) → Var Δ A → Var Γ A[σ]
rename ∷ Con → Ren → Lvl → Lvl
rename gamma r x = r !! (gamma - x - 1)

-- conv : (Γ : Con)
--        (Δ  : Con)(r  : Ren Γ Δ) (t  : Val Δ A)
--        (Δ' : Con)(r' : Ren Γ Δ')(t' : Val Δ' A')
--        {p : A[r] = A'[r']}
--        → Dec (t[r] = t[r'])
conv ∷ Con → Con → Ren → Val → Con → Ren → Val → Bool
conv gamma delta r t delta' r' t' = case (t, t') of
  (VLam gamma' σ _ t, VLam gamma'' σ' _ t') →

    -- t  : Val (Γ' , A[σ])   B[σ⁺]
    -- t' : Val (Γ'', A'[σ']) B'[σ'⁺]
    -- wk : Δ  ≥ Γ'
    -- wk': Δ' ≥ Γ''
    -- r  : Ren Γ Δ
    -- r' : Ren Γ Δ'

    -- wk∘r    : Ren Γ Γ'                        (this is given by truncating r to the first Γ' entries)
    -- (wk∘r)⁺ : Ren (Γ, A[σ∘wk∘r]) (Γ', A[σ])   (given by (len(Γ) : (wk∘r)))
    -- t       : Val (Γ', A[σ]) (B[σ⁺])

    -- recursive call:
    --   conv (Γ, A[σ∘wk∘r])
    --        (Γ', A[σ])   (wk∘r)⁺   t
    --        (Γ'',A'[σ']) (wk'∘r')⁺ t'

    conv (gamma + 1)
         (gamma'  + 1) (gamma:drop (delta  - gamma')  r ) t
         (gamma'' + 1) (gamma:drop (delta' - gamma'') r') t'

  (VLam gamma' _ _ t, t') →
    conv (gamma + 1) (gamma' + 1) (gamma:drop (delta  - gamma') r) t
                     delta' r' (VApp t' (VVar gamma))

  (t, VLam gamma'' _ _ t') →
    conv (gamma + 1) delta r (VApp t (VVar gamma))
                     (gamma'' + 1) (gamma:drop (delta' - gamma'') r') t'

  (VVar x,   VVar x')    →
    rename delta r x == rename delta' r' x'

  (VApp t u, VApp t' u') →
    conv gamma delta r t delta' r' t' && conv gamma delta r u delta' r' u'

  _ → False


-- We can also use cached values for quoting.

-- quote : (Γ : Con) → Val Γ A → Tm Γ A
quote ∷ Con → Val → Tm
quote gamma = \case
  VVar x            → Var (gamma - x - 1)
  VApp t u          → App (quote gamma t) (quote gamma u)
  VLam gamma' σ _ t → Lam (quote (gamma' + 1) t)
    -- wk : Γ ≥ Γ'
    -- t : Val (Γ', A[σ]) B[σ⁺]
    -- goal : Tm (Γ, A[σ∘wk]) B[(σ∘wk)⁺]
    --      : Tm (Γ', A[σ]) B[σ⁺]
    --      := quote (Γ', A[σ]) t

nf0 ∷ Tm → Tm
nf0 = quote 0 . eval 0 []

convTm0 :: Tm → Tm → Bool
convTm0 t t' = conv 0 0 [] (eval 0 [] t) 0 [] (eval 0 [] t')

test0 =
  Let (Lam $ Lam $ 1 $$ (1 $$ (1 $$ (1 $$ (1 $$ 0))))) $
  Let (Lam $ Lam $ Lam $ Lam $ 3 $$ 1 $$ (2 $$ 1 $$ 0)) $
  Let (Lam $ Lam $ Lam $ Lam $ 3 $$ (2 $$ 1) $$ 0) $
  Let (1 $$ 2 $$ 2) $
  Let (1 $$ 0 $$ 0) $
  Let (2 $$ 1 $$ 0) $
  0
  -- "let λ λ 1 (1 (1 (1 (1 0)))) in",    -- five = λ s z. s (s (s (s (s z))))
  -- "let λ λ λ λ 3 1 (2 1 0) in",        -- add  = λ a b s z. a s (b s z)
  -- "let λ λ λ λ 3 (2 1) 0 in",          -- mul  = λ a b s z. a (b s) z
  -- "let 1 2 2 in",                      -- ten  = add five five
  -- "let 1 0 0 in",                      -- hundred = mul ten ten
  -- "let 2 1 0 in",                      -- thousand = mul ten hundred
  -- "0"                                  -- thousand

test1 =
  Let (Lam $ Lam $ 1 $$ (1 $$ (1 $$ (1 $$ (1 $$ 0))))) $
  Let (Lam $ Lam $ Lam $ Lam $ 3 $$ 1 $$ (2 $$ 1 $$ 0)) $
  Let (Lam $ Lam $ Lam $ Lam $ 3 $$ (2 $$ 1) $$ 0) $
  Let (1 $$ 2 $$ 2) $
  Let (1 $$ 0 $$ 0) $
  Let (2 $$ 0 $$ 1) $
  0


convTest :: Bool
convTest = convTm0 test0 test1
