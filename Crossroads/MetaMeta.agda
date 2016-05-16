module MetaMeta where

data Fwd (X : Set) : Set where
  []    : Fwd X
  _,-_  : X -> Fwd X -> Fwd X
infixr 4 _,-_

data Bwd (X : Set) : Set where
  []    : Bwd X
  _-,_  : Bwd X -> X -> Bwd X
infixl 4 _-,_

data _:>_ {X : Set} : Bwd X -> X -> Set where
  ze : forall {xz x} -> (xz -, x) :> x
  su : forall {x xz y} -> xz :> x -> (xz -, y) :> x

data Syn (I : Set) : Set where
  []    : Syn I
  #   : I -> Syn I
  _=>_  : I -> Syn I -> Syn I
  _/_   : Syn I -> Syn I -> Syn I
  Sum   : Fwd (Syn I) -> Syn I
infixr 5 _/_
infixr 6 _=>_

record One : Set where constructor <>
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_

data Zero : Set where
data Two : Set where tt ff : Two
_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

Node : {I : Set}(R : Bwd I -> I -> Set) -> Syn I -> Bwd I -> Set
Choose : {I : Set}(R : Bwd I -> I -> Set) -> Fwd (Syn I) -> Bwd I -> Set
Node R [] G = One
Node R (# i) G = R G i
Node R (j => F) G = Node R F (G -, j)
Node R (F / F') G = Node R F G * Node R F' G
Node R (Sum Fs) G = Choose R Fs G
Choose R [] G = Zero
Choose R (F ,- Fs) G = Node R F G + Choose R Fs G

data BwdIn {X : Set} : Bwd X -> X -> Set where
  ze : forall {xz x} -> BwdIn (xz -, x) x
  su : forall {xz y x} -> BwdIn xz x -> BwdIn (xz -, y) x

data Tm {I : Set}(F : I -> Syn I)(G : Bwd I)(i : I) : Set where
  [_] : Node (Tm F) (F i) G -> Tm F G i
  ! : BwdIn G i -> Tm F G i

data Cx {I : Set}(F B : I -> Syn I) : Bwd I -> Set where
  [] : Cx F B []
  _-,_ : forall {G i} -> Cx F B G -> Node (Tm F) (B i) G -> Cx F B (G -, i)


data Status : Set where blk red : Status

Mode : Status -> Set
Mode blk = Two  -- tt for input; ff for output
Mode red = One

Role : Set
Role = Sg Status Mode


-- the syntax of judgment forms is given by some
--   J    : Set                    -- the judgment forms
--   JSyn : J -> Syn (Role * I)    -- the syntax of each

module ExPat {I : Set}(F B : I -> Syn I) where
  -- F is the term syntax for each sort
  -- B is the syntax of contextual bindings for variables of each sort

  data Arity : Set where
    #     : I -> Arity
    _=>_  : I -> Arity -> Arity
  infixr 6 _==>_

  _==>_ : Bwd I -> Arity -> Arity
  [] ==> t = t
  (is -, i) ==> t = is ==> (i => t)

  Sch : Set
  Sch = Status * Arity

  SCx : Set
  SCx = Bwd Sch

  AllBlk : SCx -> Set
  AllBlk [] = One
  AllBlk (G -, (blk , _)) = AllBlk G
  AllBlk (G -, (red , _)) = Zero

  data SVar (t : Sch) : SCx -> SCx -> Set where
    ze : {G : SCx} -> SVar t (G -, t) (G -, (blk , snd t))
    su : {G G' : SCx}{s : Sch} -> SVar t G G' -> SVar t (G -, s) (G' -, s)
  
  data Exp (G : SCx)(L : Bwd I)(r : Status) : Arity -> SCx -> Set
  data Exps (G : SCx)(L : Bwd I)(r : Status) : Syn I -> SCx -> Set
  data Exp G L r where
    sv : forall {T G'} -> (x : SVar (r , T) G G') -> Exp G L r T G'
    bv : forall {i} -> L :> i -> Exp G L r (# i) G
    _$_ : forall {i T G' G''} -> Exp G L r (i => T) G' -> Exp G' L r (# i) G''
           -> Exp G L r T G''
    [_] : forall {i G'} -> Exps G L r (F i) G' -> Exp G L r (# i) G'
  data Exps G L r where
    [] : Exps G L r [] G
    [_] : forall {i G'} -> Exp G L r (# i) G' -> Exps G L r (# i) G'
    _,_ : forall {S T G' G''} -> Exps G L r S G' ->
                        Exps G' L r T G'' -> Exps G L r (S / T) G''
    inl : forall {S Ts G'} -> Exps G L r S G' -> Exps G L r (Sum (S ,- Ts)) G'
    inr : forall {S Ts G'} -> Exps G L r (Sum Ts) G' -> Exps G L r (Sum (S ,- Ts)) G'
    la : forall {i T G'} -> Exps G (L -, i) r T G'  -> Exps G L r (i => T) G'

  data Pats (G : SCx)(L : Bwd I)(r : Status) : Syn I -> SCx -> Set
  data Pat (G : SCx)(L : Bwd I)(r : Status)(i : I) : SCx -> Set
  data Pat G L r i where
    [_] : forall {G'} -> Pats G L r (F i) G' -> Pat G L r i G'
    is : forall {G'} -> Exp G L blk (# i) G' -> Pat G L r i G'  -- force r = blk ?
    bi : Pat G L r i (G -, (r , (L ==> # i)))
    ov : forall {G'} -> Pats G [] blk (B i) G' -> Pat G L r i G'
  data Pats G L r where
    [] : Pats G L r [] G
    [_] : forall {i G'} -> Pat G L r i G' -> Pats G L r (# i) G'
    _,_ : forall {S T G' G''} -> Pats G L r S G' ->
                        Pats G' L r T G'' -> Pats G L r (S / T) G''
    inl : forall {S Ts G'} -> Pats G L r S G' -> Pats G L r (Sum (S ,- Ts)) G'
    inr : forall {S Ts G'} -> Pats G L r (Sum Ts) G' ->
            Pats G L r (Sum (S ,- Ts)) G'
    la : forall {i T G'} -> Pats G (L -, i) r T G' -> Pats G L r (i => T) G'

  module Judge {J : Set}(JF : J -> Fwd (Role * I)) where

    PremStuff : SCx -> Bwd I -> (Role * I) -> SCx -> Set
    PremStuff G L ((blk , tt) , i) G' = Exp G L blk (# i) G'
    PremStuff G L ((blk , ff) , i) G' = Pat G L blk i G'
    PremStuff G L ((red , <>) , i) G' = Exp G L red (# i) G'
      
    data Premise (G : SCx)(L : Bwd I) : Fwd (Role * I) -> SCx -> Set where
      [] : Premise G L [] G
      _,-_ : forall {S Ts G' G''} -> PremStuff G L S G' ->
                        Premise G' L Ts G'' -> Premise G L (S ,- Ts) G''

    ConcStuff : SCx -> (Role * I) -> SCx -> Set
    ConcStuff G ((blk , tt) , i) G' = Pat G [] blk i G'
    ConcStuff G ((blk , ff) , i) G' = Exp G [] blk (# i) G'
    ConcStuff G ((red , <>) , i) G' = Pat G [] red i G'

    data CxE (G : SCx) : Bwd I -> SCx -> Set where
      [] : CxE G [] G
      _-,_ : forall {L G' G''} ->
             CxE G L G' -> (z : Sg I \ i -> Exps G' L blk (B i) G'') ->
             CxE G (L -, fst z) G''

    data Rule (G : SCx) : Fwd (Role * I) -> Set where
      [] : {_ : AllBlk G} -> Rule G []
      _,-_ : forall {S G' Ts} -> ConcStuff G S G' -> Rule G' Ts ->
               Rule G (S ,- Ts)
      _!_!-_&_ : forall {G' G'' Ts L} -> CxE G L G' ->
                   (j : J) -> Premise G' L (JF j) G'' ->
                   Rule G'' Ts -> Rule G Ts
    infixr 4 _,-_ _!_!-_&_

    -- how do we check each context entry for validity?
    RulesCon : Set
    RulesCon = (i : I) -> Fwd
       (Sg SCx \ G -> Pats [] [] red (B i) G * Rule G [])

    -- what are the rules for each judgment form?
    RulesSyn : Set
    RulesSyn = (j : J) -> Fwd (Rule [] (JF j))

    -- for each judgment form,
    -- what is demanded of inputs? what is delivered by outputs?



----------------

data TTSort : Set where term elim : TTSort
TTSyn TTCxE : TTSort -> Syn TTSort
TTSyn term = Sum ([]
             ,-   # term  /  elim => # term
             ,-   elim => # term
             ,-   # elim
             ,- [])
TTSyn elim = Sum (# elim  /  # term
             ,-   # term  /  # term
             ,- [])

TTCxE term = Sum []
TTCxE elim = # term

data TTJudge : Set where chk syn sub : TTJudge
TTJudgeForm : TTJudge -> Fwd (Role * TTSort)
TTJudgeForm chk = ((blk , tt) , term) ,- ((red , <>) , term) ,- []
TTJudgeForm syn = ((red , <>) , elim) ,- ((blk , ff) , term) ,- []
TTJudgeForm sub = ((blk , tt) , term) ,- ((blk , tt) , term) ,- []

open ExPat
open Judge

pattern STAR = [ inl [] ]
pattern PI S T = [ inr (inl ([ S ] , la [ T ])) ]
pattern LA T = [ inr (inr (inl (la [ T ]))) ]
pattern EN E = [ inr (inr (inr (inl [ E ]))) ]
pattern AP F S = [ inl ([ F ] , [ S ]) ]
pattern TY s S = [ inr (inl ([ s ] , [ S ])) ]

rulesC : RulesCon TTSyn TTCxE TTJudgeForm
rulesC term = []
rulesC elim = _ , ([ bi ] , ([] ! chk !- STAR ,- sv ze ,- [] & [])) ,- []

rulesS : RulesSyn TTSyn TTCxE TTJudgeForm
rulesS chk =
      (STAR ,- STAR ,- [])
  ,-  (STAR ,- PI bi bi ,-
         [] ! chk !- STAR ,- sv (su ze) ,- [] &
         ([] -, (elim , [ sv (su ze) ])) ! chk !-
            STAR ,- sv ze $ bv ze ,- [] & [])
  ,-  (PI bi bi ,- LA bi ,-
         ([] -, (elim , [ sv (su (su ze)) ])) ! chk !-
            (sv (su ze) $ bv ze) ,- ((sv ze $ bv ze) ,- []) & [])
  ,-  (bi ,- EN bi ,-
         [] ! syn !- sv ze ,- bi ,- [] &
         [] ! sub !- sv ze ,- sv (su (su ze)) ,- [] & [])
  ,- []
rulesS syn =
      (AP bi bi ,-
        [] ! syn !- sv (su ze) ,- PI bi bi ,- [] &
        [] ! chk !- sv (su ze) ,- sv (su (su ze)) ,- [] &
        sv ze $ TY (sv (su (su ze))) (sv (su ze)) ,- [])
  ,-  (TY bi bi ,-
        [] ! chk !- STAR ,- sv ze ,- [] &
        [] ! chk !- sv ze ,- sv (su ze) ,- [] &
        sv ze ,- [])
  ,- ((ov [ bi ] ,- sv ze ,- []))
  ,- []
rulesS sub = (bi ,- is (sv ze) ,- [])
  ,- []
