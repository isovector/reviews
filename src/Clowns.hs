{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE DerivingVia            #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoStarIsType           #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Clowns where

import Data.Functor.Identity
import Data.Functor.Const
import Data.Bifunctor
import Data.Void
import Data.Kind
import GHC.Generics


data Expr = Val Int | Add Expr Expr

eval :: Expr -> Int
eval (Val n) = n
eval (Add ex ex') = eval ex + eval ex'

eval' :: Expr -> Int
eval' e = load e []

load :: Expr -> [Either Expr Int] -> Int
load (Val n) s = unload n s
load (Add ex ex') s = load ex $ Left ex' : s

unload :: Int -> [Either Expr Int] -> Int
unload v [] = v
unload v (Left e : s) = load e $ Right v : s
unload v2 (Right v1 : s) = unload (v1 + v2) s

data ExprF a = ValF Int | AddF a a
  deriving stock (Functor, Generic, Generic1, Show)
  deriving Dissectable via (Generically ExprF)

data Pair a = Pair a a
  deriving (Functor, Show, Generic1)
  deriving Dissectable via (Generically Pair)

deriving via Generically (Either a) instance Dissectable (Either a)

data ExprF' a = ExprF (Either Int (Pair a))
  deriving stock (Functor, Generic, Generic1, Show)
  deriving Dissectable via (Generically ExprF')

pattern ValF' :: Int -> ExprF' a
pattern ValF' a = ExprF (Left a)

pattern AddF' :: a -> a -> ExprF' a
pattern AddF' a b = ExprF (Right (Pair a b))


data K2 a x y = K2 a
  deriving Functor

instance Bifunctor (K2 a) where
  bimap _ _ (K2 a) = K2 a

type Zero1 = Const Void
type Zero2 = K2 Void

data Clown p a b = Clown { unClown :: p a }
  deriving Functor

instance Functor p => Bifunctor (Clown p) where
  bimap fab _ (Clown pa) = Clown (fmap fab pa)

data Joker p a b = Joker { unJoker :: p b }
  deriving Functor

instance Functor p => Bifunctor (Joker p) where
  bimap _ fcd (Joker pc) = Joker (fmap fcd pc)

type Fst = Clown Identity
type Snd = Joker Identity

class (Functor p, Bifunctor (Dissected p)) => Dissectable p where
  type Dissected p :: Type -> Type -> Type
  start :: p j -> Suspension p (Dissected p) c j
  proceed :: c -> Dissected p c j -> Suspension p (Dissected p) c j
  plug :: x -> Dissected p x x -> p x

newtype Generically p a = Generically { unGenerically :: p a }
  deriving Functor

instance ( Generic1 p
         , Functor p
         , Bifunctor (GDissected (Rep1 p))
         , GDissectable (Rep1 p)
         )
    => Dissectable (Generically p) where
  type Dissected (Generically p) = GDissected (Rep1 p)
  start (Generically pj) = bihoist (Generically . to1) id $ gstart $ from1 pj
  proceed x = bihoist (Generically . to1) id . gproceed x
  plug x = Generically . to1 . gplug x

data Suspension p k c j
  = More j (k c j)
  | Done (p c)
  deriving Functor

instance Applicative (k c) => Applicative (Suspension p k c) where
  pure a = More a $ pure a
  More fab fk <*> More a kca =
    More (fab a) (fk <*> kca)
  Done pc <*> _ = Done pc
  _ <*> Done pc = Done pc


bihoist
    :: (forall x. p x -> p' x)
    -> (forall a b. k a b -> k' a b)
    -> Suspension p  k  c j
    -> Suspension p' k' c j
bihoist _ g (More j kcj) = More j (g kcj)
bihoist f _ (Done pc)    = Done (f pc)

instance (Functor p, Bifunctor k) => Bifunctor (Suspension p k) where
  bimap fab fcd (More c kac)
    = More (fcd c) (first fab (second fcd kac))
  bimap fab _ (Done pa) = Done (fmap fab pa)


class GDissectable p where
  type GDissected p :: Type -> Type -> Type
  gstart :: p j -> Suspension p (GDissected p) c j
  gproceed :: c -> GDissected p c j -> Suspension p (GDissected p) c j
  gplug :: x -> GDissected p x x -> p x

instance GDissectable U1 where
  type GDissected U1 = K2 Void
  gstart _ = Done U1
  gproceed _ (K2 v) = absurd v
  gplug _ (K2 vo) = absurd vo

instance GDissectable (K1 _1 a) where
  type GDissected (K1 _1 a) = K2 Void
  gstart (K1 a) = Done (K1 a)
  gproceed _ (K2 v) = absurd v
  gplug _ (K2 vo) = absurd vo

instance GDissectable Par1 where
  type GDissected Par1 = K2 ()
  gstart (Par1 j) = More j (K2 ())
  gproceed c _ = Done (Par1 c)
  gplug x _ = Par1 x

instance (Generic1 f, Dissectable f) => GDissectable (Rec1 f) where
  type GDissected (Rec1 f) = Dissected f
  gstart (Rec1 f) = bihoist Rec1 id $ start f
  gproceed c f = bihoist Rec1 id $ proceed c f
  gplug x gd = Rec1 $ plug x gd

instance GDissectable f => GDissectable (M1 _1 _2 f) where
  type GDissected (M1 _1 _2 f) = GDissected f
  gstart (M1 fj) = bihoist M1 id $ gstart fj
  gproceed fc = bihoist M1 id . gproceed fc
  gplug x dis = M1 $ gplug x dis

instance (GDissectable f, GDissectable g) => GDissectable (f :+: g) where
  type GDissected (f :+: g) = Sum2 (GDissected f) (GDissected g)
  gstart (L1 fj) = bihoist L1 L2 $ gstart fj
  gstart (R1 gj) = bihoist R1 R2 $ gstart gj
  gproceed c (L2 dis) = bihoist L1 L2 $ gproceed c dis
  gproceed c (R2 dis) = bihoist R1 R2 $ gproceed c dis
  gplug x (L2 dis) = L1 (gplug x dis)
  gplug x (R2 dis) = R1 (gplug x dis)

instance (GDissectable f, GDissectable g) => GDissectable (f :*: g) where
  type GDissected (f :*: g) =
    Sum2 (Product2 (GDissected f) (Joker g))
         (Product2 (Clown f) (GDissected g))
  gstart (pj :*: qj) = mindp (gstart @f pj) qj
  gproceed c (L2 (Product2 pd (Joker qj))) = mindp (gproceed @f c pd) qj
  gproceed c (R2 (Product2 (Clown pc) qd)) = mindq pc (gproceed @g c qd)
  gplug x (L2 (Product2 f (Joker g))) = gplug x f :*: g
  gplug x (R2 (Product2 (Clown f) g)) = f :*: gplug x g


mindp
    :: GDissectable g
    => Suspension f (GDissected f) c j
    -> g j
    -> Suspension (f :*: g)
                 (Sum2 (Product2 (GDissected f) (Joker g))
                       (Product2 (Clown f) (GDissected g)))
                 c j
mindp (More j pd) qj = More j $ L2 $ Product2 pd $ Joker qj
mindp (Done pc) qj = mindq pc (gstart qj)

mindq
    :: f c
    -> Suspension g (GDissected g) c j
    -> Suspension (f :*: g)
                 (Sum2 (Product2 (GDissected f) (Joker g))
                       (Product2 (Clown f) (GDissected g)))
                 c j
mindq pc (More j qd) = More j $ R2 $ Product2 (Clown pc) qd
mindq pc (Done qc) = Done (pc :*: qc)


newtype Compose2 f g a b = Compose2 (f (g a) (g b))

instance (Bifunctor f, Functor g) => Functor (Compose2 f g a) where
  fmap fab (Compose2 f) = Compose2 $ bimap id (fmap fab) f

instance (Bifunctor f, Functor g) => Bifunctor (Compose2 f g) where
  bimap fab fcd (Compose2 f) = Compose2 $ bimap (fmap fab) (fmap fcd) f

instance (Generic1 f, Functor f, Bifunctor (Dissected f), Dissectable f, GDissectable g) => GDissectable (f :.: g) where
  type GDissected (f :.: g) =
    Product2
      (Compose2 (Dissected f) g)
      (GDissected g)
  gstart (Comp1 fg) =
    case start @f $ fg of
      More gj gd -> pump gj gd
      Done f -> Done $ Comp1 f
    where
      pump
          :: g j
          -> Dissected f (g c) (g j)
          -> Suspension
               (f :.: g)
               (Product2 (Compose2 (Dissected f) g) (GDissected g))
               c j
      pump gj gd =
        case gstart gj of
          More j gd' ->
            More j (Product2 (Compose2 gd) gd')
          Done g ->
            case proceed @f g gd of
              More gj gd -> pump gj gd
              Done fg -> Done $ Comp1 fg
  gproceed c (Product2 cfg@(Compose2 fg) gd) =
    case gproceed @g c gd of
      More j gd -> More j $ Product2 cfg gd
      Done gc -> finish gc
    where
      -- finish
      --     :: g c
      --     -> Suspension
      --          (f :.: g)
      --          (Product2 (Compose2 (Dissected f) g) (GDissected g))
      --          c j
      finish gc =
        case proceed @f gc fg of
          More gj gd ->
            case gstart gj of
              More j gd' -> More j $ Product2 (Compose2 gd) gd'
              Done gc -> finish gc
          Done f -> Done $ Comp1 f
  gplug x (Product2 (Compose2 fg) gd) =
    Comp1 $ plug @f (gplug @g x gd) fg


data Sum2 f g a b = L2 (f a b) | R2 (g a b)
  deriving Functor

instance (Bifunctor f, Bifunctor g) => Bifunctor (Sum2 f g) where
  bimap fab fcd (L2 fac) = L2 (first fab (second fcd fac))
  bimap fab fcd (R2 gac) = R2 (second fcd (first fab gac))

data Product2 f g a b = Product2 (f a b) (g a b)
  deriving Functor

instance (Bifunctor f, Bifunctor g) => Bifunctor (Product2 f g) where
  bimap fab fcd (Product2 fac gac)
    = Product2
        (first fab (second fcd fac)) (second fcd (first fab gac))


divide :: Dissectable p => p x -> Either (x, Dissected p Void x) (p Void)
divide px = case start px of
  More x dis -> Left (x, dis)
  Done p -> Right p



newtype Fix f = Fix { unFix :: f (Fix f) }

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f (Fix f') = f $ fmap (cata f) f'

tmap :: forall p a b. Dissectable p => (a -> b) -> p a -> p b
tmap fab = pump . start
  where
    pump :: Suspension p (Dissected p) b a -> p b
    pump (More a dis) = pump $ proceed (fab a) dis
    pump (Done j) = j

tcata :: forall p v. Dissectable p => (p v -> v) -> Fix p -> v
tcata f t = load' t []
  where
    load'
        :: Fix p
        -> [Dissected p v (Fix p)]
        -> v
    load' (Fix t) stk = next (start t) stk

    next
        :: Suspension p (Dissected p) v (Fix p)
        -> [Dissected p v (Fix p)]
        -> v
    next (More p dis) stk = load' p (dis : stk)
    next (Done p) stk = unload' (f p) stk

    unload'
        :: v
        -> [Dissected p v (Fix p)]
        -> v
    unload' v [] = v
    unload' v (pd : stk) = next (proceed v pd) stk


tsequence :: forall p f a. (Dissectable p, Monad f) => p (f a) -> f (p a)
tsequence = pump . start
  where
    pump :: Suspension p (Dissected p) a (f a) -> f (p a)
    pump (More fa dis) = do
      a <- fa
      pump $ proceed a dis
    pump (Done pa) = pure pa


-- blah :: Fix ExprF
-- blah = Fix $ AddF (Fix $ ValF 5) $ Fix $ AddF (Fix (ValF 1)) $ Fix $ ValF 3

blah :: Fix ExprF
blah = Fix $ AddF (Fix $ ValF 5) $ Fix $ AddF (Fix (ValF 1)) $ Fix $ ValF 3

blah1 :: ExprF [Int]
blah1 = AddF [1,2,3] [4,5]



main = tcata (\ ef
   -> case ef of
        (ValF n) -> n
        (AddF v v') -> v + v') blah

