module Data.Crypto.Security

%default total

public
data SecurityLevel : Type where
  Secure : SecurityLevel
  Unknown : SecurityLevel
  Insecure : List String -> SecurityLevel

instance Semigroup SecurityLevel where
  (Insecure reasons) <+> (Insecure reasons') = Insecure (reasons ++ reasons')
  (Insecure reasons) <+> _                   = Insecure reasons
  _                  <+> (Insecure reasons)  = Insecure reasons
  Unknown            <+> _                   = Unknown
  _                  <+> Unknown             = Unknown
  Secure             <+> Secure              = Secure

instance Monoid SecurityLevel where
  neutral = Secure

public
data Security : Type -> Type where
  MkSecure : SecurityLevel -> a -> Security a

instance Functor Security where
  map f (MkSecure level a) = MkSecure (Unknown <+> level) (f a)

instance Applicative Security where
  pure a = MkSecure neutral a
  (MkSecure level f) <$> (MkSecure level' a) = MkSecure (level <+> level') (f a)

instance Monad Security where
  (MkSecure level a) >>= f =
    case f a of
      MkSecure level' b => MkSecure (level <+> level') b

-- instance Serializable a => Serializable (Security a) where
--   encode (MkSecure _ a) = encode a
--   decode = MkSecure Unknown . decode
