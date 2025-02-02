{-# LANGUAGE AllowAmbiguousTypes #-}
module KnownBool where
class KnownBool (s :: Bool) where fromBoolKind :: Bool
instance KnownBool True where fromBoolKind = True
instance KnownBool False where fromBoolKind = False
