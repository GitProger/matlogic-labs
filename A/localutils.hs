module LocalUtils where

(~>) = flip (.)

interlayer :: Monad m => m a -> (a -> b) -> (b -> m c) -> m c
interlayer from main to = from >>= main ~> to
