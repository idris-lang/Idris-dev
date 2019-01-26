module Control.Catchable

import Control.IOExcept
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Trans

%access public export
%default total

interface Catchable (m : Type -> Type) t | m where
    throw : t -> m a
    catch : m a -> (t -> m a) -> m a

implementation Catchable Maybe () where
    catch Nothing  h = h ()
    catch (Just x) h = Just x

    throw () = Nothing

implementation Catchable (Either a) a where
    catch (Left err) h = h err
    catch (Right x)  h = (Right x)

    throw = Left

implementation Catchable (IOExcept err) err where
    catch (IOM prog) h = IOM (do p' <- prog
                                 case p' of
                                      Left e => let IOM he = h e in he
                                      Right val => pure (Right val))
    throw = ioe_fail

implementation Catchable List () where
    catch [] h = h ()
    catch xs h = xs

    throw () = []

||| Adapted from https://hackage.haskell.org/package/mtl-2.2.1/docs/src/Control.Monad.Error.Class.html#line-138
implementation (Monad m, Catchable m t) => Catchable (ReaderT r m) t where
    -- TODO: rewrite this with apply2way combinator when implemented
    catch m h = RD $ \ r => catch (runReaderT m r) (\ e => runReaderT (h e) r)
    -- catch m h = RD $ \ r => catch (runReaderT m r) (\ e => runReaderT (h e) r)

    throw = lift . throw

||| Adapted from https://hackage.haskell.org/package/transformers-0.5.4.0/docs/src/Control.Monad.Trans.Writer.Lazy.html#local-6989586621679059673
implementation (Monad m, Monoid w, Catchable m t) => Catchable (WriterT w m) t where
    catch m h = WR $ runWriterT m `catch` runWriterT . h
    throw = lift . throw

||| Adapted from https://hackage.haskell.org/package/mtl-2.2.1/docs/src/Control.Monad.Error.Class.html#line-138
implementation (Monad m, Monoid w, Catchable m t) => Catchable (RWST r w s m) t where
    catch m h = MkRWST $ \ r, s => runRWST m r s `catch` \ e => runRWST (h e) r s
    throw = lift . throw
