module Control.Catchable

import Control.IOExcept

%access public export

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
