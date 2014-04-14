module Control.Catchable

import Control.IOExcept

class Catchable (m : Type -> Type) t where
    throw : t -> m a
    catch : m a -> (t -> m a) -> m a

instance Catchable Maybe () where
    catch Nothing  h = h ()
    catch (Just x) h = Just x

    throw () = Nothing

instance Catchable (Either a) a where
    catch (Left err) h = h err
    catch (Right x)  h = (Right x)

    throw x = Left x

instance Catchable (IOExcept err) err where
    catch (ioM prog) h = ioM (do p' <- prog
                                 case p' of
                                      Left e => let ioM he = h e in he
                                      Right val => return (Right val))
    throw x = ioM (return (Left x))

instance Catchable List () where
    catch [] h = h ()
    catch xs h = xs

    throw () = []
