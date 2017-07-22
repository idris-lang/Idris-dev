interface Foo a where

interface Foo2 a where

interface Foo a => Bar a where

interface Foo a => Bar2 a where
  implementation Foo a where

-- Foo is found in parent
interface Bar a => Bar3 a where
  implementation Foo a where

-- not necessary but should compile
interface (Foo a, Bar a) => Bar4 a where
  implementation Foo a where

-- should fail to compile (Foo2 isn't found in parent interfaces)
interface Foo a => Bar5 a where
  implementation Foo2 a where
