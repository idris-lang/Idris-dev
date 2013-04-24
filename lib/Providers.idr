module Providers

public
data Provider a = Provide a | Error String

partial public
unProv : IO (Provider a) -> a
unProv p = case unsafePerformIO p of
              Provide x => x
