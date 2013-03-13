module Providers

public
data Provider a = Provide (IO a) | Error (IO String)

abstract partial
unProv : Provider a -> a
unProv (Provide x) = unsafePerformIO x
