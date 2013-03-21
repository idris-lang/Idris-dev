module Providers

public
data Provider a = Provide (IO a) | Error (IO String)

partial public
unProv : Provider a -> a
unProv (Provide x) = unsafePerformIO x
