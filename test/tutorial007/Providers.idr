module Providers

%access export

%dynamic "./nativetypes.so"

sizeOfSizeT : IO Int
sizeOfSizeT = foreign FFI_C "sizeof_size_t" (IO Int)

public export
data NativeTypeSize = OneByte | TwoBytes | FourBytes | EightBytes

Show NativeTypeSize where
  show OneByte = "1 byte"
  show TwoBytes = "2 bytes"
  show FourBytes = "4 bytes"
  show EightBytes = "8 bytes"

bytesToType : Int -> Provider NativeTypeSize
bytesToType 1 = Provide OneByte
bytesToType 2 = Provide TwoBytes
bytesToType 4 = Provide FourBytes
bytesToType 8 = Provide EightBytes
bytesToType _ = Error "Unsupported size"

getSizeOfSizeT : IO (Provider NativeTypeSize)
getSizeOfSizeT = map bytesToType sizeOfSizeT
