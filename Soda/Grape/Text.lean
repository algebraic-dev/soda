import Soda.Grape

namespace Grape
namespace Text

@[inline]
def Char.upperCase  : UInt8 → Bool :=
  λchr => chr >= 65 && chr <= 90

@[inline]
def Char.lowerCase  : UInt8 → Bool :=
  λchr => chr >= 97 && chr <= 122

@[inline]
def Char.number : UInt8 → Bool :=
  λchr => chr >= 48 && chr <= 57

@[inline]
def Char.whitespace : UInt8 → Bool :=
  λchr => chr == 32 || chr == 10 || chr == 13 || chr == 9

@[inline]
def Char.hex : UInt8 → Bool :=
  λchr => Char.number chr || (chr >= 65 && chr <= 70) || (chr >= 97 && chr <= 102)

@[inline]
def upperCase : Grape ByteSlice := takeWhile1 Char.upperCase

@[inline]
def lowerCase : Grape ByteSlice := takeWhile1 Char.lowerCase

@[inline]
def number : Grape Nat := Grape.map (String.toNat! ∘ ByteSlice.toASCIIString) (takeWhile1 Char.number)

@[inline]
def digit : Grape Nat := Grape.map (String.toNat! ∘ ByteSlice.toASCIIString) (takeWhile1 Char.number)

@[inline]
def trailing : Grape α → Grape α :=
  fun p => takeWhile Char.whitespace *> p

@[inline]
def takeToStr (pred: UInt8 → Bool) : Grape String :=
  Grape.map ByteSlice.toASCIIString (takeWhile1 pred)

end Text
end Grape