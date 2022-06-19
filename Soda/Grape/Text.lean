import Soda.Grape

namespace Grape
namespace Text

def Char.upperCase  : UInt8 → Bool := λchr => chr >= 65 && chr <= 90

def Char.lowerCase  : UInt8 → Bool := λchr => chr >= 97 && chr <= 122

def Char.number     : UInt8 → Bool := λchr => chr >= 48 && chr <= 57

def Char.whitespace : UInt8 → Bool := λchr => chr == 32 || chr == 10 || chr == 13

def Char.hex : UInt8 → Bool := λchr => Char.number chr || (chr >= 65 && chr <= 70) || (chr >= 97 && chr <= 102)

def upperCase : Grape String := Grape.map String.fromUTF8Unchecked (takeWhile1 Char.upperCase)

def lowerCase : Grape String := Grape.map String.fromUTF8Unchecked (takeWhile1 Char.lowerCase)

def number : Grape Nat := Grape.map (String.toNat! ∘ String.fromUTF8Unchecked) (takeWhile1 Char.number)

def digit : Grape Nat := Grape.map (String.toNat! ∘ String.fromUTF8Unchecked) (takeWhile1 Char.number)

def trailing : Grape α → Grape α := fun p => takeWhile Char.whitespace *> p

def takeToStr (pred: UInt8 → Bool) : Grape String := Grape.map String.fromUTF8Unchecked (takeWhile1 pred)

end Text
end Grape