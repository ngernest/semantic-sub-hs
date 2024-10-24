module Types.NSubtypeSpec (spec) where


import Test.Hspec
import qualified Types.NSubtype as N
import qualified Types.LazyBDD as BDD
import Types.SubtypeTests


spec :: Spec
spec = genSubtypeSpec BDD.parseTy N.subtype N.overlap N.equiv
