
namespace C0deine

structure Context.State where
  nextTemp : String

def Context := StateM Context.State

instance : Monad Context := show Monad (StateM _) from inferInstance
