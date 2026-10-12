module
public import Aeneas.SepLogic.IProp
@[expose] public section

namespace Aeneas.SepLogic

open Lean PrettyPrinter Delaborator SubExpr

@[app_delab ipure]
meta def delabIpure : Delab := do
  guard ((← getExpr).isAppOfArity ``ipure 1)
  let proposition ← withAppArg delab
  `(⌜$proposition⌝)

@[app_delab iand]
meta def delabIand : Delab := do
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `(iprop($lhs ∧ $rhs))

@[app_delab Entails]
meta def delabEntails : Delab := do
  guard ((← getExpr).isAppOfArity ``Entails 2)
  let lhs ← withNaryArg 0 delab
  let rhs ← withNaryArg 1 delab
  `($lhs ⊢ $rhs)

/-- `iexists fun x => H` as `iprop(∃ x, H)`; an eta-reduced `iexists J` is left as is. -/
@[app_delab iexists]
meta def delabIexists : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``iexists 2 && e.appArg!.isLambda)
  withAppArg <| withBindingBodyUnusedName fun x => do
    `(iprop(∃ $(⟨x⟩):ident, $(← delab)))

/-- `iforall fun x => H` as `iprop(∀ x, H)`; an eta-reduced `iforall J` is left as is. -/
@[app_delab iforall]
meta def delabIforall : Delab := do
  let e ← getExpr
  guard (e.isAppOfArity ``iforall 2 && e.appArg!.isLambda)
  withAppArg <| withBindingBodyUnusedName fun x => do
    `(iprop(∀ $(⟨x⟩):ident, $(← delab)))

end Aeneas.SepLogic
