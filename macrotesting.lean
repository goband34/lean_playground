import Lean
open Lean

/-
  A small macro example to generate the functions that in turn generate the round constant
  functions needed for AES key scheduling. There isn't much practical utility for this, but
  it was a fun little example that quite possibly can be improved but I don't know enough
  about macros for that
-/

syntax (name := gen_rcon) "rcondef" num : term

def test (x : Fin 10) : (x.1 < 10) :=
  let ⟨_, p⟩ := x
  p

@[macro gen_rcon] def genRconImpl : Macro
  | `(rcondef $n:num) => 
    (let n' : Nat := Syntax.toNat n
    match n' with
    | 10 | 8 | 7 => do
      let r ← go n' (n'-1)
      `(fun (y : Fin $n) => 
        let y := y.val
        $r)
    | _ => Macro.throwUnsupported)
  | _ => Macro.throwUnsupported
  where
    vals : Array UInt8 := #[0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]
    valsacc (m : Nat) (n : Nat) : UInt8 := vals[m-n]!
    go (x y : Nat) : MacroM (TSyntax `term) :=
    match x with
    | 0 =>
      let r : TSyntax numLitKind := Syntax.mkNumLit (toString (valsacc y 0))
      let res : MacroM (TSyntax `term) := `(match y with | _ => $r)
      res
    | x+1 => do
      let r : TSyntax numLitKind := Syntax.mkNumLit (toString (valsacc y x))
      let res : MacroM (TSyntax `term) := `(match y with | 0 => $r | y+1 => $(← go x y))
      res