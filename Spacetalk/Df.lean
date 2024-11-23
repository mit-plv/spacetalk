import Std.Data.DHashMap.Basic
import Mathlib.Data.Vector.Basic

-- No custom types, all types are 32-bit ints
-- Otherwise a lot of annoying type matching would have to happen
-- Some of which probably requires heavy dependent types
abbrev Ty := BitVec 32

open Mathlib

inductive BinOp
  | add
  | sub
  | eq
  | steer : (flavor : Ty) → BinOp

inductive Inp
  | const : Ty → Inp
  | port : Nat → Inp

abbrev Outputs := List (Nat × Nat)

inductive Node
  | enter : Outputs → Node
  | exit : Node
  | binop : BinOp → Inp → Inp → Outputs → Node
  | ctxEnter : (ctx : Nat) → (arg : Nat) → Node
  -- | ctxExit : (ctx : Nat) → (ret : Nat) → Outputs → Node

structure Ctx where
  numNodes : Nat
  nodes : Vector Node numNodes

structure Prog where
  numCtxs : Nat
  contexts : Vector Ctx numCtxs
  main : Nat
  inputs : List Nat
  outputs : List Nat

-- Semantics

def BinOp.eval (e1 e2 : Ty) : BinOp → Option Ty
  | .add => some (e1 + e2)
  | .sub => some (e1 - e2)
  | .eq => if e1 == e2 then some 1 else some 0
  | .steer flavor => if e1 == flavor then some e2 else none

structure CtxCall where
  ctx : Nat
  arg : Nat

abbrev CtxEnv :=
  Std.HashMap (Nat × Nat) (List Ty)

def CtxEnv.broadcast (env : CtxEnv) (v : Ty) (receivers : List (Nat × Nat)) : CtxEnv :=
  receivers.foldl
    (λ env receiver =>
      let q := (env.get? receiver).getD []
      env.insert receiver (q.concat v)
    ) env

def Port.fetch? (nid : Nat) (pid : Nat) (env : CtxEnv) : Option (Ty × CtxEnv) :=
  env.get? (nid, pid)
    >>= (λ l =>
      match l with
      | [] => none
      | hd :: tl => some (hd, env.insert (nid, pid) tl)
    )

def Inp.fetch? (nid : Nat) (env : CtxEnv) : Inp → Option (Ty × CtxEnv)
  | .const v => some (v, env)
  | .port pid => Port.fetch? nid pid env

def Node.fire? (cid : Nat) (nid : Nat) (env : CtxEnv) : Node → Option CtxEnv
  | .enter outputs => do
    let (v, env) ← Port.fetch? nid 0 env
    CtxEnv.broadcast env v outputs
  | .exit => none
  | .binop bop e1 e2 outputs => do
    let (e1, env) ← e1.fetch? nid env
    let (e2, env) ← e2.fetch? nid env
    match bop.eval e1 e2 with
    | some ret => CtxEnv.broadcast env ret outputs
    | none => env
  | .ctxEnter ctx arg => sorry
  -- | .ctxExit ctx ret outputs => sorry

def Ctx.step (context : Ctx) (env : CtxEnv) : Option (CtxEnv × Option CtxCall) :=

  sorry

namespace Example
  -- def add : Ctx := .ofList [
  --   (0, .enter .int), -- x
  --   (1, .enter .int), -- y
  --   (2, .exit .int), -- ret
  --   (3, .const 0), -- 0
  --   (4, .const 1), -- 1
  --   (5, .sub 0 4), -- x - 1
  --   (6, .eq 0 3), -- x == 0
  --   (7, .steerFalse 6 5), -- (x - 1) if !(x == 0)
  --   (8, .add 1 4), -- y + 1
  --   (9, .steerTrue 6 1), -- y if (x == 0)
  --   (10, .steerFalse 6 8), -- (y + 1) if !(x == 0)
  --   (11, .contextEnter 7 0 0), -- add x ← (x - 1) if !(x == 0)
  --   (12, .contextEnter 10 0 1), -- add y ← (y + 1) if !(x == 0)
  --   (13, .contextExit 9 2), -- ret ← y if (x == 0)
  -- ]

  -- def p : Prog := ⟨.ofList [(0, add)], 0, [(0, .int), (1, .int)], [(2, .int)]⟩
end Example
