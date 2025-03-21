import Spacetalk.Arith
import Spacetalk.DF

open Arith DF

namespace Compiler

structure MarkedDFG where
  dfg : DFG
  ret : Port

@[simp]
def sameVarInputIdx (dfg : DFG) (var : String) : Nat :=
  dfg.findIdx
    (λ node =>
      match node with
      | ⟨_, .input var' _⟩ => var' = var
      | _ => false
    )

-- Merge consumers of input nodes that map to the same variable
@[simp]
def mergeVarsAux (dfg : DFG) (node : Node) : DFG :=
  match node with
  | ⟨_, .input var newPorts⟩ =>
    let idx := sameVarInputIdx dfg var
    match dfg[idx]? with
    | some ⟨nid, .input var ports⟩ =>
      dfg.set idx ⟨nid, .input var (ports ++ newPorts)⟩
    | _ => dfg.concat node
  | _ => dfg.concat node

@[simp]
def mergeVars (g1 g2 : DFG) : DFG :=
  g2.foldl mergeVarsAux g1

@[simp]
def updateReturnAux (ret : Port) (newRet : Port) (node : Node) :=
  let replace (p : Port) := if p = ret then newRet else p
  {node with op :=
    match node.op with
    | .input var ports => .input var (ports.map replace)
    | .output => .output
    | .binOp op ports => .binOp op (ports.map replace)
  }

-- Update the "return" value of a graph to be the port of the new output node
@[simp]
def updateReturn (dfg : DFG) (ret : Port) (newRet : Port) : DFG :=
  dfg.map (updateReturnAux ret newRet)

@[simp]
def removeOutputNodes (dfg : DFG) : DFG :=
  dfg.filter Node.notOutput

@[simp]
def mergeTwo (g1 g2 : MarkedDFG) (newOutput : Nat)
  : DFG :=
  let dfg := mergeVars g1.dfg g2.dfg
  -- Update links to the original output nodes
  let dfg := updateReturn dfg g1.ret ⟨newOutput, 0⟩
  let dfg := updateReturn dfg g2.ret ⟨newOutput, 1⟩
  removeOutputNodes dfg

@[simp]
def compileAux (maxNid : Nat) : Exp → MarkedDFG × Nat
  | .var var =>
    let inpId := maxNid
    let outId := maxNid + 1
    let dfg := [⟨inpId, .input var [⟨outId, 0⟩]⟩, ⟨outId, .output⟩]
    (⟨dfg, ⟨outId, 0⟩⟩, maxNid + 2)
  | .plus e1 e2 =>
    let (e1, maxNid) := compileAux maxNid e1
    let (e2, maxNid) := compileAux maxNid e2
    let plusId := maxNid
    let outId := maxNid + 1
    let dfg := mergeTwo e1 e2 plusId
    let dfg := ⟨plusId, .binOp .plus [⟨outId, 0⟩]⟩ :: ⟨outId, .output⟩ :: dfg
    (⟨dfg, ⟨outId, 0⟩⟩, maxNid + 2)

@[simp]
def compile (e : Exp) : MarkedDFG :=
  (compileAux 0 e).fst

end Compiler
