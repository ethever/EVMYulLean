import Std.Data.HashMap
import EvmYul.Yul.Ast
import EvmYul.UInt256

namespace EvmYul

/-- Simple Yul state as a mapping from identifiers to values. -/
abbrev YState := Std.HashMap Identifier UInt256

namespace YState

/-- Lookup variable value. Defaults to 0 if not present. -/
@[simp]
def findD (s : YState) (x : Identifier) : UInt256 :=
  s.findD x ⟨0⟩

/-- Update variable. -/
def insert (s : YState) (x : Identifier) (v : UInt256) : YState :=
  s.insert x v

end YState

/-- A very small EVM used for the compiler correctness proof. -/
namespace MiniEVM

/-- Memory modelled as a map from addresses to values. -/
structure State where
  stack : List UInt256 := []
  mem   : Std.HashMap UInt256 UInt256 := {}
  deriving Inhabited

inductive Instr where
  | push (v : UInt256)
  | add
  | mload  (addr : UInt256)
  | mstore (addr : UInt256)
  deriving Inhabited

/-- Execute one instruction. Returns none on stack underflow. -/
def step : Instr → State → Option State
  | .push v, s => some { s with stack := v :: s.stack }
  | .add, s =>
      match s.stack with
      | v₁ :: v₂ :: stk => some { s with stack := (v₁ + v₂) :: stk }
      | _ => none
  | .mload a, s =>
      let v := s.mem.findD a ⟨0⟩
      some { s with stack := v :: s.stack }
  | .mstore a, s =>
      match s.stack with
      | v :: stk => some { stack := stk, mem := s.mem.insert a v }
      | _ => none

/-- Execute a list of instructions. -/
def run (code : List Instr) (st : State) : Option State :=
  code.foldlM (fun s i => step i s) st

lemma run_append (c₁ c₂ : List Instr) (s : State) :
    run (c₁ ++ c₂) s =
      (do
        let s' ← run c₁ s
        run c₂ s') := by
  induction c₁ generalizing s with
  | nil =>
    simp [run]
  | cons i is ih =>
    simp [run, List.foldlM, ih, bind_assoc]

end MiniEVM

open MiniEVM

/--
Evaluation of expressions in our small fragment of Yul consisting of literals,
variables and `add` primitive calls.
-/
def evalExpr (σ : YState) : Yul.Ast.Expr → Option UInt256
  | .Lit v => some v
  | .Var x => some (σ.findD x)
  | .PrimCall (.StopArith .ADD) [e₁, e₂] => do
      let v₁ ← evalExpr σ e₁
      let v₂ ← evalExpr σ e₂
      pure (v₁ + v₂)
  | _ => none

/-- Execution of a single assignment statement. -/
def execStmt (σ : YState) : Yul.Ast.Stmt → Option YState
  | .Assign x e => do
      let v ← evalExpr σ e
      pure (σ.insert x v)
  | _ => none

/-- Compile expressions of the fragment to mini EVM instructions. -/
def compileExpr (layout : Std.HashMap Identifier UInt256) : Yul.Ast.Expr → List Instr
  | .Lit v => [.push v]
  | .Var x => [.mload (layout.findD x ⟨0⟩)]
  | .PrimCall (.StopArith .ADD) [e₁, e₂] =>
      compileExpr layout e₁ ++ compileExpr layout e₂ ++ [.add]
  | _ => []

/-- Compile an assignment statement. -/
def compileStmt (layout : Std.HashMap Identifier UInt256) : Yul.Ast.Stmt → List Instr
  | .Assign x e =>
      compileExpr layout e ++ [.mstore (layout.findD x ⟨0⟩)]
  | _ => []

/-- Sequential execution of a list of statements. -/
def execProgram (σ : YState) : List Yul.Ast.Stmt → Option YState
  | []      => some σ
  | s :: ss => do
      let σ' ← execStmt σ s
      execProgram σ' ss

/-- Compile a list of statements into MiniEVM instructions. -/
def compileProgram (layout : Std.HashMap Identifier UInt256)
    : List Yul.Ast.Stmt → List Instr
  | []      => []
  | s :: ss => compileStmt layout s ++ compileProgram layout ss

/--
Convert a Yul state into a MiniEVM memory using a variable layout.
-/
def memOf (layout : Std.HashMap Identifier UInt256) (σ : YState) : Std.HashMap UInt256 UInt256 :=
  σ.fold (init := {}) (fun m k v => m.insert (layout.findD k ⟨0⟩) v)

lemma compileStmt_correct
    (layout : Std.HashMap Identifier UInt256)
    (σ : YState) (x : Identifier) (e : Yul.Ast.Expr)
    (stk : List UInt256) (v : UInt256)
    (h : evalExpr σ e = some v) :
    MiniEVM.run (compileStmt layout (.Assign x e)) {stack := stk, mem := memOf layout σ} =
      some {stack := stk, mem := (memOf layout σ).insert (layout.findD x ⟨0⟩) v} := by
  have hv := compileExpr_correct layout σ e v stk h
  simp [compileStmt, memOf] at hv
  simpa [compileStmt, memOf] using hv

/-- Correctness of expression compilation. -/
lemma compileExpr_correct
    (layout : Std.HashMap Identifier UInt256)
    (σ : YState) (e : Yul.Ast.Expr) (v : UInt256) (stk : List UInt256)
    (h : evalExpr σ e = some v) :
    MiniEVM.run (compileExpr layout e) {stack := stk, mem := memOf layout σ} =
      some {stack := v :: stk, mem := memOf layout σ} := by
  induction e generalizing σ stk v with
  | Lit v' =>
      simp [compileExpr, evalExpr] at h
      simp [compileExpr, MiniEVM.run, MiniEVM.step, h]
  | Var x =>
      simp [compileExpr, evalExpr] at h
      simp [compileExpr, MiniEVM.run, MiniEVM.step, memOf, YState.findD, h]
  | .PrimCall (.StopArith .ADD) [e₁, e₂] ih₁ ih₂ =>
      simp [compileExpr, evalExpr] at h
      cases h₁ : evalExpr σ e₁ with
      | none => simp [h₁] at h
      | some v₁ =>
          cases h₂ : evalExpr σ e₂ with
          | none => simp [h₁, h₂] at h
          | some v₂ =>
              simp [h₁, h₂] at h; cases h
              have ih₁' := ih₁ _ _ _ h₁
              have ih₂' := ih₂ _ _ _ h₂
              simp [compileExpr, MiniEVM.run, run_append, ih₁', ih₂']
  | PrimCall _ _ _ _ => cases h
  | _ => cases h

end EvmYul

