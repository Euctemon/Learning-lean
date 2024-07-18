inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr := plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)


def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

#eval (eval sampleVal sampleExpr)

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
 | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
 | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
 | e => e

def anotherExpr : Expr := times (plus (const 1) (const 2)) (plus (const 5) (var 0))

#eval (fuse anotherExpr)

theorem simpConst_eq (v : Nat → Nat) : ∀ e : Expr, eval v (simpConst e) = eval v e := by
intro e
cases e with
| const a => rfl
| var a => rfl
| plus r s => cases r with
  | const r => cases s <;> rw [simpConst]; rfl
  | _ => rw [simpConst]
| times r s => cases r with
  | const r => cases s <;> rw [simpConst]; rfl
  | _ => rw [simpConst]

theorem fuse_eq (v : Nat → Nat) : ∀ e : Expr, eval v (fuse e) = eval v e := by
intro e
induction e with
| const a => rfl
| var a => rfl
| plus a b ha hb => simp [fuse,simpConst_eq,eval,ha, hb]
| times a b ha hb => simp [fuse,simpConst_eq,eval,ha, hb]
