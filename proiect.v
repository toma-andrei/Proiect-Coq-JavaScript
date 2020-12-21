Require Import String.
Inductive identif := a | b | c | d | e | f | g | h | i.

Inductive Value :=
| undefined : Value
| Number : nat -> Value
| Boolean : bool -> Value.

Definition Env : identif -> Value.

Inductive Exp :=
| evar : Value -> Exp
| estring : string -> Exp
| enum : nat -> Exp
| plus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp
| minus : Exp -> Exp -> Exp
| true : Exp
| false : Exp
| blessthan : Exp -> Exp -> Exp
| bgreaterthan : Exp -> Exp -> Exp
| blesseqthan : Exp -> Exp -> Exp
| bgreatereqthan : Exp -> Exp -> Exp
| beqto: Exp -> Exp -> Exp
| notbeqto : Exp -> Exp -> Exp
| eqValeqType : Exp -> Exp -> Exp
| noteqValeqType : Exp -> Exp -> Exp
| not : Exp -> Exp
| and : Exp -> Exp -> Exp
| or : Exp -> Exp -> Exp.

Notation "A +' B" := (plus A B) (at level 50).
Notation "A -' B" := (minus A B) (at level 50).
Notation "A *' B" := (times A B) (at level 46).
Notation "A /' B" := (div A B) (at level 46).
Notation "A <' B" := (blessthan A B) (at level 53).
Notation "A <=' B" := (blesseqthan A B) (at level 53).
Notation "A >' B" := (bgreaterthan A B) (at level 53).
Notation "A >=' B" := (bgreatereqthan A B) (at level 53).
Notation "! A" := (not A) (at level 52).
Notation "A &&' B" := (and A B) (at level 60).
Notation "A ||' B" := (or A B) (at level 61).
Notation "A == B" := (beqto A B) (at level 62).
Notation "A != B" := (notbeqto A B) (at level 62).
Notation "A === B" := (eqValeqType A B) (at level 62).
Notation "A !== B" := (noteqValeqType A B) (at level 62).
Notation "' A '" := (estring A) (at level 62).

Coercion enum : nat >-> Exp.

Compute (true +' 1).
Compute (true +' true).
Compute (true == 1).
Compute (' "str" ').

Inductive Statement :=
| declaration : identif -> Statement
| assign : identif -> Value -> Statement
| sequence : Statement -> Statement -> Statement
| ifElse : Exp -> Statement -> Statement -> Statement
| ifThen : Exp -> Statement -> Statement
| while : Exp -> Statement -> Statement
| For : Statement -> Exp -> Exp -> Statement -> Statement.

Notation "'var' A" := (declaration A) (at level 100).
Notation "'Let' A" := (declaration A) (at level 100).
Notation "'const' A" := (declaration A) (at level 100).
Notation "A =' B" := (assign A B) (at level 101).
Notation "A ; B" := (sequence A B) (at level 101).
Notation "'If' A { B } 'Else' { C }" := (ifElse A B C) (at level 102).
Notation "'If' A { B }" := (ifThen A B) (at level 90).











