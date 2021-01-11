Require Import String.
Inductive identif := a | b | c | d | e | f | g | h | i | n | s.

Inductive Value :=
| undefined : Value
| Number : nat -> Value
| Boolean : bool -> Value.

Inductive Exp :=
| evar : identif -> Exp
| estring : string -> Exp
| enum : nat -> Exp
| plus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp (**)
| mod : Exp -> Exp -> Exp
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
Notation "A %' B" := (mod A B) (at level 46).
Notation "A <' B" := (blessthan A B) (at level 53).
Notation "A <=' B" := (blesseqthan A B) (at level 53).
Notation "A >' B" := (bgreaterthan A B) (at level 53).
Notation "A >=' B" := (bgreatereqthan A B) (at level 53).
Notation "! A" := (not A) (at level 52).
Notation "A &&' B" := (and A B) (at level 60).
Notation "A ||' B" := (or A B) (at level 61).
Notation "A ==' B" := (beqto A B) (at level 62).
Notation "A != B" := (notbeqto A B) (at level 62).
(*Notation "A === B" := (eqValeqType A B) (at level 62).
Notation "A !== B" := (noteqValeqType A B) (at level 62).*)
Notation "' A '" := (estring A) (at level 62).

Coercion enum : nat >-> Exp.
Coercion evar : identif >-> Exp.

Compute (true +' 1).
Compute (true +' true).
Compute (true ==' 1).
Compute (' "str" ').
Compute (1 <' 2).

Inductive Statement :=
| declaration : identif -> Statement
| assign : identif -> Exp -> Statement
| sequence : Statement -> Statement -> Statement
| ifElse : Exp -> Statement -> Statement -> Statement
| ifThen : Exp -> Statement -> Statement
| While : Exp -> Statement -> Statement
| For : Statement -> Exp -> Statement -> Statement -> Statement.

Notation "'Let' A" := (declaration A) (at level 100).
Notation "A =' B" := (assign A B) (at level 101).
Notation "A ; B" := (sequence A B) (at level 102).
Notation "'If' ( A ) { B } 'Else' { C }" := (ifElse A B C) (at level 102).
Notation "'If' A 'Then' B " := (ifThen A B) (at level 102).
Notation "'while' ( A ) { B }" := (While A B) (at level 102).
Notation "'For' ( A ;; B ;; C ) { D }" := (For A B C D) (at level 102).



Scheme Equality for identif. 
 
Definition Env := identif -> nat.

Definition envA : Env :=
  fun var =>
  if (identif_eq_dec var a)
          then 1
  else if (identif_eq_dec var b)
          then 10
  else if (identif_eq_dec var c)
          then 15
  else if (identif_eq_dec var d)
          then 20
  else if (identif_eq_dec var e)
          then 4
  else 0.

Definition update (env : Env) (z : identif) (value : nat) : Env :=
  fun var =>
    if(identif_eq_dec var z)
      then value
    else (env var).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Reserved Notation "A =[ State ]=> N" (at level 60).
Inductive exp_eval : Exp -> Env -> nat -> Prop :=
| const : forall n sigma, enum n =[ sigma ]=> n  
| var : forall v sigma, evar v =[ sigma ]=> (sigma v)
| add : forall a1 a2 i1 i2 sigma result,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  result = i1 + i2 ->
  a1 +' a2 =[ sigma ]=> result
| timesEval : forall a1 a2 i1 i2 sigma result,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  result = i1 * i2 ->
  a1 *' a2 =[ sigma ]=> result
| div_not_0 : forall a1 a2 i1 i2 sigma result,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  result = Nat.div i1 i2 ->
  a1 /' a2 =[ sigma ]=> result
| div_0 : forall a1 a2 i1 sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> 0 ->
  a1 /' a2 =[ sigma ]=> 0
| mod_not_0 : forall a1 a2 i1 i2 sigma result,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  result = Nat.modulo i1 i2 ->
  a1 %' a2 =[ sigma ]=> result
| notEval : forall a1 i1 state,
  a1 =[ state ]=> i1 ->
  !a1 =[ state ]=> if(Nat.eqb i1 0) then 1 else 0
| mod_0 : forall a1 a2 i1 sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> 0 ->
  a1 %' a2 =[ sigma ]=> 0
| minusEval : forall a1 a2 i1 i2 sigma result,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  result = i1 - i2 ->
  a1 -' a2 =[ sigma ]=> result
| trueEval : forall state, true =[ state ]=> 1
| falseEval : forall state, false =[ state ]=> 0
| lessthanEval : forall a1 i1 a2 i2 state comp,
  a1 =[ state ]=> i1 ->
  a2 =[ state ]=> i2 ->
  comp = Nat.ltb i1 i2 ->
  a1 <' a2 =[ state ]=> if(comp) then 1 else 0
| lesseqthanEval : forall a1 i1 a2 i2 state,
  a1 =[ state ]=> i1 ->
  a2 =[ state ]=> i2 ->
  a1 <=' a2 =[ state ]=> if(Nat.leb i1 i2) then 1 else 0
| greaterthanEval : forall a1 i1 a2 i2 state,
  a1 =[ state ]=> i1 ->
  a2 =[ state ]=> i2 ->
  a1 >' a2 =[ state ]=> if(Nat.ltb i2 i1) then 1 else 0
| greatereqthan : forall a1 i1 a2 i2 state,
  a1 =[ state ]=> i1 ->
  a2 =[ state ]=> i2 ->
  a1 >=' a2 =[ state ]=> if (Nat.leb i2 i1) then 1 else 0
| eqtoEval : forall a1 a2 i1 i2 state comp,
  a1 =[ state ]=> i1 ->
  a2 =[ state ]=> i2 ->
  comp = Nat.eqb i1 i2 ->
  (a1 ==' a2) =[ state ]=> if (comp) then 1 else 0
| neqtoEval : forall a1 a2 i1 i2 state comp, 
  a1 =[ state ]=> i1 -> 
  a2 =[ state ]=> i2 ->
  comp = Nat.eqb i1 i2 ->
  (notbeqto a1 a2) =[ state ]=> if (comp) then 0 else 1
| andEval_true : forall a1 a2 state boolean,
  a1 =[ state ]=> 1 ->
  a2 =[ state ]=> boolean ->
  a1 &&' a2 =[ state ]=> boolean 
| andEval_false : forall a1 a2 state boolean,
  a1 =[ state ]=> 0 ->
  a1 &&' a2 =[ state ]=> boolean
| orEval_true : forall a1 a2 state,
  a1 =[ state ]=> 1 ->
  (a1 ||' a2) =[ state ]=> 1
| orEval_false : forall a1 a2 state boolean,
  a1 =[ state ]=> 0 ->
  a2 =[ state ]=> boolean ->
  (a1 ||' a2) =[ state ]=> boolean
where "a =[ s ]=> n" := (exp_eval a s n).



Reserved Notation " S ={ state }=> state'" (at level 60).
Inductive Stmt_eval : Statement -> Env -> Env -> Prop :=
| assign_eval : forall a i x state1 state2,
    a =[ state1 ]=> i ->
    state2 = (update state1 x i) ->
    (x =' a) ={ state1 }=> state2
| seq_eval : forall s1 s2 state state1 state2,
    s1 ={ state }=> state1 -> 
    s2 ={ state1 }=> state2 ->
    (s1 ; s2) ={ state }=> state2 
| if_true_eval : forall cond s1 s2 state state',
    cond =[ state ]=> 1 ->
    s1 ={ state }=> state'->
    ifElse cond s1 s2 ={ state }=> state'
| if_false_eval : forall cond s1 s2 state state',
    cond =[state]=> 0 ->
    s2 ={ state }=> state'->
    ifElse cond s1 s2 ={ state }=> state'  
| while_true : forall cond s1 state state',
    cond =[ state ]=> 1 ->
    s1 ={ state }=> state' ->
    While cond s1 ={ state }=> state'
| while_false : forall cond s1 state,
    cond =[ state ]=> 0 ->
    While cond s1 ={ state }=> state
where "s ={ state }=> state'" := (Stmt_eval s state state').

Require Import Omega.

Example e1 : 3 +' a *' ( 2 %' 2) =[ envA ]=> 3.
Proof.
  eapply add.
  eapply const.
  eapply timesEval.
  eapply var.
  eapply mod_not_0.
  eapply const.
  eapply const.
  eauto.
  eauto.
  omega.
Qed.

Example e2 : b +' (!((true ==' false))) =[ envA ]=> 11.
Proof.
  eapply add.
  eapply var.
  eapply notEval.
  eapply eqtoEval.
  eapply trueEval.
  eapply falseEval.
  simpl.
  eauto.
  simpl.
  reflexivity.
Qed.

Definition program :=
  a =' 2 +' (! false) ;

  If ( a ==' 2 ) { a =' 4 } Else { a =' 5 } ;
  
  while ( (a %' 2) ==' 1 ) { 
              a =' a +' 1 
                          }  
.

Definition stateFirst := fun (x : identif) => 0.

Example evalProgram : exists state, program ={ stateFirst }=> state /\ state a = 6.
Proof.
  eexists.
  split.
  unfold program.
  eapply seq_eval.
  eapply assign_eval.
  eapply add. 
  eapply const.
  eapply notEval.
  eapply falseEval.
  eauto.
  eauto.
  eapply seq_eval.  
  eapply if_false_eval.
  simpl.
  eapply eqtoEval.
Abort.
  
  




  














