(*Mapping helpers*)
From Coq Require Import FSets.FMapWeakList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Structures.DecidableTypeEx.
From Coq Require Import Structures.OrderedTypeEx.
Module Import SMAP := FMapWeakList.Make (String_as_OT).

Module Import MapHelper := WProperties_fun String_as_OT SMAP. 

From Coq Require Import String.
From ExtLib Require Import Monads.
From ExtLib Require Import OptionMonad.
Import MonadNotation.


(*
  Hello, to run this demo you will need to have installed Coq and the library 
  ExtLib

  The goal is to introduce in a minimal workflow modeling language the concept
  of effects to track task dependency. The concept of task dependency we are 
  tackling is also simple:
    we say that a task A is dependent of another task B if we must execute B 
    before we can execute A.

  The language we are considering uses Actors as the executors and its methods
  as actions. The goal is to enforce such dependencies via a type&effect system.

  This demo serves as a base to then build more interesting restrictions in more 
  complex languages.

  The initial language we are working on is one without concurrency, just actors 
  that have methods that call eachother.
  The syntax is as following:
*)

Open Scope string.

Module SimpleSyntax.
  Definition t := unit.

  Definition ident := string.

  Inductive expression : Type := 
    | call : ident -> ident -> expression
    | wait : expression
    | done : expression.

  Inductive method : Type :=
    | def : ident -> t -> expression -> method. 

  Inductive actor : Type := 
    | class : SMAP.t method -> expression -> actor.

  Definition program := SMAP.t actor.

  (* helper function for later *)
  Definition getExpressionById (c m : ident) (p : program) : option expression :=
    (
      theActor <- (SMAP.find c p);;
      theMethod <- (match theActor with 
      | class ms _ => (SMAP.find m ms)
      end) ;;
      (match theMethod with 
      | def _ _ exp => Some exp
      end)
    )%monad.

End SimpleSyntax.
(*
  So we can just write actors that call eachother conceiding execution
  to the fellow actor.

  for example:
  LeadSinger {                  FirstGuitar {
    sing () {                     solo () {
      FirstGuitar.solo()            LeadSinger.sing()
    }                             }
    start := sing()               start := wait.
  }                             }

  The effect should be obvious, just an infinite jump from 
  singing to sick guitar solos.
  LeadSinger.sing -> FirstGuitar -> LeadSinger.sing -> ...

  But that isn't a workflow, there is no end:

  LeadSinger {                  FirstGuitar {
    sing () {                     solo () {
      FirstGuitar.solo()            LeadSinger.outro()
    }                             }
    outro () {                    start := wait.
      done                      }
    }
    start := sing()               
  }

  now it looks more like:

  LeadSinger.sing() -> FirstGuitar.solo -> LeadSinger.outro().

  The type system should check that there is a done somewhere down 
  the line.

  Let's first define the effect system for this toy language
*)
Module SimpleEffects.
  Include SimpleSyntax.

  Inductive effect : Type := 
    | ϵ
    | C (m: ident) (*(c : ident)*)
    | Sync (e1 e2 : effect) 
  .
  Notation "e1 '|->' e2" := (Sync e1 e2) (at level 100). 

  (* has to be bounded if we don't reach a "done" *)
  Fixpoint getEffect (bound : nat) (e: expression) (p: program) : option effect :=
    match bound with 
    | 0 => None 
    | S n => match e with 
      | call a m => (exp <- (getExpressionById a m p) ;; 
                    next <- (getEffect n exp p) ;;
                    Some ((C m) |-> next))%monad
      | wait => Some ϵ
      | done => Some ϵ
      end
    end.
End SimpleEffects.

(* 
  The effects we've just defined allow us to state that nothing happens (ϵ), 
  that an activity is executed (C) and that something happens after somthing 
  else (Sync)

  Let's write the first example in our syntax and extract its effect.
*)

Module FirstExample.
  Include SimpleEffects.

  Definition emptyActor := SMAP.empty method.
  Definition emptyProgram := SMAP.empty actor.


  Definition sing := def "sing" tt (call "FirstGuitar" "solo" ).
  Definition solo := def "solo" tt (call "LeadSinger" "outro" ).
  Definition outro := def "outro" tt (done).
  Definition start := (call "LeadSinger" "sing").

  Definition LeadSinger : actor := 
    class (SMAP.add "outro" outro (SMAP.add "sing" sing emptyActor)) start.
  Definition FirstGuitar : actor := 
    class (SMAP.add "solo" solo emptyActor) (wait).

  Definition exampleProgram :=
    SMAP.add "FirstGuitar" FirstGuitar (SMAP.add "LeadSinger" LeadSinger emptyProgram).

  (* we get the effect of calling the start expression! *)
  Compute getEffect 10 start exampleProgram.
End FirstExample.
(*
And we get:
= Some (C "LeadSinger" "sing" --> (C "FirstGuitar" "solo" --> (C "LeadSinger" "outro" --> ϵ)))
: option effect

*)


(* 
  Before introducing concurrency let's check how can we use modelchecking 
  in this scenario.
  Let's say we want to have a condition "don't play the outro before a
  sick guitar solo" 
  We can tag "outro" with the dependency "solo"
...
    outro () after solo {
      done
    }
...

  From the quick model we just saw we can think, oh let's model check 
  and in such a simple model is quite straight forward. In this case 
  it would give us a thumbsup, no counterexamples, and if we mess up 
  the order it would show a counter example.

  The scope of this research is to bigger workflows with concurrency 
  involved, where the cause of the counterexample might not be so 
  clear. An good treat of using a type and effect system is that we
  can model check backwards for dependencies in method calls and point
  to the call that is not allowed. 
  This is also benefitial in the evolution of the workflow. We keep
  the type inference tree as a fixed and upon a change in a term we 
  rebuild the affected branches. So no breaking changes can be 
  introduced.

  The main difference with performing a batch of modelchecking props
  in the continuos integration pipeline is that errors are signaled to
  the programer on the run, pointing in the direction of the allowed
  solution.
*)

(*
  Before implementing a type&effect system that checks for dependencies, we 
  need to give meaning to our effects. The semantics of effects come from the 
  dependencies that they conform. 

  Due that we are only checking for existence of certain activities, our 
  property language is just "no constraint", or "this task must be executed".
  Later one we can add complexity by saying "this 2 task" or "n tasks", between
  more interesting properties.

  So let's write a relation between effects and the dependencies that they 
  conform:
*)


Module SimplyModel.
  Include SimpleEffects.

  Definition dependency := option ident. (* so far is only the one we want to be
                                           executed earlier *)

  Inductive models : effect -> dependency -> Prop := 
    | FoundIt : forall d,
      models (C d) (Some d)
    | Next : forall d e1 e2,
      models e1 d \/ models e2 d ->
      models (Sync e1 e2) d 
    | NoDep: forall e,
      models (e) None
  .
  Notation "m |= d" := (models m d) (at level 10).
  
  (* 
    The structure is pretty much a list and we could have defined
    "models" as a List.In of the list, but we are keeping the 
    effects to build up to something more expressive. 
    e.g.
    Definition traces := list ident.
  *)
End SimplyModel.


(* 
  Now we can assert if the effect of an expression is good enough to go to a 
  task dependent task.
  So let's write a simple type&effect system to see how this would all come 
  together.
*)

(* no typing context everything is unit *)
(* we only have an effect context *)

(* helper to define the typesystem *)
Definition all_true {A: Type} (m: SMAP.t A) (acceptor: A -> Prop) : Prop :=
  fold (fun _ x => fun y => and x y) (map (acceptor) m) True.

(* usefull tactics *)

Ltac split_all :=
  repeat match goal with
        | [ |- _ /\ _ ] => split
        end.
Ltac open_block :=  constructor ; unfold all_true; rewrite fold_1; simpl; 
                    split_all; auto.


(* Initial implementation *)
Module SimplyTyped.
  Include SimplyModel.
  Definition context := effect.

  (* hardcoded for example *)
  Definition dependencyOf (c m: ident) : dependency := 
    match c, m with 
    | "LeadSinger", "outro" => Some "solo"
    | _ , _ => None
    end.
  
  Inductive welltyped_expression : context -> expression -> Prop :=
    | T_Call : forall eff c m, 
      eff |= (dependencyOf c m) ->
      welltyped_expression eff (call c m)
    | T_Wait : forall eff,
      welltyped_expression eff wait
    | T_Done : forall eff,
      welltyped_expression eff done
  .

  Inductive welltyped_method : context -> method -> Prop :=
    | T_Method : forall id e t eff,
      welltyped_expression (Sync eff (C id)) e ->
      welltyped_method eff (def id t e)
  .

  Inductive welltyped_actor : context -> actor -> Prop :=
    | T_Actor : forall ms start,
      all_true ms (welltyped_method ϵ) ->
      welltyped_actor ϵ (class ms start)
  .

  Inductive welltyped_program : context -> program -> Prop := 
    | T_Program (p: program) : 
      all_true p (welltyped_actor ϵ) ->
      welltyped_program ϵ p
  .

  Import FirstExample.

  Lemma easyTyped:  welltyped_program ϵ exampleProgram.
  Proof.
    open_block; open_block; constructor; constructor;
    constructor.
    - right. constructor.
    - left. constructor. 
  Qed.

  Print easyTyped.

End SimplyTyped.

(*
  SymplyTyped is a simple scenario for the dependency being complied at the 
  previous task. But we want to catch dependencies that happend even sooner.
  Let's imagine that the guitarist what's to implement a riff after its 
  solo and then call the outro.
  We get a new program like:
*)
Module SecondExample.
  Include FirstExample.
  Definition solo' := def "solo" tt (call "FirstGuitar" "riff" ).
  Definition riff := def "riff" tt (call "LeadSinger" "outro" ).


  Definition FirstGuitar' : actor := 
    class (SMAP.add "riff" riff (SMAP.add "solo" solo' emptyActor)) (wait).

  Definition exampleProgram' :=
    SMAP.add "FirstGuitar" FirstGuitar' (SMAP.add "LeadSinger" LeadSinger emptyProgram).

  (* 
    If we try to type check this program we get stuck:
  *)
  Module Import ST := SimplyTyped.
  Example wontPass : ST.welltyped_program ϵ exampleProgram'.
    Proof. open_block; open_block.
    - constructor. constructor. constructor. right.
      simpl. Abort. 
End SecondExample.

(*
  But we know the "solo" is always executed before the "riff", so the "outro" 
  will still come after the "solo".
  To let our type&effect system know this we need to go a bit deeper.
*)


From Coq Require Import Lists.List.
Module DeeperDependencies.
  Include SimplyModel.
  Definition context := effect.
  
  (* hardcoded for example but the implementation is straightforward TODO *)
  Definition getCallsTo (i: ident): list (ident * expression) :=
    match i with 
    | "riff" => ("solo", (call "FirstGuitar" "riff" )) :: nil
    | _ => nil 
    end.
  
  (* hardcoded for example *)
  Definition dependencyOf (c m: ident) : dependency := 
    match c, m with 
    | "LeadSinger", "outro" => Some "solo"
    | _ , _ => None
    end.
  
  Inductive welltyped_expression : context -> expression -> Prop :=
    | T_Call : forall eff c m, 
      eff |= (dependencyOf c m) ->
      welltyped_expression eff (call c m)
    | T_Call2 : forall eff thisMethod c m exp caller, (* one step deeper *) 
      List.In (caller, exp) (getCallsTo thisMethod) ->
      (* We check that for every caller we can comply the dependency *)
      (Sync (C caller) (Sync eff (C thisMethod))) |= (dependencyOf c m) -> 
      welltyped_expression (Sync eff (C thisMethod)) (call c m)
    | T_Wait : forall eff,
      welltyped_expression eff wait
    | T_Done : forall eff,
      welltyped_expression eff done
  .

  Inductive welltyped_method : context -> method -> Prop :=
    | T_Method : forall id e t eff,
      welltyped_expression (Sync eff (C id)) e ->
      welltyped_method eff (def id t e)
  .

  Inductive welltyped_actor : context -> actor -> Prop :=
    | T_Actor : forall ms start,
      all_true ms (welltyped_method ϵ) ->
      welltyped_actor ϵ (class ms start)
  .

  Inductive welltyped_program : context -> program -> Prop := 
    | T_Program (p: program) : 
      all_true p (welltyped_actor ϵ) ->
      welltyped_program ϵ p
  .

  Import SecondExample.
  (* In this proof we can see how we can go one call deeper looking for the called dependency *)
  Lemma deeperTyped:  welltyped_program ϵ exampleProgram'.
  Proof.
    open_block; open_block; constructor.
    - eapply T_Call2. (* Go one level deep *)
      + unfold getCallsTo. simpl. left. trivial.
      + constructor. left. unfold dependencyOf. constructor.
    - constructor. constructor. left. constructor.
    - constructor.
    - constructor. constructor. left. constructor.
  Qed.
End DeeperDependencies.



(*
  And now let's add concurrency.

  Let's say that during the riff the Singer want's to do a Chorus:

    LeadSinger {                  FirstGuitar {
      sing () {                     solo () {
        FirstGuitar.solo()            LeadSinger.chorus() & FirstGuitar.riff()
      }                             }
      outro () {                    riff () {
        done                          FirstGuitar.outro()
      }                             }
      chorus () {
        wait
      }
      start := sing()               
    }


  So we need to extend our syntax expressions to admit the & for parallel execution,
  and our effect system to model permutations.
 
*)

Module ConcurrentSyntax.
  Definition t := unit.

  Definition ident := string.

  Inductive expression : Type := 
    | call : ident -> ident -> expression
    | callAnd : ident -> ident -> expression -> expression
    | wait : expression
    | done : expression.

  Inductive method : Type :=
    | def : ident -> t -> expression -> method. 

  Inductive actor : Type := 
    | class : SMAP.t method -> expression -> actor.

  Definition program := SMAP.t actor.


  Definition getExpressionById (c m : ident) (p : program) : option expression :=
    (
      theActor <- (SMAP.find c p);;
      theMethod <- (match theActor with 
      | class ms _ => (SMAP.find m ms)
      end) ;;
      (match theMethod with 
      | def _ _ exp => Some exp
      end)
    )%monad.

  (*
    We implement the helpers we need to extract part of the program during 
    type check
  *)
  Fixpoint exp_isCallTo (i: ident) (e: expression) : option (expression) :=
    match e with 
    | call _ i' => if (i=?i') then Some (e) else None
    | callAnd _ i' e' => if (i=?i') then Some (e) else exp_isCallTo i e' (* we lose the left side of the expression! *)
    | _ => None
    end.

  Definition optionToList {A} (a: option A) : list A :=
    match a with 
    | Some x => x :: nil
    | None => nil
    end. 

  Definition meth_isCallTo (i: ident) (m: method) : option (ident * expression) :=
    match m with 
    | def this t e => (x <- exp_isCallTo i e ;;
                      Some (this, e))%monad
    end.

  Definition act_getCallsTo (i: ident) (a: actor) : list (ident * expression) :=
    match a with 
    | class ms exp =>  
      (map (fun x => ("start", x)) (optionToList (exp_isCallTo i exp))) ++
      flat_map optionToList (
        (map (snd) (elements (SMAP.map (meth_isCallTo i) ms)))
      )
    end.

  Fixpoint prog_getCallsTo (i: ident) (p: list (actor)) : list (ident * expression) :=
    match p with 
    | nil => nil
    | ac :: acs => act_getCallsTo (i: ident) (ac: actor) ++ prog_getCallsTo i acs
    end.

  Definition classesOf (p: program) : list actor := map snd (elements p).

End ConcurrentSyntax.

(*
  And now we can write the new workflow with the new syntax
*)

Module ConcurrentExample.
  Include ConcurrentSyntax.


  Definition emptyActor := SMAP.empty method.
  Definition emptyProgram := SMAP.empty actor.


  Definition sing := def "sing" tt (call "FirstGuitar" "solo" ).
  Definition solo := def "solo" tt (callAnd "FirstGuitar" "riff" (call "LeadSinger" "chorus")).
  Definition chorus := def "chorus" tt (wait).
  Definition riff := def "riff" tt (call "LeadSinger" "outro" ).
  Definition outro := def "outro" tt (done).

  Definition LeadSinger : actor := 
    class (SMAP.add "chorus" chorus (SMAP.add "outro" outro (SMAP.add "sing" sing emptyActor))) (call "LeadSinger" "sing").
  Definition FirstGuitar : actor := 
    class (SMAP.add "riff" riff (SMAP.add "solo" solo emptyActor)) (wait).

  Definition exampleProgram :=
    SMAP.add "FirstGuitar" FirstGuitar (SMAP.add "LeadSinger" LeadSinger emptyProgram).

  Compute prog_getCallsTo "solo" (classesOf exampleProgram).
  Compute prog_getCallsTo "riff" (classesOf exampleProgram).
  Compute prog_getCallsTo "chorus" (classesOf exampleProgram).
  Example riffAndChorusAllCalledTogether : prog_getCallsTo "riff" (classesOf exampleProgram) = prog_getCallsTo "chorus" (classesOf exampleProgram).
    Proof. reflexivity. Qed.

End ConcurrentExample.

(*
  The effects should now model also the posibility of async tasks finishing 
  in different orders.
*)

Module ConcurrentEffects.
  Include ConcurrentSyntax.

  Inductive effect : Type := 
    | ϵ
    | C (m: ident) (*(c : ident)*)
    | Sync (e1 e2 : effect) 
    | Async (e1 e2 : effect)
  .
  Notation "e1 '|->' e2" := (Sync e1 e2) (right associativity, at level 51). 
  Notation "e1 ';' e2 " := (Async e1 e2) (at level 100).

  Definition exampleEffect := C "primero" |-> C "segundo" |-> ( C "segundo'" ; C "segundo''" ) |-> C "tercero".
  (* 
    This effect should model two different traces:
      primero -> segundo -> segundo' -> segundo'' -> tercero 
      primero -> segundo -> segundo'' -> segundo' -> tercero
    But we still don't have semantics (we need a Modeling Module)
  *) 

  Fixpoint getExpEff (bound: nat) (e: expression) : effect :=
    match bound with
    | 0 => ϵ
    | S n => match e with 
      | call a m => C m 
      | callAnd a m e' => (Async (C m) (getExpEff n e'))
      | wait => ϵ
      | done => ϵ
      end
    end.

  (* has to be bounded if we don't reach a "done" *)
  Fixpoint getEffect (bound : nat) (e: expression) (p: program) : option effect :=
    match bound with 
    | 0 => None 
    | S n => match e with 
      | call a m => (exp <- (getExpressionById a m p) ;; 
                    next <- (getEffect n exp p) ;;
                    Some ((C m) |-> next))%monad
      | callAnd a m e => (exp <- (getExpressionById a m p) ;; 
                          next <- (getEffect n exp p) ;;
                          next' <- (getEffect n e p) ;;
                          Some ((Async (C m) ((getExpEff 10 e))) |-> next))%monad
      | wait => Some ϵ
      | done => Some ϵ
      end
    end.

  (*
    So let's check the effect we get from our concurrent example
  *)
  Import ConcurrentExample.
  Compute getEffect (100) (call "LeadSinger" "sing") exampleProgram.
  (*
    = Some (C "sing" --> (C "solo" --> ((C "riff"; C "chorus") --> (C "outro" --> ϵ))))
    : option effect
  *)
End ConcurrentEffects.

(* 
  Now for the new effect to actually mean anything we need to give it semantics by defining 
  proper Modeling rules 
*)

Module ConcurrentModel.
  Include ConcurrentEffects.


  Definition dependency := option ident. (* so far is only the one we want to be executed earlier *)

  Inductive models : effect -> dependency -> Prop := 
    | FoundIt : forall d,
      models (C d) (Some d)
    | Next : forall d e1 e2,
      models e1 d \/ models e2 d ->
      models (Sync e1 e2) d
    | Permutation : forall d e1 e2,
      models e1 d /\ models e2 d -> 
      models (Async e1 e2) d
    | NoDep: forall e,
      models (e) None
  .
  Notation "m |= d" := (models m d) (at level 10).

End ConcurrentModel.

(* Now let's check how everything comes together in the type&effect system *)


Module ConcurrentTyped.
  Include ConcurrentModel.
  (* Now we need to carry around the static data of the program *)
  Definition context := (effect * program)%type.
  
  (* hardcoded for example *)
  Definition dependencyOf (c m: ident) : dependency := 
    match c, m with 
    | "LeadSinger", "outro" => Some "solo"
    | _ , _ => None
    end.
  

  (* 
    Here comes' the tricky part
    we can search back for previous calls that satisfy the dependecy,
    We have T_Call as base case: the current effect satisfies the dependency of the expression I want to execute
    And an recursive case: going back to every caller of the current executing method, checking that
                           for every path the dependency is satisfied.
  *)
  Inductive welltyped_expression : context -> expression -> Prop :=
    | T_Call : forall eff p c m, 
      eff |= (dependencyOf c m) ->
      welltyped_expression (eff, p) (call c m)
    | T_Call2 : forall eff p thisMethod c m exp caller, 
      List.In (caller, exp) (prog_getCallsTo thisMethod (classesOf p)) ->
      (* (Sync (C caller) (Sync eff (C thisMethod))) |= (dependencyOf c m) ->   *)
      (* Change to allow for arbitraty calls *)
      welltyped_expression (C caller |-> C thisMethod |-> eff, p) (call c m) ->
      (* welltyped_expression (Sync (C caller) (Sync eff (C thisMethod)), p) exp -> *)
      welltyped_expression (C thisMethod |-> eff, p) (call c m)
    | T_CallAsync : forall eff p eff1 c m,
      eff |= (dependencyOf c m) /\ eff1 |= (dependencyOf c m) -> (* Both must comply *)
      welltyped_expression (Async eff eff1, p) (call c m)
    | T_CallAnd : forall eff p c m e, 
      eff |= (dependencyOf c m) ->
      welltyped_expression (Sync eff (Async (C m) ϵ), p) e -> 
      welltyped_expression (eff, p) (callAnd c m e)
    | T_Wait : forall eff p,
      welltyped_expression (eff, p) wait
    | T_Done : forall ctx,
      welltyped_expression ctx done
  .

  Inductive welltyped_method : context -> method -> Prop :=
    | T_Method : forall id e t p,
      welltyped_expression ((C id) |-> ϵ, p) e ->
      welltyped_method (ϵ, p) (def id t e) (* no trailing effects on start of an activity! *)
  .

  Inductive welltyped_actor : context -> actor -> Prop :=
    | T_Actor : forall p ms start,
      all_true ms (welltyped_method (ϵ, p)) ->
      welltyped_actor (ϵ,p) (class ms start)
  .

  Inductive welltyped_program : context -> program -> Prop := 
    | T_Program (p: program) : 
      all_true p (welltyped_actor (ϵ, p)) ->
      welltyped_program (ϵ, p) p
  .

  Import ConcurrentExample.

  Print exampleProgram.
  Compute prog_getCallsTo "riff" (classesOf exampleProgram).
  (* In this proof we can see how we can go one call deeper looking for the called dependency *)
  Lemma concurrentTyped:  welltyped_program (ϵ, exampleProgram) exampleProgram.
  Proof.
    open_block; open_block; constructor.
    - (* call to outro *)
      eapply T_Call2. (* we use the recursive case to go back *)
      + simpl. auto.
      + constructor. constructor. left. constructor.  
    - do 5 constructor. left. constructor.  
    - do 5 constructor.
    - do 5 constructor.
    - do 4 constructor.
     (* the rest are all by default *) 
  Qed.
    
End ConcurrentTyped.
(* 
  But it's pretty much the same, because riff is called by solo and then solo is always 
  before outro. So let's break the workflow:
  
  LeadSinger {                  FirstGuitar {
    sing () {                     solo () {
      FirstGuitar.solo()            LeadSinger.chorus() 
      & LeadSinger.chorus()
    }                             }
    outro () {                    riff () {
      done                          done
    }                             }
    chorus () {
      FirstGuitar.outro
    }
    start := sing()               
  }

  Now the outro being played after the solo depends on the order of execution of the concurrent threads.
*)

Module BreakingExample.
  Include ConcurrentSyntax.


  Definition emptyActor := SMAP.empty method.
  Definition emptyProgram := SMAP.empty actor.


  Definition sing := def "sing" tt (callAnd "FirstGuitar" "solo" (call "LeadSinger" "chorus") ).
  Definition solo := def "solo" tt (call "FirstGuitar" "riff").
  Definition chorus := def "chorus" tt (call "LeadSinger" "outro").
  Definition riff := def "riff" tt (done).
  Definition outro := def "outro" tt (done).

  Definition LeadSinger : actor := 
    class (SMAP.add "chorus" chorus (SMAP.add "outro" outro (SMAP.add "sing" sing emptyActor))) (call "LeadSinger" "sing").
  Definition FirstGuitar : actor := 
    class (SMAP.add "riff" riff (SMAP.add "solo" solo emptyActor)) (wait).

  Definition exampleProgram :=
    SMAP.add "FirstGuitar" FirstGuitar (SMAP.add "LeadSinger" LeadSinger emptyProgram).

  Definition getCallsTo (i: ident): list (ident * expression) :=
    match i with 
    | "riff" => ("solo", (call "FirstGuitar" "riff" )) :: nil
    | "chorus" => ("sing", (callAnd "FirstGuitar" "solo" (call "LeadSinger" "chorus") )) :: nil
    | "solo" => ("sing", (callAnd "FirstGuitar" "solo" (call "LeadSinger" "chorus") )) :: nil
    | _ => nil 
    end.
End BreakingExample.

Module CheckBreakingExample.
  Import ConcurrentTyped.
  Include BreakingExample.

  Lemma wontPass:  welltyped_program (ϵ, exampleProgram) exampleProgram.
  Proof.
    open_block; open_block; constructor.
    - constructor.
    - constructor. constructor. left. constructor.
    - (* The call to outro *)
      eapply T_Call2.
      + simpl. left. trivial.
      + eapply T_Call2.
        * simpl. auto.
        * eapply T_Call2.
          ** simpl. Abort.  (* Nobody calls "start" so we get False and it's impossible to proof! *)  

End CheckBreakingExample.


(* 
  An usual feature of a workflow model is synchronisity. We would like to start 
  a task, perform other steps, await for the task (sync) and continue the flow.
  To maintain the language declarative and simple we can generalize the feature
  with a sequencing statement and an await command, so instead of writing:
    FirstGuitar.solo() & LeadSinger.chorus()
  we can write :
    FirstGuitar.solo(); do stuff; await; LeadSinger.chorus()

  Where the await command awaits for all the running processes.
*)


Module ImperativeSyntax.

  Definition ident := string.

  Definition t := unit.

  Inductive expression : Type := 
    | call : ident -> ident -> expression
    | callAnd : ident -> ident -> expression -> expression
    | wait : expression
    | done : expression.

  (* we introduce a higher level for statements *)
  Inductive statement : Type :=
    | Exp : expression -> statement
    | Seq : expression -> statement -> statement (* do smth and continue execution *).


  Inductive method : Type :=
    | def : ident -> t -> statement -> method. 

  Inductive actor : Type := 
    | class : SMAP.t method -> statement -> actor.

  Definition program := SMAP.t actor.


  Definition getStmtById (c m : ident) (p : program) : option statement :=
    (
      theActor <- (SMAP.find c p);;
      theMethod <- (match theActor with 
      | class ms _ => (SMAP.find m ms)
      end) ;;
      (match theMethod with 
      | def _ _ exp => Some exp
      end)
    )%monad. 

  (*
    We implement the helpers we need to extract part of the program during 
    type check
  *)
  Fixpoint exp_isCallTo (i: ident) (e: expression) : option (expression) :=
    match e with 
    | call _ i' => if (i=?i') then Some (e) else None
    | callAnd _ i' e' => if (i=?i') then Some (e) else exp_isCallTo i e' (* we lose the left side of the expression! *)
    | _ => None
    end.

  Definition optionToList {A} (a: option A) : list A :=
    match a with 
    | Some x => x :: nil
    | None => nil
    end. 

  Fixpoint stmt_hasCallTo (i: ident) (s: statement) : option (statement) :=
    match s with 
    | Exp e => (x <- exp_isCallTo i e ;; Some (s))%monad
    | Seq e s' => match exp_isCallTo i e with 
                  | Some _ => Some s 
                  | None => stmt_hasCallTo i s'
                  end
    end. (* TODO: this one is clearly wront don't forget *)

  Definition meth_hasCallTo (i: ident) (m: method) : option (ident * statement) :=
    match m with 
    | def this t s => (x <- stmt_hasCallTo i s ;;
                      Some (this, s))%monad
    end.

  Definition act_getCallsTo (i: ident) (a: actor) : list (ident * statement) :=
    match a with 
    | class ms stmt =>  
      (map (fun x => ("start", x)) (optionToList (stmt_hasCallTo i stmt))) ++
      flat_map optionToList (
        (map (snd) (elements (SMAP.map (meth_hasCallTo i) ms)))
      )
    end.
  Fixpoint prog_getCallsTo (i: ident) (p: list (actor)) : list (ident * statement) :=
    match p with 
    | nil => nil
    | ac :: acs => act_getCallsTo (i: ident) (ac: actor) ++ prog_getCallsTo i acs
    end. 

  Definition classesOf (p: program) : list actor := map snd (elements p).

End ImperativeSyntax.

(*
  And we need to modify how we obtain the effects from a program
*)


Module ImperativeEffects.
  Include ImperativeSyntax.

  Inductive effect : Type := 
    | ϵ
    | C (m: ident) (*(c : ident)*)
    | Sync (e1 e2 : effect) 
    | Async (e1 e2 : effect)
    | N (* we introduce the non terminal symbol to handle imperative effects *)
  .


  (*
    The Non-terminal N allows us to jump out of a parallel composition,
    for example:

    and effect growing in parallel compositions:
    (a1 & (a2 & a3)) -> (a1 & (a2 & (a3 & a4)))
    can be awaited (force syncronisity) and continue out of the loop
    (a1 & (a2 & a3)) -> (a1 & (a2 & a3)); a4 

  *)

  Notation "e1 '|->' e2" := (Sync e1 e2) (right associativity, at level 51). 
  Notation "e1 ';' e2 " := (Async e1 e2) (at level 100).

  Fixpoint getExpEff (e: expression) : effect :=
    match e with 
      | call a m => C m 
      | callAnd a m e' => (Async (C m) (getExpEff e'))
      | wait => ϵ
      | done => ϵ
      end
    .

  (* place an effect in the terminal symbol *)
  (* for convention we only recurse in the right operand, to avoid a recursive mess *)
  Fixpoint placeEffect (eff neff: effect) : effect :=
    match neff with 
      | N => eff
      | ϵ => ϵ
      | C m => C m 
      | Sync e1 e2 => Sync e1 (placeEffect eff e2)
      | Async e1 e2 => Async e1 (placeEffect eff e2)
    end.

  Fixpoint getStmtEff (s: statement) (curr: effect) : effect :=
    match s with
      | Exp e => placeEffect (getExpEff e) curr 
      | Seq e1 s2 => match e1 with 
                     | wait => getStmtEff s2 (Sync (placeEffect (getExpEff e1) curr) N)
                     | _ => getStmtEff s2 (Async (placeEffect (getExpEff e1) curr) N)
                     end
    end.

  (* Let's try this *)

  Definition exampleStmt := 
    Seq (call "A" "a") (Seq (call "B" "b") (Seq wait (Seq (call "C" "c") (Exp (call "D" "d"))))). 
    (* 
    basically 
    {
      call A.a
      call B.b
      wait
      call C.c
      call D.d
    }
    we expect an effect: (a ; b) |-> (c ; d)
    where a and b can permute and c will happen strictly after
    *)

  Compute getStmtEff exampleStmt N.

End ImperativeEffects.


(*
  To continue with our song workflow let's try to fix the breaking example
  by using imperative calls and awaits.

    
  LeadSinger {                  FirstGuitar {
    sing () {                     solo () {
      FirstGuitar.solo();           LeadSinger.chorus() 
      wait;
      LeadSinger.chorus()
    }                             }
    outro () {                    riff () {
      done                          done
    }                             }
    chorus () {
      FirstGuitar.outro
    }
    start := sing()               
  }

*)
Module ImperativeExample.
  Include ImperativeSyntax.

  Definition emptyActor := SMAP.empty method.
  Definition emptyProgram := SMAP.empty actor.

  Definition sing := def "sing" tt (
    Seq (call "FirstGuitar" "solo") 
      (Seq wait (Exp (call "LeadSinger" "chorus"))) ).
  Definition solo := def "solo" tt (Exp (call "FirstGuitar" "riff")).
  Definition chorus := def "chorus" tt (Exp (call "LeadSinger" "outro")).
  Definition riff := def "riff" tt (Exp done).
  Definition outro := def "outro" tt (Exp done).

  Definition LeadSinger : actor := 
    class (SMAP.add "chorus" chorus (SMAP.add "outro" outro (SMAP.add "sing" sing emptyActor))) (Exp (call "LeadSinger" "sing")).
  Definition FirstGuitar : actor := 
    class (SMAP.add "riff" riff (SMAP.add "solo" solo emptyActor)) (Exp wait).

  Definition exampleProgram :=
    SMAP.add "FirstGuitar" FirstGuitar (SMAP.add "LeadSinger" LeadSinger emptyProgram).

  Definition getCallsTo (i: ident): list (ident * expression) :=
    match i with 
    | "riff" => ("solo", (call "FirstGuitar" "riff" )) :: nil
    | "chorus" => ("sing", (callAnd "FirstGuitar" "solo" (call "LeadSinger" "chorus") )) :: nil
    | "solo" => ("sing", (callAnd "FirstGuitar" "solo" (call "LeadSinger" "chorus") )) :: nil
    | _ => nil 
    end.

End ImperativeExample.

(* The model is pretty much the same but we need to re-define it in terms of 
   the new effects *)

Module ImperativeModel.
  Include ImperativeEffects.


  Definition dependency := option ident. (* so far is only the one we want to be executed earlier *)

  Inductive models : effect -> dependency -> Prop := 
    | FoundIt : forall d,
      models (C d) (Some d)
    | Next : forall d e1 e2,
      models e1 d \/ models e2 d ->
      models (Sync e1 e2) d
    | Divide2 : forall d e1 e2 e3,
      models e1 d \/ models e2 d \/ models e3 d ->
      models (Sync (Async e1 e2) e3) d
    | Permutation : forall d e1 e2,
      models e1 d /\ models e2 d -> 
      models (Async e1 e2) d
    | PermutationEpsilon : forall d e1, (* We need them because we place epsilons when we finish an async recursion *)
      models e1 d -> 
      models (Async e1 ϵ) d
    | PermutationEpsilon2 : forall d e1,
      models e1 d -> 
      models (Async ϵ e1) d
    | NoDep: forall e,
      models (e) None
  .
  Notation "m |= d" := (models m d) (at level 10).

End ImperativeModel.

(* And we need to change the typing rules *)


Module ImperativeTyped.
  Include ImperativeModel.
  Definition context := (effect * program)%type.
  
  Definition dependencyOf (c m: ident) : dependency := 
    match c, m with 
    | "LeadSinger", "outro" => Some "solo"
    | _ , _ => None
    end.
  
  Inductive welltyped_expression : context -> expression -> Prop :=
    | T_Call : forall eff p c m, 
      eff |= (dependencyOf c m) ->
      welltyped_expression (eff, p) (call c m)
    | T_Call2 : forall eff p thisMethod c m stmt caller, 
      List.In (caller, stmt) (prog_getCallsTo thisMethod (classesOf p)) ->
      (* (Sync (C caller) (Sync eff (C thisMethod))) |= (dependencyOf c m) ->   *)
      (* Change to allow for arbitraty calls *)
      welltyped_expression ((getStmtEff stmt N) |-> eff, p) (call c m) ->
      (* welltyped_expression (Sync (C caller) (Sync eff (C thisMethod)), p) exp -> *)
      welltyped_expression (C thisMethod |-> eff, p) (call c m)
    | T_CallAsync : forall eff p eff1 c m,
      eff |= (dependencyOf c m) /\ eff1 |= (dependencyOf c m) -> (* Both must comply *)
      welltyped_expression (Async eff eff1, p) (call c m)
    | T_CallAnd : forall eff p c m e, 
      eff |= (dependencyOf c m) ->
      welltyped_expression (Sync eff (Async (C m) ϵ), p) e -> 
      welltyped_expression (eff, p) (callAnd c m e)
    | T_Wait : forall eff p,
      welltyped_expression (eff, p) wait
    | T_Done : forall ctx,
      welltyped_expression ctx done
  .

  (* New *)
  Inductive welltyped_statement : context -> statement -> Prop :=
    | T_Exp : forall p e eff,
      welltyped_expression (eff, p) e ->
      welltyped_statement (eff, p) (Exp e)
    | T_Seq : forall eff p s e,
      welltyped_expression (eff, p) (e) -> 
      welltyped_statement (eff, p) s ->
      welltyped_statement (eff, p) (Seq e s)
  .

  Inductive welltyped_method : context -> method -> Prop :=
    | T_Method : forall id s t p,
      welltyped_statement ((C id) |-> ϵ, p) s ->
      welltyped_method (ϵ, p) (def id t s) (* no trailing effects on start of an activity! *)
  .

  Inductive welltyped_actor : context -> actor -> Prop :=
    | T_Actor : forall p ms start,
      all_true ms (welltyped_method (ϵ, p)) ->
      welltyped_actor (ϵ,p) (class ms start)
  .

  Inductive welltyped_program : context -> program -> Prop := 
    | T_Program (p: program) : 
      all_true p (welltyped_actor (ϵ, p)) ->
      welltyped_program (ϵ, p) p
  .

  Import ImperativeExample.

  Print exampleProgram.
  Compute prog_getCallsTo "riff" (classesOf exampleProgram).
  (* In this proof we can see how we can go one call deeper looking for the called dependency *)
  Lemma concurrentTyped:  welltyped_program (ϵ, exampleProgram) exampleProgram.
  Proof.
    open_block; open_block.
    - do 5 constructor.
    - do 6 constructor.
    - constructor. constructor.
      eapply T_Call2.
      + simpl. left. trivial.
      + unfold getStmtEff. unfold getExpEff. unfold placeEffect. constructor. constructor.
        left. constructor. left. apply PermutationEpsilon. constructor.
    - do 5 constructor.
    - do 8 constructor.
  Qed.
    
End ImperativeTyped.

(* 
(* 
  How do we know if the type&effect system we implemented is correct?
  Our intention was to capture the ordering of tasks to ensure task dependency,
  to be able to prove that we in fact capture all the possible ordering of tasks
  in a concurrent workflow we need to compare it the language semantics.

  Now we will define semantics for the workflow modelling language, so we can 
  proof bisimulation between the language and the effect system.
  
*)

From Coq Require Import Multiset.
From Coq Require Import Classes.EquivDec.
From Coq Require Import String.
From Coq Require Import Relations.Relation_Operators.

Module ImperativeSemantics.

  Include ImperativeTyped.

  (* A process is a stament awaiting to be executed *)
  Definition process := statement.

  Definition pool := multiset process.
  (* 
    we are not storing variables, we just have running processes in the 
    context of a program
  *)
  Definition configuration := (SMAP.t (SMAP.t pool) * program)%type.
  (* 
    We don't produce a value, just an execution trace (to compare with our model)
  *)
  Definition trace := list ident.

  (* and because coq is annoying we need a decidable equality for statements *)

  Instance stmt_eqdec: EqDec statement eq . Admitted. 

  Definition removeFromBag (p: pool) (a: statement) : pool :=
    match p with 
    | Bag f => Bag (fun x => (if stmt_eqdec a x then (f a - 1) else f x))
    end.
  
  Definition addToBag (p: pool) (a: statement) : pool := 
    match p with 
    | Bag f => Bag (fun x => (if stmt_eqdec a x then (f a + 1) else f x))
    end.

  Reserved Notation "a => b" (at level 100).
  Inductive big_step : (configuration * trace)%type -> (configuration * trace)%type -> Prop := 
  | S_done : forall pool p (t: trace), 
    0 < pool (Exp done) ->  (* If any of the processes reaches a "done" the workflow is finished *)
    ((Bag pool, p), t) => ((EmptyBag process, p), t)
  | S_call : forall (c m : ident) p1 p t stmt,
    0 < p1 (Exp (call c m)) -> 
    getStmtById c m p = Some stmt -> (* is possible to get the body of the called method *)
    ((Bag p1, p), t) => ((addToBag
                          (* we also need to fetch from the program the body of the called method *) 
                            (removeFromBag (Bag p1) (Exp (call c m)))
                            (stmt)
                            , p), t ++ (m :: nil)) 
  | S_callAnd : forall (c m : ident) p1 p t exp2,
     0 < p1 (Exp (callAnd c m exp2)) -> 
    ((Bag p1, p), t) => (((
                        addToBag
                          (addToBag 
                            (removeFromBag (Bag p1) (Exp (callAnd c m exp2))) (* Dissect the and in two *)
                            (Exp (call c m)))
                          (Exp exp2)), p), t)
  | S_seq : forall exp stmt1 p1 prog t,
    0 < p1 (Seq exp stmt1) ->
    ~ exp = wait -> 
    ((Bag p1, prog), t) => ((addToBag
                              (addToBag
                                (removeFromBag (Bag p1) (Seq exp stmt1))
                                (Exp exp))
                              (stmt1), prog), t)
  | S_seq_wait : forall exp stmt1 p1 prog t,
    0 < p1 (Seq exp stmt1) ->
    exp = wait -> 
    ((Bag p1, prog), t) => ((addToBag
                              (addToBag
                                (removeFromBag (Bag p1) (Seq exp stmt1))
                                (Exp exp))
                              (stmt1), prog), t)
  where "a => b" := (big_step a b) 
  .  

  (* 
    With the semantics defined we need a couple more concepts to check our 
    type&effect system 
  *)

  (* 
    firstly, in a trace what does it mean to "happen before", that's what we are
    checking in our model 
  *)
  (* a happens before than b in t *)
  Definition happens_before (a b : ident) (t : trace) : Prop :=
    forall (n: nat), nth_error t n = Some b -> 
                     exists n1, n1 < n -> 
                                nth_error t n1 = Some a. 

  Reserved Notation "a =>* b" (at level 50).
  Inductive trans_closure_big_step : (configuration * trace)%type -> (configuration * trace)%type -> Prop :=
  | step : forall (a b c : (configuration * trace)), (a => b) -> (b => c) -> a =>* c
  where "a =>* b" := (trans_closure_big_step a b). 


  (* dependencyOf is still hardcoded *)
  Theorem soundness : forall prog dep (t : trace) (m c : ident ) (pl : pool), 
    welltyped_program (ϵ, prog) prog -> 
    forall c m, dependencyOf c m = Some dep -> 
       ((EmptyBag process, prog), nil) =>* ((pl, prog), t) -> 
       happens_before dep m t . Admitted.

(* To prove by bisimulation we should pick up a trace by transt closure and check that the model actually allows the trace, 
meanwhile prove that if the model allows a trace it can be reach by transt closure of big step. 
Given that is not relevant (YET) I'm sticking to this shorter proof.*)



End ImperativeSemantics.


 *)
