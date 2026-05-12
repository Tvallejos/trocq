(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Trocq Require Import Relnm. 
From Trocq Require Export HoTTNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

#[prefix="Bool_"] Elpi derive Bool.

(* Enables to generically deal with Bool
despite one is a notation to bool and the other an inductive Bool*)
Definition Bool := Bool.
Elpi derive.param2 Bool.

Definition BoolR := Bool_R.
Definition trueR := true_R.
Definition Param44_Bool := Bool_rel44.
