From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
From Trocq Require Import coverage sym.

Elpi derive.param2 False.
Elpi derive.sym False.

Elpi derive.param2 Unit.
Elpi derive.sym Unit.

Elpi derive.param2 Bool.
Elpi derive.sym Bool.

Elpi derive.param2 Wrap.
Elpi derive.sym Wrap.

Elpi derive.param2 WrapMore.
Elpi derive.sym WrapMore.

Elpi derive.param2 nat.
Elpi derive.sym nat.

Elpi derive.param2 option.
Elpi Trace Browser.
Elpi derive.sym option.
Compute option_sym.

Elpi derive.param2 prod.
Elpi derive.sym prod.

Elpi derive.param2 list.
Elpi derive.sym list.