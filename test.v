Print LoadPath.
Require Import MetaCoq.ErasurePlugin.Loader.

Definition f (n: nat): nat := match n with O => O | S n => n end.

Definition idat (A: Type): A -> A := fun a: A => a.
Definition i := let U := unit in idat U.

MetaCoq Erase i.

