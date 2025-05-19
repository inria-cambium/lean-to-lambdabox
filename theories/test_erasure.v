Require Import MetaCoq.ErasurePlugin.Loader.

Fixpoint
  even n := match n with O => true | S n => odd n end
with
  odd n := match n with O => false | S n => even n end
.
MetaCoq Erase even.
