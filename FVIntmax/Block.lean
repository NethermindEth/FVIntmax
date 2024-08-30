import Mathlib.Data.Finmap

namespace Intmax

-- transfer (aggregator : K₁) (extradata : ByteArray) (commitment : C) (validUsers : K₂) (sigma : Sigma)
/--
2.4

NB the `V` here does not _yet_ need the fact that it is a latticed-ordered abelian group.

𝔹 := Bdeposit ⨿ Btransf er ⨿ Bwithdrawal
-/
inductive Block (K₁ K₂ : Type) (C Sigma : Type)
                (V : Type) [OfNat V 0] [LE V] :=
  /--
    Bdeposit - (2.5 - Bdeposit := K₂ × V+)
    
    TODO(REVIEW): > A deposit block contains only one deposit tx?
                  I have no intuition for this, but formally they state this is in fact the case.
  -/
  | deposit (recipient : K₂) (amount : {v : V // 0 ≤ v})
  /--
    Btransfer - (2.6 - Btransfer = Btransf er = K1 × {0, 1}∗ × AD.C × P(K) × SA.Σ)

    NB I can _not_ bring myself to abuse DTT to express `validUsers : K₂` beyond `K₂`.
    The intent is to subset en passant in subsequent statements about transfers.
  -/
  | transfer (aggregator : K₁) (extradata : ByteArray) (commitment : C) (validUsers : K₂) (sigma : Sigma)
  /--
    Bwithdrawal - (2.7 - Bwithdrawal = V^{K_1}_+)

    NB we will see later about total/partial in this particular instance.
  -/ 
  | withdraval (withdravals : Finmap (λ _ : K₁ ↦ {v : V // 0 ≤ v}))

end Intmax
