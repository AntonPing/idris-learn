module DoubleNeg

pem_to_dne : Either a (Not a) -> Not (Not a) -> a
pem_to_dne prf nna =
    case prf of
        Left a => a
        Right na => absurd $ nna na

lemma : Not $ Not $ Either a (Not a)
lemma npem = npem $ Right $ \x => npem (Left x)

dne_to_pem : (forall a. Not (Not a) -> a) -> Either a (Not a)
dne_to_pem dne = dne $ lemma

dne_to_pem' : Not $ Not $ (Not (Not a) -> a) -> Either a (Not a)