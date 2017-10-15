{-

x variable names
p pointer names

ρ ::= ∅ | (x,p) : ρ

ρ[x ↦ p] = (x,p) : ρ

-- lookup
-- ((y,p):ρ)(x) := if x = y then p else ρ(x)
-- important to take the first match to preserve scoping/shadowing

t,u ::= x | t u | λ x. t

v ::= λ x. t

tc ::= t / ρ
vc ::= v / ρ

H ::= ∅ | (p,tc) : ρ

H[p ↦ tc] := (p,tc) : H

((p1,tc):H)(p) := if p = p1 then tc else H(p)
-- the freshness conditions guarantee there's only one tc matching.

p fresh for H := p does not appear in H

-- evaluation relation
H ; tc ⇓ H' ; vc


------------------------------------
H ; (λ x. t) / ρ ⇓ H ; (λ x. t) / ρ


H  ; t / ρ ⇓ H1 ; (λ x. t1) / ρ1
p fresh for H1
H1[p ↦ u / ρ] ; t1 / ρ1[x ↦ p] ⇓ H2 ; vc
------------------------------------
H ; t u / ρ ⇓ H2 ; vc


p  = ρ(x)
tc = H(p)
H ; tc ⇓ H1 ; vc
------------------------
H ; x / ρ ⇓ H1[p ↦ vc] ; vc



p1, ..., pn fresh for H
ρ' = ρ[x1 ↦ p1, ..., xn ↦ pn]
-- we use ρ' everywhere to allow for mutual recursion
H[p1 ↦ e1 / ρ', ..., pn ↦ en / ρ'] ; e / ρ' ⇓ H1 ; vc
--------------------------------------------
H ; let x1 = e1 .. xn = en in e / ρ ⇓ H1 ; vc

-}
