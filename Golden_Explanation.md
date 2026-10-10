Golden Explanation

This explanation follows `TuringTask/Basic.lean` in source order. The proof uses a maximum integer dual value and a closest pair of minimizers, rather than assuming a general negative-cycle or arbitrary-matrix shortcut theorem. Every structural lemma used to establish the certificate is proved in the project.

Step 1 — `moveUnit`

This is the task's original unit-exchange operation. At coordinate `i` it subtracts one, and at coordinate `j` it adds one. Its pointwise definition also handles `i = j`, when the two changes cancel. No coordinate nonnegativity is assumed.

Step 2 — `integerPairing`

This original definition is the finite integer sum of `p i * x i`. It provides the linear price term in both objectives. Because the coordinates and prices are integers, the pairing is an integer, including when the finite index type is empty.

Step 3 — `IntegerExchangeAxioms`

The original hypothesis has two parts. Every feasible vector has total coordinate sum `r`. Also, whenever `x` has more than `y` at coordinate `i`, there is a compensating coordinate `j` where `x` has less than `y`. Both opposite unit exchanges remain feasible, and their combined cost does not exceed the original combined cost. The proof uses exactly these hypotheses.

Step 4 — `integerPairing_moveUnit`

The lemma proves the exact price identity

`integerPairing p (moveUnit x i j) = integerPairing p x - p i + p j`.

It distributes multiplication and the finite sum across the pointwise exchange. This identity is used to preserve exchange axioms under price changes and to calculate local costs in the cut arguments.

Step 5 — `tilt_exchange`

Adding the linear term `integerPairing p x` to a cost preserves `IntegerExchangeAxioms`. Feasibility and the common-sum condition remain the same. In the simultaneous exchange inequality, the two price changes are opposite and cancel. The lemma later supplies the exchange axioms for positively tilted costs and cut-modified objectives.

Step 6 — `gap`

The distance measure is the natural number

`sum_i (x i - y i).toNat`.

It counts the positive coordinate excess of `x` over `y`. Negative differences contribute zero. Its natural-number codomain permits strong induction and selection of a closest minimizer pair without any assumption that the coordinates themselves are nonnegative.

Step 7 — `exists_excess`

If two distinct integer vectors have equal total coordinate sum, some coordinate satisfies `y i < x i`. Otherwise every coordinate would satisfy `x i <= y i`. A strict inequality at any coordinate would make the total sums unequal; consequently all coordinates would be equal, contradicting distinctness. The lemma supplies an exchange coordinate in local-to-global optimality and a strictly positive coordinate in the cut contradiction.

Step 8 — `gap_exchange_right`

Suppose `y i < x i` and `x j < y j`. Moving one unit in `y` from `j` to `i` decreases `gap x y` by exactly one. The proof checks coordinates separately. At `i`, the positive excess drops by one. At `j`, the difference remains nonpositive after the unit change, so its natural-number contribution remains zero. All other contributions are unchanged. Summing yields

`gap x (moveUnit y j i) + 1 = gap x y`.

Step 9 — `local_global`

This proves that a feasible vector which is no worse than every feasible unit exchange is a global minimizer. The induction variable is `gap x y`, where `y` is an arbitrary feasible competitor.

If `x = y`, the inequality is immediate. Otherwise the common-sum axiom and `exists_excess` provide a coordinate of excess. The simultaneous exchange axiom produces opposite exchanges from `x` and `y`. The exchange from `y` has strictly smaller gap, so the induction hypothesis bounds its cost below by `c x`. Local optimality supplies the corresponding bound for the exchange from `x`. Combining these bounds with the simultaneous exchange inequality gives `c x <= c y`.

This is the bridge that turns local cut calculations into the global minimizer inequalities used later.

Step 10 — `minimizers_exchange`

For two global minimizers of one exchange cost, the simultaneous exchange axiom produces opposite feasible exchanges that preserve each minimizer's cost exactly. Global minimality bounds both new costs below by their respective old costs. The exchange axiom bounds their sum above by the old sum. Therefore neither individual cost can increase. This lemma establishes closure of minimizer sets under simultaneous exchange.

Step 11 — `ExchangeSet`

This auxiliary property records simultaneous exchange closure for a set of integer vectors, without specifying a cost. It requires a compensating coordinate and feasibility of both opposite exchanges. It is used for the minimizer sets in the transitivity and multiple-exchange arguments.

Step 12 — `minimizer_set_exchange`

The set of feasible global minimizers of an exchange cost satisfies `ExchangeSet`. Applying `minimizers_exchange` gives feasible exchanged vectors with unchanged costs; their global optimality follows from that equality. Later, the two tilted minimizer sets are the exchange sets to which the route augmentation is applied.

Step 13 — `moveUnit_cancel_middle`

The pointwise identity

`moveUnit (moveUnit x u v) j u = moveUnit x j v`

cancels the subtraction and addition at the intermediate coordinate `u`. It is proved algebraically, including coincident-coordinate cases. It identifies a forbidden shortcut in `no_shortcut_on` and a feasible shortcut in `exchange_transitive`.

Step 14 — `exchange_transitive`

Within an exchange set, feasible moves `i -> j` and `j -> k` from the same base vector imply feasibility of the move `i -> k`, under the stated distinct-coordinate hypotheses. The proof applies simultaneous exchange to the two moved vectors at coordinate `j`.

The compensating coordinate must be `i` or `k`: outside these coordinates, the required strict comparison cannot hold. In either case, one of the exchanged vectors is exactly the shortcut vector. This property is derived from `ExchangeSet`; it is not asserted for an arbitrary graph or arbitrary cost matrix. It later excludes consecutive route edges assigned to the same minimizer set.

Step 15 — `pairing_neg_price`

Negating a price vector negates its integer pairing. The proof distributes negation through multiplication and the finite sum. This algebraic fact converts positive tilting into negative tilting in the next lemma.

Step 16 — `tilt_exchange_minus`

Subtracting `integerPairing p x` also preserves the exchange axioms. It follows from `tilt_exchange` with price `-p` and `pairing_neg_price`. This supplies the exchange structure for the first objective `c1 - pairing p`.

Step 17 — `IsMin`

This abbreviation combines feasibility with the universal global-minimum inequality for a cost on a finite domain. It does not encode uniqueness. The subsequent dual and augmentation statements use it to retain both feasibility and optimality together.

Step 18 — `finite_min`

Every nonempty finite domain has a global minimizer for any integer cost. The proof uses the existing finite minimum-image lemma and packages its witness as `IsMin`. This establishes nonemptiness of the dual-value family at the zero price.

Step 19 — `DualPair`

A dual pair consists of a price `p` and two vectors: `x` minimizes `c1 - pairing p` on `D1`, while `y` minimizes `c2 + pairing p` on `D2`. The definition initially allows `x` and `y` to differ. The final argument proves that a suitable closest pair at a maximizing price must coincide.

Step 20 — `dualValue`

This integer is the sum of the two tilted objective values at a dual pair:

`c1 x - pairing p x + c2 y + pairing p y`.

It is used to select a maximizing integer price and to detect a strict improvement caused by a cut price change.

Step 21 — `dual_maximum`

The common-point assumption provides a vector `z` feasible in both domains. For any dual pair, its two minimum inequalities can be evaluated at `z`. Adding them cancels the price terms, giving the uniform upper bound `c1 z + c2 z` on every attainable dual value.

At price zero, each nonempty finite domain has a minimizer by `finite_min`, so at least one dual value is attainable. The attainable values form a nonempty, bounded-above family of integers. The integer greatest-element theorem therefore provides an attained maximum. Unpacking its witness gives integer price `p`, two minimizers, and a bound on every other dual pair's value.

This selects an integer price directly. No real or rational certificate, unproved duality principle, or limiting argument is used.

Step 22 — `multiMoveOn`

For a finite indexed family of sources `u t` and targets `v t`, this defines the aggregate vector by adding the sum of all unit-exchange increments to the original vector. It records simultaneous changes algebraically; feasibility is proved separately. It is later applied to the edges assigned to each minimizer set.

Step 23 — `multiMoveOn_away`

If a coordinate is neither a source nor a target of any indexed exchange, its aggregate increment is zero. The proof shows every summand vanishes. The lemma is used to identify the new exchange source exactly during the induction in `no_shortcut_on`.

Step 24 — `multiMoveOn_nondecrease`

If a coordinate is not a source of any indexed exchange, its aggregate value is at least its original value. Every remaining contribution is a nonnegative target increment. In the multiple-exchange proof, this forces a compensating deficit coordinate to be a previous source unless it is the new target.

Step 25 — `multiMoveOn_insert`

Inserting a fresh exchange index into the finite family is algebraically equivalent to applying its unit exchange to the previous aggregate vector. The finite-sum insertion identity proves this pointwise. The lemma assembles the final induction step in `no_shortcut_on`.

Step 26 — `no_shortcut_on`

This is the general multiple-exchange feasibility lemma. The indexed sources and targets satisfy the stated distinctness and disjointness conditions. Each individual exchange from the original vector is feasible. For indices `a < b`, the forward cross exchange from source `u a` to target `v b` is forbidden.

The proof inducts by inserting the largest index. Let `y` be the feasible aggregate for the previous indices, and let `z` be the original vector with only the new individual exchange. At the new source, `y` has its original coordinate and `z` has one less. Applying simultaneous exchange to `y` and `z` supplies a compensating coordinate.

If that coordinate were not the new target, `multiMoveOn_nondecrease` forces it to be a previous source. The opposite exchange from `z`, simplified by `moveUnit_cancel_middle`, would then be exactly a forbidden forward cross exchange. This contradiction forces the new target. The feasible exchange from `y` is the desired enlarged aggregate, identified by `multiMoveOn_insert`.

This proves the full finite-family statement. The final augmentation uses ordinary index order for the first minimizer set and reversed index order for the second.

Step 27 — `Route`

A route is represented by an edge count `n` and a total vertex sequence `v`. Its first vertex belongs to the source predicate, its vertex at index `n` belongs to the target predicate, and each consecutive pair before `n` satisfies the directed-edge relation. Values of the sequence after `n` are irrelevant.

Step 28 — `route_extend`

This appends one valid directed edge to an existing source-rooted route. The new sequence agrees with the old sequence through its last vertex and then takes the new endpoint. Checking old edges and the final edge separately proves validity. This is used to prove that the reachable set is closed under zero-cost arcs.

Step 29 — `minimal_route`

Given at least one route, the natural-number least-witness principle selects the smallest attainable edge count and a route attaining it. The result includes comparison with every other valid source-to-target route. No enumeration of all paths is required.

Step 30 — `minimal_route_no_shortcut`

A shortest route cannot have a forward directed edge from vertex `a` to vertex `b` when `a + 1 < b`. Such an edge would permit deletion of the intervening edges. The proof explicitly constructs the shortened vertex sequence, checks its source, target and edges, and contradicts minimality of the original edge count. This supplies the forward-cross-exchange exclusions needed by `no_shortcut_on`.

Step 31 — `minimal_route_injective`

Vertices of a shortest route are distinct over indices from zero through `n`. If two such vertices were equal and the later one were the endpoint, the earlier prefix would already be a shorter source-to-target route. Otherwise, the edge leaving the later vertex would give a forbidden forward shortcut from the earlier equal vertex. The proof derives injectivity from route minimality alone. The additional irreflexivity hypothesis is supplied by the zero-arc application; no extra graph property is assumed.

This injectivity is used to establish distinct exchange sources and targets along the augmentation route.

Step 32 — `indicatorPrice`

This is an integer price vector equal to one on a chosen coordinate set `W` and zero elsewhere. Classical decidability is used for set membership. Subtracting this vector from an existing integer price remains an integer price. It is the cut adjustment used in `zero_route_exists`.

Step 33 — `cut_min_plus`

Suppose a global minimizer's zero-cost feasible exchanges cannot leave `W`. The lemma proves that the same vector minimizes the cost after adding its pairing with `indicatorPrice W`.

The exchange axioms remain valid by `tilt_exchange`, so it suffices to check local optimality. A zero-cost exchange cannot incur a negative cut increment, because that would leave `W`. Every exchange whose old cost is strictly greater has an integer cost increase of at least one, which compensates for the cut increment's possible decrease of one. `local_global` converts these local inequalities into global optimality.

Step 34 — `cut_min_minus`

This proves the corresponding result for subtracting the indicator pairing. The closure hypothesis is reversed: a zero-cost exchange with its target in `W` must have its source in `W`. Zero-cost moves therefore cannot acquire a negative adjusted cost. Strictly positive integer marginal costs again absorb the possible unit decrease. Negative tilting preserves the exchange axioms, and `local_global` finishes the global inequality.

Step 35 — `pairing_sub_price`

The pairing with `p - q` is the pairing with `p` minus the pairing with `q`. This follows by distributing multiplication and the finite sum. It translates the cut-modified objectives into the original objectives with the new price and computes their dual-value change.

Step 36 — `ZeroArc`

A zero arc joins distinct coordinates and has one of two justifications. Either moving one unit in `x` in the forward direction preserves the first cost, or moving one unit in `y` in the reverse direction preserves the second cost. Feasibility and exact cost equality are part of each justification. This graph uses only exchanges from the two specified minimizers.

Step 37 — `zero_route_exists`

For a dual-maximizing price and a distinct minimizer pair, this proves existence of a zero-arc route from a coordinate where `x` exceeds `y` to one where `x` is below `y`.

Assume no such route exists. Let `W` contain all coordinates reachable by zero arcs from any excess coordinate. Zero-edge routes show that all excess coordinates belong to `W`; `route_extend` shows that `W` is closed under zero arcs. The assumed absence of a route means no deficit coordinate belongs to `W`.

The two closure properties allow `cut_min_plus` and `cut_min_minus` to preserve both minimizers when replacing `p` by `p - indicatorPrice W`. On `W`, every coordinate of `x` is at least the corresponding coordinate of `y`. Equal total sums and distinctness provide an excess coordinate in `W`, so the indicator pairing of `x` is strictly larger than that of `y`.

The new dual value therefore exceeds the old one by this strictly positive pairing difference. That contradicts dual maximality. Thus a zero-arc source-to-target route exists. This is a proved cut argument, not an assumed graph-separation theorem.

Step 38 — `gap_from_difference`

This extends the gap-reduction calculation to two aggregate vectors. If their coordinatewise difference equals the old difference with one unit removed at excess coordinate `s` and added at deficit coordinate `t`, their gap decreases by exactly one. The proof identifies their gap with `gap x (moveUnit y t s)` and applies `gap_exchange_right`.

Step 39 — `sum_range_telescope`

The finite sum of consecutive integer differences `f (i+1) - f i` equals `f n - f 0`. Natural-number induction and the final-summand formula prove it. It is used to cancel the internal vertices of the route when comparing the aggregate vectors.

Step 40 — `zero_route_augment`

This proves that a shortest zero-cost source-to-target route produces a strictly closer pair of global minimizers at the same price.

First, the two global-minimizer sets satisfy `ExchangeSet`. Route minimality supplies injectivity of its vertices and absence of forward shortcuts. An edge is assigned to the first set whenever its forward exchange belongs to that set; every other edge belongs to the second set in reverse direction.

Two consecutive edges cannot both belong to the first set: `exchange_transitive` would create a forbidden forward shortcut. The same argument, with exchange directions reversed, excludes two consecutive edges assigned to the second set. These facts establish the disjointness conditions required for the multiple-exchange lemma.

The finite edge indices are divided into two complementary families. `no_shortcut_on` proves that the first family's aggregate is still a first-cost minimizer. Applying the same lemma with reversed index order proves that the second family's reverse aggregate is still a second-cost minimizer. The shortcut exclusions in both applications come directly from shortest-route minimality.

Finally, adding the two complementary edge sums accounts for the entire route. `sum_range_telescope` cancels all internal coordinate increments. The new difference equals the old difference minus one at the route's excess source and plus one at its deficit target. `gap_from_difference` proves that the gap drops by exactly one. Consequently, both global minimum properties are preserved while the pair becomes strictly closer.

Step 41 — `dualValue_eq`

At a fixed price, any two dual pairs have the same dual value. The first minimizers bound each other's tilted costs in both directions, so those costs are equal. The same holds for the second minimizers. Adding gives equality of the dual values. This permits replacement of the initial maximizing pair by a closest pair without losing the global dual bound.

Final Step — `integer_exchange_price_certificate`

The theorem first applies `dual_maximum` to obtain an integer price `p` and a dual-maximizing minimizer pair. It then forms the finite set of all pairs in `D1 x D2` which are minimizers at that price. This set is nonempty because it contains the initial pair. The finite minimum-image lemma selects a pair `(x,y)` with the smallest `gap x y`.

By `dualValue_eq`, this closest pair has the same dual value as the initial pair, so the global maximum bound still applies. Suppose `x` and `y` differed. `zero_route_exists` would produce a zero-cost route, and `minimal_route` would select a shortest one. The positively and negatively tilted costs satisfy the exchange axioms by the two tilting lemmas. Applying `zero_route_augment` would therefore give another minimizer pair at the same price with a strictly smaller gap. That pair belongs to the same finite candidate set, contradicting its minimum-gap property. Hence `x = y`.

The final witnesses are this common vector `x` and the already integer-valued price `p`. The first `IsMin` gives `x` in `D1` and the inequality

`c1 x - integerPairing p x <= c1 z - integerPairing p z`

for every `z` in `D1`. Substituting `x = y` into the second `IsMin` gives `x` in `D2` and

`c2 x + integerPairing p x <= c2 z + integerPairing p z`

for every `z` in `D2`. These are exactly the four conjuncts requested by the original theorem.

No nonemptiness assumption on the coordinate type is added. If the selected vectors coincide immediately, the route argument is unnecessary. The proof therefore covers empty and singleton finite index types, as well as negative coordinates, costs and prices.
