/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;

/**
 * Domain delegating all the work to multiple subdomains.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class CompoundDomain implements IDomain {

	private final SymbolicTools mTools;
	private final Collection<IDomain> mSubdomains;

	/**
	 * Creates a new compound domain from the given subdomains.
	 * It is even possible to use the same domain type multiple times as a subdomain.
	 * This can be useful when using different settings for each of the "duplicates".
	 * The iteration order of {@code subdomains} can be important. For instance,
	 * using faster domains first can speed up {@link #isEqBottom(IPredicate)}.
	 *
	 * @param subdomains Domains to be used by this compound domain
	 */
	public CompoundDomain(final SymbolicTools tools, final Collection<IDomain> subdomains) {
		mTools = tools;
		mSubdomains = subdomains;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		final Collection<IPredicate> joinFromEachDomain = new ArrayList<>(mSubdomains.size());
		for (final IDomain domain : mSubdomains) {
			joinFromEachDomain.add(domain.join(lhs, rhs));
		}
		return mTools.and(joinFromEachDomain);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO does this guarantee that a fixpoint is reached?
		final Collection<IPredicate> widenFromEachDomain = new ArrayList<>(mSubdomains.size());
		for (final IDomain domain : mSubdomains) {
			widenFromEachDomain.add(domain.widen(old, widenWith));
		}
		return mTools.and(widenFromEachDomain);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		final Collection<IPredicate> abstractedLhsConjunction = new ArrayList<>(mSubdomains.size());
		for (final IDomain domain : mSubdomains) {
			final ResultForAlteredInputs result = domain.isEqBottom(pred);
			if (result.isTrueForAbstraction() || !result.wasAbstracted()) {
				// Either: over-approximation = bottom    ==implies=>    original = bottom
				// Or:     original != bottom
				return result;
			}
			// over-approximation != bottom  (could mean original is bottom or not)
			abstractedLhsConjunction.add(result.getLhs());
		}
		return new ResultForAlteredInputs(mTools.and(abstractedLhsConjunction), mTools.bottom(), false, true);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final Collection<ResultForAlteredInputs> trueResults = new ArrayList<>(mSubdomains.size());
		final Collection<ResultForAlteredInputs> falseResults = new ArrayList<>(mSubdomains.size());
		for (final IDomain domain : mSubdomains) {
			final ResultForAlteredInputs result = domain.isSubsetEq(subset, superset);
			if (!result.wasAbstracted()) {
				return result;
			}
			(result.isTrueForAbstraction() ? trueResults : falseResults).add(result);
		}
		// TODO offer different settings for picking an answer, for instance
		// [X] prefer true (current approach)
		//       Faster convergence in fixpoint iteration
		//       (but not necessarily less precise than other methods?)
		// [_] majority voting
		// [_] prefer false
		final boolean pickedTrueResults = !trueResults.isEmpty();
		final Collection<ResultForAlteredInputs> resultList = pickedTrueResults ? trueResults : falseResults;
		return new ResultForAlteredInputs(
			mTools.and(mapAndCollect(resultList, ResultForAlteredInputs::getLhs)),
			mTools.and(mapAndCollect(resultList, ResultForAlteredInputs::getRhs)),
			pickedTrueResults, true
		);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		return mTools.and(mapAndCollect(mSubdomains, dom -> dom.alpha(pred)));
	}

	private static <I, O> Collection<O> mapAndCollect(final Collection<I> input, final Function<I, O> mapper) {
		return input.stream().map(mapper).collect(Collectors.toList());
	}
}
