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
package de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiPredicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;

/**
 * Stores summaries for one single procedure or loop.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class SummaryCache {

	private final Map<IPredicate, IPredicate> mKnownSummaries = new LinkedHashMap<>();

	/**
	 * Re-uses cached summaries if possible or else computes an caches a new summary from a given supplier.
	 *
	 * @param input Input of the loop or procedure which we want to summarize. The procedure or loop are
	 *              not visible to this object since they are hidden in the supplier {@code computeSummary}.
	 * @param isSubsetEq Test to check whether we can re-use another summary.
	 * @param computeSummary If no summaries can be re-used, this supplier is used to compute a new summary.
	 * @return A summary for a procedure or loop and the given input.
	 */
	public IPredicate reUseOrCompute(final IPredicate input, final BiPredicate<IPredicate, IPredicate> isSubsetEq,
			final Supplier<IPredicate> computeSummary, final SymbolicTools tools) {

		final List<IPredicate> supersets = mKnownSummaries.entrySet().stream()
				.filter(knownSummary -> isSubsetEq.test(input, knownSummary.getKey()))
				.map(Map.Entry::getValue)
				.collect(Collectors.toList());

		if (!supersets.isEmpty()) {
			// intersection is a summary because
			//     ∀ x : (x ∊ in1 → f(x) ∊ sum1) ∧ (x ∊ in2 → f(x) ∊ sum2)
			// ==> ∀ x : (x ∊ in1 ∩ in2 → f(x) ∊ sum1 ∩ sum2)
			return tools.and(supersets);
		}

		final IPredicate summary = computeSummary.get();
		mKnownSummaries.put(input, summary);
		return summary;
	}

}
