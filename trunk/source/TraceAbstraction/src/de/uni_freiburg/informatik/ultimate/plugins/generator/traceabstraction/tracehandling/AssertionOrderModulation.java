/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

/**
 * Changes the assertion order based on the trace histogram to detect and reduce loop unwindings.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class AssertionOrderModulation {
	private static final AssertCodeBlockOrder[] ASSERTION_ORDERS = { AssertCodeBlockOrder.INSIDE_LOOP_FIRST1,
			AssertCodeBlockOrder.MIX_INSIDE_OUTSIDE, AssertCodeBlockOrder.NOT_INCREMENTALLY,
			AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST1, AssertCodeBlockOrder.OUTSIDE_LOOP_FIRST2,
			AssertCodeBlockOrder.TERMS_WITH_SMALL_CONSTANTS_FIRST };
	
	private final List<HistogramOfIterable<CodeBlock>> mHistograms;
	private int mCurrentIndex;
	
	/**
	 * Constructor.
	 */
	public AssertionOrderModulation() {
		mHistograms = new ArrayList<>();
	}
	
	/**
	 * A user reports a new counterexample and receives as answer the assertion order to use.
	 * 
	 * @param counterexample
	 *            counterexample
	 * @return which assertion order to use
	 */
	public AssertCodeBlockOrder reportAndGet(final IRun<CodeBlock, IPredicate, ?> counterexample) {
		final HistogramOfIterable<CodeBlock> traceHistogram = new HistogramOfIterable<>(counterexample.getWord());
		
		if (mHistograms.isEmpty()) {
			mCurrentIndex = getInitialAssertionOrderIndex(traceHistogram);
		} else if (histogramRepeats(traceHistogram)) {
			mCurrentIndex = getNextAssertionOrderIndex();
		}
		mHistograms.add(traceHistogram);
		
		return ASSERTION_ORDERS[mCurrentIndex];
	}
	
	private static int getInitialAssertionOrderIndex(final HistogramOfIterable<CodeBlock> traceHistogram) {
		// Current policy: We start with the first element in the array.
		return 0;
	}
	
	private boolean histogramRepeats(final HistogramOfIterable<CodeBlock> traceHistogram) {
		assert !mHistograms.isEmpty();
		/*
		 * Current policy: The histogram repeats if the number of entries that occur more than once has increased wrt.
		 * the previous iteration.
		 */
		final int sumOfPreviousRepeatingEntries =
				getSumOfEntriesGreaterThanOne(mHistograms.get(mHistograms.size() - 1));
		final int sumOfCurrentRepeatingEntries = getSumOfEntriesGreaterThanOne(traceHistogram);
		
		return sumOfPreviousRepeatingEntries < sumOfCurrentRepeatingEntries;
	}
	
	private static int getSumOfEntriesGreaterThanOne(final HistogramOfIterable<CodeBlock> histogram) {
		int result = 0;
		for (final int value : histogram.getVisualizationArray()) {
			if (value > 1) {
				result += value;
			} else {
				break;
			}
		}
		return result;
	}
	
	private int getNextAssertionOrderIndex() {
		/*
		 * Current policy: The assertion order is just advanced.
		 */
		return (mCurrentIndex + 1) % ASSERTION_ORDERS.length;
	}
}
