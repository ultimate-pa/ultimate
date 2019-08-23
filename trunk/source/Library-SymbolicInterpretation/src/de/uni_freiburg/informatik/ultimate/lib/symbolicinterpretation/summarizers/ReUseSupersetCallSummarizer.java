/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.ProcedureResourceCache;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.ProcedureResources;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain.ResultForAlteredInputs;

/**
 * Re-uses call summaries whenever possible.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
// TODO consider implementing this summarizer as a wrapper for other call summarizers
public class ReUseSupersetCallSummarizer implements ICallSummarizer {

	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final ProcedureResourceCache mProcResCache;
	private final DagInterpreter mDagIpreter;

	/** Maps each procedure (name) to its summary cache. */
	private final Map<String, SummaryCache> mSummaryCache = new HashMap<>();

	public ReUseSupersetCallSummarizer(final SymbolicTools tools, final IDomain domain,
			final ProcedureResourceCache procResCache, final DagInterpreter dagIpreter) {
		mTools = tools;
		mDomain = domain;
		mProcResCache = procResCache;
		mDagIpreter = dagIpreter;
	}

	@Override
	public IPredicate summarize(final String callee, final IPredicate inputAfterCall) {
		return mSummaryCache.computeIfAbsent(callee, unused -> new SummaryCache())
				.reUseOrCompute(inputAfterCall, this::isSubsetEq, () -> computeSummary(callee, inputAfterCall), mTools);
	}

	private boolean isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final ResultForAlteredInputs subsetEq = mDomain.isSubsetEq(subset, superset);
		return subsetEq.isTrueForAbstraction() && subsetEq.getRhs() == superset;
	}

	private IPredicate computeSummary(final String callee, final IPredicate inputAfterCall) {
		final ProcedureResources res = mProcResCache.resourcesOf(callee);
		return mDagIpreter.interpret(res.getRegexDag(), res.getDagOverlayPathToReturn(), inputAfterCall);
	}
}





