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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ProcedureResourceCache;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ProcedureResources;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Always computes a new call summary by interpreting the callee's path expression
 * from its entry node to its exit node.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class InterpretCallSummarizer implements ICallSummarizer {

	private final SifaStats mStats;
	private final ProcedureResourceCache mProcResCache;
	private final DagInterpreter mDagIpreter;

	public InterpretCallSummarizer(
			final SifaStats stats, final ProcedureResourceCache procResCache, final DagInterpreter dagIpreter) {
		mStats = stats;
		mProcResCache = procResCache;
		mDagIpreter = dagIpreter;
	}

	@Override
	public IPredicate summarize(final String callee, final IPredicate inputAfterCall) {
		mStats.start(SifaStats.Key.CALL_SUMMARIZER_NEW_COMPUTATION_TIME);
		mStats.increment(SifaStats.Key.CALL_SUMMARIZER_CACHE_MISSES);

		final ProcedureResources res = mProcResCache.resourcesOf(callee);
		final IPredicate result = mDagIpreter.interpret(
				res.getRegexDag(), res.getDagOverlayPathToReturn(), inputAfterCall);

		mStats.stop(SifaStats.Key.CALL_SUMMARIZER_NEW_COMPUTATION_TIME);
		return result;
	}
}
