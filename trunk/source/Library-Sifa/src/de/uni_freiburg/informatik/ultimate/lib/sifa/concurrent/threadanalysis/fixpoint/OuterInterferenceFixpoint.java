/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.fixpoint;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadAnalyzer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadInvariants;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class OuterInterferenceFixpoint {
	private final ILogger mLogger;
	private final GroupedInterferenceFactory<?> mInterferenceFactory;
	private final ThreadAnalyzer mThreadAnalysis;
	private final InterferenceFixpoint mInterferences;
	private final InvariantFixpoint mInvariants;

	public OuterInterferenceFixpoint(final ILogger logger, final ConcurrentSymbolicTools tools, final IDomain domain,
			final GroupedInterferenceFactory<?> interferenceFactory, final PublishOnAcquire initialMutexInvariants,
			final int wideningThreshold, final ThreadAnalyzer threadAnalysis) {
		mLogger = logger;
		mInterferenceFactory = interferenceFactory;
		mThreadAnalysis = threadAnalysis;
		mInterferences = new InterferenceFixpoint(domain, wideningThreshold);
		mInvariants = new InvariantFixpoint(tools, domain, initialMutexInvariants, wideningThreshold,
				threadAnalysis.getJoinedExitLocations());
	}

	public ThreadInvariants compute() {
		final ThreadInvariants threadInvariants = new ThreadInvariants();
		mInvariants.resetStabilityCheck();

		for (int iteration = 1;; iteration++) {
			mLogger.info("Iteration %d", iteration);
			mInvariants.configureForAnalysis(threadInvariants);

			mThreadAnalysis.analyzeAllThreads(mInterferences.current(), threadInvariants);
			final IInterferenceSet extractedInterferences = mInterferenceFactory.buildFromAllStates(threadInvariants);

			if (mInterferences.isStable(extractedInterferences)) {
				switch (mInvariants.checkInvariantStability(threadInvariants, iteration)) {
				case STABLE:
					return threadInvariants;
				case ONE_EXTRA_ROUND:
					continue;
				case UPDATE:
					break;
				}
			} else {
				mInvariants.advance(threadInvariants, iteration);
			}

			mInterferences.advance(extractedInterferences, iteration);
		}
	}
}
