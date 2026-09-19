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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ThreadAnalyzer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class OuterInterferenceFixpoint {
	private final ILogger mLogger;
	private final GroupedInterferenceFactory<?> mInterferenceFactory;
	private final ThreadAnalyzer mThreadAnalysis;
	private final InterferenceFixpoint mInterferences;
	private final MutexInvariantFixpoint mMutexInvariants;
	private final Invariants mInvariants;

	public OuterInterferenceFixpoint(final ILogger logger, final ConcurrentSymbolicTools tools, final IDomain domain,
			final GroupedInterferenceFactory<?> interferenceFactory, final PublishOnAcquire initialMutexInvariants,
			final int wideningThreshold, final ThreadAnalyzer threadAnalysis) {
		mLogger = logger;
		mInterferenceFactory = interferenceFactory;
		mThreadAnalysis = threadAnalysis;
		mInterferences = new InterferenceFixpoint(domain, wideningThreshold);
		mMutexInvariants = new MutexInvariantFixpoint(tools, domain, initialMutexInvariants, wideningThreshold);
		mInvariants = new Invariants(domain, threadAnalysis.getJoinedExitLocations());
	}

	public ThreadModularFixpointResult compute() {
		final Map<IcfgLocation, IPredicate> allPredicates = new LinkedHashMap<>();
		boolean rerunWithStableInterferences = false;

		for (int iteration = 1;; iteration++) {
			mLogger.info("Iteration %d", iteration);
			mInvariants.rememberCurrentStates(allPredicates);
			mMutexInvariants.configureForAnalysis();
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = mThreadAnalysis.analyze(
					mInterferences.current(), allPredicates);
			final IInterferenceSet extractedInterferences = mInterferenceFactory.buildFromAllStates(perThreadPredicates);
			mMutexInvariants.extractFrom(allPredicates);
			final boolean interferencesAreStable = mInterferences.isStable(extractedInterferences);
			final boolean mutexInvariantsAreStable = mMutexInvariants.isStable();

			if (interferencesAreStable && mutexInvariantsAreStable) {
				if (rerunWithStableInterferences || mInvariants.areUnchanged(allPredicates)) {
					return new ThreadModularFixpointResult(allPredicates, perThreadPredicates);
				}
				rerunWithStableInterferences = true;
				mMutexInvariants.acceptExtracted();
				continue;
			}

			rerunWithStableInterferences = false;
			mMutexInvariants.advance(iteration);
			mInterferences.advance(extractedInterferences, iteration);
		}
	}
}
