/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformation plug-in.
 *
 * The ULTIMATE IcfgTransformation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntEqualityProvider implements IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Map<IcfgLocation, Set<IEqualityProvidingState>> mLoc2States;
	
	private boolean mPreprocessed;

	public AbsIntEqualityProvider(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void preprocess(final IIcfg<?> icfg) {
		final IProgressAwareTimer timer = mServices.getProgressMonitorService();
		
		final IAbstractInterpretationResult<? extends IEqualityProvidingState, 
				IcfgEdge, IProgramVarOrConst, IcfgLocation> absIntResult =
				AbstractInterpreter.runFutureSMTDomain(icfg, timer, mServices, true, mLogger);
//				AbstractInterpreter.runFutureEqualityDomain(icfg, timer, mServices, true, mLogger);
		final Map<IcfgLocation, ?> loc2states = absIntResult.getLoc2States();
		mLoc2States = (Map<IcfgLocation, Set<IEqualityProvidingState>>) loc2states;
		assert mLoc2States != null : "There was no AbsInt result";
		assert !mPreprocessed;
		mPreprocessed = true;
	}

	@Override
	public EqualityAnalysisResult getAnalysisResult(final IcfgLocation location,
			final Set<Doubleton<Term>> doubletons) {
		assert mPreprocessed;
		final Set<IEqualityProvidingState> states = mLoc2States.get(location);
		if (states == null) {
			return new EqualityAnalysisResult(doubletons);
		}

		final Set<Doubleton<Term>> equal = new HashSet<>();
		final Set<Doubleton<Term>> distinct = new HashSet<>();
		final Set<Doubleton<Term>> unknown = new HashSet<>();
		for (final Doubleton<Term> unorderedPair : doubletons) {
			if (states.stream()
					.allMatch(a -> a.areEqual(unorderedPair.getOneElement(), unorderedPair.getOtherElement()))) {
				equal.add(unorderedPair);
			} else if (states.stream()
					.allMatch(a -> a.areUnequal(unorderedPair.getOneElement(), unorderedPair.getOtherElement()))) {
				distinct.add(unorderedPair);
			} else {
				unknown.add(unorderedPair);
			}
		}
		return new EqualityAnalysisResult(equal, distinct, unknown);
	}

	@Override
	public IEqualityProvidingState getEqualityProvidingStateForLocationSet(
			final Set<IcfgLocation> locSet) {
		assert mPreprocessed;
		IEqualityProvidingState result = null;

		for (IcfgLocation loc : locSet) {
			final IEqualityProvidingState unionStateForCurrentLoc = 
					mLoc2States.get(loc).stream().reduce((s1, s2) -> s1.union(s2)).get();
			result = result == null ? unionStateForCurrentLoc : result.union(unionStateForCurrentLoc);
		}

		return result;
	}

}
