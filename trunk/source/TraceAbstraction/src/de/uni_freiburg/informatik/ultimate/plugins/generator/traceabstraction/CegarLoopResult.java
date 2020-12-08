/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class CegarLoopResult<L extends IIcfgTransition<?>> {
	private final Result mOverallResult;
	private final IProgramExecution<L, Term> mProgramExecution;
	private final List<UnprovabilityReason> mUnprovabilityReasons;
	private final IRunningTaskStackProvider mRunningTaskStackProvider;
	private final IStatisticsDataProvider mCegarLoopStatisticsGenerator;
	private final IElement mArtifact;
	private final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomata;

	public CegarLoopResult(final Result overallResult, final IProgramExecution<L, Term> programExecution,
			final List<UnprovabilityReason> unprovabilityReasons,
			final IRunningTaskStackProvider runningTaskStackProvider,
			final IStatisticsDataProvider cegarLoopStatisticsGenerator, final IElement artifact,
			final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> floydHoareAutomata) {
		super();
		mOverallResult = overallResult;
		mProgramExecution = programExecution;
		mUnprovabilityReasons = unprovabilityReasons;
		mRunningTaskStackProvider = runningTaskStackProvider;
		mCegarLoopStatisticsGenerator = cegarLoopStatisticsGenerator;
		mArtifact = artifact;
		mFloydHoareAutomata = floydHoareAutomata;
	}

	public Result getOverallResult() {
		return mOverallResult;
	}

	public IProgramExecution<L, Term> getProgramExecution() {
		return mProgramExecution;
	}

	public List<UnprovabilityReason> getUnprovabilityReasons() {
		return mUnprovabilityReasons;
	}

	public IRunningTaskStackProvider getRunningTaskStackProvider() {
		return mRunningTaskStackProvider;
	}

	public IStatisticsDataProvider getCegarLoopStatisticsGenerator() {
		return mCegarLoopStatisticsGenerator;
	}

	public IElement getArtifact() {
		return mArtifact;
	}

	public List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> getFloydHoareAutomata() {
		return mFloydHoareAutomata;
	}
}
