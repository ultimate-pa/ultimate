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

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Collects result information of a CEGAR loop.
 *
 * @param <L>
 *            The type of transitions in the program analysed by the CEGAR loop
 * @param <P>
 *            The type of proof contained in this result (if any proof has been computed)
 */
public class CegarLoopResult<L, P> {
	private final Map<IcfgLocation, CegarLoopLocalResult<L>> mLocalResults;
	private final IStatisticsDataProvider mCegarLoopStatisticsGenerator;
	private final IElement mArtifact;
	private final P mProof;

	private final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomata;

	public CegarLoopResult(final Map<IcfgLocation, CegarLoopLocalResult<L>> localResults,
			final IStatisticsDataProvider cegarLoopStatisticsGenerator, final IElement artifact, final P proof,
			final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> floydHoareAutomata) {
		mLocalResults = Collections.unmodifiableMap(localResults);
		mCegarLoopStatisticsGenerator = cegarLoopStatisticsGenerator;
		mArtifact = artifact;
		mProof = proof;
		mFloydHoareAutomata = floydHoareAutomata;
	}

	public Stream<Result> resultStream() {
		return mLocalResults.values().stream().map(CegarLoopLocalResult::getResult);
	}

	public Map<IcfgLocation, CegarLoopLocalResult<L>> getResults() {
		return mLocalResults;
	}

	public IStatisticsDataProvider getCegarLoopStatisticsGenerator() {
		return mCegarLoopStatisticsGenerator;
	}

	public IElement getArtifact() {
		return mArtifact;
	}

	public boolean hasProvenAnything() {
		return mLocalResults.values().stream().anyMatch(a -> a.getResult() == Result.SAFE);
	}

	/**
	 * A proof computed by the CEGAR loop which certifies the result. Returns null if no proof was computed.
	 */
	public P getProof() {
		return mProof;
	}

	public List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> getFloydHoareAutomata() {
		return mFloydHoareAutomata;
	}
}
