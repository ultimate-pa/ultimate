/*
 * Copyright (C) 2020 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.SmtFeatureHeuristicPartitioningType;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class AssertOrderSmtFeatureHeuristic<L extends IAction> implements IAssertOrder<L> {
	private final ScoringMethod mScoringMethod;
	private final int mNumberOfPartitions;
	private final double mHeuristicThreshold;
	private final SmtFeatureHeuristicPartitioningType mPartitioningType;
	private final ILogger mLogger;

	public AssertOrderSmtFeatureHeuristic(final ScoringMethod scoringMethod, final int numberOfPartitions,
			final double heuristicThreshold, final SmtFeatureHeuristicPartitioningType partitioningType,
			final ILogger logger) {
		mScoringMethod = scoringMethod;
		mNumberOfPartitions = numberOfPartitions;
		mHeuristicThreshold = heuristicThreshold;
		mPartitioningType = partitioningType;
		mLogger = logger;
	}

	// Function to score a trace, using the SMTFeatureExtractionTermClassifier.
	private List<Triple<Term, Double, Integer>> scoreTrace(final NestedWord<? extends IAction> trace) {
		final List<Triple<Term, Double, Integer>> termScoreIndexTriples = new ArrayList<>();
		for (int i = 0; i < trace.length(); i++) {
			final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
			final Term term = trace.getSymbol(i).getTransformula().getFormula();
			tc.checkTerm(term);
			final Double score = tc.getScore(mScoringMethod);
			termScoreIndexTriples.add(new Triple<>(term, score, i));
		}
		// sort reverse
		Collections.sort(termScoreIndexTriples, Comparator.comparing(p -> -p.getSecond()));
		return termScoreIndexTriples;
	}

	private List<Set<Integer>>
			partitionFixedNumberOfPartitions(final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final LinkedHashSet<Integer> indices = termScoreIndexTriples.stream()
				.map(Triple<Term, Double, Integer>::getThird).collect(Collectors.toCollection(LinkedHashSet::new));

		final int chunksize = (int) Math.ceil(termScoreIndexTriples.size() * (1.0 / mNumberOfPartitions));

		LinkedHashSet<Integer> currentChunk = new LinkedHashSet<>();

		int numProcessed = 0;

		final List<Set<Integer>> partitions = new ArrayList<>();
		for (final int index : indices) {
			currentChunk.add(index);
			numProcessed += 1;
			if (currentChunk.size() == chunksize || numProcessed == indices.size()) {
				partitions.add(new LinkedHashSet<>(currentChunk));
				currentChunk = new LinkedHashSet<>();
			}
		}
		return partitions;
	}

	private List<Set<Integer>>
			partitionUsingThreshold(final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final Set<Integer> partitionOne = new LinkedHashSet<>();
		final Set<Integer> partitionTwo = new LinkedHashSet<>();

		for (final Triple<Term, Double, Integer> triple : termScoreIndexTriples) {
			final Double score = triple.getSecond();
			final Integer index = triple.getThird();
			if (score >= mHeuristicThreshold) {
				partitionOne.add(index);
			} else {
				partitionTwo.add(index);
			}
		}

		final List<Set<Integer>> partitions = new ArrayList<>();
		if (!partitionOne.isEmpty()) {
			partitions.add(partitionOne);
		}
		if (!partitionTwo.isEmpty()) {
			partitions.add(partitionTwo);
		}
		return partitions;
	}

	// Function to partition a list of Terms according to their scores.
	private List<Set<Integer>>
			partitionStmtsAccordingToTermScores(final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {
		return switch (mPartitioningType) {
		case FIXED_NUM_PARTITIONS -> partitionFixedNumberOfPartitions(termScoreIndexTriples);
		case THRESHOLD -> partitionUsingThreshold(termScoreIndexTriples);
		};
	}

	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		// Score Trace Terms and order them according to score.
		final List<Triple<Term, Double, Integer>> termScoreIndexTriples = scoreTrace(counterexample.getWord());
		final List<Set<Integer>> partitions = partitionStmtsAccordingToTermScores(termScoreIndexTriples);
		assert !partitions.isEmpty();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Trace: " + counterexample.getWord().toString());
			mLogger.debug("TermScoreTriples: " + termScoreIndexTriples.toString());
			mLogger.debug("Partitions: " + partitions.toString());
		}
		return partitions;
	}

}
