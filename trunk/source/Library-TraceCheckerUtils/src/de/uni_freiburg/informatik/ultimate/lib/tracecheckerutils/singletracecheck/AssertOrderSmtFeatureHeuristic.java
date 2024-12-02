package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class AssertOrderSmtFeatureHeuristic<L extends IAction> extends AssertOrder<L> {
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

	private static LinkedHashSet<Integer> getIndices(final List<Triple<Term, Double, Integer>> termScoreIndexTriples,
			final boolean random) {
		final List<Integer> indices = termScoreIndexTriples.stream().map(Triple<Term, Double, Integer>::getThird)
				.collect(Collectors.toList());
		if (random) {
			Collections.shuffle(indices);
		}
		return new LinkedHashSet<>(indices);
	}

	private void partitionFixedNumberOfPartitions(final LinkedHashSet<LinkedHashSet<Integer>> partitions,
			final List<Triple<Term, Double, Integer>> termScoreIndexTriples, final boolean random) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final LinkedHashSet<Integer> indices = getIndices(termScoreIndexTriples, random);

		final int chunksize = (int) Math.ceil(termScoreIndexTriples.size() * (1.0 / mNumberOfPartitions));

		LinkedHashSet<Integer> currentChunk = new LinkedHashSet<>();

		int numProcessed = 0;

		for (final int index : indices) {
			currentChunk.add(index);
			numProcessed += 1;
			if (currentChunk.size() == chunksize || numProcessed == indices.size()) {
				partitions.add(new LinkedHashSet<>(currentChunk));
				currentChunk = new LinkedHashSet<>();
			}
		}
	}

	private void partitionUsingThreshold(final LinkedHashSet<LinkedHashSet<Integer>> partitions,
			final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {

		// The incremental Strategy creates N partitions.
		// Example:
		// Indices = [1,2,3,4,5,6]
		// N = 4
		// percentage_per_chunk = 1 / 4 = 0.25
		// Chunk_size = 2
		// Partitions = [1,2], [3,4], [5,6]

		final LinkedHashSet<Integer> partitionOne = new LinkedHashSet<>();
		final LinkedHashSet<Integer> partitionTwo = new LinkedHashSet<>();

		for (final Triple<Term, Double, Integer> triple : termScoreIndexTriples) {
			final Double score = triple.getSecond();
			final Integer index = triple.getThird();
			if (score >= mHeuristicThreshold) {
				partitionOne.add(index);
			} else {
				partitionTwo.add(index);
			}
		}

		if (!partitionOne.isEmpty()) {
			partitions.add(partitionOne);
		}
		if (!partitionTwo.isEmpty()) {
			partitions.add(partitionTwo);
		}
	}

	// Function to partition a list of Terms according to their scores.
	private List<Set<Integer>>
			partitionStmtsAccordingToTermScores(final List<Triple<Term, Double, Integer>> termScoreIndexTriples) {
		final LinkedHashSet<LinkedHashSet<Integer>> partitions = new LinkedHashSet<>();
		switch (mPartitioningType) {
		case FIXED_NUM_PARTITIONS:
			partitionFixedNumberOfPartitions(partitions, termScoreIndexTriples, false);
			break;
		case THRESHOLD:
			partitionUsingThreshold(partitions, termScoreIndexTriples);
			break;
		default:
			throw new UnsupportedOperationException("Unknown partitioning type " + mPartitioningType);
		}
		assert !partitions.isEmpty();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("TermScoreTriples: " + termScoreIndexTriples.toString());
			mLogger.debug("Partitions: " + partitions.toString());
		}
		return new ArrayList<>(partitions);
	}

	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Trace: " + trace.toString());
		}
		// Score Trace Terms and order them according to score.
		return partitionStmtsAccordingToTermScores(scoreTrace(trace));
	}

}
