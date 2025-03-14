package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.OptionalInt;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LargeBlockEncoding {

	/**
	 * Omit compositions if this would lead to the removal of a loop location or of a location of interest.
	 */
	public static final boolean PRESERVE_LOOP_HEADS_AND_LOCATIONS_OF_INTEREST = true;

	/**
	 * Defines which statements will be composed.
	 */
	public enum InternalLbeMode {
		ONLY_ATOMIC_BLOCK, ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS, ALL_EXCEPT_ATOMIC_BOUNDARIES, ALL
	}

	private enum SequentialCompositionType {
		NONE, STRAIGHTLINE, COMPLEX
	}

	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mIcfg;
	private final CodeBlockFactory mCbf;
	private final InternalLbeMode mInternalLbeMode;
	final boolean mSimplifyCodeBlocks;

	private final ILogger mLogger;

	private final Set<BoogieIcfgLocation> mEntryNodes;
	private final AtomicBlockAnalyzer mAtomicAnalysis;

	// straight-line sequential composition points
	private final HashDeque<BoogieIcfgLocation> mSequentialQueue = new HashDeque<>();

	// Y-to-V and upside-down Y-to-V composition points
	private final PriorityQueue<ComplexComposition> mComplexSequentialQueue = new PriorityQueue<>();

	private final LinkedHashMap<BoogieIcfgLocation, List<List<CodeBlock>>> mParallelQueue = new LinkedHashMap<>();

	// some statistics
	private int mStraightlineSequentialCompositions;
	private int mOneToNSequentialCompositions;
	private int mComplexSequentialCompositions;
	private int mParallelCompositions;

	public LargeBlockEncoding(final IUltimateServiceProvider services, final BoogieIcfgContainer icfg,
			final CodeBlockFactory cbf, final InternalLbeMode internalLbeMode) {
		final long startTime = System.nanoTime();

		mServices = services;
		mIcfg = icfg;
		mCbf = cbf;
		mInternalLbeMode = internalLbeMode;
		mLogger = services.getLoggingService().getLogger(LargeBlockEncoding.class);
		mSimplifyCodeBlocks = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLIFY);
		mEntryNodes = new HashSet<>(mIcfg.getProcedureEntryNodes().values());
		mAtomicAnalysis = new AtomicBlockAnalyzer(mIcfg);

		mLogger.info(
				"Applying CFG Large Block Encoding to ICFG that has %d procedures, %d locations, %d edges, "
						+ "%d initial locations, %d loop locations, and %d error locations.",
				icfg.getProcedureEntryNodes().size(), IcfgUtils.getNumberOfLocations(icfg),
				IcfgUtils.getNumberOfEdges(icfg), icfg.getInitialNodes().size(), icfg.getLoopLocations().size(),
				IcfgUtils.getErrorLocations(icfg).size());

		final var initialNodes = getInitialThreadLocations();

		// initialize queues of locations that are candidates for different kind of compositions
		new IcfgLocationIterator<>(initialNodes).asStream().forEach(pp -> considerCompositionCandidate(pp, true));

		// We distinguish 3 types of compositions: straight-line sequential compositions, parallel compositions, and
		// complex sequential compositions.
		// We employ complex compositions extremely sparingly, as they can lead to the creation of an exponential
		// number of edges for code with a lot of branching. Often, all these edges are later reduced through
		// parallel composition to very few edges (but a timeout occurs before this happens).
		while (!mSequentialQueue.isEmpty() || !mParallelQueue.isEmpty() || !mComplexSequentialQueue.isEmpty()) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "performing CFG large-block encoding");
			}

			while (mSequentialQueue.isEmpty() && mParallelQueue.isEmpty() && !mComplexSequentialQueue.isEmpty()) {
				final BoogieIcfgLocation superfluousPP = mComplexSequentialQueue.poll().programPoint();
				composeSequential(superfluousPP);
				mLogger.debug("Complex sequential composition at %s", superfluousPP);
			}

			while (mSequentialQueue.isEmpty() && !mParallelQueue.isEmpty()) {
				final Entry<BoogieIcfgLocation, List<List<CodeBlock>>> superfluous = mParallelQueue.firstEntry();
				final BoogieIcfgLocation pp = superfluous.getKey();
				mParallelQueue.remove(pp);
				for (final List<CodeBlock> outgoing : superfluous.getValue()) {
					composeParallel(pp, outgoing);
					mLogger.debug("parallel composition of %d edges at %s", pp, outgoing.size());
				}
			}

			while (!mSequentialQueue.isEmpty()) {
				final BoogieIcfgLocation superfluousPP = mSequentialQueue.pollFirst();
				composeSequential(superfluousPP);
				mLogger.debug("sequential composition at %s", superfluousPP);
			}

			mComplexSequentialQueue.clear();
			mParallelQueue.clear();
			mSequentialQueue.clear();

			new IcfgLocationIterator<>(initialNodes).asStream().forEach(pp -> considerCompositionCandidate(pp, true));
		}

		final long elapsedTime = System.nanoTime() - startTime;
		mLogger.info(
				"LargeBlockEncoding completed in %d ms, with %d straightline sequential compositions, "
						+ "%d parallel compositions, %d 1:n/n:1 sequential compositions "
						+ "and %d complex sequential compositions.",
				elapsedTime / 1000 / 1000, mStraightlineSequentialCompositions, mParallelCompositions,
				mOneToNSequentialCompositions, mComplexSequentialCompositions);
	}

	private List<BoogieIcfgLocation> getInitialThreadLocations() {
		Stream<BoogieIcfgLocation> initialNodes = mIcfg.getInitialNodes().stream();
		if (IcfgUtils.isConcurrent(mIcfg)) {
			// As the CFG does not yet contain ForkOther edges at this point, the initial locations of thread templates
			// cannot be reached from the initial location. Hence we collect them separately.
			final var threadInits = mIcfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()
					.stream().map(fork -> mIcfg.getProcedureEntryNodes().get(fork.getNameOfForkedProcedure()));
			initialNodes = Stream.concat(initialNodes, threadInits);
		}
		return initialNodes.toList();
	}

	/**
	 * Determines if the given node is a composition candidate. If so, it is placed in the appropriate queue, depending
	 * on what kind of composition is to be performed.
	 */
	private void considerCompositionCandidate(final BoogieIcfgLocation pp, final boolean allowComplex) {
		if (PRESERVE_LOOP_HEADS_AND_LOCATIONS_OF_INTEREST
				&& (mIcfg.getLoopLocations().contains(pp) || mIcfg.getLocationsOfInterest().contains(pp))) {
			return;
		}
		mLogger.debug("Considering composition at " + pp);
		final SequentialCompositionType seq = classifySequentialCompositionNode(pp);
		if (seq == SequentialCompositionType.STRAIGHTLINE) {
			mSequentialQueue.offerLast(pp);
			mLogger.debug("decided on straightline sequential composition");
			return;
		}

		// As explained above, we prefer parallel over Y-to-V compositions.
		final List<List<CodeBlock>> parallelCompositions = computeOutgoingCandidatesForParallelComposition(pp);
		if (!parallelCompositions.isEmpty()) {
			mParallelQueue.put(pp, parallelCompositions);
			mLogger.debug("decided on parallel composition");
		} else if (seq == SequentialCompositionType.COMPLEX && allowComplex) {
			// Create a ComplexComposition object, which implements prioritization rules between complex compositions.
			final var composition = ComplexComposition.create(pp);
			mComplexSequentialQueue.offer(composition);
			if (composition.isUnavoidable()) {
				mLogger.debug("decided on (unavoidable) complex sequential composition");
			} else {
				mLogger.debug("decided on complex sequential composition");
			}
		} else {
			mLogger.debug("decided on NO composition");
		}
	}

	/**
	 * Performs a (straight-line or Y-to-V) sequential composition. Afterwards, the new predecessors and successors are
	 * again considered for further compositions.
	 */
	private void composeSequential(final BoogieIcfgLocation pp) {
		assert !pp.getIncomingEdges().isEmpty();
		assert !pp.getOutgoingEdges().isEmpty();

		final List<IcfgEdge> incomingEdges = new ArrayList<>(pp.getIncomingEdges());
		final List<IcfgEdge> outgoingEdges = new ArrayList<>(pp.getOutgoingEdges());
		final List<IcfgEdge> newEdges = new ArrayList<>();

		if (incomingEdges.size() == 1 && outgoingEdges.size() == 1) {
			mStraightlineSequentialCompositions++;
		} else if (incomingEdges.size() > 1 && outgoingEdges.size() > 1) {
			mComplexSequentialCompositions++;
			mLogger.warn("Complex %d:%d sequential composition. "
					+ "Such compositions can cause exponential blowup and should not occur in structured programs.",
					incomingEdges.size(), outgoingEdges.size());
		} else {
			mOneToNSequentialCompositions++;
		}

		for (final IcfgEdge incoming : incomingEdges) {
			for (final IcfgEdge outgoing : outgoingEdges) {
				final BoogieIcfgLocation predecessor = (BoogieIcfgLocation) incoming.getSource();
				final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.getTarget();
				final List<CodeBlock> sequence = Arrays.asList((CodeBlock) incoming, (CodeBlock) outgoing);

				final SequentialComposition comp = mCbf.constructSequentialComposition(predecessor, successor,
						mSimplifyCodeBlocks, false, sequence, CfgBuilder.SIMPLIFICATION_TECHNIQUE);

				// transfer annotations (special handling for AtomicBlockInfo, as it cannot be merged)
				ModelUtils.copyAnnotationsFiltered(incoming, comp, ann -> !(ann instanceof AtomicBlockInfo));
				ModelUtils.copyAnnotationsFiltered(outgoing, comp, ann -> !(ann instanceof AtomicBlockInfo));
				AtomicBlockInfo.mergeSequential(incoming, outgoing, comp);

				newEdges.add(comp);
			}
		}

		// remove composed edges from Icfg
		for (final IcfgEdge currentCodeblock : incomingEdges) {
			currentCodeblock.disconnectSource();
			currentCodeblock.disconnectTarget();
		}
		for (final IcfgEdge currentCodeblock : outgoingEdges) {
			currentCodeblock.disconnectSource();
			currentCodeblock.disconnectTarget();
		}

		// Continue composition where needed.
		// For correct detection, this must happen after edge removal.
		final Set<BoogieIcfgLocation> candidates = new HashSet<>();
		newEdges.forEach(e -> candidates.add((BoogieIcfgLocation) e.getSource()));
		newEdges.forEach(e -> candidates.add((BoogieIcfgLocation) e.getTarget()));
		for (final BoogieIcfgLocation candidate : candidates) {
			considerCompositionCandidate(candidate, false);
		}

		// remove location from Icfg
		final Map<DebugIdentifier, BoogieIcfgLocation> id2loc = mIcfg.getProgramPoints().get(pp.getProcedure());
		id2loc.remove(pp.getDebugIdentifier());
		mAtomicAnalysis.removeLocation(pp);
	}

	/**
	 * Performs a parallel composition. Afterwards, the predecessor and successor are again considered for further
	 * compositions.
	 */
	private void composeParallel(final BoogieIcfgLocation pp, final List<CodeBlock> outgoing) {
		mParallelCompositions++;
		final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.get(0).getTarget();

		// Compute the atomic delta for the composed edge
		final OptionalInt composedAtomicDelta;
		if (outgoing.stream().anyMatch(AtomicBlockInfo::hasAnnotation)) {
			final int[] deltas = outgoing.stream().mapToInt(AtomicBlockInfo::getAnnotatedDelta).distinct().toArray();
			assert deltas.length == 1
					: "cannot perform parallel compositions of edges with different atomic block deltas";
			composedAtomicDelta = OptionalInt.of(deltas[0]);
		} else {
			composedAtomicDelta = OptionalInt.empty();
		}

		// remove these annotations as constructParallelComposition would try to merge them (which fails)
		// (this should be fine hopefully, as a once-composed edge is never used again; unlike for seq. compositions)
		for (final var edge : outgoing) {
			AtomicBlockInfo.removeAnnotation(edge);
		}

		final var result = mCbf.constructParallelComposition(pp, successor, Collections.unmodifiableList(outgoing),
				CfgBuilder.SIMPLIFICATION_TECHNIQUE);

		// add the atomic edge annotation to the composed edge, if necessary
		if (composedAtomicDelta.isPresent()) {
			AtomicBlockInfo.addAnnotation(result, composedAtomicDelta.orElseThrow());
		}

		considerCompositionCandidate(pp, false);
		considerCompositionCandidate(successor, false);
	}

	/**
	 * Determines what kind of sequential composition (if any) should be performed at this node.
	 */
	private SequentialCompositionType classifySequentialCompositionNode(final BoogieIcfgLocation pp) {
		if (pp.getIncomingEdges().isEmpty() || pp.getOutgoingEdges().isEmpty() || mEntryNodes.contains(pp)) {
			return SequentialCompositionType.NONE;
		}

		if (DataStructureUtils.haveNonEmptyIntersection(new HashSet<>(pp.getIncomingEdges()),
				new HashSet<>(pp.getOutgoingEdges()))) {
			// do not allow loops
			return SequentialCompositionType.NONE;
		}

		final boolean edgesComposable = pp.getIncomingEdges().stream().allMatch(this::isComposableEdge)
				&& pp.getOutgoingEdges().stream().allMatch(this::isComposableEdge);
		if (!edgesComposable) {
			return SequentialCompositionType.NONE;
		}

		if (mInternalLbeMode == InternalLbeMode.ALL_EXCEPT_ATOMIC_BOUNDARIES && mAtomicAnalysis.isAtomicBoundary(pp)) {
			return SequentialCompositionType.NONE;
		}

		final boolean isStraightline = pp.getIncomingEdges().size() == 1 && pp.getOutgoingEdges().size() == 1;
		final boolean isBetweenSequencePoints = false; // TODO #FaultLocalization
		final boolean isInAtomicBlock = mAtomicAnalysis.isInsideAtomicBlock(pp);

		return switch (mInternalLbeMode) {
		// atomic boundaries already handled above, so ALL_EXCEPT_ATOMIC_BOUNDARIES and ALL are treated the same way.
		case ALL_EXCEPT_ATOMIC_BOUNDARIES, ALL:
			yield isStraightline ? SequentialCompositionType.STRAIGHTLINE : SequentialCompositionType.COMPLEX;
		case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
			// TODO #FaultLocalization
			// return isInAtomicBlock || isBetweenSequencePoints;
			throw new UnsupportedOperationException();
		case ONLY_ATOMIC_BLOCK:
			if (!isInAtomicBlock) {
				yield SequentialCompositionType.NONE;
			}
			yield isStraightline ? SequentialCompositionType.STRAIGHTLINE : SequentialCompositionType.COMPLEX;
		};
	}

	private boolean isComposableEdge(final IcfgEdge edge) {
		if (edge instanceof RootEdge || edge instanceof Call || edge instanceof Return) {
			return false;
		}
		if (edge instanceof IIcfgForkTransitionThreadCurrent || edge instanceof IIcfgForkTransitionThreadOther
				|| edge instanceof IIcfgJoinTransitionThreadCurrent || edge instanceof IIcfgJoinTransitionThreadOther) {
			return false;
		}
		assert edge instanceof StatementSequence || edge instanceof SequentialComposition
				|| edge instanceof ParallelComposition || edge instanceof Summary || edge instanceof GotoEdge
				: "unexpected type of edge: " + edge.getClass().getSimpleName();
		return true;
	}

	/**
	 * Check if ProgramPoint pp has several outgoing edges whose target is the same ProgramPoint.
	 *
	 * @return For some successor ProgramPoint the list of all outgoing edges whose target is this (successor)
	 *         ProgramPoint, if there can be such a list with more than one element. Otherwise (each outgoing edge leads
	 *         to a different ProgramPoint) return null.
	 */
	private List<List<CodeBlock>> computeOutgoingCandidatesForParallelComposition(final BoogieIcfgLocation pp) {
		return pp.getOutgoingEdges().stream()
				// cast edges to CodeBlocks
				.map(CodeBlock.class::cast)
				// filter edges that can never be composed (in parallel)
				.filter(this::isParallelComposableEdge)
				// group by successor location and atomic delta
				// (cannot compose e.g. edges entering and not entering atomic block)
				.collect(Collectors.groupingBy(
						cb -> new Pair<>((BoogieIcfgLocation) cb.getTarget(), AtomicBlockInfo.getAnnotatedDelta(cb))))
				.entrySet().stream()
				// skip trivial composition groups
				.filter(e -> e.getValue().size() > 1)
				// forget the grouping keys and just return the composable groups of edges.
				.map(Map.Entry::getValue).toList();
	}

	private boolean isParallelComposableEdge(final CodeBlock cb) {
		if (cb instanceof Return || cb instanceof Summary) {
			return false;
		}

		final var src = (BoogieIcfgLocation) cb.getSource();
		final var tgt = (BoogieIcfgLocation) cb.getTarget();

		final boolean srcAllowed;
		final boolean tgtAllowed;
		return switch (mInternalLbeMode) {
		case ALL:
			yield true;

		// TODO What is the reason for these conditions? Shouldn't parallel compositions always be ok?
		case ALL_EXCEPT_ATOMIC_BOUNDARIES:
			srcAllowed = (IcfgUtils.isConcurrent(mIcfg) && !mAtomicAnalysis.isAtomicBegin(src))
					|| mAtomicAnalysis.isInsideAtomicBlock(src);
			tgtAllowed = (IcfgUtils.isConcurrent(mIcfg) && !mAtomicAnalysis.isAtomicEnd(tgt))
					|| mAtomicAnalysis.isInsideAtomicBlock(tgt);
			yield srcAllowed && tgtAllowed;

		case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
			// TODO #FaultLocalization
			throw new UnsupportedOperationException();

		// In order to only perform compositions within atomic blocks, we have these conditions.
		// It would also be sound to return true, as more parallel compositions are not a threat to soundness.
		case ONLY_ATOMIC_BLOCK:
			srcAllowed = mAtomicAnalysis.isInsideAtomicBlock(src) || mAtomicAnalysis.isAtomicBegin(src);
			tgtAllowed = mAtomicAnalysis.isInsideAtomicBlock(tgt) || mAtomicAnalysis.isAtomicEnd(tgt);
			yield srcAllowed && tgtAllowed;
		};
	}

	// Used as entries in the mComplexSequentialCompositions priority queue.
	// Prioritizes compositions depending on whether they are unavoidable and how many edges they produce.
	private record ComplexComposition(BoogieIcfgLocation programPoint, boolean isUnavoidable, int degreeProduct)
			implements Comparable<ComplexComposition> {
		public ComplexComposition {
			assert degreeProduct > 1;
		}

		public static ComplexComposition create(final BoogieIcfgLocation programPoint) {
			// An upside-down Y-to-V composition is called "unavoidable" if it has multiple distinct successor
			// nodes, and at least one of them is terminal.
			// The primary case where this happens are assert statements, as the error location is terminal.
			// In such cases, other compositions cannot avoid the need for a complex sequential composition
			// (e.g. parallel composition of the outgoing edges is impossible).
			final boolean isUnavoidable = programPoint.getIncomingEdges().size() == 1
					&& programPoint.getOutgoingNodes().stream().anyMatch(s -> s.getOutgoingEdges().isEmpty())
					&& programPoint.getOutgoingNodes().stream().distinct().count() > 1;

			final int degreeProduct = programPoint.getIncomingEdges().size() * programPoint.getOutgoingEdges().size();
			return new ComplexComposition(programPoint, isUnavoidable, degreeProduct);
		}

		@Override
		public int compareTo(final ComplexComposition other) {
			// If two compositions concern the same program point, they should be equal.
			// This check is meant to catch accidental comparison of compositions created at different points of time,
			// with inconsistent information about the CFG structure.
			assert !programPoint.equals(other.programPoint) || equals(other)
					: "Comparing compositions with inconsistent information";

			if (isUnavoidable != other.isUnavoidable) {
				// We prioritize unavoidable upside-down Y-to-V compositions since they must occur at some point anyway,
				// and they might in turn enable other, more preferable compositions.
				// (The comparison order below is swapped intentionally, as false < true.)
				return Boolean.compare(other.isUnavoidable, isUnavoidable);
			}
			// Prefer compositions with a smaller degree product, i.e., which will produce fewer edges.
			// Again, one such composition might in turn enable other, more preferable (e.g. parallel) compositions.
			return Integer.compare(degreeProduct, other.degreeProduct);
		}
	}
}
