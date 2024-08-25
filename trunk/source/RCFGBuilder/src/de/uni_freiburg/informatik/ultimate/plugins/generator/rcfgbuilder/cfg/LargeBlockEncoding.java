package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;

class LargeBlockEncoding {
	/**
	 * Defines which statements will be composed.
	 */
	enum InternalLbeMode {
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
	private final HashDeque<BoogieIcfgLocation> mComplexSequentialQueue = new HashDeque<>();

	private final Map<BoogieIcfgLocation, List<CodeBlock>> mParallelQueue = new HashMap<>();

	public LargeBlockEncoding(final IUltimateServiceProvider services, final BoogieIcfgContainer icfg,
			final CodeBlockFactory cbf, final InternalLbeMode internalLbeMode) {
		mServices = services;
		mIcfg = icfg;
		mCbf = cbf;
		mInternalLbeMode = internalLbeMode;
		mLogger = services.getLoggingService().getLogger(LargeBlockEncoding.class);
		mSimplifyCodeBlocks = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(RcfgPreferenceInitializer.LABEL_SIMPLIFY);
		mEntryNodes = new HashSet<>(mIcfg.getProcedureEntryNodes().values());
		mAtomicAnalysis = new AtomicBlockAnalyzer(mIcfg);

		// initialize queues of locations that are candidates for different kind of compositions
		IcfgUtils.getAllLocations(mIcfg).forEach(pp -> considerCompositionCandidate(pp, true));

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
				final BoogieIcfgLocation superfluousPP = mComplexSequentialQueue.pollFirst();
				composeSequential(superfluousPP);
				mLogger.debug("Complex sequential composition at %s", superfluousPP);
			}

			while (mSequentialQueue.isEmpty() && !mParallelQueue.isEmpty()) {
				final Entry<BoogieIcfgLocation, List<CodeBlock>> superfluous =
						mParallelQueue.entrySet().iterator().next();
				final BoogieIcfgLocation pp = superfluous.getKey();
				final List<CodeBlock> outgoing = superfluous.getValue();
				mParallelQueue.remove(pp);
				composeParallel(pp, outgoing);
				mLogger.debug("parallel composition at %s", pp);
			}

			while (!mSequentialQueue.isEmpty()) {
				final BoogieIcfgLocation superfluousPP = mSequentialQueue.pollFirst();
				composeSequential(superfluousPP);
				mLogger.debug("sequential composition at %s", superfluousPP);
			}

			mComplexSequentialQueue.clear();
			mParallelQueue.clear();
			mSequentialQueue.clear();

			IcfgUtils.getAllLocations(mIcfg).forEach(pp -> considerCompositionCandidate(pp, true));
		}
	}

	/**
	 * Determines if the given node is a composition candidate. If so, it is placed in the appropriate queue, depending
	 * on what kind of composition is to be performed.
	 */
	private void considerCompositionCandidate(final BoogieIcfgLocation pp, final boolean allowComplex) {
		mLogger.debug("Considering composition at " + pp);
		final SequentialCompositionType seq = classifySequentialCompositionNode(pp);
		if (seq == SequentialCompositionType.STRAIGHTLINE) {
			mSequentialQueue.offerLast(pp);
			mLogger.debug("decided on straightline sequential composition");
			return;
		}

		// As explained above, we prefer parallel over Y-to-V compositions.
		final List<CodeBlock> list = computeOutgoingCandidatesForParallelComposition(pp);
		if (list != null) {
			mParallelQueue.put(pp, list);
			mLogger.debug("decided on parallel composition");
		} else if (seq == SequentialCompositionType.COMPLEX && allowComplex) {
			// An upside-down Y-to-V composition is called "unavoidable" if it has multiple distinct successor
			// nodes, and at least one of them is terminal.
			// The primary case where this happens are assert statements, as the error location is terminal.
			// In such cases, other compositions cannot avoid the need for a complex sequential composition
			// (e.g. parallel composition of the outgoing edges is impossible).
			final boolean isUnavoidable = pp.getIncomingEdges().size() == 1
					&& pp.getOutgoingNodes().stream().anyMatch(s -> s.getOutgoingEdges().isEmpty())
					&& pp.getOutgoingNodes().stream().distinct().count() > 1;

			// We prioritize unavoidable upside-down Y-to-V compositions since they must occur at some point anyway,
			// and they might in turn enable other, more preferable compositions.
			if (isUnavoidable) {
				mComplexSequentialQueue.offerFirst(pp);
				mLogger.debug("decided on (unavoidable) complex sequential composition");
			} else {
				mComplexSequentialQueue.offerLast(pp);
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

		if (incomingEdges.size() > 1 && outgoingEdges.size() > 1) {
			mLogger.warn("Complex %d:%d sequential composition. "
					+ "Such compositions can cause exponential blowup and should not occur in structured programs.",
					incomingEdges.size(), outgoingEdges.size());
		}

		for (final IcfgEdge incoming : incomingEdges) {
			for (final IcfgEdge outgoing : outgoingEdges) {
				final BoogieIcfgLocation predecessor = (BoogieIcfgLocation) incoming.getSource();
				final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.getTarget();
				final List<CodeBlock> sequence = Arrays.asList((CodeBlock) incoming, (CodeBlock) outgoing);

				final SequentialComposition comp =
						mCbf.constructSequentialComposition(predecessor, successor, mSimplifyCodeBlocks, false,
								sequence, CfgBuilder.XNF_CONVERSION_TECHNIQUE, CfgBuilder.SIMPLIFICATION_TECHNIQUE);
				ModelUtils.mergeAnnotations(comp, incoming, outgoing);
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
		final BoogieIcfgLocation successor = (BoogieIcfgLocation) outgoing.get(0).getTarget();
		mCbf.constructParallelComposition(pp, successor, Collections.unmodifiableList(outgoing),
				CfgBuilder.XNF_CONVERSION_TECHNIQUE, CfgBuilder.SIMPLIFICATION_TECHNIQUE);
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

		switch (mInternalLbeMode) {
		case ALL_EXCEPT_ATOMIC_BOUNDARIES:
			// atomic boundaries already handled above, so fall-through to the case for ALL
		case ALL:
			if (isStraightline) {
				return SequentialCompositionType.STRAIGHTLINE;
			}
			if (isInAtomicBlock || isBetweenSequencePoints) {
				// Y-V currently unsupported outside atomic blocks (implementation cannot handle loops properly)
				// TODO (Dominik 2020-09-16) Check if above comment still holds after Y-to-V fix, may work now (as
				// loop entry is reverse Y-to-V).
				return SequentialCompositionType.COMPLEX;
			}
			return SequentialCompositionType.NONE;
		case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
			// TODO #FaultLocalization
			// return isInAtomicBlock || isBetweenSequencePoints;
			throw new UnsupportedOperationException();
		case ONLY_ATOMIC_BLOCK:
			if (!isInAtomicBlock) {
				return SequentialCompositionType.NONE;
			}
			if (isStraightline) {
				return SequentialCompositionType.STRAIGHTLINE;
			}
			return SequentialCompositionType.COMPLEX;
		default:
			throw new AssertionError("unknown value " + mInternalLbeMode);
		}
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
				|| edge instanceof ParallelComposition || edge instanceof Summary
				|| edge instanceof GotoEdge : "unexpected type of edge: " + edge.getClass().getSimpleName();
		return true;
	}

	/**
	 * Check if ProgramPoint pp has several outgoing edges whose target is the same ProgramPoint.
	 *
	 * @return For some successor ProgramPoint the list of all outgoing edges whose target is this (successor)
	 *         ProgramPoint, if there can be such a list with more than one element. Otherwise (each outgoing edge leads
	 *         to a different ProgramPoint) return null.
	 */
	private List<CodeBlock> computeOutgoingCandidatesForParallelComposition(final BoogieIcfgLocation pp) {
		if (!canBePredecessorOfParallelComposition(pp)) {
			return null;
		}
		List<CodeBlock> result = null;
		final Map<BoogieIcfgLocation, List<CodeBlock>> succ2edge = new HashMap<>();
		for (final IcfgEdge edge : pp.getOutgoingEdges()) {
			if (!(edge instanceof Return) && !(edge instanceof Summary)) {
				final CodeBlock cb = (CodeBlock) edge;
				final BoogieIcfgLocation succ = (BoogieIcfgLocation) cb.getTarget();
				if (canBeSuccessorOfParallelComposition(succ)) {
					final List<CodeBlock> edges = succ2edge.computeIfAbsent(succ, x -> new ArrayList<>());
					edges.add(cb);
					if (result == null && edges.size() > 1) {
						result = edges;
					}
				}
			}
		}
		return result;
	}

	private boolean canBePredecessorOfParallelComposition(final BoogieIcfgLocation pp) {
		switch (mInternalLbeMode) {
		case ALL:
			return true;
		case ALL_EXCEPT_ATOMIC_BOUNDARIES:
			return (IcfgUtils.isConcurrent(mIcfg) && !mAtomicAnalysis.isAtomicBegin(pp))
					|| mAtomicAnalysis.isInsideAtomicBlock(pp);
		case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
			// TODO #FaultLocalization
			throw new UnsupportedOperationException();
		case ONLY_ATOMIC_BLOCK:
			// In order to only perform compositions within atomic blocks, we have this condition.
			// It would also be sound to return true, as more parallel compositions are not a threat to soundness.
			return mAtomicAnalysis.isInsideAtomicBlock(pp);
		default:
			throw new AssertionError("unknown value " + mInternalLbeMode);
		}
	}

	private boolean canBeSuccessorOfParallelComposition(final BoogieIcfgLocation pp) {
		switch (mInternalLbeMode) {
		case ALL:
			return true;
		case ALL_EXCEPT_ATOMIC_BOUNDARIES:
			return (IcfgUtils.isConcurrent(mIcfg) && !mAtomicAnalysis.isAtomicEnd(pp))
					|| mAtomicAnalysis.isInsideAtomicBlock(pp);
		case ATOMIC_BLOCK_AND_INBETWEEN_SEQUENCE_POINTS:
			// TODO #FaultLocalization
			throw new UnsupportedOperationException();
		case ONLY_ATOMIC_BLOCK:
			// In order to only perform compositions within atomic blocks, we have this condition.
			// It would also be sound to return true, as more parallel compositions are not a threat to soundness.
			//
			// In order to catch all possible compositions within atomic blocks,
			// we would also have to allow error locations and possibly (see atomicModeCorrect) return / exit nodes.
			// However, this is not strictly necessary, as less parallel compositions are not a threat to soundness.
			return mAtomicAnalysis.isInsideAtomicBlock(pp);
		default:
			throw new AssertionError("unknown value " + mInternalLbeMode);
		}
	}
}