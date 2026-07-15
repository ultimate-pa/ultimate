package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ThreadModularProofChecker {

	private final IIcfg<IcfgLocation> mIcfg;
	private final MonolithicHoareTripleChecker mHoareTripleChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final Set<TermVariable> mGhostLocationVariables;
	private final ProofEdgeInterferenceTranslator mProofInterferenceTranslator;
	private final ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private final Set<String> mSelfInterferingThreads;

	public ThreadModularProofChecker(final IIcfg<IcfgLocation> icfg,
			final RelationalPredicatePostcondition postcondition, final TransFormulaToInterferencePredicate translator,
			final IDomain domain, final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis threadActivityPreanalysis) {
		mIcfg = Objects.requireNonNull(icfg);
		mHoareTripleChecker = new MonolithicHoareTripleChecker(icfg.getCfgSmtToolkit());
		mPostcondition = postcondition;
		mDomain = domain;
		mGhostLocationVariables =
				ghostVariables == null ? Set.of() : Set.copyOf(ghostVariables.getLocationTermVariables());
		mProofInterferenceTranslator = new ProofEdgeInterferenceTranslator(translator, postcondition, ghostVariables);
		mThreadActivityPreanalysis = Objects.requireNonNull(threadActivityPreanalysis);
		mSelfInterferingThreads = threadActivityPreanalysis.getMultiForkedThreads();
	}

	public void checkAllOrThrow(final Map<IcfgLocation, IPredicate> locationPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds, final ILogger logger) {
		logger.info("Thread-modular proof checking started");
		final PhaseTally initial = checkInitialStates(locationPreds);
		final PhaseTally hoare = checkHoareTriples(locationPreds);
		final PhaseTally interference = checkInterferenceStability(threadPreds);
		if (initial.valid() && hoare.valid() && interference.valid()) {
			logger.info(
					"Thread-modular proof checking passed (%d initial checks, %d hoare checks, %d interference checks)",
					initial.checked(), hoare.checked(), interference.checked());
			return;
		}
		logPhaseFailure(logger, "Initial state checks", initial);
		logPhaseFailure(logger, "Hoare edge checks", hoare);
		logPhaseFailure(logger, "Interference stability checks", interference);
		throw new IllegalStateException("Thread-modular proof checking failed");
	}

	private static void logPhaseFailure(final ILogger logger, final String checkName, final PhaseTally tally) {
		if (tally.valid()) {
			return;
		}
		logger.error("Proof check '%s': FAILED (%d checked, %d invalid)", checkName, tally.checked(), tally.invalid());
		logger.error("  %s: %s", checkName, tally.details().get(0));
	}

	private record PhaseTally(int checked, int invalid, List<String> details) {
		boolean valid() {
			return invalid == 0;
		}
	}

	private PhaseTally checkInitialStates(final Map<IcfgLocation, IPredicate> locationPreds) {
		int checked = 0;
		final List<String> details = new ArrayList<>();
		for (final IcfgLocation initLoc : mIcfg.getInitialNodes()) {
			checked++;
			final IPredicate predicate = locationPreds.get(initLoc);
			if (predicate == null || !SmtUtils.isTrueLiteral(predicate.getFormula())) {
				details.add(String.format("Initial location %s is not true", initLoc));
			}
		}
		return new PhaseTally(checked, details.size(), details);
	}

	private PhaseTally checkHoareTriples(final Map<IcfgLocation, IPredicate> locationPreds) {
		int checked = 0;
		final List<String> details = new ArrayList<>();
		final Map<IPredicate, IPredicate> projectionCache = new HashMap<>();
		for (final var entry : locationPreds.entrySet()) {
			final IPredicate pre = entry.getValue();
			if (pre == null) {
				continue;
			}
			for (final IcfgEdge edge : entry.getKey().getOutgoingEdges()) {
				final IPredicate post = locationPreds.get(edge.getTarget());
				if (post == null || !(edge instanceof IIcfgInternalTransition<?>)) {
					continue;
				}
				checked++;
				final IPredicate projectedPre = projectAwayGhostLocations(pre, projectionCache);
				final IPredicate projectedPost = projectAwayGhostLocations(post, projectionCache);
				if (mHoareTripleChecker.checkInternal(projectedPre, (IInternalAction) edge,
						projectedPost) == Validity.INVALID) {
					details.add(formatInvalidHoareCheck(entry.getKey(), edge, pre, post));
				}
			}
		}
		return new PhaseTally(checked, details.size(), details);
	}

	private PhaseTally checkInterferenceStability(final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		int checked = 0;
		final List<String> details = new ArrayList<>();
		for (final var threadEntry : threadPreds.entrySet()) {
			final String threadId = threadEntry.getKey();
			IThreadLocalDomainContext.setIfApplicable(mDomain, threadId);
			final Map<IcfgLocation, IPredicate> targetThreadStates = threadEntry.getValue();
			if (targetThreadStates == null) {
				continue;
			}
			for (final var locEntry : targetThreadStates.entrySet()) {
				final IcfgLocation location = locEntry.getKey();
				final IPredicate pred = locEntry.getValue();
				if (pred == null) {
					continue;
				}
				checked += checkInterferenceAtLocation(threadPreds, threadId, location, pred, details);
			}
		}
		return new PhaseTally(checked, details.size(), details);
	}

	private int checkInterferenceAtLocation(final Map<String, Map<IcfgLocation, IPredicate>> threadPreds,
			final String threadId, final IcfgLocation location, final IPredicate pred, final List<String> details) {
		int checked = 0;
		for (final var otherEntry : threadPreds.entrySet()) {
			final String otherThreadId = otherEntry.getKey();
			if (otherThreadId.equals(threadId) && !mSelfInterferingThreads.contains(threadId)) {
				continue;
			}
			if (!mThreadActivityPreanalysis.mayBeActiveAt(location, otherThreadId)) {
				continue;
			}
			final Map<IcfgLocation, IPredicate> otherThreadStates = otherEntry.getValue();
			if (otherThreadStates == null) {
				continue;
			}
			for (final var otherLocEntry : otherThreadStates.entrySet()) {
				final IcfgLocation otherLoc = otherLocEntry.getKey();
				final IPredicate otherLocPred = otherLocEntry.getValue();
				for (final IcfgEdge edge : otherLoc.getOutgoingEdges()) {
					final IPredicate itfPred = mProofInterferenceTranslator
							.tryTranslateInterferenceEdge(otherThreadId, otherLoc, otherLocPred, edge);
					if (itfPred == null) {
						continue;
					}
					checked++;
					final IPredicate postState = mPostcondition.strongestPostcondition(pred, itfPred);
					if (!mDomain.isSubsetEq(postState, pred).isTrueForAbstraction()) {
						details.add(formatInvalidInterferenceCheck(threadId, location, pred, otherThreadId, otherLoc,
								otherLocPred, edge, itfPred, postState));
					}
				}
			}
		}
		return checked;
	}

	private IPredicate projectAwayGhostLocations(final IPredicate predicate,
			final Map<IPredicate, IPredicate> projectionCache) {
		if (mGhostLocationVariables.isEmpty()) {
			return predicate;
		}
		final IPredicate cached = projectionCache.get(predicate);
		if (cached != null) {
			return cached;
		}
		if (!RelationalPredicateUtils.hasFreeVarIn(predicate.getFormula(), mGhostLocationVariables)) {
			projectionCache.put(predicate, predicate);
			return predicate;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(predicate.getFormula(),
				mGhostLocationVariables, mPostcondition.getServices(), mPostcondition.getManagedScript());
		final IPredicate result = mPostcondition.getPredicateFactory().newPredicate(projected);
		projectionCache.put(predicate, result);
		return result;
	}

	private static String formatInvalidHoareCheck(final IcfgLocation source, final IcfgEdge edge,
			final IPredicate sourcePredicate, final IPredicate targetPredicate) {
		return String.format("Invalid Hoare check: sourceLoc=%s targetLoc=%s edge=%s pre=%s post=%s", source,
				edge.getTarget(), edge, sourcePredicate, targetPredicate);
	}

	private static String formatInvalidInterferenceCheck(final String targetThreadId, final IcfgLocation targetLocation,
			final IPredicate targetPredicate, final String sourceThreadId, final IcfgLocation sourceLocation,
			final IPredicate sourcePredicate, final IcfgEdge edge, final IPredicate interferencePredicate,
			final IPredicate postState) {
		return String.format(
				"Invalid interference check: targetThread=%s targetLoc=%s targetPred=%s sourceThread=%s sourceLoc=%s sourcePred=%s edge=%s itf=%s post=%s",
				targetThreadId, targetLocation, targetPredicate, sourceThreadId, sourceLocation, sourcePredicate, edge,
				interferencePredicate, postState);
	}
}
