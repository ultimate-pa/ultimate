package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
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
			final ThreadActivityPreanalysis threadActivityPreanalysis, final Set<String> selfInterferingThreads,
			final boolean includeInterferencePreState) {
		mIcfg = Objects.requireNonNull(icfg);
		mHoareTripleChecker = new MonolithicHoareTripleChecker(icfg.getCfgSmtToolkit());
		mPostcondition = postcondition;
		mDomain = domain;
		mGhostLocationVariables = ghostVariables == null ? Set.of()
				: Set.copyOf(new HashSet<>(ghostVariables.getLocationTermVariables()));
		mProofInterferenceTranslator = new ProofEdgeInterferenceTranslator(translator, postcondition, ghostVariables,
				includeInterferencePreState);
		mThreadActivityPreanalysis = Objects.requireNonNull(threadActivityPreanalysis);
		mSelfInterferingThreads = Set.copyOf(Objects.requireNonNull(selfInterferingThreads));
	}

	public static record CheckReport(boolean overallValid, boolean initialChecksValid, boolean hoareChecksValid,
			boolean interferenceChecksValid, int checkedInitialStates, int invalidInitialStates,
			int checkedHoareTriples, int invalidHoareTriples, int checkedInterferenceTriples,
			int invalidInterferenceTriples, List<String> invalidInitialDetails, List<String> invalidHoareDetails,
			List<String> invalidInterferenceDetails) {
	}

	public void checkAllOrThrow(final Map<IcfgLocation, IPredicate> locationPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds, final ILogger logger) {
		logger.info("Thread-modular proof checking started");
		final CheckReport report = checkAllDetailed(locationPreds, threadPreds);
		if (report.overallValid()) {
			logger.info(
					"Thread-modular proof checking passed (%d initial checks, %d hoare checks, %d interference checks)",
					report.checkedInitialStates(), report.checkedHoareTriples(), report.checkedInterferenceTriples());
			return;
		}

		if (!report.initialChecksValid()) {
			logger.error("Proof check 'Initial state checks': FAILED (%d checked, %d invalid)",
					report.checkedInitialStates(), report.invalidInitialStates());
			logFirstInvalidDetail(logger, "Initial state checks", report.invalidInitialDetails());
		}
		if (!report.hoareChecksValid()) {
			logger.error("Proof check 'Hoare edge checks': FAILED (%d checked, %d invalid)",
					report.checkedHoareTriples(), report.invalidHoareTriples());
			logFirstInvalidDetail(logger, "Hoare edge checks", report.invalidHoareDetails());
		}
		if (!report.interferenceChecksValid()) {
			logger.error("Proof check 'Interference stability checks': FAILED (%d checked, %d invalid)",
					report.checkedInterferenceTriples(), report.invalidInterferenceTriples());
			logFirstInvalidDetail(logger, "Interference stability checks", report.invalidInterferenceDetails());
		}
		throw new IllegalStateException("Thread-modular proof checking failed");
	}

	public CheckReport checkAllDetailed(final Map<IcfgLocation, IPredicate> locationPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		boolean initialChecksValid = true;
		boolean hoareChecksValid = true;
		boolean interferenceChecksValid = true;
		int checkedInitialStates = 0;
		int invalidInitialStates = 0;
		int checkedHoareTriples = 0;
		int invalidHoareTriples = 0;
		int checkedInterferenceTriples = 0;
		int invalidInterferenceTriples = 0;
		final List<String> invalidInitialDetails = new ArrayList<>();
		final List<String> invalidHoareDetails = new ArrayList<>();
		final List<String> invalidInterferenceDetails = new ArrayList<>();
		final Map<IPredicate, IPredicate> hoareProjectionCache = new HashMap<>();

		for (final IcfgLocation initLoc : mIcfg.getInitialNodes()) {
			checkedInitialStates++;
			final IPredicate predicate = locationPreds.get(initLoc);
			if (predicate == null || !SmtUtils.isTrueLiteral(predicate.getFormula())) {
				initialChecksValid = false;
				invalidInitialStates++;
				invalidInitialDetails.add(String.format("Initial location %s is not true", initLoc));
			}
		}

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
				checkedHoareTriples++;
				final IPredicate projectedPre = projectAwayGhostLocations(pre, hoareProjectionCache);
				final IPredicate projectedPost = projectAwayGhostLocations(post, hoareProjectionCache);
				if (mHoareTripleChecker.checkInternal(projectedPre, (IInternalAction) edge,
						projectedPost) == Validity.INVALID) {
					hoareChecksValid = false;
					invalidHoareTriples++;
					invalidHoareDetails.add(formatInvalidHoareCheck(entry.getKey(), edge, pre, post));
				}
			}
		}

		for (final var threadEntry : threadPreds.entrySet()) {
			final String threadId = threadEntry.getKey();
			configureDomainContext(threadId);
			final Map<IcfgLocation, IPredicate> targetThreadStates = threadEntry.getValue();
			if (targetThreadStates == null) {
				continue;
			}

			for (final var locEntry : targetThreadStates.entrySet()) {
				final IcfgLocation location = locEntry.getKey();
				final var pred = locEntry.getValue();
				if (pred == null) {
					continue;
				}

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
							checkedInterferenceTriples++;
							final IPredicate postState = mPostcondition.strongestPostcondition(pred, itfPred);
							if (!mDomain.isSubsetEq(postState, pred).isTrueForAbstraction()) {
								interferenceChecksValid = false;
								invalidInterferenceTriples++;
								invalidInterferenceDetails.add(formatInvalidInterferenceCheck(threadId, location, pred,
										otherThreadId, otherLoc, otherLocPred, edge, itfPred, postState));
							}
						}
					}
				}
			}
		}
		final boolean overallValid = initialChecksValid && hoareChecksValid && interferenceChecksValid;
		return new CheckReport(overallValid, initialChecksValid, hoareChecksValid, interferenceChecksValid,
				checkedInitialStates, invalidInitialStates, checkedHoareTriples, invalidHoareTriples,
				checkedInterferenceTriples, invalidInterferenceTriples, invalidInitialDetails, invalidHoareDetails,
				invalidInterferenceDetails);
	}

	private void configureDomainContext(final String threadId) {
		if (mDomain instanceof final IThreadLocalDomainContext threadLocalDomainContext) {
			threadLocalDomainContext.setCurrentThreadId(threadId);
		}
	}

	public boolean isCheckingEnabled() {
		return true;
	}

	private static void logFirstInvalidDetail(final ILogger logger, final String checkName,
			final List<String> details) {
		if (!details.isEmpty()) {
			logger.error("  %s: %s", checkName, details.get(0));
		}
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
		if (!containsAnyGhostLocationVariable(predicate.getFormula())) {
			projectionCache.put(predicate, predicate);
			return predicate;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(predicate.getFormula(),
				mGhostLocationVariables, mPostcondition.getServices(), mPostcondition.getManagedScript());
		final IPredicate result = mPostcondition.getPredicateFactory().newPredicate(projected);
		projectionCache.put(predicate, result);
		return result;
	}

	private boolean containsAnyGhostLocationVariable(final Term formula) {
		for (final TermVariable freeVar : formula.getFreeVars()) {
			if (mGhostLocationVariables.contains(freeVar)) {
				return true;
			}
		}
		return false;
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
