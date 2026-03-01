package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.HashMap;
import java.util.HashSet;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ThreadModularProofChecker {

	private final MonolithicHoareTripleChecker mHoareTripleChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final Set<TermVariable> mGhostLocationVariables;
	private final ProofEdgeInterferenceTranslator mProofInterferenceTranslator;
	private final ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private final Set<String> mSelfInterferingThreads;

	public ThreadModularProofChecker(final CfgSmtToolkit cfgSmtToolkit,
			final RelationalPredicatePostcondition postcondition, final TransFormulaToInterferencePredicate translator,
			final IDomain domain, final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis threadActivityPreanalysis, final Set<String> selfInterferingThreads,
			final boolean includeInterferencePreState) {
		mHoareTripleChecker = new MonolithicHoareTripleChecker(cfgSmtToolkit);
		mPostcondition = postcondition;
		mDomain = domain;
		mGhostLocationVariables =
				ghostVariables == null ? Set.of() : Set.copyOf(new HashSet<>(ghostVariables.getLocationTermVariables()));
		mProofInterferenceTranslator =
				new ProofEdgeInterferenceTranslator(translator, postcondition, ghostVariables, includeInterferencePreState);
		mThreadActivityPreanalysis = Objects.requireNonNull(threadActivityPreanalysis);
		mSelfInterferingThreads = Set.copyOf(Objects.requireNonNull(selfInterferingThreads));
	}

	public static record CheckReport(boolean overallValid, boolean hoareChecksValid, boolean interferenceChecksValid,
			int checkedHoareTriples, int invalidHoareTriples, int checkedInterferenceTriples,
			int invalidInterferenceTriples, List<String> invalidHoareDetails, List<String> invalidInterferenceDetails) {
	}

	public boolean checkAll(final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, IPredicate> locPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		return checkAllDetailed(icfg, locPreds, threadPreds).overallValid();
	}

	public CheckReport checkAllDetailed(final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, IPredicate> locPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		boolean hoareChecksValid = true;
		boolean interferenceChecksValid = true;
		int checkedHoareTriples = 0;
		int invalidHoareTriples = 0;
		int checkedInterferenceTriples = 0;
		int invalidInterferenceTriples = 0;
		final List<String> invalidHoareDetails = new ArrayList<>();
		final List<String> invalidInterferenceDetails = new ArrayList<>();
		final Map<IPredicate, IPredicate> hoareProjectionCache = new HashMap<>();

		// Check 1: edge-local Hoare triples
		for (final var entry : locPreds.entrySet()) {
			final var pre = entry.getValue();
			if (pre == null) {
				continue;
			}
			for (final IcfgEdge edge : entry.getKey().getOutgoingEdges()) {
				final var post = locPreds.get(edge.getTarget());
				if (post == null || !(edge instanceof IIcfgInternalTransition<?>)) {
					continue;
				}
				checkedHoareTriples++;
				if (mHoareTripleChecker.checkInternal(projectAwayGhostLocations(pre, hoareProjectionCache),
						(IInternalAction) edge,
						projectAwayGhostLocations(post, hoareProjectionCache)) == Validity.INVALID) {
					hoareChecksValid = false;
					invalidHoareTriples++;
					invalidHoareDetails.add(formatInvalidHoareTriple(edge, pre, post));
				}
			}
		}

		// Check 2: predicate stability under interferences
		for (final var threadEntry : threadPreds.entrySet()) {
			final String threadId = threadEntry.getKey();
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
							final IPredicate itfPred = mProofInterferenceTranslator.tryTranslateInterferenceEdge(
									otherThreadId, otherLoc, otherLocPred, edge);
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
		final boolean valid = hoareChecksValid && interferenceChecksValid;
		return new CheckReport(valid, hoareChecksValid, interferenceChecksValid, checkedHoareTriples,
				invalidHoareTriples, checkedInterferenceTriples, invalidInterferenceTriples, invalidHoareDetails,
				invalidInterferenceDetails);
	}

	public boolean isCheckingEnabled() {
		return true;
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

	private static String formatInvalidHoareTriple(final IcfgEdge edge, final IPredicate pre, final IPredicate post) {
		return String.format(
				"Invalid Hoare triple: src=%s tgt=%s edge=%s pre=%s post=%s",
				edge.getSource(), edge.getTarget(), edge, pre, post);
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
