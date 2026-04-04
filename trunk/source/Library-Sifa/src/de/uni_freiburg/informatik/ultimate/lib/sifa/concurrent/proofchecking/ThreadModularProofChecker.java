package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public class ThreadModularProofChecker {

	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;
	private final ProofEdgeInterferenceTranslator mProofInterferenceTranslator;
	private final ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private final Set<String> mSelfInterferingThreads;

	public ThreadModularProofChecker(final RelationalPredicatePostcondition postcondition,
			final TransFormulaToInterferencePredicate translator, final IDomain domain,
			final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis threadActivityPreanalysis, final Set<String> selfInterferingThreads,
			final boolean includeInterferencePreState) {
		mPostcondition = postcondition;
		mDomain = domain;
		mProofInterferenceTranslator =
				new ProofEdgeInterferenceTranslator(translator, postcondition, ghostVariables, includeInterferencePreState);
		mThreadActivityPreanalysis = Objects.requireNonNull(threadActivityPreanalysis);
		mSelfInterferingThreads = Set.copyOf(Objects.requireNonNull(selfInterferingThreads));
	}

	public static record CheckReport(boolean overallValid, boolean hoareChecksValid, boolean interferenceChecksValid,
			int checkedHoareTriples, int invalidHoareTriples, int checkedInterferenceTriples,
			int invalidInterferenceTriples, List<String> invalidHoareDetails, List<String> invalidInterferenceDetails) {
	}

	public boolean checkAll(final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		return checkAllDetailed(threadPreds).overallValid();
	}

	public CheckReport checkAllDetailed(final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		boolean interferenceChecksValid = true;
		int checkedHoareTriples = 0;
		int invalidHoareTriples = 0;
		int checkedInterferenceTriples = 0;
		int invalidInterferenceTriples = 0;
		final List<String> invalidHoareDetails = new ArrayList<>();
		final List<String> invalidInterferenceDetails = new ArrayList<>();

		// Check: predicate stability under interferences
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
		return new CheckReport(interferenceChecksValid, true, interferenceChecksValid, checkedHoareTriples,
				invalidHoareTriples, checkedInterferenceTriples, invalidInterferenceTriples, invalidHoareDetails,
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
