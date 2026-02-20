package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class ThreadModularProofChecker {

	private final MonolithicHoareTripleChecker mHoareTripleChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final IDomain mDomain;
	private final boolean mGhostInstrumentationEnabled;
	private final boolean mIncludeInterferencePreState;

	public ThreadModularProofChecker(final CfgSmtToolkit cfgSmtToolkit,
			final RelationalPredicatePostcondition postcondition, final TransFormulaToInterferencePredicate translator,
			final IDomain domain, final boolean ghostInstrumentationEnabled,
			final boolean includeInterferencePreState) {
		mHoareTripleChecker = new MonolithicHoareTripleChecker(cfgSmtToolkit);
		mPostcondition = postcondition;
		mTranslator = translator;
		mDomain = domain;
		mGhostInstrumentationEnabled = ghostInstrumentationEnabled;
		mIncludeInterferencePreState = includeInterferencePreState;
	}

	public boolean checkAll(final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, IPredicate> locPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {
		boolean valid = true;
		if (mGhostInstrumentationEnabled) {
			// Hoare checks use uninstrumented edges and ignore ghost updates
			return true;
		}

		// Check 1: edge-local Hoare triples
		for (final var entry : locPreds.entrySet()) {
			final var pre = entry.getValue();
			for (final IcfgEdge edge : entry.getKey().getOutgoingEdges()) {
				final var post = locPreds.get(edge.getTarget());
				if (post != null && edge instanceof IIcfgInternalTransition<?>
						&& mHoareTripleChecker.checkInternal(pre, (IInternalAction) edge, post) == Validity.INVALID) {
					valid = false;
				}
			}
		}

		// Check 2: predicate stability under interferences
		for (final var threadEntry : threadPreds.entrySet()) {
			final String threadId = threadEntry.getKey();

			for (final var locEntry : threadEntry.getValue().entrySet()) {
				final var location = locEntry.getKey();
				final var pred = locEntry.getValue();

				for (final var otherEntry : threadPreds.entrySet()) {
					if (otherEntry.getKey().equals(threadId)) {
						continue;
					}
					for (final var otherLocEntry : otherEntry.getValue().entrySet()) {
						final IcfgLocation otherLoc = otherLocEntry.getKey();
						final IPredicate otherLocPred = otherLocEntry.getValue();
						if (mIncludeInterferencePreState && otherLocPred == null) {
							// Mirrors extraction behavior when includePreState=true.
							continue;
						}
						for (final IcfgEdge edge : otherLoc.getOutgoingEdges()) {
							if (modifiesGlobals(edge.getTransformula())) {
								IPredicate itfPred = mTranslator.translateForInterference(edge.getTransformula(),
										otherEntry.getKey(), otherLoc, edge.getTarget());
								if (mIncludeInterferencePreState && otherLocPred != null) {
									itfPred = withSourcePreState(otherLocPred, itfPred);
								}
								final IPredicate postState = mPostcondition.strongestPostcondition(pred, itfPred);
								if (!mDomain.isSubsetEq(postState, pred).isTrueForAbstraction()) {
									valid = false;
								}
							}
						}
					}
				}
			}
		}
		return valid;
	}

	private IPredicate withSourcePreState(final IPredicate sourcePreState, final IPredicate edgeInterference) {
		final var script = mPostcondition.getManagedScript().getScript();
		return mPostcondition.getPredicateFactory()
				.newPredicate(SmtUtils.and(script, sourcePreState.getFormula(), edgeInterference.getFormula()));
	}

	private static boolean modifiesGlobals(final TransFormula tf) {
		return tf != null && tf.getAssignedVars().stream().anyMatch(pv -> pv.isGlobal());
	}
}
