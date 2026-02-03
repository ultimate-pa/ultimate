package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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

/**
 * Checks: (1) initial locations are true, (2) edges are inductive, (3) predicates are interference-stable.
 */
public class ThreadModularProofChecker {

	private final ILogger mLogger;
	private final MonolithicHoareTripleChecker mHoareTripleChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final TransFormulaToInterferencePredicate mTranslator;
	private final IDomain mDomain;

	public ThreadModularProofChecker(final ILogger logger, final CfgSmtToolkit cfgSmtToolkit,
			final RelationalPredicatePostcondition postcondition, final TransFormulaToInterferencePredicate translator,
			final IDomain domain) {
		mLogger = logger;
		mHoareTripleChecker = new MonolithicHoareTripleChecker(cfgSmtToolkit);
		mPostcondition = postcondition;
		mTranslator = translator;
		mDomain = domain;
	}

	/** Returns true if proof is valid, false otherwise. Violations are logged. */
	public boolean checkAll(final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, IPredicate> locPreds,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPreds) {

		boolean valid = true;

		// Check 1: Initial location(s) must be true
		for (final var loc : icfg.getInitialNodes()) {
			final var pred = locPreds.get(loc);
			if (pred == null || !SmtUtils.isTrueLiteral(pred.getFormula())) {
				mLogger.error("Initial location %s is not true", loc);
				valid = false;
			}
		}

		// Check 2: Hoare Triple Check
		// TODO: do we only need to check internals, since interferences might change even skips()?
		for (final var entry : locPreds.entrySet()) {
			final var pre = entry.getValue();
			for (final IcfgEdge edge : entry.getKey().getOutgoingEdges()) {
				final var post = locPreds.get(edge.getTarget());
				if (post != null && edge instanceof IIcfgInternalTransition<?>
						&& mHoareTripleChecker.checkInternal(pre, (IInternalAction) edge, post) == Validity.INVALID) {
					mLogger.error("Invalid: {%s} %s->%s {%s}", pre.getFormula(), edge.getSource(), edge.getTarget(),
							post.getFormula());
					valid = false;
				}
			}
		}

		// Check 3: Predicates must be stable under interferences
		for (final var threadEntry : threadPreds.entrySet()) {
			final String threadId = threadEntry.getKey();

			for (final var locEntry : threadEntry.getValue().entrySet()) {
				final var location = locEntry.getKey();
				final var pred = locEntry.getValue();

				// TODO: must adjust depending on self-interference
				for (final var otherEntry : threadPreds.entrySet()) {
					if (otherEntry.getKey().equals(threadId)) {
						continue;
					}
					for (final var otherLoc : otherEntry.getValue().keySet()) {
						for (final IcfgEdge edge : otherLoc.getOutgoingEdges()) {
							if (modifiesGlobals(edge.getTransformula())) {
								final IPredicate itfPred = mTranslator.translate(edge.getTransformula());
								final IPredicate postState = mPostcondition.strongestPostcondition(pred, itfPred);
								if (!mDomain.isSubsetEq(postState, pred).isTrueForAbstraction()) {
									mLogger.error("Unstable %s under edge %s->%s: P=%s", location, edge.getSource(),
											edge.getTarget(), pred.getFormula());
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

	private static boolean modifiesGlobals(final TransFormula tf) {
		return tf != null && tf.getAssignedVars().stream().anyMatch(pv -> pv.isGlobal());
	}
}
