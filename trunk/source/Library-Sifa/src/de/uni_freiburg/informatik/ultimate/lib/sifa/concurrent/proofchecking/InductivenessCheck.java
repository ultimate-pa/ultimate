package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * Checks Hoare triple validity: {pre} edge {post}.
 */
public class InductivenessCheck {

	private final IHoareTripleChecker mHoareTripleChecker;

	public InductivenessCheck(final IHoareTripleChecker hoareTripleChecker) {
		mHoareTripleChecker = hoareTripleChecker;
	}

	public ProofCheckResult check(final Map<IcfgLocation, IPredicate> locationPredicates) {
		final List<String> violations = new ArrayList<>();

		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationPredicates.entrySet()) {
			final IPredicate pre = entry.getValue();
			for (final IcfgEdge edge : entry.getKey().getOutgoingEdges()) {
				final String violation = checkEdge(pre, edge, locationPredicates.get(edge.getTarget()));
				if (violation != null) {
					violations.add(violation);
				}
			}
		}

		return violations.isEmpty() ? ProofCheckResult.valid() : ProofCheckResult.invalid(violations);
	}

	private String checkEdge(final IPredicate pre, final IcfgEdge edge, final IPredicate post) {
		// TODO: do we only need to check internals, since interferences might change even skips() ?
		if (post == null || !(edge instanceof IIcfgInternalTransition<?>)) {
			return null;
		}

		final Validity result = mHoareTripleChecker.checkInternal(pre, (IInternalAction) edge, post);
		if (result == Validity.INVALID) {
			return String.format("Invalid triple: {%s} %s -> %s {%s}", pre.getFormula(), edge.getSource(),
					edge.getTarget(), post.getFormula());
		}
		return null;
	}
}
