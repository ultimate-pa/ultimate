package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;

public class InvariantResultTransformer {

	private InvariantResultTransformer() {
		// Utility
		// This class could serve for more purposes in the future and also allow
		// instances if needed but right now it's really just to have the extraction
		// outside of other classes where it doesn't belong. In the future perhaps it could
		// post-process for several reqcheck properties such as e.g., vacuity too.
	}

	public static Set<String> extractRedundancySet(final Expression invariant) {
		final var redSet = new HashSet<String>();
		extractRedundancySetHelper(invariant, redSet);
		return redSet;
	}

	private static void extractRedundancySetHelper(final Expression expr, final HashSet<String> redSet) {
		switch (expr) {
		case final BinaryExpression binop:
			extractRedundancySetHelper(binop.getLeft(), redSet);
			extractRedundancySetHelper(binop.getRight(), redSet);
			break;
		case final UnaryExpression unop:
			extractRedundancySetHelper(unop.getExpr(), redSet);
			break;
		case final IdentifierExpression iexpr:
			final var id = iexpr.getIdentifier();
			// This check works for now as even if a variable is ill named,
			// i.e. conflicts with the program counter variables, it will just be added
			// and has to be removed manually again when looking for the redundancy reason
			// However, better ideas can be created to solve this issue in the future
			if (id.endsWith("_total_pc") || id.endsWith("_total")) {
				redSet.add(iexpr.getIdentifier().split("_ct")[0]);
			}
			break;
		default:
			break;
		}
	}
}
