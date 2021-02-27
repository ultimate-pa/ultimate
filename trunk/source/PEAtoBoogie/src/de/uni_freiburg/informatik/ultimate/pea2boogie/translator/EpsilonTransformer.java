package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.LiteralUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class EpsilonTransformer {

	private final Rational mEpsilon;

	public EpsilonTransformer(final Rational epsilon) {
		// mEpsilon = epsilon;
		mEpsilon = SmtUtils.toRational("11");
	}

	public Expression transform(final Expression e) {
		return e.accept(new BoogieEpsilonTransformer());
	}

	public Term transform(final Script script, final Term guardTerm) {
		return new SmtEpsilonTransformer(script).transform(guardTerm);
	}

	private final class BoogieEpsilonTransformer extends GeneratedBoogieAstTransformer {
		@Override
		public Expression transform(final BinaryExpression node) {
			switch (node.getOperator()) {
			case COMPGT:
			case COMPLT:
				return epsilonBounded(node);
			default:
				return node;
			}
		}

		private Expression epsilonBounded(final BinaryExpression node) {
			final Expression nleft = substractEpsilonIfLiteral(node.getLeft());
			final Expression nright = substractEpsilonIfLiteral(node.getRight());
			if (nleft != node.getLeft() || nright != node.getRight()) {
				return new BinaryExpression(node.getLoc(), node.getOperator(), nleft, nright);
			}
			return node;
		}

		private Expression substractEpsilonIfLiteral(final Expression n) {
			final Optional<Rational> val = LiteralUtils.toRational(n);
			if (val.isPresent()) {
				final Rational newLiteralvalue = val.get().sub(mEpsilon);
				return LiteralUtils.toExpression(n.getLoc(), newLiteralvalue, true);
			}
			return n;
		}
	}

	private final class SmtEpsilonTransformer extends TermTransformer {

		private final Script mScript;

		public SmtEpsilonTransformer(final Script script) {
			mScript = script;
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
			final String func = appTerm.getFunction().getName();
			if (func.equals("<") || func.equals(">")) {
				if (args.length != 2) {
					throw new UnsupportedOperationException("not yet implemented");
				}
				final Term[] nargs = new Term[args.length];
				for (int i = 0; i < args.length; ++i) {
					if (args[i] instanceof ConstantTerm) {
						final Rational val = SmtUtils.toRational((ConstantTerm) args[i]);
						final Rational newVal = val.sub(mEpsilon);
						nargs[i] = newVal.toTerm(SmtSortUtils.getRealSort(mScript));
					} else {
						nargs[i] = args[i];
					}
				}
				setResult(mScript.term(func, nargs));
				return;
			}
			super.convertApplicationTerm(appTerm, args);
		}
	}

}