package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

/**
 * {@link Decision} expressed by a BoogieAST Expression.
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 */
public class BoogieBooleanExpressionDecision extends Decision {

	private final Expression mExpression;

	/**
	 *
	 * @param expression
	 *            A Boogie expression which evaluates to boolean but has no boolean expressions as children.
	 */
	public BoogieBooleanExpressionDecision(final Expression expression) {
		mExpression = expression;
	}

	public Expression getExpression() {
		return mExpression;
	}

	/**
	 * Create an boogie expression constraint and enclosing CDD
	 *
	 * @param var
	 *            the condition that must hold.
	 */
	public static CDD create(final Expression e) {
		return CDD.create(new BoogieBooleanExpressionDecision(e), CDD.trueChilds);
	}

	@Override
	public int compareTo(final Object o) {
		if (!(o instanceof BoogieBooleanExpressionDecision)) {
			return 1;
		}

		// TODO: is there somethin better than a string comparison for that
		return ((BoogieBooleanExpressionDecision) o).getExpression().toString().compareTo(mExpression.toString());

	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof BoogieBooleanExpressionDecision)) {
			return false;
		}
		if (!mExpression.equals(((BoogieBooleanExpressionDecision) o).getExpression())) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		return mExpression.hashCode();
	}

	@Override
	public Decision prime() {
		return this.prime(null);
	}

	@Override
	public Decision unprime() {
		return this.unprime(null);
	}

	@Override
	public Decision unprime(final String ignore) {
		final BoogieRemovePrimeIdentifierTransformer bpit = new BoogieRemovePrimeIdentifierTransformer();
		bpit.setIgnore(ignore);
		final Expression primed = bpit.processExpression(mExpression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public Decision prime(final String ignore) {
		final BoogiePrimeIdentifierTransformer bpit = new BoogiePrimeIdentifierTransformer();
		bpit.setIgnore(ignore);
		final Expression primed = bpit.processExpression(mExpression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public String toString(final int child) {
		if (child != 0) {
			final BoogieLocation loc = new BoogieLocation("", 0, 0, 0, 0, false);
			return BoogiePrettyPrinter.print(new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, mExpression));
		}
		return BoogiePrettyPrinter.print(mExpression);
	}

	@Override
	public String toSmtString(final int child) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toTexString(final int child) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toUppaalString(final int child) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String getVar() {
		throw new UnsupportedOperationException(
				"getVar not supported by BoogieBooleanExpressionDecision (use getVars)!");
	}

	/**
	 * Collects variable names and types from the expression.
	 *
	 * @return Map: ident -> type
	 */
	public Map<String, String> getVars() {
		final Map<String, String> vars = new HashMap<>();

		final BoogieIdentifierCollector collector = new BoogieIdentifierCollector();
		final List<IdentifierExpression> idents = collector.getIdentifiers(mExpression);

		for (final IdentifierExpression ident : idents) {
			vars.put(ident.getIdentifier(), ident.getType().toString());
		}

		return vars;
	}

	/**
	 * Collects all identifier statements from a boogie expression
	 */
	private static final class BoogieIdentifierCollector extends BoogieVisitor {

		private final ArrayList<IdentifierExpression> mIdentifiers = new ArrayList<>();
		private BoogieType mAproxType = BoogieType.TYPE_BOOL;

		@Override
		protected void visit(final IdentifierExpression expr) {
			mIdentifiers.add(expr);
		}

		@Override
		protected void visit(final RealLiteral expr) {
			mAproxType = BoogieType.TYPE_REAL;
		}

		@Override
		protected void visit(final BooleanLiteral expr) {
			mAproxType = BoogieType.TYPE_BOOL;
		}

		@Override
		protected void visit(final IntegerLiteral expr) {
			mAproxType = BoogieType.TYPE_INT;
		}

		public List<IdentifierExpression> getIdentifiers(final Expression expr) {
			processExpression(expr);

			// try to find a solution to what type the variables of the expression are, by giving them
			// simply the type of type the literals in the expression had.
			// TODO: get a better solution for this!
			for (final IdentifierExpression ident : mIdentifiers) {
				if (ident.getType() == null) {
					ident.setType(mAproxType);
				}
			}
			return mIdentifiers;
		}
	}

	/**
	 * Transforms a BoggieExpressino to a BoogieExpression with primed Variable names
	 *
	 */
	private static final class BoogiePrimeIdentifierTransformer extends BoogieTransformer {
		private String mIgnore;

		public void setIgnore(final String ignore) {
			if (ignore != null) {
				mIgnore = ignore;
			}
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				if (mIgnore != null && ((IdentifierExpression) expr).getIdentifier().equals(mIgnore)) {
					return expr;
				}
				return new IdentifierExpression(expr.getLocation(),
						((IdentifierExpression) expr).getIdentifier().replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + "'"));
			}
			return super.processExpression(expr);
		}

	}

	/**
	 * Transforms a BoggieExpressino to a BoogieExpression with unprimed Variable names
	 *
	 */
	private static final class BoogieRemovePrimeIdentifierTransformer extends BoogieTransformer {
		private String mIgnore;

		public void setIgnore(final String ignore) {
			if (ignore != null) {
				mIgnore = ignore;
			}
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				if (mIgnore != null && ((IdentifierExpression) expr).getIdentifier().equals(mIgnore)) {
					return expr;
				}
				return new IdentifierExpression(expr.getLocation(),
						((IdentifierExpression) expr).getIdentifier().replaceAll("([a-zA-Z_])(\\w*)" + "'", "$1$2"));
			}
			return super.processExpression(expr);
		}
	}

}
