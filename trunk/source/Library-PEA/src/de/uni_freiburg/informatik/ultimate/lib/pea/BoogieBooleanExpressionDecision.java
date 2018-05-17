package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

/**
 * {@link Decision} expressed by a BoogieAST Expression.
 *
 * @author Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 */
public class BoogieBooleanExpressionDecision extends Decision<BoogieBooleanExpressionDecision> {

	private final Expression mExpression;
	private static final NormalFormTransformer<Expression> TRANSFORMER =
			new NormalFormTransformer<>(new BoogieExpressionTransformer());

	/**
	 *
	 * @param expression
	 *            A Boogie expression which evaluates to boolean but has no boolean expressions as children.
	 */
	private BoogieBooleanExpressionDecision(final Expression expression) {
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
		final CDD rtr = new BoogieToCdd().createCdd(e);
		return rtr;
	}

	/**
	 * Only used for testing, does not reduce the boolean structure.
	 */
	public static CDD createWithoutReduction(final Expression e) {
		return CDD.create(new BoogieBooleanExpressionDecision(e), CDD.TRUE_CHILDS);
	}

	public static CDD createTrue() {
		return CDD.TRUE;
	}

	@Override
	public BoogieBooleanExpressionDecision prime() {
		return prime(null);
	}

	@Override
	public BoogieBooleanExpressionDecision unprime() {
		return unprime(null);
	}

	@Override
	public BoogieBooleanExpressionDecision unprime(final String ignore) {
		final BoogieRemovePrimeIdentifierTransformer bpit = new BoogieRemovePrimeIdentifierTransformer();
		bpit.setIgnore(ignore);
		final Expression primed = bpit.processExpression(mExpression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public BoogieBooleanExpressionDecision prime(final String ignore) {
		final BoogiePrimeIdentifierTransformer bpit = new BoogiePrimeIdentifierTransformer();
		bpit.setIgnore(ignore);
		final Expression primed = bpit.processExpression(mExpression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public String toString(final int child) {
		if (child != 0) {
			final BoogieLocation loc = new BoogieLocation("", 0, 0, 0, 0);
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
		return toString(child);
	}

	@Override
	public String toBoogieString(final int child) {
		return toString(child);
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
			vars.put(ident.getIdentifier(), null);
		}

		return vars;
	}

	@Override
	public int compareToSimilar(final Decision<?> otherDec) {
		final BoogieBooleanExpressionDecision other = (BoogieBooleanExpressionDecision) otherDec;
		if (mExpression == null && other.mExpression == null) {
			return 0;
		} else if (mExpression == null && other.mExpression != null) {
			return -1;
		} else if (mExpression != null && other.mExpression == null) {
			return 1;
		} else {
			final String expr = BoogiePrettyPrinter.print(mExpression);
			final String otherExpr = BoogiePrettyPrinter.print(other.mExpression);
			return expr.compareTo(otherExpr);
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mExpression == null ? 0 : mExpression.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final BoogieBooleanExpressionDecision other = (BoogieBooleanExpressionDecision) obj;
		if (mExpression == null) {
			if (other.mExpression != null) {
				return false;
			}
		} else {
			final String expr = BoogiePrettyPrinter.print(mExpression);
			final String otherExpr = BoogiePrettyPrinter.print(other.mExpression);
			if (!expr.equals(otherExpr)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Collects all identifier statements from a boogie expression
	 */
	private static final class BoogieIdentifierCollector extends BoogieVisitor {

		private final ArrayList<IdentifierExpression> mIdentifiers = new ArrayList<>();

		@Override
		protected void visit(final IdentifierExpression expr) {
			mIdentifiers.add(expr);
		}

		public List<IdentifierExpression> getIdentifiers(final Expression expr) {
			processExpression(expr);
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

	private static final class BoogieToCdd extends GeneratedBoogieAstVisitor {

		private Deque<CDD> mOpenCDDs;

		public CDD createCdd(final Expression expr) {
			mOpenCDDs = new ArrayDeque<>();
			final Expression simplifiedExpression = TRANSFORMER.toNnf(expr);
			simplifiedExpression.accept(this);
			assert mOpenCDDs.size() == 1;
			return mOpenCDDs.pop();
		}

		@Override
		public boolean visit(final QuantifierExpression node) {
			// stop descend, take the whole remaining expression as decision
			mOpenCDDs.push(CDD.create(new BoogieBooleanExpressionDecision(node), CDD.TRUE_CHILDS));
			return false;
		}

		@Override
		public boolean visit(final BinaryExpression node) {
			switch (node.getOperator()) {
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
			case BITVECCONCAT:
				throw new AssertionError("The tree root should be boolean");
			case COMPEQ:
			case COMPGEQ:
			case COMPGT:
			case COMPLEQ:
			case COMPLT:
			case COMPNEQ:
			case COMPPO:
				// stop descend, take the whole remaining expression as decision
				mOpenCDDs.push(CDD.create(new BoogieBooleanExpressionDecision(node), CDD.TRUE_CHILDS));
				return false;
			case LOGICAND:
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICOR:
				break;
			default:
				throw new UnsupportedOperationException();
			}

			node.getLeft().accept(this);
			final CDD left = mOpenCDDs.pop();
			node.getRight().accept(this);
			final CDD right = mOpenCDDs.pop();

			switch (node.getOperator()) {
			case LOGICAND:
				mOpenCDDs.push(left.and(right));
				break;
			case LOGICIMPLIES:
				mOpenCDDs.push(left.negate().or(right));
				break;
			case LOGICIFF:
				mOpenCDDs.push(left.negate().and(right.negate()).or(left.and(right)));
				break;
			case LOGICOR:
				mOpenCDDs.push(left.or(right));
				break;
			default:
				throw new UnsupportedOperationException();
			}

			return false;
		}

		@Override
		public boolean visit(final BooleanLiteral node) {
			if (node.getValue()) {
				mOpenCDDs.push(CDD.TRUE);
			} else {
				mOpenCDDs.push(CDD.FALSE);
			}
			return super.visit(node);
		}

		@Override
		public boolean visit(final IdentifierExpression node) {
			mOpenCDDs.push(CDD.create(new BooleanDecision(node.getIdentifier()), CDD.TRUE_CHILDS));
			return super.visit(node);
		}

		@Override
		public boolean visit(final UnaryExpression node) {
			switch (node.getOperator()) {
			case ARITHNEGATIVE:
			case OLD:
				throw new AssertionError("The tree root should be boolean");
			case LOGICNEG:
				node.getExpr().accept(this);
				mOpenCDDs.push(mOpenCDDs.pop().negate());
				return false;
			default:
				throw new UnsupportedOperationException();

			}
		}
	}

}
