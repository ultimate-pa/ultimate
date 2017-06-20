package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.HashMap;
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
 * Pea Decision expressed by a BoogieAST Expression.
 *
 * @author langenfeld
 * @see pea.Decision
 */
public class BoogieBooleanExpressionDecision extends Decision {

	private final Expression expression;

	public Expression getExpression() {
		return expression;
	}

	/**
	 *
	 * @param expression
	 *            A Boogie expression which evaluates to boolean but has no boolean expressions as children.
	 */
	public BoogieBooleanExpressionDecision(final Expression expression) {
		this.expression = expression;
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
		return ((BoogieBooleanExpressionDecision) o).getExpression().toString().compareTo(expression.toString());

	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof BoogieBooleanExpressionDecision)) {
			return false;
		}
		if (!expression.equals(((BoogieBooleanExpressionDecision) o).getExpression())) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		return expression.hashCode();
	}

	/**
	 * Transforms a BoggieExpressino to a BoogieExpression with primed Variable names
	 *
	 */
	class BoogiePrimeIdentifierTransformer extends BoogieTransformer {
		private String ignore = new String();

		public void setIgnore(final String ignore) {
			if (ignore != null) {
				this.ignore = ignore;
			}
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				if (ignore != null && ((IdentifierExpression) expr).getIdentifier().equals(ignore)) {
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
	class BoogieRemovePrimeIdentifierTransformer extends BoogieTransformer {
		private String ignore = new String();

		public void setIgnore(final String ignore) {
			if (ignore != null) {
				this.ignore = ignore;
			}
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				if (ignore != null && ((IdentifierExpression) expr).getIdentifier().equals(ignore)) {
					return expr;
				}
				return new IdentifierExpression(expr.getLocation(),
						((IdentifierExpression) expr).getIdentifier().replaceAll("([a-zA-Z_])(\\w*)" + "'", "$1$2"));
			}
			return super.processExpression(expr);
		}

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
		final Expression primed = bpit.processExpression(expression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public Decision prime(final String ignore) {
		final BoogiePrimeIdentifierTransformer bpit = new BoogiePrimeIdentifierTransformer();
		bpit.setIgnore(ignore);
		final Expression primed = bpit.processExpression(expression);
		return new BoogieBooleanExpressionDecision(primed);
	}

	@Override
	public String toString(final int child) {
		if (child != 0) {
			final BoogieLocation loc = new BoogieLocation("", 0, 0, 0, 0, false);
			return BoogiePrettyPrinter.print(new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, expression));
		}
		return BoogiePrettyPrinter.print(expression);
	}

	@Override
	public String toSmtString(final int child) {
		return null;
	}

	@Override
	public String toTexString(final int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toUppaalString(final int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getVar() {
		throw new RuntimeException("getVar not supported by BoogieBooleanExpressionDecision (use getVars)!");
	}

	/**
	 * Collects all identifier statements from a boogie expression
	 */
	class BoogieIdentifierCollector extends BoogieVisitor {

		private final ArrayList<IdentifierExpression> identifiers = new ArrayList<IdentifierExpression>();
		private BoogieType aproxType = BoogieType.TYPE_BOOL;

		@Override
		protected void visit(final IdentifierExpression expr) {
			identifiers.add(expr);
		}

		@Override
		protected void visit(final RealLiteral expr) {
			aproxType = BoogieType.TYPE_REAL;
		}

		@Override
		protected void visit(final BooleanLiteral expr) {
			aproxType = BoogieType.TYPE_BOOL;
		}

		@Override
		protected void visit(final IntegerLiteral expr) {
			aproxType = BoogieType.TYPE_INT;
		}

		public ArrayList<IdentifierExpression> getIdentifiers(final Expression expr) {
			processExpression(expr);

			// try to find a solution to what type the variables of the expression are, by giving them
			// simply the type of type the literals in the expression had.
			// TODO: get a better solution for this!
			for (final IdentifierExpression ident : identifiers) {
				if (ident.getType() == null) {
					ident.setType(aproxType);
				}
			}
			return identifiers;
		}

	}

	/**
	 * Collects variable names and types from the expression.
	 *
	 * @return Map: ident -> type
	 */
	public Map<String, String> getVars() {
		final Map<String, String> vars = new HashMap<String, String>();

		final BoogieIdentifierCollector collector = new BoogieIdentifierCollector();
		final ArrayList<IdentifierExpression> idents = collector.getIdentifiers(expression);

		for (final IdentifierExpression ident : idents) {
			vars.put(ident.getIdentifier().toString(), ident.getType().toString());
		}

		return vars;
	}

}
