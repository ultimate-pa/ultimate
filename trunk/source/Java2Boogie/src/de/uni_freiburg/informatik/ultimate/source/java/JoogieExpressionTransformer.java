package de.uni_freiburg.informatik.ultimate.source.java;

import org.joogie.boogie.constants.Constant;
import org.joogie.boogie.constants.RealConstant;
import org.joogie.boogie.constants.TypeExpression;
import org.joogie.boogie.constants.UboundedIntConstant;
import org.joogie.boogie.expressions.ArrayReadExpression;
import org.joogie.boogie.expressions.BinOpExpression;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.IteExpression;
import org.joogie.boogie.expressions.QuantifiedExpression;
import org.joogie.boogie.expressions.SimpleHeapAccess;
import org.joogie.boogie.expressions.UnaryExpression;
import org.joogie.boogie.expressions.Variable;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class JoogieExpressionTransformer<T> {

	protected T visit(Expression expr) {
		if (expr instanceof ArrayReadExpression) {
			return visit((ArrayReadExpression) expr);
		} else if (expr instanceof BinOpExpression) {
			return visit((BinOpExpression) expr);
		} else if (expr instanceof Constant) {
			return visit((Constant) expr);
		} else if (expr instanceof InvokeExpression) {
			return visit((InvokeExpression) expr);
		} else if (expr instanceof IteExpression) {
			return visit((IteExpression) expr);
		} else if (expr instanceof QuantifiedExpression) {
			return visit((QuantifiedExpression) expr);
		} else if (expr instanceof SimpleHeapAccess) {
			return visit((SimpleHeapAccess) expr);
		} else if (expr instanceof TypeExpression) {
			return visit((TypeExpression) expr);
		} else if (expr instanceof UnaryExpression) {
			return visit((UnaryExpression) expr);
		} else if (expr instanceof Variable) {
			return visit((Variable) expr);
		} else {
			throw new UnsupportedOperationException("did not implement " + expr.getClass().getSimpleName());
		}
	}

	protected T visit(ArrayReadExpression expr) {
		return null;
	}

	protected T visit(BinOpExpression expr) {
		return null;
	}

	protected T visit(Constant expr) {
		if (expr instanceof RealConstant) {
			return visit((RealConstant) expr);
		} else if (expr instanceof UboundedIntConstant) {
			return visit((UboundedIntConstant) expr);
		} else {
			throw new UnsupportedOperationException("did not implement " + expr.getClass().getSimpleName());
		}
	}

	protected T visit(RealConstant expr) {
		return null;
	}

	protected T visit(UboundedIntConstant expr) {
		return null;
	}

	protected T visit(InvokeExpression expr) {
		return null;
	}

	protected T visit(IteExpression expr) {
		return null;
	}

	protected T visit(QuantifiedExpression expr) {
		return null;
	}

	protected T visit(SimpleHeapAccess expr) {
		return null;
	}

	protected T visit(TypeExpression expr) {
		return null;
	}

	protected T visit(UnaryExpression expr) {
		return null;
	}

	protected T visit(Variable expr) {
		return null;
	}

}
