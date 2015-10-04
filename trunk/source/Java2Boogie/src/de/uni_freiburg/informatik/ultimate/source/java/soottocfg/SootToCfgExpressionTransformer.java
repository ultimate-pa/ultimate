package de.uni_freiburg.informatik.ultimate.source.java.soottocfg;

import soottocfg.cfg.expression.ArrayAccessExpression;
import soottocfg.cfg.expression.ArrayStoreExpression;
import soottocfg.cfg.expression.BinaryExpression;
import soottocfg.cfg.expression.BooleanLiteral;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.expression.InstanceOfExpression;
import soottocfg.cfg.expression.IntegerLiteral;
import soottocfg.cfg.expression.IteExpression;
import soottocfg.cfg.expression.UnaryExpression;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SootToCfgExpressionTransformer<T> {

	protected T visit(Expression expr) {
		if (expr instanceof ArrayAccessExpression) {
			return visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			return visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			return visit((BinaryExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			return visit((BooleanLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			return visit((IdentifierExpression) expr);
		} else if (expr instanceof InstanceOfExpression) {
			return visit((InstanceOfExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			return visit((IntegerLiteral) expr);
		} else if (expr instanceof IteExpression) {
			return visit((IteExpression) expr);
		} else if (expr instanceof UnaryExpression) {
			return visit((UnaryExpression) expr);
		} else if (expr instanceof UnaryExpression) {
			return visit((UnaryExpression) expr);
		} else {
			throw new UnsupportedOperationException(
					"Expression type not implemented " + expr == null ? "null" : expr.getClass().getSimpleName());
		}
	}

	protected T visit(ArrayAccessExpression expr) {
		return null;
	}

	protected T visit(ArrayStoreExpression expr) {
		return null;
	}

	protected T visit(BinaryExpression expr) {
		return null;
	}

	protected T visit(BooleanLiteral expr) {
		return null;
	}

	protected T visit(IdentifierExpression expr) {
		return null;
	}

	protected T visit(InstanceOfExpression expr) {
		return null;
	}

	protected T visit(IntegerLiteral expr) {
		return null;
	}

	protected T visit(IteExpression expr) {
		return null;
	}

	protected T visit(UnaryExpression expr) {
		return null;
	}

}
