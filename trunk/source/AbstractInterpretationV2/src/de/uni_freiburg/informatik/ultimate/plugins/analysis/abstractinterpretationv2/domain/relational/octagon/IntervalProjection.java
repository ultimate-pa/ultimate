package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;

public class IntervalProjection {

	public static List<OctDomainState> assignNumericVarWithoutIfs(String var, Expression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (OctDomainState state : oldStates) {
			IntervalDomainValue i = projectNumericExprWithoutIfs(rhs, state);
			OctInterval oi = new OctInterval(i);
			state.assignNumericVarInterval(var, oi.getMin(), oi.getMax());
		}
		return oldStates;
	}

	public static List<OctDomainState> assignNumericVarAffine(String var, AffineExpression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (OctDomainState state : oldStates) {
			IntervalDomainValue i = projectAffineExpr(rhs, state);
			OctInterval oi = new OctInterval(i);
			state.assignNumericVarInterval(var, oi.getMin(), oi.getMax());
		}
		return oldStates;
	}
	
	public static IntervalDomainValue projectNumericExprWithoutIfs(Expression expr, OctDomainState state) {
		// TODO (?) cache interval projections of each variable

		if (expr instanceof IntegerLiteral) {
			IntervalValue c = new IntervalValue(((IntegerLiteral) expr).getValue());
			return new IntervalDomainValue(c, c);
		
		} else if (expr instanceof RealLiteral) {
			IntervalValue c = new IntervalValue(((IntegerLiteral) expr).getValue());
			return new IntervalDomainValue(c, c);
		
		} else if (expr instanceof IdentifierExpression) {
			String var = ((IdentifierExpression) expr).getIdentifier();
			OctInterval oi = state.projectToInterval(var);
			return oi.toIvlInterval();

		} else if (expr instanceof UnaryExpression) {
			UnaryExpression ue = (UnaryExpression) expr;
			switch (ue.getOperator()) {
			case ARITHNEGATIVE:
				return projectNumericExprWithoutIfs(ue.getExpr(), state).negate();
			default:
				// see end of this method
			}
			
		} else if (expr instanceof BinaryExpression) {
			BinaryExpression be = (BinaryExpression) expr;
			IntervalDomainValue left = projectNumericExprWithoutIfs(be.getLeft(), state);
			IntervalDomainValue right = projectNumericExprWithoutIfs(be.getRight(), state);
			switch (be.getOperator()) {
			case ARITHPLUS:
				return left.add(right);
			case ARITHMINUS:
				return left.subtract(right);
			case ARITHMUL:
				return left.multiply(right);
			case ARITHDIV:
				if (TypeUtil.isNumericInt(be.getType())) {
					return left.integerDivide(right);
				} else {
					return left.divide(right);
				}
			case ARITHMOD:
				return left.modulo(right);
			default:
				// see end of this method
			}

		}
		return new IntervalDomainValue(); // \top = safe over-approximation
	}
	
	public static IntervalDomainValue projectAffineExpr(AffineExpression expr, OctDomainState state) {
		IntervalDomainValue i = new IntervalDomainValue(0, 0);
		for (Map.Entry<String, BigDecimal> summand : expr.getCoefficients().entrySet()) {
			IntervalDomainValue varIvl = state.projectToInterval(summand.getKey()).toIvlInterval();
			IntervalValue factor = new IntervalValue(summand.getValue());
			i = i.add(varIvl.multiply(new IntervalDomainValue(factor, factor)));
		}
		IntervalValue constant = new IntervalValue(expr.getConstant());
		i = i.add(new IntervalDomainValue(constant, constant));
		return i;
	}

}
