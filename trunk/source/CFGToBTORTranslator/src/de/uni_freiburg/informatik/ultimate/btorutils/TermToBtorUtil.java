package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermToBtorUtil {

	public static BtorExpression convertConditionalToBtorExpression(final Term term, final TransFormula tf,
			final Map<String, BtorExpression> variableMap) {
		final BtorExpression lhs;
		final BtorExpression rhs;
		if (SmtUtils.isTrueLiteral(term)) {
			return new BtorExpression(1, BtorExpressionType.ONE, new ArrayList<>());
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			switch (appTerm.getFunction().getName()) {
			case "+":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.ADD, Arrays.asList(lhs, rhs));
			case "-":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				if (appTerm.getParameters().length > 1) {
					rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
					return new BtorExpression(64, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));
				}
				return new BtorExpression(64, BtorExpressionType.SUB, Arrays.asList(lhs));
			case "*":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.MUL, Arrays.asList(lhs, rhs));
			case "/":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
			case "<":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SLT, Arrays.asList(lhs, rhs));
			case "<=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));
			case ">":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SGT, Arrays.asList(lhs, rhs));
			case ">=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));
			case "=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.EQ, Arrays.asList(lhs, rhs));
			case "and":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.AND, Arrays.asList(lhs, rhs));
			case "or":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.OR, Arrays.asList(lhs, rhs));
			case "not":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.NEG, Arrays.asList(lhs));
			}
		} else if (term instanceof TermVariable) {
			return variableMap
					.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
		} else if (term instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) term).getValue();
			return new BtorExpression(64, rational.numerator().longValue());
		}
		return null;
	}

	public static BtorExpression convertRHSToBtorExpression(final Term term, final TransFormula tf,
			final Map<String, BtorExpression> variableMap) {
		final BtorExpression lhs;
		final BtorExpression rhs;
		if (SmtUtils.isTrueLiteral(term)) {
			// havoc handling
			return new BtorExpression(64, BtorExpressionType.INPUT, new ArrayList<>());
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			switch (appTerm.getFunction().getName()) {
			case "+":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.ADD, Arrays.asList(lhs, rhs));
			case "-":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				if (appTerm.getParameters().length > 1) {
					rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
					return new BtorExpression(64, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));
				}
				return new BtorExpression(64, BtorExpressionType.SUB, Arrays.asList(lhs));
			case "*":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.MUL, Arrays.asList(lhs, rhs));
			case "/":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(64, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
			case "<":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SLT, Arrays.asList(lhs, rhs));
			case "<=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));
			case ">":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SGT, Arrays.asList(lhs, rhs));
			case ">=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));
			case "=":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.EQ, Arrays.asList(lhs, rhs));
			case "and":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.AND, Arrays.asList(lhs, rhs));
			case "or":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.OR, Arrays.asList(lhs, rhs));
			case "not":
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				return new BtorExpression(1, BtorExpressionType.NEG, Arrays.asList(lhs));
			}
		} else if (term instanceof TermVariable) {
			return variableMap
					.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
		} else if (term instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) term).getValue();
			return new BtorExpression(64, rational.numerator().longValue());
		}
		return null;
	}

}
