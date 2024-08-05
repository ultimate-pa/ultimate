package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermToBtorUtil {

	public static BtorExpression convertConditionalToBtorExpression(final Term term, final TransFormula tf,
			final Map<String, BtorExpression> variableMap) {
		if (SmtUtils.isTrueLiteral(term)) {
			return new BtorExpression(1, BtorExpressionType.ONE, new ArrayList<>());

		} else if (SmtUtils.isFalseLiteral(term)) {
			return new BtorExpression(1, BtorExpressionType.ZERO, new ArrayList<>());

		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap);
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
			final Map<String, BtorExpression> variableMap, final int lhsSort) {
		if (SmtUtils.isTrueLiteral(term)) {
			// havoc handling
			return new BtorExpression(lhsSort, BtorExpressionType.INPUT, new ArrayList<>());
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap);
		} else if (term instanceof TermVariable) {
			return variableMap
					.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
		} else if (term instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) term).getValue();
			return new BtorExpression(64, rational.numerator().longValue());
		}
		return null;
	}

	public static BtorExpression convertApplicationTermToBtorExpression(final ApplicationTerm appTerm,
			final TransFormula tf, final Map<String, BtorExpression> variableMap) {
		BtorExpression lhs;
		BtorExpression rhs;
		final int sort;
		final String appName = appTerm.getFunction().getName();
		switch (appName) {
		case "bvadd":
		case "+":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort() == rhs.getSort());
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.ADD, Arrays.asList(lhs, rhs));
		case "bvsub":
		case "-":
			if (appTerm.getParameters().length > 1) {
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				assert (lhs.getSort() == rhs.getSort());
				sort = lhs.getSort();
				return new BtorExpression(sort, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));
			}
		case "bvneg":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.NEG, Arrays.asList(lhs));
		case "bvmul":
		case "*":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort() == rhs.getSort());
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.MUL, Arrays.asList(lhs, rhs));
		case "/":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort() == rhs.getSort());
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
		case "bvslt":
		case "<":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.SLT, Arrays.asList(lhs, rhs));
		case "bvsle":
		case "<=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));
		case "bvsgt":
		case ">":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.SGT, Arrays.asList(lhs, rhs));
		case "bvsge":
		case ">=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));
		case "=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.EQ, Arrays.asList(lhs, rhs));
		case "bvand":
		case "and":
			final Term[] andParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(andParams[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(andParams[1], tf, variableMap);
			BtorExpression latestAnd = new BtorExpression(1, BtorExpressionType.AND, Arrays.asList(lhs, rhs));
			for (int i = 2; i < andParams.length; i++) {
				rhs = convertConditionalToBtorExpression(andParams[i], tf, variableMap);
				latestAnd = new BtorExpression(1, BtorExpressionType.AND, Arrays.asList(latestAnd, rhs));
			}

			return latestAnd;
		case "bvor":
		case "or":
			final Term[] orParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(orParams[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(orParams[1], tf, variableMap);
			BtorExpression latestOr = new BtorExpression(1, BtorExpressionType.OR, Arrays.asList(lhs, rhs));
			for (int i = 2; i < orParams.length; i++) {
				rhs = convertConditionalToBtorExpression(orParams[i], tf, variableMap);
				latestOr = new BtorExpression(1, BtorExpressionType.OR, Arrays.asList(latestOr, rhs));
			}
			return latestOr;
		case "bvnot":
		case "not":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			return new BtorExpression(1, BtorExpressionType.NOT, Arrays.asList(lhs));
		default:
			if (BitvectorUtils.isBitvectorConstant(appTerm.getFunction())) {
				final long value = Long.parseLong(appName.substring(2));
				return new BtorExpression(Integer.parseInt(appTerm.getSort().getIndices()[0]), value);
			}
			return null;
		}
	}

}
