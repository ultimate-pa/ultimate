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
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermToBtorUtil {

	public static BtorExpression convertConditionalToBtorExpression(final Term term, final TransFormula tf,
			final Map<String, BtorExpression> variableMap) {
		if (SmtUtils.isTrueLiteral(term)) {
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ONE, new ArrayList<>());

		} else if (SmtUtils.isFalseLiteral(term)) {
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ZERO, new ArrayList<>());

		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap);
		} else if (term instanceof TermVariable) {
			return variableMap
					.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
		} else if (term instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) term).getValue();
			return new BtorExpression(new BtorSort(64), rational.numerator().longValue());
		} else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("Quantified Formulas not supported by BTOR2 Translation.");
		}
		throw new UnsupportedOperationException("Conditional term is of an unsupported instance");
		// return null;
	}

	public static BtorExpression convertRhsToBtorExpression(final Term term, final TransFormula tf,
			final Map<String, BtorExpression> variableMap, final BtorSort lhsSort) {
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
			return new BtorExpression(new BtorSort(64), rational.numerator().longValue());
		}
		throw new UnsupportedOperationException("Rhs term is of an unsupported instance");
		// return null;
	}

	public static BtorExpression convertApplicationTermToBtorExpression(final ApplicationTerm appTerm,
			final TransFormula tf, final Map<String, BtorExpression> variableMap) {
		BtorExpression lhs;
		BtorExpression rhs;
		BtorExpression index;
		final BtorSort sort;
		final String appName = appTerm.getFunction().getName();
		switch (appName) {

		// case sign_extend:
		// case zero_extend:
		// case "sign_extend":
		// lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
		// // rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
		// sort = lhs.getSort();
		// return new BtorExpression(sort, BtorExpressionType.SEXT, Arrays.asList(lhs));

		// case extract: (slice)
		case "bvnot":
		case "not":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.NOT, Arrays.asList(lhs));

		case "bvneg":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.NEG, Arrays.asList(lhs));

		case "=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.EQ, Arrays.asList(lhs, rhs));

		case "bvsgt":
		case ">":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGT, Arrays.asList(lhs, rhs));

		case "bvugt":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGT, Arrays.asList(lhs, rhs));

		case "bvsge":
		case ">=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));

		case "bvuge":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGTE, Arrays.asList(lhs, rhs));

		case "bvslt":
		case "<":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLT, Arrays.asList(lhs, rhs));

		case "bvult":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULT, Arrays.asList(lhs, rhs));

		case "bvsle":
		case "<=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));

		case "bvule":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULTE, Arrays.asList(lhs, rhs));

		case "bvand":
		case "and":
			final Term[] andParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(andParams[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(andParams[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestAnd = new BtorExpression(sort, BtorExpressionType.AND, Arrays.asList(lhs, rhs));
			for (int i = 2; i < andParams.length; i++) {
				rhs = convertConditionalToBtorExpression(andParams[i], tf, variableMap);
				latestAnd = new BtorExpression(sort, BtorExpressionType.AND, Arrays.asList(latestAnd, rhs));
			}
			return latestAnd;

		case "bvor":
		case "or":
			final Term[] orParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(orParams[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(orParams[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestOr = new BtorExpression(sort, BtorExpressionType.OR, Arrays.asList(lhs, rhs));
			for (int i = 2; i < orParams.length; i++) {
				rhs = convertConditionalToBtorExpression(orParams[i], tf, variableMap);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = new BtorExpression(sort, BtorExpressionType.OR, Arrays.asList(latestOr, rhs));
			}
			return latestOr;

		case "bvxor":
			final Term[] xorParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(xorParams[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(xorParams[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			final BtorExpression latestXor = new BtorExpression(sort, BtorExpressionType.XOR, Arrays.asList(lhs, rhs));
			for (int i = 2; i < xorParams.length; i++) {
				rhs = convertConditionalToBtorExpression(xorParams[i], tf, variableMap);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = new BtorExpression(sort, BtorExpressionType.XOR, Arrays.asList(latestXor, rhs));
			}
			return latestXor;

		case "bvshl":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SLL, Arrays.asList(lhs, rhs));

		case "bvashr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRA, Arrays.asList(lhs, rhs));

		case "bvlshr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRL, Arrays.asList(lhs, rhs));

		case "bvadd":
		case "+":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.ADD, Arrays.asList(lhs, rhs));

		case "bvmul":
		case "*":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.MUL, Arrays.asList(lhs, rhs));

		case "bvsdiv":
		case "/":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
		case "bvudiv":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UDIV, Arrays.asList(lhs, rhs));

		case "bvsmod":
		case "mod":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SMOD, Arrays.asList(lhs, rhs));

		case "bvsrem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SREM, Arrays.asList(lhs, rhs));

		case "bvurem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UREM, Arrays.asList(lhs, rhs));

		case "bvsub":
		case "-":
			if (appTerm.getParameters().length > 1) {
				lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
				rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
				assert (lhs.getSort().equals(rhs.getSort()));
				sort = lhs.getSort();
				return new BtorExpression(sort, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));
			}

			// case concat:
		case "select":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			assert (lhs.getSort().keySort != null);
			assert (lhs.getSort().keySort.equals(rhs.getSort()));
			return new BtorExpression(lhs.getSort().valueSort, BtorExpressionType.READ, Arrays.asList(lhs, rhs));

		case "store":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap);
			index = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[2], tf, variableMap);
			assert (lhs.getSort().keySort != null);
			assert (lhs.getSort().keySort.equals(index.getSort()));
			assert (lhs.getSort().valueSort.equals(rhs.getSort()));
			return new BtorExpression(lhs.getSort(), BtorExpressionType.WRITE, Arrays.asList(lhs, index, rhs));

		default:
			if (BitvectorUtils.isBitvectorConstant(appTerm.getFunction())) {
				final long value = Long.parseLong(appName.substring(2));
				return new BtorExpression(new BtorSort(Integer.parseInt(appTerm.getSort().getIndices()[0])), value);
			}
			throw new UnsupportedOperationException("Converting currently unsupported btor2 expression");
		// return null;
		}
	}

}