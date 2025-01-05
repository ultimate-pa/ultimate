package de.uni_freiburg.informatik.ultimate.btorutils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
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
			final Map<String, BtorExpression> variableMap, final Boogie2SMT boogie2SMT) {
		if (SmtUtils.isTrueLiteral(term)) {
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ONE, new ArrayList<>());

		} else if (SmtUtils.isFalseLiteral(term)) {
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ZERO, new ArrayList<>());

		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap, boogie2SMT);
		} else if (term instanceof TermVariable) {
			try {
				return variableMap
						.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
			} catch (final NullPointerException e) {
				return variableMap.get(
						boogie2SMT.getBoogie2SmtSymbolTable().getProgramVar((TermVariable) term).getGloballyUniqueId());
			}
		} else if (term instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) term).getValue();
			return new BtorExpression(new BtorSort(64), rational.numerator().longValue());
		} else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("Quantified Formulas not supported by BTOR2 Translation.");
		}
		throw new UnsupportedOperationException("Conditional term is of an unsupported instance");
		// return null;
	}

	public static BtorExpression convertRhsToBtorExpression(final Term rhs, final TransFormula tf,
			final Map<String, BtorExpression> variableMap, final BtorSort lhsSort, final Boogie2SMT boogie2SMT) {
		if (SmtUtils.isTrueLiteral(rhs)) {
			// havoc handling
			return new BtorExpression(lhsSort, BtorExpressionType.INPUT, new ArrayList<>());
		} else if (rhs instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) rhs;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap, boogie2SMT);
		} else if (rhs instanceof TermVariable) {
			return variableMap
					.get(boogie2SMT.getBoogie2SmtSymbolTable().getProgramVar((TermVariable) rhs).getGloballyUniqueId());
		} else if (rhs instanceof ConstantTerm) {
			final Rational rational = (Rational) ((ConstantTerm) rhs).getValue();
			return new BtorExpression(new BtorSort(64), rational.numerator().longValue());
		}
		throw new UnsupportedOperationException("Rhs term is of an unsupported instance");
		// return null;
	}

	public static BtorExpression convertApplicationTermToBtorExpression(final ApplicationTerm appTerm,
			final TransFormula tf, final Map<String, BtorExpression> variableMap, final Boogie2SMT boogie2SMT) {
		BtorExpression lhs;
		BtorExpression rhs;
		BtorExpression array;
		BtorExpression index;
		BtorExpression arrayValue;
		final BtorSort sort;
		final String appName = appTerm.getFunction().getName();
		Term[] params;
		Term idx;
		List<Term> idxs;
		int i;
		switch (appName) {

		// case sign_extend:
		// case zero_extend:
		case "sign_extend":
			final BtorExpression ext =
					convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			sort = ext.getSort();
			return new BtorExpression(sort, BtorExpressionType.SEXT, Arrays.asList(ext));

		// case extract: (slice)
		case "bvnot":
		case "not":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.NOT, Arrays.asList(lhs));

		case "bvneg":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.NEG, Arrays.asList(lhs));

		case "=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.EQ, Arrays.asList(lhs, rhs));

		case "bvsgt":
		case ">":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGT, Arrays.asList(lhs, rhs));

		case "bvugt":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGT, Arrays.asList(lhs, rhs));

		case "bvsge":
		case ">=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));

		case "bvuge":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGTE, Arrays.asList(lhs, rhs));

		case "bvslt":
		case "<":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLT, Arrays.asList(lhs, rhs));

		case "bvult":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULT, Arrays.asList(lhs, rhs));

		case "bvsle":
		case "<=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));

		case "bvule":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULTE, Arrays.asList(lhs, rhs));

		case "bvand":
		case "and":
			final Term[] andParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(andParams[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(andParams[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestAnd = new BtorExpression(sort, BtorExpressionType.AND, Arrays.asList(lhs, rhs));
			for (i = 2; i < andParams.length; i++) {
				rhs = convertConditionalToBtorExpression(andParams[i], tf, variableMap, boogie2SMT);
				latestAnd = new BtorExpression(sort, BtorExpressionType.AND, Arrays.asList(latestAnd, rhs));
			}
			return latestAnd;

		case "bvor":
		case "or":
			final Term[] orParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(orParams[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(orParams[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestOr = new BtorExpression(sort, BtorExpressionType.OR, Arrays.asList(lhs, rhs));
			for (i = 2; i < orParams.length; i++) {
				rhs = convertConditionalToBtorExpression(orParams[i], tf, variableMap, boogie2SMT);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = new BtorExpression(sort, BtorExpressionType.OR, Arrays.asList(latestOr, rhs));
			}
			return latestOr;

		case "bvxor":
			final Term[] xorParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(xorParams[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(xorParams[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			final BtorExpression latestXor = new BtorExpression(sort, BtorExpressionType.XOR, Arrays.asList(lhs, rhs));
			for (i = 2; i < xorParams.length; i++) {
				rhs = convertConditionalToBtorExpression(xorParams[i], tf, variableMap, boogie2SMT);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = new BtorExpression(sort, BtorExpressionType.XOR, Arrays.asList(latestXor, rhs));
			}
			return latestXor;

		case "bvshl":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SLL, Arrays.asList(lhs, rhs));

		case "bvashr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRA, Arrays.asList(lhs, rhs));

		case "bvlshr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRL, Arrays.asList(lhs, rhs));

		case "bvadd":
		case "+":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.ADD, Arrays.asList(lhs, rhs));

		case "bvmul":
		case "*":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.MUL, Arrays.asList(lhs, rhs));

		case "bvsdiv":
		case "div":
		case "/":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
		case "bvudiv":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UDIV, Arrays.asList(lhs, rhs));

		case "bvsmod":
		case "mod":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SMOD, Arrays.asList(lhs, rhs));

		case "bvsrem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SREM, Arrays.asList(lhs, rhs));

		case "bvurem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UREM, Arrays.asList(lhs, rhs));

		case "bvsub":
		case "-":
			// if (appTerm.getParameters().length > 1) {
			// lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			// rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			// assert (lhs.getSort().equals(rhs.getSort()));
			// sort = lhs.getSort();
			// return new BtorExpression(sort, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));
			// }
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));

		case "concat":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			return new BtorExpression(new BtorSort(lhs.getSort().size + rhs.getSort().size), BtorExpressionType.CONCAT,
					Arrays.asList(lhs, rhs));

		case "select":
			params = appTerm.getParameters();
			idx = params[1];
			idxs = new ArrayList<>();
			idxs.add(idx);
			while (params[0] instanceof ApplicationTerm
					&& ((ApplicationTerm) params[0]).getFunction().getName().equals("select")) {
				params = ((ApplicationTerm) params[0]).getParameters();
				idx = params[1];
				idxs.add(idx);
			}
			i = 1;
			index = convertConditionalToBtorExpression(idxs.get(0), tf, variableMap, boogie2SMT);
			while (i < idxs.size()) {
				final BtorExpression nextIndex =
						convertConditionalToBtorExpression(idxs.get(i), tf, variableMap, boogie2SMT);
				index = new BtorExpression(new BtorSort(index.getSort().size + nextIndex.getSort().size),
						BtorExpressionType.CONCAT, Arrays.asList(index, nextIndex));
				i++;
			}

			array = convertConditionalToBtorExpression(params[0], tf, variableMap, boogie2SMT);
			assert (array.getSort().keySort != null);
			assert (array.getSort().keySort.equals(index.getSort()));
			return new BtorExpression(array.getSort().valueSort, BtorExpressionType.READ, Arrays.asList(array, index));

		case "ite":
			final BtorExpression iteIf =
					convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT);
			final BtorExpression iteThen =
					convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT);
			final BtorExpression iteElse =
					convertConditionalToBtorExpression(appTerm.getParameters()[2], tf, variableMap, boogie2SMT);
			assert (iteThen.getSort().equals(iteElse.getSort()));
			return new BtorExpression(iteThen.getSort(), BtorExpressionType.ITE,
					Arrays.asList(iteIf, iteThen, iteElse));

		case "store":
			params = appTerm.getParameters();
			idx = params[1];
			idxs = new ArrayList<>();
			idxs.add(idx);
			array = convertConditionalToBtorExpression(params[0], tf, variableMap, boogie2SMT);
			while (params[2] instanceof ApplicationTerm
					&& ((ApplicationTerm) params[2]).getFunction().getName().equals("store")) {
				params = ((ApplicationTerm) params[2]).getParameters();
				idx = params[1];
				idxs.add(0, idx);
			}
			final Term val = params[2];
			arrayValue = convertConditionalToBtorExpression(val, tf, variableMap, boogie2SMT);
			i = 1;
			index = convertConditionalToBtorExpression(idxs.get(0), tf, variableMap, boogie2SMT);
			while (i < idxs.size()) {
				final BtorExpression nextindex =
						convertConditionalToBtorExpression(idxs.get(i), tf, variableMap, boogie2SMT);
				index = new BtorExpression(new BtorSort(index.getSort().size + nextindex.getSort().size),
						BtorExpressionType.CONCAT, Arrays.asList(index, nextindex));
				i++;
			}
			// arrayValue = convertConditionalToBtorExpression(appTerm.getParameters()[2], tf, variableMap, boogie2SMT);
			assert (array.getSort().keySort != null);
			assert (array.getSort().keySort.equals(index.getSort()));
			assert (array.getSort().valueSort.equals(arrayValue.getSort()));
			return new BtorExpression(array.getSort(), BtorExpressionType.WRITE,
					Arrays.asList(array, index, arrayValue));

		case "true":
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ONE);

		case "false":
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ZERO);

		default:
			if (BitvectorUtils.isBitvectorConstant(appTerm.getFunction())) {
				final long value = Long.parseLong(appName.substring(2));
				return new BtorExpression(new BtorSort(Integer.parseInt(appTerm.getSort().getIndices()[0])), value);
			}
			throw new UnsupportedOperationException(
					"Converting currently unsupported btor2 expression" + appTerm.getFunction().getName());
		// as const
		// myFunc
		// return null;
		}
	}

}