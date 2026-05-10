package de.uni_freiburg.informatik.ultimate.btor;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.btor.expression.AddExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.AndExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.BtorExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.ConcatExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.EqExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.MulExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NegExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.NotExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.OrExpression;
import de.uni_freiburg.informatik.ultimate.btor.expression.XorExpression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
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
			final Map<String, BtorExpression> variableMap, final Boogie2SMT boogie2SMT, final BtorScript script) {
		if (SmtUtils.isTrueLiteral(term)) {
			// true literal is a 1-bit one
			return script.createOneExpression(new BtorSort(1));
		} else if (SmtUtils.isFalseLiteral(term)) {
			// false literal is a 1-bit zero
			return script.createZeroExpression(new BtorSort(1));
		} else if (term instanceof ApplicationTerm) {
			// if the term is an application term, then convert it to an btor expression
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap, boogie2SMT, script);
		} else if (term instanceof TermVariable) {
			try {
				// attempt to retrieve btor expression from variable map via the transformula
				return variableMap
						.get(TransFormulaUtils.getProgramVarForTerm(tf, (TermVariable) term).getGloballyUniqueId());
			} catch (final NullPointerException e) {
				// if that fails, attempt to retrieve btor expression from variable map via the boogie2SMT table
				return variableMap.get(
						boogie2SMT.getBoogie2SmtSymbolTable().getProgramVar((TermVariable) term).getGloballyUniqueId());
			}
		} else if (term instanceof ConstantTerm) {
			// get rational representation of the constant term
			final Object maybeInteger = ((ConstantTerm) term).getValue();
			if (maybeInteger instanceof Rational) {
				final Rational rational = (Rational) maybeInteger;
				assert (rational.isIntegral());
				return script.createConstdExpression(new BtorSort(64), rational.numerator().longValue());
			} else if (maybeInteger instanceof BigInteger) {
				final BigInteger integer = (BigInteger) maybeInteger;
				return script.createConstdExpression(new BtorSort(64), integer.longValue());
			} else {
				throw new UnsupportedOperationException("Non-integral constant.");
			}
		} else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("Quantified Formulas not supported by BTOR2 Translation.");
		}
		throw new UnsupportedOperationException("Conditional term is of an unsupported instance");
	}

	public static BtorExpression convertRhsToBtorExpression(final Term rhs, final TransFormula tf,
			final Map<String, BtorExpression> variableMap, final BtorSort lhsSort, final Boogie2SMT boogie2SMT,
			final BtorScript script) {
		if (SmtUtils.isTrueLiteral(rhs)) {
			// literal true, not havoc
			assert (lhsSort.size == 1);
			return script.createOneExpression(lhsSort);
		} else if (rhs instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) rhs;
			return convertApplicationTermToBtorExpression(appTerm, tf, variableMap, boogie2SMT, script);
		} else if (rhs instanceof TermVariable) {
			final IProgramVar programVar = boogie2SMT.getBoogie2SmtSymbolTable().getProgramVar((TermVariable) rhs);
			if (programVar == null) {
				throw new UnsupportedOperationException("Rhs cannot be mapped to a variable.");
			}
			return variableMap.get(programVar.getGloballyUniqueId());
		} else if (rhs instanceof ConstantTerm) {
			// Assume the constant term is an integer
			final Rational rational = (Rational) ((ConstantTerm) rhs).getValue();
			return script.createConstdExpression(new BtorSort(64), rational.numerator().longValue());
		}
		throw new UnsupportedOperationException("Rhs term is of an unsupported instance");
	}

	public static BtorExpression convertApplicationTermToBtorExpression(final ApplicationTerm appTerm,
			final TransFormula tf, final Map<String, BtorExpression> variableMap, final Boogie2SMT boogie2SMT,
			final BtorScript script) {
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
					convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			sort = ext.getSort();
			return new BtorExpression(sort, BtorExpressionType.SEXT, Arrays.asList(ext));

		// case extract: (slice)
		case "bvnot":
		case "not":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			sort = lhs.getSort();
			return script.createUnaryExpression(NotExpression.class, lhs);

		case "bvneg":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			sort = lhs.getSort();
			return script.createUnaryExpression(NegExpression.class, lhs);

		case "=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return script.createBinaryExpression(EqExpression.class, lhs, rhs);
		case "bvsgt":
		case ">":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGT, Arrays.asList(lhs, rhs));

		case "bvugt":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGT, Arrays.asList(lhs, rhs));

		case "bvsge":
		case ">=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SGTE, Arrays.asList(lhs, rhs));

		case "bvuge":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.UGTE, Arrays.asList(lhs, rhs));

		case "bvslt":
		case "<":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLT, Arrays.asList(lhs, rhs));

		case "bvult":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULT, Arrays.asList(lhs, rhs));

		case "bvsle":
		case "<=":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.SLTE, Arrays.asList(lhs, rhs));

		case "bvule":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(new BtorSort(1), BtorExpressionType.ULTE, Arrays.asList(lhs, rhs));

		case "bvand":
		case "and":
			// Handle nonbinary `and`
			final Term[] andParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(andParams[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(andParams[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestAnd = script.createBinaryExpression(AndExpression.class, lhs, rhs);
			for (i = 2; i < andParams.length; i++) {
				rhs = convertConditionalToBtorExpression(andParams[i], tf, variableMap, boogie2SMT, script);
				latestAnd = script.createBinaryExpression(AndExpression.class, latestAnd, rhs);
			}
			return latestAnd;

		case "bvor":
		case "or":
			// Handle nonbinary `or`
			final Term[] orParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(orParams[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(orParams[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			BtorExpression latestOr = script.createBinaryExpression(OrExpression.class, lhs, rhs);
			for (i = 2; i < orParams.length; i++) {
				rhs = convertConditionalToBtorExpression(orParams[i], tf, variableMap, boogie2SMT, script);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = script.createBinaryExpression(OrExpression.class, latestOr, rhs);
			}
			return latestOr;

		case "bvxor":
			// Handle nonbinary `xor`
			final Term[] xorParams = appTerm.getParameters();
			lhs = convertConditionalToBtorExpression(xorParams[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(xorParams[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			final BtorExpression latestXor = script.createBinaryExpression(XorExpression.class, lhs, rhs);
			for (i = 2; i < xorParams.length; i++) {
				rhs = convertConditionalToBtorExpression(xorParams[i], tf, variableMap, boogie2SMT, script);
				assert (lhs.getSort().equals(rhs.getSort()));
				latestOr = script.createBinaryExpression(XorExpression.class, latestXor, rhs);
			}
			return latestXor;

		case "bvshl":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SLL, Arrays.asList(lhs, rhs));

		case "bvashr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRA, Arrays.asList(lhs, rhs));

		case "bvlshr":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return new BtorExpression(lhs.getSort(), BtorExpressionType.SRL, Arrays.asList(lhs, rhs));

		case "bvadd":
		case "+":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return script.createBinaryExpression(AddExpression.class, lhs, rhs);

		case "bvmul":
		case "*":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return script.createBinaryExpression(MulExpression.class, lhs, rhs);

		case "bvsdiv":
		case "div":
		case "/":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SDIV, Arrays.asList(lhs, rhs));
		case "bvudiv":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UDIV, Arrays.asList(lhs, rhs));

		case "bvsmod":
		case "mod":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SMOD, Arrays.asList(lhs, rhs));

		case "bvsrem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SREM, Arrays.asList(lhs, rhs));

		case "bvurem":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.UREM, Arrays.asList(lhs, rhs));

		case "bvsub":
		case "-":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			assert (lhs.getSort().equals(rhs.getSort()));
			sort = lhs.getSort();
			return new BtorExpression(sort, BtorExpressionType.SUB, Arrays.asList(lhs, rhs));

		case "concat":
			lhs = convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			rhs = convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			return script.createBinaryExpression(ConcatExpression.class, lhs, rhs);

		case "select":
			params = appTerm.getParameters();
			idx = params[1];
			idxs = new ArrayList<>();
			idxs.add(idx);
			// Collect indices of `select` statements
			while (params[0] instanceof ApplicationTerm
					&& ((ApplicationTerm) params[0]).getFunction().getName().equals("select")) {
				params = ((ApplicationTerm) params[0]).getParameters();
				idx = params[1];
				idxs.add(idx);
			}
			i = 1;
			index = convertConditionalToBtorExpression(idxs.get(0), tf, variableMap, boogie2SMT, script);
			// Concatenate the indices
			while (i < idxs.size()) {
				final BtorExpression nextIndex =
						convertConditionalToBtorExpression(idxs.get(i), tf, variableMap, boogie2SMT, script);
				index = new BtorExpression(new BtorSort(index.getSort().size + nextIndex.getSort().size),
						BtorExpressionType.CONCAT, Arrays.asList(index, nextIndex));
				i++;
			}

			array = convertConditionalToBtorExpression(params[0], tf, variableMap, boogie2SMT, script);
			assert (array.getSort().keySort != null);
			assert (array.getSort().keySort.equals(index.getSort()));
			// Apply `read` with concatenated indices
			return new BtorExpression(array.getSort().valueSort, BtorExpressionType.READ, Arrays.asList(array, index));

		case "ite":
			final BtorExpression iteIf =
					convertConditionalToBtorExpression(appTerm.getParameters()[0], tf, variableMap, boogie2SMT, script);
			final BtorExpression iteThen =
					convertConditionalToBtorExpression(appTerm.getParameters()[1], tf, variableMap, boogie2SMT, script);
			final BtorExpression iteElse =
					convertConditionalToBtorExpression(appTerm.getParameters()[2], tf, variableMap, boogie2SMT, script);
			assert (iteThen.getSort().equals(iteElse.getSort()));
			return new BtorExpression(iteThen.getSort(), BtorExpressionType.ITE,
					Arrays.asList(iteIf, iteThen, iteElse));

		case "store":
			params = appTerm.getParameters();
			idx = params[1];
			idxs = new ArrayList<>();
			idxs.add(idx);
			array = convertConditionalToBtorExpression(params[0], tf, variableMap, boogie2SMT, script);
			// Collect indices of `store` statements
			while (params[2] instanceof ApplicationTerm
					&& ((ApplicationTerm) params[2]).getFunction().getName().equals("store")) {
				params = ((ApplicationTerm) params[2]).getParameters();
				idx = params[1];
				idxs.add(0, idx);
			}
			final Term val = params[2];
			arrayValue = convertConditionalToBtorExpression(val, tf, variableMap, boogie2SMT, script);
			i = 1;
			index = convertConditionalToBtorExpression(idxs.get(0), tf, variableMap, boogie2SMT, script);
			// Concatenate the indices
			while (i < idxs.size()) {
				final BtorExpression nextindex =
						convertConditionalToBtorExpression(idxs.get(i), tf, variableMap, boogie2SMT, script);
				index = new BtorExpression(new BtorSort(index.getSort().size + nextindex.getSort().size),
						BtorExpressionType.CONCAT, Arrays.asList(index, nextindex));
				i++;
			}
			assert (array.getSort().keySort != null);
			assert (array.getSort().keySort.equals(index.getSort()));
			assert (array.getSort().valueSort.equals(arrayValue.getSort()));
			// Apply `write` with concatenated indices
			return new BtorExpression(array.getSort(), BtorExpressionType.WRITE,
					Arrays.asList(array, index, arrayValue));

		case "true":
			return script.createOneExpression(new BtorSort(1));

		case "false":
			return script.createZeroExpression(new BtorSort(1));

		default:
			if (BitvectorUtils.isBitvectorConstant(appTerm.getFunction())) {
				final long value = Long.parseLong(appName.substring(2));
				return new BtorExpression(new BtorSort(Integer.parseInt(appTerm.getSort().getIndices()[0])), value);
			}
			throw new UnsupportedOperationException(
					"Converting currently unsupported btor2 expression " + appTerm.getFunction().getName());
		// as const
		// myFunc
		// return null;
		}
	}

}