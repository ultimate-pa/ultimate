package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

/**
 * Helper class to factor out coercions needed in IRA-Logics
 * @author Juergen Christ
 */
public class Coercion {
	public static Term toInt(Term t) {
		assert t.getSort().getName().equals("Real");
		if (t instanceof ConstantTerm) {
			Rational val = SMTAffineTerm.create(t).getConstant();
			assert val.isIntegral();
			return val.toSMTLIB(t.getTheory());
		}
		return t.getTheory().term("to_int", t);
	}
	public static Term toReal(Term t) {
		assert t.getSort().getName().equals("Int");
		if (t instanceof ConstantTerm) {
			SMTAffineTerm tmp = SMTAffineTerm.create(t);
			assert tmp.getConstant().isIntegral();
			BigInteger val = tmp.getConstant().numerator();
			return t.getTheory().constant(
					// Convention: No scale=0 BigDecimals...
					new BigDecimal(val.multiply(BigInteger.TEN), 1),
					t.getTheory().getSort("Real"));
		}
		return t.getTheory().term("to_real", t);
	}
	public static Term coerce(Term t, Sort s) {
		if (t.getSort() == s)
			return t;
		if (s.getName().equals("Int"))
			return toInt(t);
		if (s.getName().equals("Real"))
			return toReal(t);
		throw new InternalError("Should only be called with numeric sort!");
	}
	/// BE CAREFUL: args might be modified!!!
	public static Term buildApp(FunctionSymbol fsymb, Term[] args) {
		if (fsymb.getTheory().getLogic().isIRA())
			for (int i = 0; i < args.length; ++i)
				if (args[i].getSort() != fsymb.getParameterSort(i))
					args[i] = coerce(args[i], fsymb.getParameterSort(i));
		return fsymb.getTheory().term(fsymb, args);
	}
	
	public static Term buildEq(Term lhs, Term rhs) {
		if (lhs.getSort() != rhs.getSort()) {
			assert lhs.getTheory().getLogic().isIRA();
			if (!lhs.getSort().getName().equals("Real"))
				lhs = toReal(lhs);
			if (!rhs.getSort().getName().equals("Real"))
				rhs = toReal(rhs);
		}
		return lhs.getTheory().term("=", lhs, rhs);
	}
	
	public static Term buildDistinct(Term lhs, Term rhs) {
		if (lhs.getSort() != rhs.getSort()) {
			assert lhs.getTheory().getLogic().isIRA();
			if (!lhs.getSort().getName().equals("Real"))
				lhs = toReal(lhs);
			if (!rhs.getSort().getName().equals("Real"))
				rhs = toReal(rhs);
		}
		return lhs.getTheory().distinct(lhs, rhs);
	}
}
