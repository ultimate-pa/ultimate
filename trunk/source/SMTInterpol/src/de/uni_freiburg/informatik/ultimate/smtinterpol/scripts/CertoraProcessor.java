package de.uni_freiburg.informatik.ultimate.smtinterpol.scripts;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

public class CertoraProcessor extends LoggingScript {
	private final HashSet<String> mNonLinearFunctions = new HashSet<>();
	private final NonLinearExpander mExpander = new NonLinearExpander();

	public CertoraProcessor() throws IOException {
		super("processed.smt2", true);
	}

	class LinearChecker extends TermTransformer {
		boolean isNonLinear = false;

		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			final FunctionSymbol fs = appTerm.getFunction();
			if (fs.isIntern()) {
				switch (fs.getName()) {
				case "*": {
					final Term leftArg = SMTAffineTerm.parseConstant(newArgs[0]);
					final Term rightArg = SMTAffineTerm.parseConstant(newArgs[1]);
					if (newArgs.length != 2
							|| (!(leftArg instanceof ConstantTerm) && !(rightArg instanceof ConstantTerm))) {
						isNonLinear = true;
					}
					break;
				}
				default:
					break;
				}
			}
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	class TVReplacer extends TermTransformer {
		private final Map<TermVariable, Term> mReplacements;

		public TVReplacer(Map<TermVariable, Term> replacements) {
			mReplacements = replacements;
		}

		@Override
		public void convert(Term term) {
			if (term instanceof TermVariable) {
				final TermVariable tv = (TermVariable) term;
				if (mReplacements.containsKey(tv)) {
					setResult(mReplacements.get(tv));
					return;
				}
			}
			super.convert(term);
		}

		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			final FunctionSymbol fs = appTerm.getFunction();
			// replace constant operations by result
			if (fs.isIntern() && fs.getName().equals(SMTLIBConstants.MINUS) && newArgs.length == 2
					&& newArgs[0] instanceof ConstantTerm && newArgs[1] instanceof ConstantTerm) {
				final SMTAffineTerm diff = new SMTAffineTerm(newArgs[0]);
				diff.add(Rational.MONE, newArgs[1]);
				assert (diff.isConstant());
				setResult(diff.getConstant().toTerm(appTerm.getSort()));
				return;
			}
			if (fs.isIntern() && fs.getName().equals(SMTLIBConstants.MUL) && newArgs.length == 2
					&& newArgs[0] instanceof ConstantTerm && newArgs[1] instanceof ConstantTerm) {
				Rational result = new SMTAffineTerm(newArgs[0]).getConstant();
				result = result.mul(new SMTAffineTerm(newArgs[1]).getConstant());
				setResult(result.toTerm(appTerm.getSort()));
				return;
			}
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	class NonLinearExpander extends TermTransformer {
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			final FunctionSymbol fs = appTerm.getFunction();
			if (mNonLinearFunctions.contains(fs.getName())) {
				final TermVariable[] vars = fs.getDefinitionVars();

				final ArrayList<TermVariable> newTvs = new ArrayList<>();
				final ArrayList<Term> newTerms = new ArrayList<>();
				final HashMap<TermVariable, Term> replacements = new HashMap<>();
				for (int i = 0; i < newArgs.length; i++) {
					if (newArgs[i] instanceof ConstantTerm
							|| (newArgs[i] instanceof ApplicationTerm
									&& ((ApplicationTerm) newArgs[i]).getParameters().length == 0)
							|| newArgs[i] instanceof TermVariable) {
						replacements.put(vars[i], newArgs[i]);
					} else {
						newTvs.add(vars[i]);
						newTerms.add(newArgs[i]);
					}
				}
				Term body = new TVReplacer(replacements).transform(fs.getDefinition());
				body = expandNonLinear(body);
				if (!newTvs.isEmpty()) {
					final TermVariable[] tvs = newTvs.toArray(new TermVariable[newTvs.size()]);
					final Term[] values = newTerms.toArray(new Term[newTerms.size()]);
					body = mScript.let(tvs, values, body);
				}
				setResult(body);
				return;
			}
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	private boolean isNonLinearDefinition(Term definition) {
		final LinearChecker checker = new LinearChecker();
		checker.transform(definition);
		return checker.isNonLinear;
	}

	private Term expandNonLinear(Term term) {
		return mExpander.transform(term);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, Term definition)
			throws SMTLIBException {
		definition = expandNonLinear(definition);
		if (isNonLinearDefinition(definition)) {
			mNonLinearFunctions.add(fun);
			mScript.defineFun(fun, params, resultSort, definition);
		} else {
			super.defineFun(fun, params, resultSort, definition);
		}
	}

	@Override
	public LBool assertTerm(Term term) {
		term = expandNonLinear(term);
		return super.assertTerm(term);
	}
}
