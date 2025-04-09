package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the n-ary function "X * Y * Z * ..."
 */
public class MultiplicationTerm extends IntegerTerm {
	private final IntegerTerm[] mSubTerms;

	public MultiplicationTerm(final IntegerTerm... subterms) {
		super(SMTLIBConstants.MUL);
		mSubTerms = subterms;
		assert mSubTerms.length > 1;
		for (final IntegerTerm subTerm : mSubTerms) {
			assert subTerm.returnType == ReturnType.Int;
		}
	}

	/**
	 * Returns "X * Y * Z ..." with arguments simplified
	 */
	@Override
	public IntegerTerm simplify() {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		// ... * -X * -Y * ... is equal to ... * X * Y * ...
		int negatedCount = 0;
		for (int i = 0; i < mSubTerms.length; i++) {
			IntegerTerm subTerm = mSubTerms[i];
			if (subTerm instanceof NegationTerm) {
				int stackedMinus = 1;

				while (subTerm instanceof NegationTerm) {
					subTerm = ((NegationTerm) subTerm).getSubTerms().get(0);
					stackedMinus++;
				}
				// After this process, we have innerTerm, which is the first non-Negation child
				// and we have stackedMinus, the amount of negations that were stacked.
				// An even amount cancels out; (-(-X)) = X
				negatedCount += stackedMinus % 2;
			}
			subTerms[i] = subTerm;
		}

		for (int i = 0; i < subTerms.length; i++) {
			subTerms[i] = subTerms[i].simplify();
		}

		final List<IntegerTerm> subTermList = Arrays.asList(subTerms);
		Collections.sort(subTermList, (final IntegerTerm x, final IntegerTerm y) -> Util.compareBaseOrder(x, y));

		// Now, all arguments in mSubTerms are not negation terms.
		// If negatedCount is odd, then the first argument becomes negative.
		if (negatedCount % 2 == 1) {
			subTermList.set(0, subTermList.get(0).negate().simplify());
		}

		return new MultiplicationTerm(subTermList.toArray(new IntegerTerm[subTermList.size()]));
	}

	/**
	 * Returns "-X * Y * Z ..."
	 */
	@Override
	public IntegerTerm negate() {
		final IntegerTerm[] subTerms = mSubTerms.clone();
		subTerms[0] = new NegationTerm(mSubTerms[0]);
		return new MultiplicationTerm(subTerms);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(mSubTerms));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		mSubTerms[0].toString(out, 0);
		for (int i = 1; i < mSubTerms.length; i++) {
			out.append(" * ");
			mSubTerms[i].toString(out, 0);
		}
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof MultiplicationTerm)) {
			return false;
		}
		final MultiplicationTerm castB = (MultiplicationTerm) b;

		final HashSet<IntegerTerm> subTermsA = new HashSet<>(Arrays.asList(mSubTerms));
		final HashSet<IntegerTerm> subTermsB = new HashSet<>(Arrays.asList(castB.mSubTerms));

		return subTermsA.containsAll(subTermsB) && subTermsB.containsAll(subTermsA);
	}

	@Override
	public int hashCode() {
		int result = 71;
		for (final IntegerTerm subTerm : mSubTerms) {
			result = result * 31 + subTerm.hashCode();
		}
		return result;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mSubTerms[0].getVariables();
		for (int i = 1; i < mSubTerms.length; i++) {
			out.addAll(mSubTerms[i].getVariables());
		}
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		final Term[] parameters = new Term[mSubTerms.length];
		for (int i = 0; i < mSubTerms.length; i++) {
			parameters[i] = mSubTerms[i].toSMTTerm(theory);
		}
		return Util.makeTerm(mSymbol, theory, parameters);
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		long out = 1L;

		for (final IntegerTerm subTerm : mSubTerms) {
			out *= subTerm.evaluate(currentState, nextState);
		}

		return out;
	}

	@Override
	public String toCode() {
		final ArrayList<String> elements = new ArrayList<>();
		for (final IntegerTerm subTerm : mSubTerms) {
			elements.add(subTerm.toCode());
		}
		if (elements.size() == 1) {
			return elements.get(0);
		}
		return "(" + String.join(" * ", elements) + ")";
	}

	@Override
	protected MultiplicationTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final IntegerTerm[] subTerms = new IntegerTerm[mSubTerms.length];

		for (int i = 0; i < mSubTerms.length; i++) {
			subTerms[i] = mSubTerms[i].replaceTerm(old, replacement);
		}

		return new MultiplicationTerm(subTerms);
	}
}