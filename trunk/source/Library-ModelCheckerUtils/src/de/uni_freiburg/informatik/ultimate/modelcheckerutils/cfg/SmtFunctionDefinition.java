package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class SmtFunctionDefinition {

	private final String mId;
	private final String[] mParamIds;
	private final Sort[] mParamSorts;
	private final Sort mResultSort;
	private final Term mDefinition;

	private Term[] mParamVars;

	/**
	 * Define a SMT function without body.
	 */
	public SmtFunctionDefinition(final String smtID, final Sort[] paramSorts, final Sort resultSort) {
		mId = Objects.requireNonNull(smtID);
		mParamSorts = Objects.requireNonNull(paramSorts);
		mResultSort = Objects.requireNonNull(resultSort);
		mParamIds = null;
		mDefinition = null;
	}

	/**
	 * Define a SMT function with body.
	 */
	public SmtFunctionDefinition(final String smtID, final String[] paramIds, final Sort[] paramSorts,
			final Sort resultSort, final Term subformula) {
		mId = Objects.requireNonNull(smtID);
		mParamSorts = Objects.requireNonNull(paramSorts);
		mResultSort = Objects.requireNonNull(resultSort);
		mParamIds = Objects.requireNonNull(paramIds);
		mDefinition = Objects.requireNonNull(subformula);
	}

	/**
	 * Create an {@link SmtFunctionDefinition} from Strings and Sorts using {@link TermParseUtils}. Useful during
	 * testing or during processing :smtdefined attributes in Boogie code.
	 *
	 * @param script
	 *            A script instance.
	 * @param smtFunName
	 *            The name of the function.
	 * @param smtFunBody
	 *            The body of the function as string. May be null.
	 * @param paramIds
	 *            The name of the parameters. May be null if the body is null.
	 * @param paramSorts
	 *            The sort of the parameters.
	 * @param resultSort
	 *            The sort of the function return value.
	 */
	public static SmtFunctionDefinition create(final Script script, final String smtFunName, final String smtFunBody,
			final String[] paramIds, final Sort[] paramSorts, final Sort resultSort) {
		if (smtFunBody == null) {
			return new SmtFunctionDefinition(smtFunName, paramSorts, resultSort);
		}

		final Term bodyTerm;
		if (paramIds.length == 0) {
			bodyTerm = TermParseUtils.parseTerm(script, smtFunBody);
		} else {
			// this is rather hacky, but seems to work: we quantify the smt body so that we do not have to create
			// new symbols, and then use the body of the term together with the params we created in the actual
			// function declaration.
			final StringBuilder sb = new StringBuilder();
			sb.append("(forall (");
			for (int i = 0; i < paramIds.length; ++i) {
				sb.append("(");
				sb.append(paramIds[i]);
				sb.append(" ");
				sb.append(paramSorts[i]);
				sb.append(")");
			}
			sb.append(") ");
			sb.append(smtFunBody);
			sb.append(")");

			final QuantifiedFormula term = (QuantifiedFormula) TermParseUtils.parseTerm(script, sb.toString());
			bodyTerm = term.getSubformula();
			assert UltimateNormalFormUtils
					.respectsUltimateNormalForm(bodyTerm) : "SMT function body not in Ultimate normal form";
		}
		return new SmtFunctionDefinition(smtFunName, paramIds, paramSorts, resultSort, bodyTerm);
	}

	public void defineOrDeclareFunction(final Script script, final TermTransferrer tt) {
		final Sort[] newParamSorts = tt.transferSorts(mParamSorts);
		final Sort newResultSort = tt.transferSort(mResultSort);
		final SmtFunctionDefinition newFunDef;
		if (mDefinition != null) {
			final Term newDefinition = tt.transform(mDefinition);
			newFunDef = new SmtFunctionDefinition(mId, mParamIds, newParamSorts, newResultSort, newDefinition);
		} else {
			newFunDef = new SmtFunctionDefinition(mId, newParamSorts, newResultSort);
		}
		newFunDef.defineOrDeclareFunction(script);
	}

	public void defineOrDeclareFunction(final Script script) {
		if (mDefinition == null) {
			script.declareFun(mId, mParamSorts, mResultSort);
		} else {
			final TermVariable[] params = new TermVariable[mParamSorts.length];
			for (int i = 0; i < mParamSorts.length; ++i) {
				if (mParamIds[i] == null) {
					throw new IllegalSmtFunctionUsageException(
							"Unnamed parameter in function declaration together with "
									+ Boogie2SmtSymbolTable.ID_SMTDEFINED + " attribute");
				}
				params[i] = script.variable(mParamIds[i], mParamSorts[i]);
			}
			script.defineFun(mId, params, mResultSort, mDefinition);
		}
	}

	public Term getDefinition() {
		return mDefinition;
	}

	public String getName() {
		return mId;
	}

	public String[] getParamIds() {
		return mParamIds;
	}

	public Sort[] getParamSorts() {
		return mParamSorts;
	}

	public Sort getResultSort() {
		return mResultSort;
	}

	public Term[] getParamVars() {
		if (mParamVars == null) {
			mParamVars = computeParamVars();
		}
		return mParamVars;
	}

	private Term[] computeParamVars() {
		if (mDefinition == null) {
			throw new IllegalSmtFunctionUsageException("Cannot compute parameter vars if there is no body");
		}

		final Map<String, TermVariable> freeVars = new HashMap<>();
		Arrays.stream(mDefinition.getFreeVars()).forEach(a -> freeVars.put(a.getName(), a));
		mParamVars = new Term[mParamIds.length];
		for (int i = 0; i < mParamIds.length; ++i) {
			mParamVars[i] = freeVars.get(mParamIds[i]);
		}
		return mParamVars;
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	public static final class IllegalSmtFunctionUsageException extends RuntimeException {

		private static final long serialVersionUID = 1L;

		public IllegalSmtFunctionUsageException(final String msg) {
			super(msg);
		}
	}

}