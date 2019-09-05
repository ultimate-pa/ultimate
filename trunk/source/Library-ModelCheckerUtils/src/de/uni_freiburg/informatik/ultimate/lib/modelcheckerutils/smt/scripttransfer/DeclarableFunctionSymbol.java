/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class DeclarableFunctionSymbol implements ISmtDeclarable {

	private final String mId;
	private final String[] mParamIds;
	private final Sort[] mParamSorts;
	private final Sort mResultSort;
	private final Term mFunctionDefinition;

	private Term[] mParamVars;

	/**
	 * Define a SMT function without body.
	 */
	public DeclarableFunctionSymbol(final String smtID, final Sort[] paramSorts, final Sort resultSort) {
		this(smtID, null, paramSorts, resultSort, null);
	}

	/**
	 * Define a SMT function with body.
	 */
	public DeclarableFunctionSymbol(final String smtID, final String[] paramIds, final Sort[] paramSorts,
			final Sort resultSort, final Term subformula) {
		mId = Objects.requireNonNull(smtID);
		mParamSorts = Objects.requireNonNull(paramSorts);
		mResultSort = Objects.requireNonNull(resultSort);
		mParamIds = paramIds;
		mFunctionDefinition = subformula;
	}

	public static DeclarableFunctionSymbol createFromScriptDefineFun(final String fun, final TermVariable[] params,
			final Sort resultSort, final Term definition) {
		final String[] paramIds = new String[params.length];
		final Sort[] paramSorts = new Sort[params.length];
		for (int i = 0; i < params.length; ++i) {
			paramIds[i] = params[i].getName();
			paramSorts[i] = params[i].getSort();
		}
		return new DeclarableFunctionSymbol(fun, paramIds, paramSorts, resultSort, definition);
	}

	public static DeclarableFunctionSymbol createFromScriptDeclareFun(final String fun, final Sort[] paramSorts,
			final Sort resultSort) {
		return new DeclarableFunctionSymbol(fun, paramSorts, resultSort);
	}

	/**
	 * Create an {@link DeclarableFunctionSymbol} from Strings and Sorts using {@link TermParseUtils}.
	 *
	 * Only use this method during testing or to process <code>:smtdefined</code> attributes from Boogie.
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
	 * @return An {@link DeclarableFunctionSymbol} representing a function declaration or definition.
	 */
	public static DeclarableFunctionSymbol createFromString(final Script script, final String smtFunName,
			final String smtFunBody, final String[] paramIds, final Sort[] paramSorts, final Sort resultSort) {
		if (smtFunBody == null) {
			return new DeclarableFunctionSymbol(smtFunName, paramSorts, resultSort);
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
		return new DeclarableFunctionSymbol(smtFunName, paramIds, paramSorts, resultSort, bodyTerm);
	}

	/**
	 * Define or declare this object in the supplied script.
	 *
	 * If the function has a body, this function will first declare parameters with
	 * {@link Script#variable(String, Sort)}, and then define the whole function with
	 * {@link Script#defineFun(String, TermVariable[], Sort, Term)}.
	 *
	 * If the function does not have a body, it will be declared using {@link Script#declareFun(String, Sort[], Sort)}.
	 */
	@Override
	public void defineOrDeclare(final Script script) {
		final NonDeclaringTermTransferrer tt = new NonDeclaringTermTransferrer(script);
		final Sort[] newParamSorts = tt.transferSorts(mParamSorts);
		final Sort newResultSort = tt.transferSort(mResultSort);
		if (mFunctionDefinition == null) {
			script.declareFun(mId, newParamSorts, newResultSort);
		} else {
			final TermVariable[] params = new TermVariable[mParamSorts.length];
			for (int i = 0; i < mParamSorts.length; ++i) {
				if (mParamIds[i] == null) {
					throw new ISmtDeclarable.IllegalSmtDeclarableUsageException(
							"Unnamed parameter in function declaration together with "
									+ Boogie2SmtSymbolTable.ID_SMTDEFINED + " attribute");
				}
				params[i] = script.variable(mParamIds[i], newParamSorts[i]);
			}
			final Term fundef = new NonDeclaringTermTransferrer(script).transform(mFunctionDefinition);
			script.defineFun(mId, params, newResultSort, fundef);
		}
	}

	public Term getDefinition() {
		return mFunctionDefinition;
	}

	@Override
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
		if (mFunctionDefinition == null) {
			throw new ISmtDeclarable.IllegalSmtDeclarableUsageException(
					"Cannot compute parameter vars if there is no body");
		}

		final Map<String, TermVariable> freeVars = new HashMap<>();
		Arrays.stream(mFunctionDefinition.getFreeVars()).forEach(a -> freeVars.put(a.getName(), a));
		mParamVars = new Term[mParamIds.length];
		for (int i = 0; i < mParamIds.length; ++i) {
			mParamVars[i] = freeVars.get(mParamIds[i]);
		}
		return mParamVars;
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		final String name = PrintTerm.quoteIdentifier(mId);
		sb.append('(').append(name);
		for (final Sort s : mParamSorts) {
			sb.append(' ').append(s);
		}
		sb.append(' ').append(mResultSort);
		sb.append(')');
		return sb.toString();
	}

}