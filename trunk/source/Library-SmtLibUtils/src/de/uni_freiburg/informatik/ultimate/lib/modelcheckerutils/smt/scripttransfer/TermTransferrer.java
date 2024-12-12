/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2019 University of Freiburg
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

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * {@link TermTransferrer} allows you to transfer arbitrary terms from one {@link Script} instance to another, provided
 * the {@link Script} instances contain a {@link HistoryRecordingScript}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class TermTransferrer extends NonDeclaringTermTransferrer {
	protected final HistoryRecordingScript mOldScript;
	protected final HistoryRecordingScript mNewScript;

	protected final Map<Term, Term> mTransferMapping;

	public TermTransferrer(final Script oldScript, final Script newScript) {
		this(oldScript, newScript, new HashMap<>(), false);
	}

	/**
	 * Create a {@link TermTransferrer} that also performs substitution.
	 *
	 * @param oldScript
	 *            The script in which the term was declared.
	 * @param newScript
	 *            The script to which the term should be transferred.
	 * @param transferMapping
	 *            A map from {@link Term} to {@link Term} that is used to substitute {@link Term}s during the transfer.
	 *            The mapped terms must already belong to the new {@link Script} instance.
	 * @param applyLocalSimplifications
	 *            true if new {@link ApplicationTerm}s should be simplified, false otherwise.
	 */
	public TermTransferrer(final Script oldScript, final Script newScript, final Map<Term, Term> transferMapping,
			final boolean applyLocalSimplifications) {
		super(newScript, applyLocalSimplifications);
		mOldScript = Objects.requireNonNull(HistoryRecordingScript.extractHistoryRecordingScript(oldScript),
				"no HistoryRecordingScript");
		mNewScript = Objects.requireNonNull(HistoryRecordingScript.extractHistoryRecordingScript(newScript),
				"no HistoryRecordingScript");
		mTransferMapping = transferMapping;
	}

	public Map<Term, Term> getTransferMapping() {
		return mTransferMapping;
	}

	@Override
	protected void convert(final Term term) {
		final Term mappingResult = mTransferMapping.get(term);
		if (mappingResult != null) {
			setResult(mappingResult);
		} else {
			super.convert(term);
		}
	}

	@Override
	public Sort transferSort(final Sort sort) {
		final String sortName = sort.getName();
		if (!sort.isInternal() && !mNewScript.getSymbolTable().containsKey(sortName)) {
			final ISmtDeclarable sortToDeclare = mOldScript.getSymbolTable().get(sortName);
			sortToDeclare.defineOrDeclare(mNewScript);
		}
		return super.transferSort(sort);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final FunctionSymbol fsymb = appTerm.getFunction();
		final String funSymbName = fsymb.getName();
		if (!fsymb.isIntern() && !mNewScript.getSymbolTable().containsKey(funSymbName)) {
			final ISmtDeclarable funToDeclare = mOldScript.getSymbolTable().get(funSymbName);
			funToDeclare.defineOrDeclare(mNewScript);
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		final TermVariable[] vars = new TermVariable[oldLet.getVariables().length];
		for (int i = 0; i < oldLet.getVariables().length; i++) {
			// Check mTransferMapping first, in case a different mapping was already recorded.
			if (mTransferMapping.containsKey(oldLet.getVariables()[i])) {
				vars[i] = (TermVariable) mTransferMapping.get(oldLet.getVariables()[i]);
			} else {
				vars[i] = transferTermVariable(oldLet.getVariables()[i]);
			}
		}
		final Term result = mNewScript.let(vars, newValues, newBody);
		setResult(result);
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final TermVariable[] vars = new TermVariable[old.getVariables().length];
		for (int i = 0; i < old.getVariables().length; i++) {
			// Check mTransferMapping first, in case a different mapping was already recorded.
			if (mTransferMapping.containsKey(old.getVariables()[i])) {
				vars[i] = (TermVariable) mTransferMapping.get(old.getVariables()[i]);
			} else {
				vars[i] = transferTermVariable(old.getVariables()[i]);
			}
		}
		final Term result = mNewScript.quantifier(old.getQuantifier(), vars, newBody);
		setResult(result);
	}
}
