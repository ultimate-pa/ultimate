/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;

/**
 * Variant of TermTransferrer that transfers only the boolean structure of a term. Each relation of non-boolean
 * arguments (i.e., literals in the boolean structure) is transferred to a fresh TermVariable. QuantifiedFormulas are
 * always considered as a literal even if they only quantify boolean Variables (we might change this in the future).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TermTransferrerBooleanCore extends TermTransferrer {

	/**
	 * Auxiliary term that is used in the "recurse phase" to mark non-boolean subterms. Later, in the "construction
	 * phase" we identify literals as the {@link ApplicationTerm}s that have an argument that was replaced by the
	 * auxiliary term.
	 */
	private final Term mAuxiliaryTerm;
	private static final String FRESH_TERM_PREFIX = "FBV_";
	private int mFreshTermCounter;
	private final ConstructionCache<Term, Term> mConstructionCache;

	public TermTransferrerBooleanCore(final Script oldScript, final Script newScript) {
		super(oldScript, newScript);
		mAuxiliaryTerm = constructAuxiliaryTerm();
		mFreshTermCounter = 0;
		mConstructionCache = new ConstructionCache<>(this::constructTerm);
	}

	private Term constructAuxiliaryTerm() {
		final String name = this.getClass().getCanonicalName() + "_AUX";
		mNewScript.declareFun(name, new Sort[0], SmtSortUtils.getBoolSort(mNewScript));
		return mNewScript.term(name);
	}

	private Term constructTerm(final Term key) {
		final String name = FRESH_TERM_PREFIX + mFreshTermCounter;
		mFreshTermCounter++;
		mNewScript.declareFun(name, new Sort[0], SmtSortUtils.getBoolSort(mNewScript));
		final Term value = mNewScript.term(name);
		mBacktransferMapping.put(value, key);
		return value;
	}

	@Override
	protected void convert(final Term term) {
		if (!SmtSortUtils.isBoolSort(term.getSort())) {
			setResult(mAuxiliaryTerm);
		} else if (term instanceof QuantifiedFormula) {
			final Term result = mConstructionCache.getOrConstruct(term);
			setResult(result);
		} else {
			super.convert(term);
		}
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		if (Arrays.asList(newArgs).contains(mAuxiliaryTerm)) {
			final Term result = mConstructionCache.getOrConstruct(appTerm);
			setResult(result);
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

}
