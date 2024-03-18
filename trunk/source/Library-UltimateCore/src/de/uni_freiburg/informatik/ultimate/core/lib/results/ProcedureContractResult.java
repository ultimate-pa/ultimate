/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Report a procedure contract that holds at ELEM which is a node in an Ultimate model. The contract is given as an
 * expression of type E.
 *
 * @author Matthias Heizmann
 */
public class ProcedureContractResult<ELEM extends IElement, E> extends AbstractResultAtElement<ELEM> {

	private final String mEnsures;
	private final String mRequires;
	private final String mProcedureName;

	/**
	 * Constructor.
	 *
	 * @param location
	 *            the Location
	 */
	public ProcedureContractResult(final String plugin, final ELEM position,
			final IBacktranslationService translatorSequence, final String procedureName, final E requires,
			final E ensures) {
		super(position, plugin, translatorSequence);
		mProcedureName = procedureName;
		mRequires = translateTerm(requires);
		mEnsures = translateTerm(ensures);
	}

	@SuppressWarnings("unchecked")
	private String translateTerm(final E term) {
		final String result = mTranslatorSequence.translateExpressionToString(term, (Class<E>) term.getClass());
		if ("1".equals(result)) {
			return null;
		}
		return result;
	}

	public String getEnsuresResult() {
		return mEnsures;
	}

	public String getReqiresResult() {
		return mRequires;
	}

	@Override
	public String getShortDescription() {
		return "Procedure Contract for " + mProcedureName;
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Derived contract for procedure ");
		sb.append(mProcedureName);
		sb.append(".");
		if (mRequires != null) {
			sb.append(" Requires: ");
			sb.append(mRequires);
		}
		if (mEnsures != null) {
			sb.append(" Ensures: ");
			sb.append(mEnsures);
		}
		return sb.toString();
	}

	public boolean isTrivial() {
		return mRequires == null && mEnsures == null;
	}
}
