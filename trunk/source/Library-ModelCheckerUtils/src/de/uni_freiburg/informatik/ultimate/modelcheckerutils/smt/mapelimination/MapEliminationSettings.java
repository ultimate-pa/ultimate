/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class MapEliminationSettings {
	private final boolean mAddInequalities;
	private final boolean mOnlyTrivialImplicationsForModifiedArguments;
	private final boolean mOnlyTrivialImplicationsArrayWrite;
	private final boolean mOnlyArgumentsInFormula;

	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * @param addInequalities
	 *            If true, inequalities provided by the IndexAnalysis are also added as conjuncts to the transformula
	 *            (should be disabled for the LassoRanker).
	 * @param onlyTrivialImplicationsForModifiedArguments
	 *            If true, implications such as (i = j) => (a[i] = a[j]), that occur during handling assignments of
	 *            indices, are only added as conjuncts to the transformula, if the invariant i = j holds (so in this
	 *            case only a[i] = a[j] is added).
	 * @param onlyTrivialImplicationsArrayWrite
	 *            If true, implications such as (i = j) => (a[i] = a[j]), that occur during handling array-writes, are
	 *            only added as conjuncts to the transformula, if the invariant i = j holds (so in this case only a[i] =
	 *            a[j] is added)
	 * @param onlyArgumentsInFormula
	 *            If true, implications such as (i = j) => (a[i] = a[j]) are only added as conjuncts to the
	 *            transformula, if all free-vars of i and j occur in the transformula
	 * @param simplificationTechnique
	 *            SimplicationTechnique
	 * @param xnfConversionTechnique
	 *            XnfConversionTechnique
	 */
	public MapEliminationSettings(final boolean addInequalities,
			final boolean onlyTrivialImplicationsForModifiedArguments, final boolean onlyTrivialImplicationsArrayWrite,
			final boolean onlyArgumentsInFormula, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mAddInequalities = addInequalities;
		mOnlyTrivialImplicationsForModifiedArguments = onlyTrivialImplicationsForModifiedArguments;
		mOnlyTrivialImplicationsArrayWrite = onlyTrivialImplicationsArrayWrite;
		mOnlyArgumentsInFormula = onlyArgumentsInFormula;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}

	public boolean addInequalities() {
		return mAddInequalities;
	}

	public boolean onlyTrivialImplicationsForModifiedArguments() {
		return mOnlyTrivialImplicationsForModifiedArguments;
	}

	public boolean onlyTrivialImplicationsArrayWrite() {
		return mOnlyTrivialImplicationsArrayWrite;
	}

	public boolean onlyArgumentsInFormula() {
		return mOnlyArgumentsInFormula;
	}

	public SimplificationTechnique getSimplificationTechnique() {
		return mSimplificationTechnique;
	}

	public XnfConversionTechnique getXnfConversionTechnique() {
		return mXnfConversionTechnique;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("SimplificationTechnique=").append(getSimplificationTechnique());
		sb.append(" XnfConversionTechnique=").append(getXnfConversionTechnique());
		sb.append(" AddInequalities=").append(addInequalities());
		sb.append(" OnlyTrivialImplicationsArrayWrite=").append(onlyTrivialImplicationsArrayWrite());
		sb.append(" OnlyTrivialImplicationsForModifiedArguments=");
		sb.append(onlyTrivialImplicationsForModifiedArguments());
		sb.append(" OnlyArgumentsInFormula=").append(onlyArgumentsInFormula());
		return sb.toString();
	}
}
