/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * A way to create IBoogieVar's, that create a TermVariable only on demand (when calling getTermVariable())
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public final class TemporaryBoogieVar implements IProgramVar {
	private final String mId;
	private final Sort mSort;
	private final ManagedScript mManagedScript;
	private TermVariable mTermVariable;
	private static final long serialVersionUID = 1L;

	public TemporaryBoogieVar(final String identifier, final Sort sort, final ManagedScript managedScript) {
		mId = identifier;
		mSort = sort;
		mManagedScript = managedScript;
	}

	public boolean hasTermVariable() {
		return mTermVariable != null;
	}

	@Override
	public TermVariable getTermVariable() {
		if (mTermVariable == null) {
			mTermVariable = mManagedScript.constructFreshTermVariable(mId, mSort);
		}
		return mTermVariable;
	}

	@Override
	public String getGloballyUniqueId() {
		return mId;
	}

	@Override
	public String toString() {
		return mId;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public Term getTerm() {
		return getTermVariable();
	}

	@Override
	public boolean isGlobal() {
		return false;
	}

	@Override
	public boolean isOldvar() {
		return false;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		throw new UnsupportedOperationException("TemporaryBoogieVar's don't have default constants.");
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		throw new UnsupportedOperationException("TemporaryBoogieVar's don't have primed constants.");
	}

	@Override
	public String getProcedure() {
		throw new UnsupportedOperationException("TemporaryBoogieVar's don't have procedures.");
	}
}