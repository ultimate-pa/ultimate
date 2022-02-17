/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.concurrency;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
/*
 * Data Structure to assign constraining inVars and constraining outVars to a Letter L
 */

public class VarAbsConstraints<L extends IAction> {
	private final L mLetter;
	private Set<TermVariable> mInVars;
	private Set<TermVariable> mOutVars;

	public VarAbsConstraints(final L letter) {
		mLetter = letter;
		mInVars = Collections.emptySet();
		mOutVars = Collections.emptySet();
	}

	public VarAbsConstraints(final L letter, final Set<TermVariable> inVars, final Set<TermVariable> outVars) {
		mLetter = letter;
		mInVars = inVars;
		mOutVars = outVars;
	}

	public L getLetter() {
		return mLetter;
	}

	public Set<TermVariable> getInVars() {
		return mInVars;
	}

	public Set<TermVariable> getOutVars() {
		return mOutVars;
	}

	public void setInVars(final Set<TermVariable> inVars) {
		mInVars = inVars;
	}

	public void setOutVars(final Set<TermVariable> outVars) {
		mOutVars = outVars;
	}

	public void addInVars(final Set<TermVariable> inVars) {
		mInVars.addAll(inVars);

	}

	public void addOutVars(final Set<TermVariable> outVars) {
		mOutVars.addAll(outVars);
	}

}
