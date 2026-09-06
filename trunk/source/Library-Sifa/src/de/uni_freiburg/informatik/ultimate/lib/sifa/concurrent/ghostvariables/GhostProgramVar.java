/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GhostProgramVar implements IProgramVar {

	private static final long serialVersionUID = 1L;

	private final String mName;
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;

	private GhostProgramVar(final String name, final TermVariable termVariable, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedConstant) {
		mName = name;
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
	}

	public static GhostProgramVar construct(final String name, final Sort sort, final ManagedScript script,
			final Object lockOwner) {
		final TermVariable tv = script.constructFreshTermVariable(name, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(script, lockOwner, sort, name);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(script, lockOwner, sort, name);
		return new GhostProgramVar(name, tv, defaultConstant, primedConstant);
	}

	@Override
	public String getGloballyUniqueId() {
		return mName;
	}

	@Override
	public boolean isGlobal() {
		return true;
	}

	@Override
	public boolean isOldvar() {
		return false;
	}

	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}

	@Override
	public String getProcedure() {
		return null;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}

	@Override
	public Term getTerm() {
		return mTermVariable;
	}

	@Override
	public String toString() {
		return mName;
	}
}
