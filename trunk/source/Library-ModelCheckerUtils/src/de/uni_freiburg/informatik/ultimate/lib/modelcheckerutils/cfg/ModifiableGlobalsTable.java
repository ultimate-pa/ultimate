/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Provides information which global variables are modifiable by which procedure.
 *
 * @author Matthias Heizmann
 */
public class ModifiableGlobalsTable {

	private final HashRelation<String, IProgramNonOldVar> mProc2Globals;

	public ModifiableGlobalsTable(final HashRelation<String, IProgramNonOldVar> proc2globals) {
		mProc2Globals = new HashRelation<>();
		mProc2Globals.addAll(proc2globals);
	}

	/**
	 * Return the set of all global {@link IProgramNonOldVar}s that may be modified by procedure proc.
	 */
	public Set<IProgramNonOldVar> getModifiedBoogieVars(final String proc) {
		return Collections.unmodifiableSet(mProc2Globals.getImage(proc));
	}

	/**
	 * Returns true iff the corresponding non-oldVar of bv is modifiable by procedure proc.
	 */
	public boolean isModifiable(final IProgramOldVar bv, final String proc) {
		final IProgramNonOldVar bnov = bv.getNonOldVar();
		return mProc2Globals.containsPair(proc, bnov);
	}

	/**
	 * Returns true iff the variable bv is modifiable by procedure proc.
	 */
	public boolean isModifiable(final IProgramNonOldVar bnov, final String proc) {
		return mProc2Globals.containsPair(proc, bnov);
	}

	/**
	 * @return true iff pred contains an oldvar that is not modifiable by procedure proc.
	 */
	public boolean containsNonModifiableOldVars(final IPredicate pred, final String proc) {
		for (final IProgramVar bv : pred.getVars()) {
			if (bv instanceof IProgramOldVar) {
				final boolean modifiable = isModifiable((IProgramOldVar) bv, proc);
				if (!modifiable) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Return equality (= g oldg) where g is the default constant of the BoogieNonOldVar bv and oldg is the default
	 * constant of the corresponding oldVar. If primed is true, we return the primed constant instead of the default
	 * constant.
	 */
	public static Term constructConstantOldVarEquality(final IProgramNonOldVar bv, final boolean primed,
			final Script script) {
		final IProgramOldVar oldVar = bv.getOldVar();
		final Term nonOldConstant = (primed ? bv.getPrimedConstant() : bv.getDefaultConstant());
		final Term oldConstant = (primed ? oldVar.getPrimedConstant() : oldVar.getDefaultConstant());
		return script.term("=", oldConstant, nonOldConstant);
	}


	/**
	 * @return
	 * 		the contents of this ModifiedGlobalsTable as a hash relation
	 */
	public HashRelation<String, IProgramNonOldVar> getProcToGlobals() {
		// if we have an unmodifiableHashRelation some day, use that
		return new HashRelation<>(mProc2Globals);
	}
}
