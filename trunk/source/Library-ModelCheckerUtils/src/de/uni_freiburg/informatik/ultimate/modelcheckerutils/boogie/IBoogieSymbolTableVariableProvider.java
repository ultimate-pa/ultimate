/*
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Provides BoogieVars from BoogieSymbolTables. This is mainly used in abstract interpretation's abstract domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface IBoogieSymbolTableVariableProvider {

	/**
	 * Returns a {@link BoogieVar} for a variable with name varId.
	 *
	 * @param varId
	 *            The name of the variable.
	 * @param declarationInformation
	 *            The declaration information context.
	 * @param inOldContext
	 *            <code>true</code> if the lookup should be done in the context of old variables, <code>false</code>
	 *            otherwise.
	 * @return The corresponding {@link BoogieVar}.
	 */
	IProgramVar getBoogieVar(final String varId, final DeclarationInformation declarationInformation,
			final boolean inOldContext);

	/**
	 * Returns a {@link BoogieVar} for a variable in the context of some procedure.
	 *
	 * @param varId
	 *            The name of the variable.
	 * @param procedure
	 *            The name of the procedure.
	 * @param isInParam
	 *            <code>true</code> if the variable occurs in the in-parameters of the procedure, <code>false</code>
	 *            otherwise.
	 * @return The corresponding {@link BoogieVar}.
	 */
	IProgramVar getBoogieVar(final String varId, final String procedure, final boolean isInParam);

	/**
	 * Returns a {@link BoogieConst} for a given contant name.
	 *
	 * @param constId
	 *            The name of the constant.
	 * @return The corresponding {@link BoogieConst}.
	 */
	IProgramConst getBoogieConst(final String constId);
}
