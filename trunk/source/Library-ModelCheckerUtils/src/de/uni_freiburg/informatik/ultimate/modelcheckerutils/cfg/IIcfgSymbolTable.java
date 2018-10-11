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
 */package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Symbol table for interprocedural control flow graphs (ICFG)
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IIcfgSymbolTable {

	/**
	 * Each {@link IProgramVar} has a unique {@link TermVariable}, this method allows us to do the inverse mapping.
	 *
	 * @param at
	 *            {@link TermVariable} that is the {@link IProgramVar#getTermVariable()} of an {@link IProgramVar}
	 * @return {@link IProgramVar} such that parameter at is {@link IProgramVar#getTermVariable()}
	 */
	IProgramVar getProgramVar(TermVariable tv);

	/**
	 * Each {@link IProgramConst} has a unique {@link ApplicationTerm}, this method allows us to do the inverse mapping.
	 *
	 * @param at
	 *            {@link ApplicationTerm} that is the {@link IProgramConst#getDefaultConstant()} of an
	 *            {@link IProgramConst}
	 * @return {@link IProgramConst} such that parameter at is {@link IProgramConst#getDefaultConstant()}
	 */
	IProgramConst getProgramConst(ApplicationTerm at);

	/**
	 * @return Set of all global (non-old) variables that occur in the ICFG.
	 */
	Set<IProgramNonOldVar> getGlobals();

	/**
	 * @return all local variables, input parameters and output parameters for a given procedure.
	 */
	Set<ILocalProgramVar> getLocals(String procedurename);

	/**
	 * @return global constants;
	 */
	Set<IProgramConst> getConstants();

	/**
	 *
	 * @return a Set containing the default constants of all {@link IProgramVar}s saved in this {@link IIcfgSymbolTable}
	 *         (e.g., the ones obtainable by calling getGlobals or getLocals).
	 */
	Set<ApplicationTerm> computeAllDefaultConstants();

}