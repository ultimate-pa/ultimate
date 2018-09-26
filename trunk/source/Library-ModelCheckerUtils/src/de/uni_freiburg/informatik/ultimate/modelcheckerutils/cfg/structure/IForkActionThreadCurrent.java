/*
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.MultiTermResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Classes that implement this interface represent an {@link IAction} that
 * defines the effect that a procedure fork has to the (non-control-flow)
 * variables of the system. In our terminology, a procedure fork is the
 * transition that brings the system from the forking procedure to the forked
 * procedure. This means that the effect of the of a procedure fork is that all
 * input variables of the forking procedure are assigned and all local variables
 * of the forking procedure are havoced.
 *
 * @author Lars Nitzke (lars.nitzke@outlook.com)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IForkActionThreadCurrent extends IAction {
	/*@Override
	default UnmodifiableTransFormula getTransformula() {
		// TODO: return transormula with true or transformular without an action.
		return
	}*/

	public String getNameOfForkedProcedure();

	public ForkSmtArguments getForkSmtArguments();


	public static class ForkSmtArguments {

		private final MultiTermResult mThreadIdArguments;
		private final MultiTermResult mProcedureArguments;

		public ForkSmtArguments(final MultiTermResult threadIdArguments, final MultiTermResult procedureArguments) {
			super();
			mThreadIdArguments = threadIdArguments;
			mProcedureArguments = procedureArguments;
		}

		public MultiTermResult getThreadIdArguments() {
			return mThreadIdArguments;
		}

		public MultiTermResult getProcedureArguments() {
			return mProcedureArguments;
		}

		public UnmodifiableTransFormula constructThreadIdAssignment(final IIcfgSymbolTable symbolTable,
				final ManagedScript mgdScript, final List<IProgramVar> leftHandSides) {
			final Term[] terms = getThreadIdArguments().getTerms();
			return TransFormulaBuilder.constructAssignment(leftHandSides, Arrays.asList(terms), symbolTable, mgdScript);
		}

		public UnmodifiableTransFormula constructInVarsAssignment(final IIcfgSymbolTable symbolTable,
				final ManagedScript mgdScript, final List<? extends IProgramVar> leftHandSides) {
			final Term[] terms = getProcedureArguments().getTerms();
			return TransFormulaBuilder.constructAssignment(leftHandSides, Arrays.asList(terms), symbolTable, mgdScript);
		}
	}
}
