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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.MultiTermResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Classes that implement this interface represent an {@link IAction} that
 * defines the effect that a join has to the (non-control-flow)
 * variables of the system. A join is the transition that brings the system
 * from a forked procedure back to the joining procedure. This means that the
 * effect of the join is that
 * <ul>
 * <li> variables that are assigned by the fork get the values that are returned by the procedure
 * <li> all local variables that occure only in the context of the forked procedure are havoced.
 * <ul/>
 *
 * @author Lars Nitzke (lars.nitzke@outlook.com)
 *
 */
public interface IJoinActionThreadCurrent extends IAction {

	public JoinSmtArguments getJoinSmtArguments();


	public static class JoinSmtArguments {

		private final MultiTermResult mThreadIdArguments;
		private final List<IProgramVar> mAssignmentLhs;

		public JoinSmtArguments(final MultiTermResult threadIdArguments, final List<IProgramVar> assignmentLhs) {
			super();
			mThreadIdArguments = threadIdArguments;
			mAssignmentLhs = assignmentLhs;
		}

		public MultiTermResult getThreadIdArguments() {
			return mThreadIdArguments;
		}

		public List<IProgramVar> getAssignmentLhs() {
			return mAssignmentLhs;
		}

		public UnmodifiableTransFormula constructThreadIdAssumption(final IIcfgSymbolTable symbolTable,
				final ManagedScript mgdScript, final List<IProgramVar> leftHandSides) {
			final Term[] terms = getThreadIdArguments().getTerms();
			return TransFormulaBuilder.constructEqualityAssumption(leftHandSides, Arrays.asList(terms), symbolTable, mgdScript);
		}

		public UnmodifiableTransFormula constructResultAssignment(final ManagedScript mgdScript,
				final List<? extends IProgramVar> rightHandSides) {
			final List<IProgramVar> assignmentLhs = getAssignmentLhs();
			return TransFormulaBuilder.constructAssignment(assignmentLhs, rightHandSides, mgdScript);
		}
	}

}
