/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class EqPredicate<ACTION extends IIcfgTransition<IcfgLocation>> implements IPredicate {

	private final EqDisjunctiveConstraint<ACTION, EqNode> mConstraint;
	private final String[] mProcedures;
	private final Set<IProgramVar> mVars;
	private final Term mClosedFormula;
	private final Term mFormula;

//	public EqPredicate(EqConstraint<ACTION, EqNode> constraint) {
//
//	}

	public EqPredicate(final EqDisjunctiveConstraint<ACTION, EqNode> constraint, final Set<IProgramVar> vars,
			final String[] procedures, final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript) {
		assert vars != null;
		mConstraint = constraint;
		mVars = vars;
		mProcedures = procedures;


		final Term acc = constraint.getTerm(mgdScript.getScript());
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mgdScript.getScript(), symbolTable);
		mClosedFormula = tvp.getClosedFormula();
		mFormula = tvp.getFormula();
	}

	public EqPredicate(final Term formula, final Set<IProgramVar> vars, final String[] procedures,
			final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript) {
		mConstraint = null;
		mVars = vars;
		mProcedures = procedures;


		final Term acc = formula;
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mgdScript.getScript(), symbolTable);
		mClosedFormula = tvp.getClosedFormula();
		mFormula = tvp.getFormula();

	}


	@Override
	public String[] getProcedures() {
		return mProcedures;
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode> getEqConstraint() {
		assert mConstraint != null;
		return mConstraint;
	}


	@Override
	public String toString() {
		if (mConstraint != null) {
			return mConstraint.toString();
		} else {
			return mFormula.toString();
		}
	}

	@Override
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}
}
