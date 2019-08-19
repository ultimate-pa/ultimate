/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker plug-in.
 *
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * @author Matthias Heizmann
 */
public class TermVariableRenamer {
	private final ManagedScript mScript;

	public TermVariableRenamer(final ManagedScript script) {
		mScript = script;
	}

	/**
	 * Return a new transFormula where each {@code TermVariable} x_n corresponding to {@code BoogieVar x} is replaced by
	 * a new {@code TermVariable} named
	 * <ul>
	 * <li>prefix+In_x if x_n occurs only as inVar
	 * <li>prefix+InOut_x if x_n occurs as inVar and outVar
	 * <li>prefix+Out_x if x_n occurs only as outVar.
	 * </ul>
	 * Otherwise x_n is not replaced.
	 */
	public UnmodifiableTransFormula renameVars(final UnmodifiableTransFormula tf, final String prefix) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, tf.getNonTheoryConsts().isEmpty(),
				tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(), false, tf.getBranchEncoders(),
				false);
		final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = tf.getOutVars();

		final Collection<IProgramVar> hasInOnlyVar = new ArrayList<IProgramVar>();
		final Collection<IProgramVar> hasOutOnlyVar = new ArrayList<IProgramVar>();
		final Collection<IProgramVar> commonInOutVar = new ArrayList<IProgramVar>();

		for (final IProgramVar var : inVars.keySet()) {
			final TermVariable inVar = inVars.get(var);
			final TermVariable outVar = outVars.get(var);
			if (inVar == outVar) {
				commonInOutVar.add(var);
			} else {
				hasInOnlyVar.add(var);
			}
		}
		for (final IProgramVar var : outVars.keySet()) {
			final TermVariable outVar = outVars.get(var);
			final TermVariable inVar = inVars.get(var);
			if (inVar != outVar) {
				hasOutOnlyVar.add(var);
			}
		}
		Term formula = tf.getFormula();
		formula = renameVars(hasInOnlyVar, formula, inVars, tfb::addInVar, prefix + "In");
		formula = renameVars(commonInOutVar, formula, inVars, tfb::addInVar, prefix + "InOut");
		formula = renameVars(commonInOutVar, formula, outVars, tfb::addOutVar, prefix + "InOut");
		formula = renameVars(hasOutOnlyVar, formula, outVars, tfb::addOutVar, prefix + "Out");

		tfb.setFormula(formula);
		tfb.setInfeasibility(tf.isInfeasible());
		tfb.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mScript);
		return tfb.finishConstruction(mScript);
	}

	/**
	 * For each {@code BoogieVar x} Let tv_old=variableMapping.get(x)
	 * <ul>
	 * <li>Create a TermVariable tv_new named prefix+x
	 * <li>replace tv_old by tv_new in formula
	 * <li>add x->tv_new to the varAdder functional interface
	 * <li>remove tv_old from allVars
	 * <li>add tv_new to allVars
	 * </ul>
	 */
	private Term renameVars(final Collection<IProgramVar> boogieVars, Term formula,
			final Map<IProgramVar, TermVariable> variableMapping, final IVarAdder varAdder, final String prefix) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();

		for (final IProgramVar var : boogieVars) {
			final TermVariable oldVar = variableMapping.get(var);
			final TermVariable newVar = getNewTermVariable(var, oldVar, prefix);
			varAdder.addVar(var, newVar);
			substitutionMapping.put(oldVar, newVar);
		}
		formula = (new Substitution(mScript, substitutionMapping)).transform(formula);
		return formula;
	}

	private TermVariable getNewTermVariable(final IProgramVar var, final TermVariable tv, final String prefix) {
		// TODO: if this fails because old var and non-oldvar get same variable use getGloballyUniqueId()
		final TermVariable result = mScript.variable(prefix + "_" + var.getGloballyUniqueId(), tv.getSort());
		return result;
	}

	@FunctionalInterface
	public interface IVarAdder {
		public TermVariable addVar(final IProgramVar key, final TermVariable value);
	}
}
