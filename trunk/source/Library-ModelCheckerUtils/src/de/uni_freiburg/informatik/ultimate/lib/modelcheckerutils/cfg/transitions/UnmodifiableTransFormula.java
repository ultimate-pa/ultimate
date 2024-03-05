/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.UltimateNormalFormUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Unmodifiable variant of {@link TransFormula}
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
@SuppressWarnings("squid:S2055")
public class UnmodifiableTransFormula extends TransFormula implements Serializable {
	private static final long serialVersionUID = 7058102586141801399L;
	private final Term mFormula;
	private final Set<IProgramVar> mAssignedVars;
	private final Set<TermVariable> mBranchEncoders;
	private final Infeasibility mInfeasibility;
	private final Term mClosedFormula;

	/**
	 * Was the solver able to prove infeasiblity of a TransFormula. UNPROVEABLE means that TransFormula could be
	 * infeasible but the solver is not able to prove the infeasibility.
	 */
	public enum Infeasibility {
		INFEASIBLE, UNPROVEABLE, NOT_DETERMINED,
		// FIXME: Introduce value for FEASIBLE
	}

	/**
	 * This constructor is package-private. Use {@link TransFormulaBuilder} to construct TransFormulas.
	 *
	 * @param nonTheoryConsts
	 */
	UnmodifiableTransFormula(final Term formula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final ImmutableSet<IProgramConst> nonTheoryConsts,
			final ImmutableSet<TermVariable> auxVars, final ImmutableSet<TermVariable> branchEncoders,
			final Infeasibility infeasibility, final ManagedScript script) {
		super(inVars, outVars, auxVars, nonTheoryConsts);
		assert UltimateNormalFormUtils.respectsUltimateNormalForm(formula) : "Term not in UltimateNormalForm";

		mFormula = formula;
		mBranchEncoders = branchEncoders;
		mInfeasibility = infeasibility;
		mClosedFormula =
				computeClosedFormula(formula, super.getInVars(), super.getOutVars(), super.getAuxVars(), script);
		mAssignedVars = TransFormulaUtils.computeAssignedVars(inVars, outVars);

		assert SmtUtils.neitherKeyNorValueIsNull(inVars) : "null in inVars";
		assert SmtUtils.neitherKeyNorValueIsNull(outVars) : "null in outVars";
		assert !branchEncoders.isEmpty() || mClosedFormula.getFreeVars().length == 0 : String
				.format("free variables %s", Arrays.asList(mClosedFormula.getFreeVars()));
		assert allSubsetInOutAuxBranch() : "unexpected vars in TransFormula";
		assert eachAuxVarOccursInFormula() == null : "Superfluous aux var: " + eachAuxVarOccursInFormula();
		assert termVariablesHaveUniqueProgramVar() : "Same TermVariable used for different program variables";
		assert doConstantConsistencyCheck() : "consts inconsistent";
		assert disjointVarSets() : "non-disjoint vars in TransFormula";
	}

	/**
	 * Construct formula where
	 * <ul>
	 * <li>each inVar is replaced by default constant of corresponding BoogieVar
	 * <li>and each outVar is replaced by primed constant of corresponding BoogieVar
	 * <li>each auxVar is replaced by a constant (with the same name as the auxVar)
	 * </ul>
	 * If formula contained no branch encoders the result is a closed formula (does not contain free variables)
	 *
	 * @param existingAuxVarConsts
	 *            if true we assume that the constants for the auxVars already exist, otherwise we construct them
	 *
	 */
	public static Term computeClosedFormula(final Term formula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> auxVars, final ManagedScript script) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
			final TermVariable inTermVar = entry.getValue();
			assert !substitutionMapping.containsKey(inTermVar);
			substitutionMapping.put(inTermVar, getConstantForInVar(entry.getKey()));
		}
		for (final Entry<IProgramVar, TermVariable> entry : outVars.entrySet()) {
			final IProgramVar outVar = entry.getKey();
			final TermVariable outTermVar = entry.getValue();
			if (inVars.get(outVar) == outTermVar) {
				// is handled above
				continue;
			}
			substitutionMapping.put(outTermVar, getConstantForOutVar(entry.getKey(), inVars, outVars));
		}
		for (final TermVariable auxVarTv : auxVars) {
			final Term auxVarConst = ProgramVarUtils.constructConstantForAuxVar(script, auxVarTv);
			substitutionMapping.put(auxVarTv, auxVarConst);
		}
		return Substitution.apply(script, substitutionMapping, formula);
	}

	/**
	 * Return the constant (resp. 0-ary function symbol) that represents the inVar of the {@link IProgramVar} pv in the
	 * closed form of the formula of an {@link UnmodifiableTransFormula}.
	 *
	 */
	public static Term getConstantForInVar(final IProgramVar pv) {
		return pv.getDefaultConstant();
	}

	/**
	 * Return the constant (resp. 0-ary function symbol) that represents the outVar of the {@link IProgramVar} pv in the
	 * closed form of the formula of an {@link UnmodifiableTransFormula}.
	 *
	 */
	public static Term getConstantForOutVar(final IProgramVar pv, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		final Term inVar = inVars.get(pv);
		final Term outVar = outVars.get(pv);
		if (inVar == outVar) {
			return pv.getDefaultConstant();
		}
		return pv.getPrimedConstant();
	}

	/**
	 * Returns true if each Term variable in mVars occurs as inVar, outVar, auxVar, or branchEncoder
	 */
	private boolean allSubsetInOutAuxBranch() {
		boolean result = true;
		for (final TermVariable tv : mFormula.getFreeVars()) {
			result &= mInVars.values().contains(tv) || mOutVars.values().contains(tv) || mAuxVars.contains(tv)
					|| mBranchEncoders.contains(tv);
			assert result : "unexpected variable in formula";
		}
		return result;
	}

	private boolean disjointVarSets() {
		boolean result = true;
		for (final TermVariable tv : super.getInVars().values()) {
			result &= !super.getAuxVars().contains(tv);
			assert result : "in var is also aux var: " + tv;
		}
		for (final TermVariable tv : super.getOutVars().values()) {
			result &= !super.getAuxVars().contains(tv);
			assert result : "out var is also aux var: " + tv;
		}
		return result;
	}

	/**
	 * Returns null if each auxVar is a free variable of the formula. Returns a counterexample otherwise.
	 */
	private TermVariable eachAuxVarOccursInFormula() {
		final HashSet<TermVariable> allVars = new HashSet<>(Arrays.asList(mFormula.getFreeVars()));
		for (final TermVariable tv : super.getAuxVars()) {
			if (!allVars.contains(tv)) {
				return tv;
			}
		}
		return null;
	}

	private boolean termVariablesHaveUniqueProgramVar() {
		final Map<TermVariable, IProgramVar> progVars = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : mInVars.entrySet()) {
			final IProgramVar existing = progVars.get(entry.getValue());
			if (existing != null && existing != entry.getKey()) {
				return false;
			}
			progVars.put(entry.getValue(), entry.getKey());
		}
		for (final Map.Entry<IProgramVar, TermVariable> entry : mOutVars.entrySet()) {
			final IProgramVar existing = progVars.get(entry.getValue());
			if (existing != null && existing != entry.getKey()) {
				return false;
			}
			progVars.put(entry.getValue(), entry.getKey());
		}
		return true;
	}

	private boolean doConstantConsistencyCheck() {
		boolean consistent = true;
		final Set<ApplicationTerm> constantsInFormula = SmtUtils.extractConstants(mFormula, false);
		final Set<ApplicationTerm> nonTheoryConstantTerms = new HashSet<>();
		for (final IProgramConst programConsts : getNonTheoryConsts()) {
			consistent &= !programConsts.getDefaultConstant().getFunction().isIntern();
			assert consistent : "is theory symbol";
			nonTheoryConstantTerms.add(programConsts.getDefaultConstant());
			consistent &= constantsInFormula.contains(programConsts.getDefaultConstant());
			assert consistent : "not in formula";
		}
		for (final ApplicationTerm constInFormula : constantsInFormula) {
			if (!constInFormula.getFunction().isIntern()) {
				consistent &= nonTheoryConstantTerms.contains(constInFormula);
				assert consistent : "not in const set: " + constInFormula;
			}
		}
		return consistent;
	}

	@Override
	public Term getFormula() {
		return mFormula;
	}

	public Set<TermVariable> getBranchEncoders() {
		return Collections.unmodifiableSet(mBranchEncoders);
	}

	public Term getClosedFormula() {
		return mClosedFormula;
	}

	/**
	 * @return the mAssignedVars
	 */
	@Override
	public Set<IProgramVar> getAssignedVars() {
		return Collections.unmodifiableSet(mAssignedVars);
	}

	@Override
	public String toString() {
		return toStringInternal(mFormula.toString());
	}

	public String toStringDirect() {
		return toStringInternal(mFormula.toStringDirect());
	}

	private String toStringInternal(final String formula) {
		return "Formula: " + formula + "  InVars " + super.getInVars() + "  OutVars" + super.getOutVars() + "  AuxVars"
				+ super.getAuxVars() + "  AssignedVars" + mAssignedVars;
	}

	public Infeasibility isInfeasible() {
		return mInfeasibility;
	}
}
