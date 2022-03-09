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

import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ConstantFinder;
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
	 * This constructor is package-private use {@link TransFormulaBuilder} to construct TransFormulas.
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
		assert SmtUtils.neitherKeyNorValueIsNull(inVars) : "null in inVars";
		assert SmtUtils.neitherKeyNorValueIsNull(outVars) : "null in outVars";
		assert !branchEncoders.isEmpty() || mClosedFormula.getFreeVars().length == 0 : String
				.format("free variables %s", Arrays.asList(mClosedFormula.getFreeVars()));
		assert allSubsetInOutAuxBranch() : "unexpected vars in TransFormula";
		assert eachAuxVarOccursInForula() == null : "Superfluous aux var: " + eachAuxVarOccursInForula();

		mAssignedVars = TransFormulaUtils.computeAssignedVars(inVars, outVars);
		// TODO: The following line is a workaround, in the future the set of
		// constants will be part of the input and we use findConstants only
		// in the assertion
		assert doConstantConsistencyCheck() : "consts inconsistent";
		// assert isSupersetOfOccurringConstants(mConstants, mFormula) :
		// "forgotten constant";
	}

	private boolean doConstantConsistencyCheck() {
		boolean consistent = true;
		final Set<ApplicationTerm> constantsInFormula = new ConstantFinder().findConstants(mFormula, false);
		final Set<ApplicationTerm> nonTheoryConstantTerms = new HashSet<>();
		for (final IProgramConst programConsts : getNonTheoryConsts()) {
			consistent &= !programConsts.getDefaultConstant().getFunction().isIntern();
			assert consistent : "is theory symbol";
			nonTheoryConstantTerms.add(programConsts.getDefaultConstant());
			consistent &= constantsInFormula.contains(programConsts.getDefaultConstant());
			assert consistent : "not in formula";
		}
		for (final ApplicationTerm constInFomula : constantsInFormula) {
			if (!constInFomula.getFunction().isIntern()) {
				consistent &= nonTheoryConstantTerms.contains(constInFomula);
				assert consistent : "not in const set: " + constInFomula;
			}
		}
		return consistent;
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
			final IProgramVar inVar = entry.getKey();
			final TermVariable inTermVar = entry.getValue();
			assert !substitutionMapping.containsKey(inTermVar);
			substitutionMapping.put(inTermVar, getConstantForInVar(entry.getKey()));
		}
		for (final Entry<IProgramVar, TermVariable> entry : outVars.entrySet()) {
			final IProgramVar outVar = entry.getKey();
			final TermVariable outTermVar = entry.getValue();
			if (inVars.get(outVar) == outTermVar) {
				// is assigned var
				continue;
			}
			substitutionMapping.put(outTermVar, getConstantForOutVar(entry.getKey(), inVars, outVars));
		}
		for (final TermVariable auxVarTv : auxVars) {
			final Term auxVarConst = ProgramVarUtils.constructConstantForAuxVar(script, auxVarTv);
			substitutionMapping.put(auxVarTv, auxVarConst);
		}
		final Term closedTerm = Substitution.apply(script, substitutionMapping, formula);
		return closedTerm;
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

	private static boolean allVarsContainsFreeVars(final Set<TermVariable> allVars, final Term term,
			final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (final TermVariable tv : freeVars) {
			if (!allVars.contains(tv)) {
				logger.error("not in allVars: " + tv);
				result = false;
			}
		}
		return result;
	}

	private static boolean freeVarsContainsAllVars(final Set<TermVariable> allVars, final Term term,
			final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (final TermVariable tv : allVars) {
			if (!freeVars.contains(tv)) {
				logger.error("not in allVars: " + tv);
				result = false;
			}
		}
		return result;
	}

	/**
	 * Returns true iff all constants (ApplicationTerm with zero parameters) that occur in term are contained in the set
	 * setOfConstants.
	 */
	private static boolean isSupersetOfOccurringConstants(final Set<ApplicationTerm> setOfConstants, final Term term) {
		final Set<ApplicationTerm> constantsInTerm = new ConstantFinder().findConstants(term, false);
		return setOfConstants.containsAll(constantsInTerm);
	}

	private static boolean freeVarsSubsetInOutAuxBranch(final Term term, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> aux,
			final Set<TermVariable> branchEncoders, final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (final TermVariable tv : freeVars) {
			if (inVars.containsValue(tv)) {
				continue;
			}
			if (outVars.containsValue(tv)) {
				continue;
			}
			if (aux.contains(tv)) {
				continue;
			}
			if (branchEncoders.contains(tv)) {
				continue;
			}
			logger.error("neither in out aux: " + tv);
			result = false;
		}
		return result;
	}

	/**
	 * Returns true if each Term variable in mVars occurs as inVar, outVar, auxVar, or branchEncoder
	 */
	private boolean allSubsetInOutAuxBranch() {
		boolean result = true;
		final HashSet<TermVariable> allVars = new HashSet<>(Arrays.asList(mFormula.getFreeVars()));
		for (final TermVariable tv : allVars) {
			result &= super.getInVars().values().contains(tv) || super.getOutVars().values().contains(tv)
					|| super.getAuxVars().contains(tv) || mBranchEncoders.contains(tv);
			assert result : "unexpected variable in formula";
		}
		for (final TermVariable tv : super.getAuxVars()) {
			result &= allVars.contains(tv);
			assert result : "unnecessary many vars in TransFormula";
		}
		return result;
	}

	/**
	 * Returns null if each auxVar is a free variable of the formula. Returns a
	 * counterexample otherwise.
	 */
	private TermVariable eachAuxVarOccursInForula() {
		final HashSet<TermVariable> allVars = new HashSet<>(Arrays.asList(mFormula.getFreeVars()));
		for (final TermVariable tv : super.getAuxVars()) {
			if (!allVars.contains(tv)) {
				return tv;
			}
		}
		return null;
	}

	/**
	 * Returns null if each inVar is a free variable of the formula. Returns a counterexample otherwise. Note that
	 * inVars (like outVars) need not occur in the formula. If we have an inVar that neither occurs as outVar nor in the
	 * formula this indicates that the value of this variable may nondeterministically get any value.
	 */
	public IProgramVar eachInVarOccursInFormula() {
		final HashSet<TermVariable> allVars = new HashSet<>(Arrays.asList(mFormula.getFreeVars()));
		for (final IProgramVar bv : super.getInVars().keySet()) {
			if (!allVars.contains(super.getInVars().get(bv))) {
				return bv;
			}
		}
		return null;
	}


	private boolean eachInVarOccursAsOutVar() {
		for (final IProgramVar bv : super.getInVars().keySet()) {
			if (!super.getOutVars().containsKey(bv)) {
				return false;
			}
		}
		return true;
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

	private static void reportTimeoutResult(final IUltimateServiceProvider services) {
		final String timeOutMessage = "Timeout during computation of TransFormula";
		final TimeoutResult timeOutRes = new TimeoutResult(ModelCheckerUtils.PLUGIN_ID, timeOutMessage);
		services.getResultService().reportResult(ModelCheckerUtils.PLUGIN_ID, timeOutRes);
	}

}
