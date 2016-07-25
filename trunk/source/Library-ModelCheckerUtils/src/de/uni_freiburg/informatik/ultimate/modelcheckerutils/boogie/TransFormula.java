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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Represents the transition of a program or a transition system as an SMT
 * formula. The formula denotes a binary relation of this-state/next-state
 * pairs, where we consider a state as a variable assignment. The variables that
 * describe the "this-state"s are given as a BoogieVar, stored as the keySet of
 * the Map mInVars. mInVars maps to each of these variables a corresponding
 * TermVariable in the formula. The variables that describe the "next-state"s
 * are given as a set of strings, stored as the keySet of the Map mOutVars.
 * mInVars maps to each of these variables a corresponding TermVariable in the
 * formula. All TermVariables that occur in the formula are stored in the Set
 * mVars. The names of all variables that are assigned/updated by this
 * transition are stored in mAssignedVars (this information is obtained from
 * mInVars and mOutVars). If a variable does not occur in the this-state, but
 * in the next-state it may have any value (think of a Havoc Statement).
 * <p>
 * A TransFormula represents the set of transitions denoted by the formula φ
 * over primed and unprimed variables where φ is obtained by
 * <ul>
 * <li>first replacing for each x ∈ dom(invar) the TermVariable invar(x) in
 * mFormula by x
 * <li>then replacing for each x ∈ dom(outvar) the TermVariable onvar(x) in
 * mFormula by x'
 * <li>finally, adding the conjunct x=x' for each x∈(dom(invar)⋂dom(outvar)
 * such that invar(x)=outvar(x)
 * </ul>
 * 
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TransFormula implements Serializable {
	private static final long serialVersionUID = 7058102586141801399L;
	private final Term mFormula;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final Set<IProgramVar> mAssignedVars;
	private final Map<TermVariable, Term> mAuxVars;
	private final Set<TermVariable> mBranchEncoders;
	private final Infeasibility mInfeasibility;
	private final Term mClosedFormula;
	private final Set<ApplicationTerm> mConstants;

	/**
	 * Was the solver able to prove infeasiblity of a TransFormula. UNPROVEABLE
	 * means that TransFormula could be infeasible but the solver is not able to
	 * prove the infeasibility.
	 */
	public enum Infeasibility {
		INFEASIBLE, UNPROVEABLE, NOT_DETERMINED
	}

	public TransFormula(final Term formula, final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Map<TermVariable, Term> auxVars, final Set<TermVariable> branchEncoders, final Infeasibility infeasibility,
			final Term closedFormula, final boolean allowSuperflousInVars) {
		mFormula = formula;
		mInVars = inVars;
		mOutVars = outVars;
		mAuxVars = auxVars;
		mBranchEncoders = branchEncoders;
		mInfeasibility = infeasibility;
		mClosedFormula = closedFormula;
		assert SmtUtils.neitherKeyNorValueIsNull(inVars) : "null in inVars";
		assert SmtUtils.neitherKeyNorValueIsNull(outVars) : "null in outVars";
		assert (branchEncoders.size() > 0 || closedFormula.getFreeVars().length == 0);
		// mVars = new
		// HashSet<TermVariable>(Arrays.asList(mFormula.getFreeVars()));
		assert allSubsetInOutAuxBranch() : "unexpected vars in TransFormula";
		assert inAuxSubsetAll(allowSuperflousInVars) : "superfluous vars in TransFormula";
		// assert mOutVars.keySet().containsAll(mInVars.keySet()) :
		// " strange inVar";

		mAssignedVars = computeAssignedVars(inVars, outVars);
		// TODO: The following line is a workaround, in the future the set of
		// constants will be part of the input and we use findConstants only
		// in the assertion
		mConstants = (new ConstantFinder()).findConstants(mFormula);
		// assert isSupersetOfOccurringConstants(mConstants, mFormula) :
		// "forgotten constant";

		// if (!eachInVarOccursAsOutVar()) {
		// System.out.println("Fixietest failed");
		// }
	}

	/**
	 * compute the assigned/updated variables. A variable is updated by this
     * transition if it occurs as outVar and
     * - it does not occur as inVar
	 * - or the inVar is represented by a different TermVariable
	 */
	private HashSet<IProgramVar> computeAssignedVars(
			final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		final HashSet<IProgramVar> assignedVars = new HashSet<IProgramVar>();
		for (final IProgramVar var : outVars.keySet()) {
			assert (outVars.get(var) != null);
			if (outVars.get(var) != inVars.get(var)) {
				assignedVars.add(var);
			}
		}
		return assignedVars;
	}

	public TransFormula(final Term formula, final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Map<TermVariable, Term> auxVars, final Set<TermVariable> branchEncoders, final Infeasibility infeasibility, final Term closedFormula) {
		this(formula, inVars, outVars, auxVars, branchEncoders, infeasibility, closedFormula, false);
	}
	
	/**
	 * Construct TransFormula that represents the identity relation restricted
	 * to the predicate pred, i.e., if x is the vector of variables occurring
	 * in pred, the result represents a formula φ(x,x') such that the following
	 * holds.
	 * <ul>
	 * <li> φ(x,x') implies x=x'
	 * <li> ∃x' φ(x,x') is equivalent to pred
	 * </ul>
	 */
	public TransFormula(final IPredicate pred, final Boogie2SMT boogie2smt) {
		final VariableManager variableManager = boogie2smt.getVariableManager();
		final Script script = boogie2smt.getScript();
		
		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		final Map<IProgramVar, TermVariable> boogieVar2TermVariable = new HashMap<IProgramVar, TermVariable>();
		for (final IProgramVar bv : pred.getVars()) {
			final TermVariable freshTv = variableManager.constructFreshTermVariable(bv);
			substitutionMapping.put(bv.getTermVariable(), freshTv);
			boogieVar2TermVariable.put(bv, freshTv);
		}
		mInVars = boogieVar2TermVariable;
		mOutVars = boogieVar2TermVariable;
		mFormula = (new SafeSubstitution(script, substitutionMapping)).transform(pred.getFormula());
		if (SmtUtils.isFalse(pred.getFormula())) {
			mInfeasibility = Infeasibility.INFEASIBLE;
		} else {
			mInfeasibility = Infeasibility.NOT_DETERMINED;
		}
		mBranchEncoders = Collections.emptySet();
		mAuxVars = Collections.emptyMap();
		mConstants = (new ConstantFinder()).findConstants(mFormula);
		mAssignedVars = computeAssignedVars(mInVars, mOutVars);
		mClosedFormula = computeClosedFormula(mFormula, mInVars, mOutVars, mAuxVars, boogie2smt);
	}

	/**
	 * Construct formula where
	 * <ul>
	 * <li>each inVar is replaced by default constant of corresponding BoogieVar
	 * <li>and each outVar is replaced by primed constant of corresponding
	 * BoogieVar
	 * <li>each auxVar is replaced by a constant (with the same name as the
	 * auxVar)
	 * </ul>
	 * If formula contained no branch encoders the result is a closed formula
	 * (does not contain free variables)
	 * 
	 * @param existingAuxVarConsts
	 *            if true we assume that the constants for the auxVars already
	 *            exist, otherwise we construct them
	 * 
	 */
	public static Term computeClosedFormula(final Term formula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Map<TermVariable, Term> auxVars,
			final Boogie2SMT boogie2smt) {
		final Map<TermVariable, Term> substitutionMapping = new HashMap<TermVariable, Term>();
		for (final IProgramVar bv : inVars.keySet()) {
			assert !substitutionMapping.containsKey(inVars.get(bv));
			substitutionMapping.put(inVars.get(bv), bv.getDefaultConstant());
		}
		for (final IProgramVar bv : outVars.keySet()) {
			if (inVars.get(bv) == outVars.get(bv)) {
				// is assigned var
				continue;
			}
			substitutionMapping.put(outVars.get(bv), bv.getPrimedConstant());
		}
		for (final Entry<TermVariable, Term> entry : auxVars.entrySet()) {
			final TermVariable auxVarTv = entry.getKey();
			final Term auxVarConst = entry.getValue();
			substitutionMapping.put(auxVarTv, auxVarConst);
		}
		final Term closedTerm = (new Substitution(substitutionMapping, boogie2smt.getScript())).transform(formula);
		return closedTerm;
	}

	/**
	 * Remove inVars, outVars and auxVars that are not necessary. Remove auxVars
	 * if it does not occur in the formula. Remove inVars if it does not occur
	 * in the formula. Remove outVar if it does not occur in the formula and is
	 * also an inVar (case where the var is not modified). Note that we may not
	 * generally remove outVars that do not occur in the formula (e.g.,
	 * TransFormula for havoc statement).
	 */
	public static void removeSuperfluousVars(final Term formula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> auxVars) {
		final Set<TermVariable> allVars = new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		auxVars.retainAll(allVars);
		final List<IProgramVar> superfluousInVars = new ArrayList<IProgramVar>();
		final List<IProgramVar> superfluousOutVars = new ArrayList<IProgramVar>();
		for (final IProgramVar bv : inVars.keySet()) {
			final TermVariable inVar = inVars.get(bv);
			if (!allVars.contains(inVar)) {
				superfluousInVars.add(bv);
			}
		}
		for (final IProgramVar bv : outVars.keySet()) {
			final TermVariable outVar = outVars.get(bv);
			if (!allVars.contains(outVar)) {
				final TermVariable inVar = inVars.get(bv);
				if (outVar == inVar) {
					superfluousOutVars.add(bv);
				}
			}
		}
		for (final IProgramVar bv : superfluousInVars) {
			inVars.remove(bv);
		}
		for (final IProgramVar bv : superfluousOutVars) {
			outVars.remove(bv);
		}
	}

	private static boolean allVarsContainsFreeVars(final Set<TermVariable> allVars, final Term term, final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (final TermVariable tv : freeVars) {
			if (!allVars.contains(tv)) {
				logger.error("not in allVars: " + tv);
				result = false;
			}
		}
		return result;
	}

	private static boolean freeVarsContainsAllVars(final Set<TermVariable> allVars, final Term term, final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
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
	 * Returns true iff all constants (ApplicationTerm with zero parameters)
	 * that occur in term are contained in the set setOfConstants.
	 */
	private static boolean isSupersetOfOccurringConstants(final Set<ApplicationTerm> setOfConstants, final Term term) {
		final Set<ApplicationTerm> constantsInTerm = (new ConstantFinder()).findConstants(term);
		return setOfConstants.containsAll(constantsInTerm);
	}

	private static boolean freeVarsSubsetInOutAuxBranch(final Term term, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> aux, final Set<TermVariable> branchEncoders, final ILogger logger) {
		final Set<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
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
	 * Returns true if each Term variable in mVars occurs as inVar, outVar,
	 * auxVar, or branchEncoder
	 */
	private boolean allSubsetInOutAuxBranch() {
		boolean result = true;
		final HashSet<TermVariable> allVars = new HashSet<TermVariable>(Arrays.asList(mFormula.getFreeVars()));
		for (final TermVariable tv : allVars) {
			result &= (mInVars.values().contains(tv) || mOutVars.values().contains(tv) || mAuxVars.keySet().contains(tv) || mBranchEncoders
					.contains(tv));
			assert result : "unexpected variable in formula";
		}
		for (final TermVariable tv : mAuxVars.keySet()) {
			result &= allVars.contains(tv);
			assert result : "unnecessary many vars in TransFormula";
		}
		return result;
	}

	/**
	 * Returns true each auxVar is in allVars and each inVar occurs in allVars.
	 */
	private boolean inAuxSubsetAll(final boolean allowSuperflousInVars) {
		boolean result = true;
		final HashSet<TermVariable> allVars = new HashSet<TermVariable>(Arrays.asList(mFormula.getFreeVars()));
		if (!allowSuperflousInVars) {
			for (final IProgramVar bv : mInVars.keySet()) {
				result &= (allVars.contains(mInVars.get(bv)));
				assert result : "superfluous inVar";
			}
		}
		for (final TermVariable tv : mAuxVars.keySet()) {
			result &= allVars.contains(tv);
			assert result : "superfluous auxVar";
		}
		return result;
	}

	private boolean eachInVarOccursAsOutVar() {
		for (final IProgramVar bv : mInVars.keySet()) {
			if (!mOutVars.containsKey(bv)) {
				return false;
			}
		}
		return true;
	}

	public Term getFormula() {
		return mFormula;
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return Collections.unmodifiableMap(mInVars);
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return Collections.unmodifiableMap(mOutVars);
	}

	public Map<TermVariable,Term> getAuxVars() {
		return Collections.unmodifiableMap(mAuxVars);
	}

	public Set<TermVariable> getBranchEncoders() {
		return Collections.unmodifiableSet(mBranchEncoders);
	}

	public Term getClosedFormula() {
		return mClosedFormula;
	}

	public Set<ApplicationTerm> getConstants() {
		return Collections.unmodifiableSet(mConstants);
	}

	/**
	 * @return the mAssignedVars
	 */
	public Set<IProgramVar> getAssignedVars() {
		return Collections.unmodifiableSet(mAssignedVars);
	}

	@Override
	public String toString() {
		return "Formula: " + mFormula + "  InVars " + mInVars + "  OutVars" + mOutVars + "  AuxVars" + mAuxVars
				+ "  AssignedVars" + mAssignedVars;
	}

	public Infeasibility isInfeasible() {
		return mInfeasibility;
	}

	/**
	 * If this method returns true, the outVar of bv may have any value even if
	 * the value of the inVar is restricted. If the methods returns false there
	 * are constraints on the outVar or syntactic check was not able to find out
	 * that there are no constraints.
	 */
	public boolean isHavocedOut(final IProgramVar bv) {
		final TermVariable inVar = mInVars.get(bv);
		final TermVariable outVar = mOutVars.get(bv);
		if (inVar == outVar) {
			return false;
		} else {
			if (Arrays.asList(mFormula.getFreeVars()).contains(outVar)) {
				return false;
			} else {
				return true;
			}
		}
	}

	public boolean isHavocedIn(final IProgramVar bv) {
		final TermVariable inVar = mInVars.get(bv);
		final TermVariable outVar = mOutVars.get(bv);
		if (inVar == outVar) {
			return false;
		} else {
			if (Arrays.asList(mFormula.getFreeVars()).contains(inVar)) {
				return false;
			} else {
				return true;
			}
		}
	}

	// public static TermVariable getFreshAuxVariable(Boogie2SMT boogie2smt,
	// String id, Sort sort) {
	// String name = id + "_" + s_FreshVarNumber++;
	// TermVariable newVar = boogie2smt.getScript().variable(name, sort);
	// return newVar;
	// }

	// public static TermVariable getFreshVariable(Boogie2SMT boogie2smt,
	// BoogieVar var, Sort sort) {
	// String name;
	// if (var.isGlobal()) {
	// if (var.isOldvar()) {
	// name = "old(" + var.getIdentifier() + ")";
	// } else {
	// name = var.getIdentifier();
	// }
	// } else {
	// name = var.getProcedure() + "_" + var.getIdentifier();
	// }
	// name += "_" + s_FreshVarNumber++;
	// return boogie2smt.getScript().variable(name, sort);
	// }

	/**
	 * @param services
	 * @return the relational composition (concatenation) of transformula1 und
	 *         transformula2
	 */
	public static TransFormula sequentialComposition(final ILogger logger, final IUltimateServiceProvider services,
			final Boogie2SMT boogie2smt, final boolean simplify, final boolean extPqe, final boolean tranformToCNF, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique,
			final TransFormula... transFormula) {
		logger.debug("sequential composition with" + (simplify ? "" : "out") + " formula simplification");
		final Script script = boogie2smt.getScript();
		final Map<IProgramVar, TermVariable> inVars = new HashMap<IProgramVar, TermVariable>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<IProgramVar, TermVariable>();
		final Set<TermVariable> auxVars = new HashSet<TermVariable>();
		final Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
		Term formula = boogie2smt.getScript().term("true");

		final Map<TermVariable, Term> subsitutionMapping = new HashMap<TermVariable, Term>();
		for (int i = transFormula.length - 1; i >= 0; i--) {
			for (final IProgramVar var : transFormula[i].getOutVars().keySet()) {

				final TermVariable outVar = transFormula[i].getOutVars().get(var);
				TermVariable newOutVar;
				if (inVars.containsKey(var)) {
					newOutVar = inVars.get(var);
				} else {
					newOutVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
				}
				subsitutionMapping.put(outVar, newOutVar);
				// add to outvars if var is not outvar
				if (!outVars.containsKey(var)) {
					outVars.put(var, newOutVar);
				}
				final TermVariable inVar = transFormula[i].getInVars().get(var);
				if (inVar == null) {
					// case: var is assigned without reading or havoced
					if (outVars.get(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
					inVars.remove(var);
				} else if (inVar == outVar) {
					// case: var is not modified
					inVars.put(var, newOutVar);
				} else {
					// case: var is read and written
					final Sort sort = outVar.getSort();
					final TermVariable newInVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
					subsitutionMapping.put(inVar, newInVar);
					inVars.put(var, newInVar);
					if (outVars.get(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
				}
			}
			for (final TermVariable auxVar : transFormula[i].getAuxVars().keySet()) {
				final TermVariable newAuxVar = boogie2smt.getVariableManager().constructFreshCopy(auxVar);
				subsitutionMapping.put(auxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
			newBranchEncoders.addAll(transFormula[i].getBranchEncoders());

			for (final IProgramVar var : transFormula[i].getInVars().keySet()) {
				if (transFormula[i].getOutVars().containsKey(var)) {
					// nothing do to, this var was already considered above
				} else {
					// case var occurs only as inVar: var is not modfied.
					final TermVariable inVar = transFormula[i].getInVars().get(var);
					TermVariable newInVar;
					if (inVars.containsKey(var)) {
						newInVar = inVars.get(var);
					} else {
						final Sort sort = inVar.getSort();
						newInVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
						inVars.put(var, newInVar);
					}
					subsitutionMapping.put(inVar, newInVar);
				}
			}
			final Term originalFormula = transFormula[i].getFormula();
			final Term updatedFormula = (new Substitution(subsitutionMapping, script)).transform(originalFormula);
			formula = Util.and(script, formula, updatedFormula);
			// formula = new FormulaUnLet().unlet(formula);

		}

		formula = new FormulaUnLet().unlet(formula);
		if (simplify) {
			try {
				final Term simplified = SmtUtils.simplify(script, formula, services, simplificationTechnique, boogie2smt.getVariableManager());
				formula = simplified;
			} catch (final ToolchainCanceledException tce) {
				throw new ToolchainCanceledException(TransFormula.class, tce.getRunningTaskInfo() + 
						" while doing sequential composition of " + transFormula.length + " TransFormulas");
			}
		}
		removesuperfluousVariables(inVars, outVars, auxVars, formula);

		if (extPqe) {
			final Term eliminated = PartialQuantifierElimination.elim(script, QuantifiedFormula.EXISTS, auxVars, formula,
					services, logger, boogie2smt.getVariableManager(), simplificationTechnique, xnfConversionTechnique);
			logger.debug(new DebugMessage("DAG size before PQE {0}, DAG size after PQE {1}",
					new DagSizePrinter(formula), new DagSizePrinter(eliminated)));
			formula = eliminated;
		} else {
			final XnfDer xnfDer = new XnfDer(script, services, boogie2smt.getVariableManager());
			formula = Util.and(script, xnfDer.tryToEliminate(QuantifiedFormula.EXISTS, SmtUtils.getConjuncts(formula), auxVars));
		}
		if (simplify) {
			formula = SmtUtils.simplify(script, formula, services, simplificationTechnique, boogie2smt.getVariableManager());
		} else {
			final LBool isSat = Util.checkSat(script, formula);
			if (isSat == LBool.UNSAT) {
				logger.warn("CodeBlock already infeasible");
				formula = script.term("false");
			}
		}
		removesuperfluousVariables(inVars, outVars, auxVars, formula);

		Infeasibility infeasibility;
		if (formula == script.term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}

		if (tranformToCNF) {
			final Term cnf = SmtUtils.toCnf(services, script, boogie2smt.getVariableManager(), formula, xnfConversionTechnique);
			formula = cnf;
			removesuperfluousVariables(inVars, outVars, auxVars, formula);
		}

		final Map<TermVariable, Term> auxVar2Const = TransFormula.constructAuxVarMapping(auxVars, boogie2smt.getVariableManager());
		final Term closedFormula = computeClosedFormula(formula, inVars, outVars, auxVar2Const, boogie2smt);
		final TransFormula result = new TransFormula(formula, inVars, outVars, auxVar2Const, newBranchEncoders, infeasibility,
				closedFormula);

		// assert allVarsContainsFreeVars(allVars, formula);
		assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, auxVars, newBranchEncoders, logger);
		return result;

	}

	private static void reportTimeoutResult(final IUltimateServiceProvider services) {
		final String timeOutMessage = "Timeout during computation of TransFormula";
		final TimeoutResult timeOutRes = new TimeoutResult(ModelCheckerUtils.PLUGIN_ID, timeOutMessage);
		services.getResultService().reportResult(ModelCheckerUtils.PLUGIN_ID, timeOutRes);
	}

	@Deprecated
	// there is also a probably similar methods with a similar name
	private static void removesuperfluousVariables(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> auxVars, final Term formula) {
		final Set<TermVariable> occuringVars = new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		{
			final List<IProgramVar> superfluousInVars = new ArrayList<IProgramVar>();
			for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
				if (!occuringVars.contains(entry.getValue())) {
					superfluousInVars.add(entry.getKey());
				}
			}
			for (final IProgramVar bv : superfluousInVars) {
				final TermVariable inVar = inVars.get(bv);
				final TermVariable outVar = outVars.get(bv);
				if (inVar == outVar) {
					assert inVar != null;
					outVars.remove(bv);
				}
				inVars.remove(bv);
			}
		}
		// we may not remove outVars e.g., if x is outvar and formula is true
		// this means that x is havoced.
		{
			final List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
			for (final TermVariable tv : auxVars) {
				if (!occuringVars.contains(tv)) {
					superfluousAuxVars.add(tv);
				}
			}
			for (final TermVariable tv : superfluousAuxVars) {
				auxVars.remove(tv);
			}
		}
	}

	// /**
	// * @return the relational composition (concatenation) of transformula1 und
	// * transformula2
	// */
	// public static TransFormula sequentialComposition(TransFormula
	// transFormula1,
	// TransFormula transFormula2, Boogie2SMT boogie2smt, int serialNumber) {
	// Script script = boogie2smt.getScript();
	// Term formula1 = transFormula1.getFormula();
	// Map<BoogieVar, TermVariable> inVars1 = transFormula1.getInVars();
	// Map<BoogieVar, TermVariable> outVars1 = transFormula1.getOutVars();
	// Set<TermVariable> vars1 = transFormula1.getVars();
	//
	// Term formula2 = transFormula2.getFormula();
	// Map<BoogieVar, TermVariable> inVars2 = transFormula2.getInVars();
	// Map<BoogieVar, TermVariable> outVars2 = transFormula2.getOutVars();
	// Set<TermVariable> vars2 = transFormula2.getVars();
	//
	// Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar,
	// TermVariable>();
	// Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar,
	// TermVariable>();
	// Set<TermVariable> allVars = new HashSet<TermVariable>();
	// Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
	// Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
	//
	// inVars.putAll(inVars2);
	// outVars.putAll(outVars2);
	// newAuxVars.addAll(transFormula1.getAuxVars());
	// newAuxVars.addAll(transFormula2.getAuxVars());
	// newBranchEncoders.addAll(transFormula1.getBranchEncoders());
	// newBranchEncoders.addAll(transFormula2.getBranchEncoders());
	// allVars.addAll(vars1);
	// allVars.addAll(vars2);
	// ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
	// ArrayList<Term> replacers = new ArrayList<Term>();
	//
	// for (BoogieVar var :outVars1.keySet()) {
	// TermVariable outVar2 = outVars2.get(var);
	// TermVariable inVar2 = inVars2.get(var);
	// TermVariable outVar1 = outVars1.get(var);
	// TermVariable inVar1 = inVars1.get(var);
	//
	// if (inVar2 == null) {
	// if (outVar2 == null) {
	// //var does not occur in transFormula2
	// if (outVar1 != null) {
	// outVars.put(var, outVar1);
	// }
	// if (inVar1 != null) {
	// inVars.put(var, inVar1);
	// }
	// } else {
	// assert (outVar1 != outVar2 && inVar1 != outVar2) :
	// "accidently same tv is used twice, ask Matthias" +
	// "to implement this case";
	// //var is written but not read in transFormula2
	// if (inVar1 != null) {
	// inVars.put(var, inVar1);
	// }
	// if (inVar1 != outVar1) {
	// newAuxVars.add(outVar1);
	// }
	// }
	// } else {
	// TermVariable newOutVar1 = inVar2;
	// inVars.put(var, newOutVar1);
	// replacees.add(outVar1);
	// replacers.add(newOutVar1);
	// if (inVar1 == null) {
	// //var is written but not read in transFormula1
	// inVars.remove(var);
	// if (outVar2 != inVar2) {
	// //var modified by both formulas
	// newAuxVars.add(newOutVar1);
	// }
	// assert (outVar1 != inVar2 && outVar1 != outVar2) :
	// "accidently same tv is used twice, ask Matthias" +
	// "to implement this case";
	// } else if (inVar1 == outVar1) {
	// //var not modified in transFormula1
	// assert (outVar1 != inVar2 && outVar1 != outVar2) :
	// "accidently same tv is used twice, ask Matthias" +
	// "to implement this case";
	// } else {
	// if (outVar2 != inVar2) {
	// //var modified by both formulas
	// newAuxVars.add(newOutVar1);
	// }
	// String name = var.getIdentifier() + "_In" + serialNumber;
	// TermVariable newInVar = script.variable(
	// name, outVar1.getSort());
	// allVars.add(newInVar);
	// allVars.add(newInVar);
	// inVars.put(var, newInVar);
	// replacees.add(inVar1);
	// replacers.add(newInVar);
	// }
	//
	// }
	// }
	//
	// for (BoogieVar var : inVars1.keySet()) {
	// if (outVars1.containsKey(var)) {
	// // nothing do to, this var was already considered above
	// } else {
	// TermVariable outVar2 = outVars2.get(var);
	// TermVariable inVar2 = inVars2.get(var);
	// TermVariable inVar1 = inVars1.get(var);
	// assert (inVar1 != inVar2) :
	// "accidently same tv is used twice, ask Matthias" +
	// "to implement this case";
	// assert (inVar1 != outVar2) :
	// "accidently same tv is used twice, ask Matthias" +
	// "to implement this case";
	// if (inVar2 == null) {
	// if (outVar2 == null) {
	// //var does not occur in transFormula2
	// inVars.put(var, inVar1);
	// } else {
	// //var is written but not read in transFormula2
	// inVars.put(var, inVar1);
	// }
	// } else {
	// if (outVar2 == inVar2) {
	// //var not modified in transFormula2
	// inVars.put(var, inVar1);
	// } else {
	// //var modified in transFormula2
	// inVars.put(var, inVar1);
	// newAuxVars.add(inVar2);
	// }
	// }
	// }
	// }
	//
	// TermVariable[] vars = replacees.toArray(new
	// TermVariable[replacees.size()]);
	// Term[] values = replacers.toArray(new Term[replacers.size()]);
	// Term formula = script.let( vars , values, formula1);
	//
	// formula = Util.and(script, formula, formula2);
	// formula = new FormulaUnLet().unlet(formula);
	// NaiveDestructiveEqualityResolution der =
	// new NaiveDestructiveEqualityResolution(script);
	// //remove auxVars that do not occur in the formula
	// {
	// Set<TermVariable> varsOccurInTerm = new HashSet<TermVariable>(
	// Arrays.asList(formula.getFreeVars()));
	// List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
	// for (TermVariable tv : newAuxVars) {
	// if (!varsOccurInTerm.contains(tv)) {
	// superfluousAuxVars.add(tv);
	// }
	// }
	// newAuxVars.removeAll(superfluousAuxVars);
	// }
	// formula = der.eliminate(newAuxVars, formula);
	// // formula = (new SimplifyDDA(script,
	// s_Logger)).getSimplifiedTerm(formula);
	// LBool isSat = Util.checkSat(script, formula);
	// if (isSat == LBool.UNSAT) {
	// s_Logger.warn("CodeBlock already infeasible");
	// formula = script.term("false");
	// }
	// Infeasibility infeasibility;
	// if (formula == script.term("false")) {
	// infeasibility = Infeasibility.INFEASIBLE;
	// } else {
	// infeasibility = Infeasibility.UNPROVEABLE;
	// }
	// Set<TermVariable> occuringVars = new HashSet<TermVariable>(
	// Arrays.asList(formula.getFreeVars()));
	// {
	// List<BoogieVar> superfluousInVars = new ArrayList<BoogieVar>();
	// for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
	// if (!occuringVars.contains(entry.getValue())) {
	// superfluousInVars.add(entry.getKey());
	// }
	// }
	// for (BoogieVar bv : superfluousInVars) {
	// inVars.remove(bv);
	// }
	// }
	// // we may not remove outVars e.g., if x is outvar and formula is true
	// // this means that x is havoced.
	// {
	// List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
	// for (TermVariable tv : newAuxVars) {
	// if (!occuringVars.contains(tv)) {
	// superfluousAuxVars.add(tv);
	// }
	// }
	// for (TermVariable tv : superfluousAuxVars) {
	// newAuxVars.remove(tv);
	// }
	// }
	// Term closedFormula = computeClosedFormula(formula,
	// inVars, outVars, newAuxVars, boogie2smt);
	// TransFormula result = new TransFormula(formula, inVars, outVars,
	// newAuxVars, newBranchEncoders, infeasibility, closedFormula);
	// result.getAuxVars().addAll(newAuxVars);
	// assert allVarsContainsFreeVars(allVars, formula);
	// assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, newAuxVars,
	// newBranchEncoders);
	// return result;
	//
	// }

	/**
	 * The parallel composition of transFormulas is the disjunction of the
	 * underlying relations. If we check satisfiability of a path which contains
	 * this transFormula we want know one disjuncts that is satisfiable. We use
	 * additional boolean variables called branchIndicators to encode this
	 * disjunction. Example: Assume we have two TransFormulas tf1 and tf2.
	 * Instead of the Formula tf1 || tf2 we use the following formula. (BI1 ->
	 * tf1) && (BI2 -> tf2) && (BI1 || BI2) The following holds
	 * <ul>
	 * <li>tf1 || tf2 is satisfiable iff (BI1 -> tf1) && (BI2 -> tf2) && (BI1 ||
	 * BI2) is satisfiable.
	 * <li>in a satisfying assignment BIi can only be true if tfi is true for i
	 * \in {1,2}
	 * 
	 * @param logger
	 * @param services
	 * @param xnfConversionTechnique 
	 */
	public static TransFormula parallelComposition(final ILogger logger, final IUltimateServiceProvider services, final int serialNumber,
			final Boogie2SMT boogie2smt, final TermVariable[] branchIndicators, final boolean tranformToCNF, final XnfConversionTechnique xnfConversionTechnique,
			final TransFormula... transFormulas) {
		logger.debug("parallel composition");
		final Script script = boogie2smt.getScript();
		boolean useBranchEncoders;
		if (branchIndicators == null) {
			useBranchEncoders = false;
		} else {
			useBranchEncoders = true;
			if (branchIndicators.length != transFormulas.length) {
				throw new IllegalArgumentException();
			}

		}

		final Term[] renamedFormulas = new Term[transFormulas.length];
		final Map<IProgramVar, TermVariable> newInVars = new HashMap<IProgramVar, TermVariable>();
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<IProgramVar, TermVariable>();
		final Set<TermVariable> auxVars = new HashSet<TermVariable>();
		final Set<TermVariable> branchEncoders = new HashSet<TermVariable>();
		if (useBranchEncoders) {
			branchEncoders.addAll(Arrays.asList(branchIndicators));
		}

		final Map<IProgramVar, Sort> assignedInSomeBranch = new HashMap<IProgramVar, Sort>();
		for (final TransFormula tf : transFormulas) {
			for (final IProgramVar bv : tf.getInVars().keySet()) {
				if (!newInVars.containsKey(bv)) {
					final Sort sort = tf.getInVars().get(bv).getSort();
					final String inVarName = bv.getIdentifier() + "_In" + serialNumber;
					newInVars.put(bv, script.variable(inVarName, sort));
				}
			}
			for (final IProgramVar bv : tf.getOutVars().keySet()) {

				// vars which are assigned in some but not all branches must
				// also occur as inVar
				// We can omit this step in the special case where the
				// variable is assigned in all branches.
				if (!newInVars.containsKey(bv) && !assignedInAll(bv, transFormulas)) {
					final Sort sort = tf.getOutVars().get(bv).getSort();
					final String inVarName = bv.getIdentifier() + "_In" + serialNumber;
					newInVars.put(bv, script.variable(inVarName, sort));
				}

				final TermVariable outVar = tf.getOutVars().get(bv);
				final TermVariable inVar = tf.getInVars().get(bv);
				final boolean isAssignedVar = (outVar != inVar);
				if (isAssignedVar) {
					final Sort sort = tf.getOutVars().get(bv).getSort();
					assignedInSomeBranch.put(bv, sort);
				}
				// auxilliary step, add all invars. Some will be overwritten by
				// outvars
				newOutVars.put(bv, newInVars.get(bv));
			}
		}

		// overwrite (see comment above) the outvars if the outvar does not
		// coincide with the invar in some of the transFormulas
		for (final IProgramVar bv : assignedInSomeBranch.keySet()) {
			final Sort sort = assignedInSomeBranch.get(bv);
			final String outVarName = bv.getIdentifier() + "_Out" + serialNumber;
			newOutVars.put(bv, script.variable(outVarName, sort));
		}

		for (int i = 0; i < transFormulas.length; i++) {
			branchEncoders.addAll(transFormulas[i].getBranchEncoders());
			auxVars.addAll(transFormulas[i].getAuxVars().keySet());
			final Map<TermVariable, Term> subsitutionMapping = new HashMap<TermVariable, Term>();
			for (final IProgramVar bv : transFormulas[i].getInVars().keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				subsitutionMapping.put(inVar, newInVars.get(bv));
			}
			for (final IProgramVar bv : transFormulas[i].getOutVars().keySet()) {
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);

				final boolean isAssignedVar = (inVar != outVar);
				if (isAssignedVar) {
					subsitutionMapping.put(outVar, newOutVars.get(bv));
				} else {
					assert subsitutionMapping.containsKey(outVar);
					assert subsitutionMapping.containsValue(newInVars.get(bv));
				}
			}
			final Term originalFormula = transFormulas[i].getFormula();
			renamedFormulas[i] = (new Substitution(subsitutionMapping, script)).transform(originalFormula);

			for (final IProgramVar bv : assignedInSomeBranch.keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				if (inVar == null && outVar == null) {
					// bv does not occur in transFormula
					assert newInVars.get(bv) != null;
					assert newOutVars.get(bv) != null;
					final Term equality = script.term("=", newInVars.get(bv), newOutVars.get(bv));
					renamedFormulas[i] = Util.and(script, renamedFormulas[i], equality);
				} else if (inVar == outVar) {
					// bv is not modified in transFormula
					assert newInVars.get(bv) != null;
					assert newOutVars.get(bv) != null;
					final Term equality = script.term("=", newInVars.get(bv), newOutVars.get(bv));
					renamedFormulas[i] = Util.and(script, renamedFormulas[i], equality);
				}
			}

			if (useBranchEncoders) {
				renamedFormulas[i] = Util.implies(script, branchIndicators[i], renamedFormulas[i]);
			}
		}

		Term resultFormula;
		if (useBranchEncoders) {
			resultFormula = Util.and(script, renamedFormulas);
			final Term atLeastOneBranchTaken = Util.or(script, branchIndicators);
			resultFormula = Util.and(script, resultFormula, atLeastOneBranchTaken);
		} else {
			resultFormula = Util.or(script, renamedFormulas);
		}
		final LBool termSat = Util.checkSat(script, resultFormula);
		Infeasibility inFeasibility;
		if (termSat == LBool.UNSAT) {
			inFeasibility = Infeasibility.INFEASIBLE;
		} else {
			inFeasibility = Infeasibility.UNPROVEABLE;
		}
		if (tranformToCNF) {
			resultFormula = SmtUtils.toCnf(services, script, boogie2smt.getVariableManager(), resultFormula, xnfConversionTechnique);
		}
		TransFormula.removeSuperfluousVars(resultFormula, newInVars, newOutVars, auxVars);
		final Map<TermVariable, Term> auxVar2Const = TransFormula.constructAuxVarMapping(auxVars, boogie2smt.getVariableManager());
		final Term closedFormula = computeClosedFormula(resultFormula, newInVars, newOutVars, auxVar2Const, boogie2smt);
		return new TransFormula(resultFormula, newInVars, newOutVars, auxVar2Const, branchEncoders, inFeasibility,
				closedFormula);
	}

	/**
	 * Return true iff bv is assigned in all transFormulas.
	 */
	private static boolean assignedInAll(final IProgramVar bv, final TransFormula... transFormulas) {
		for (final TransFormula tf : transFormulas) {
			if (!tf.getAssignedVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}

	// /**
	// * Returns a Transformula that can be seen as procedure summary of the
	// input
	// * transformula with respect to inParams and outParams.
	// * We obtain the result by
	// * - removing all inVars that are not global or not in inParams
	// * - removing all outVars that are not global or not in outParams
	// * - considering all oldVars as non-old inVars.
	// */
	// public static TransFormula procedureSummary(Boogie2SMT boogie2smt,
	// TransFormula transFormula, Set<BoogieVar> inArgument, Set<BoogieVar>
	// outResult) {
	// Script script = boogie2smt.getScript();
	// Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar,
	// TermVariable>();
	// Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar,
	// TermVariable>();
	// Set<TermVariable> allVars = new HashSet<TermVariable>();
	// Set<TermVariable> auxVars = new HashSet<TermVariable>();
	// Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
	//
	// ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
	// ArrayList<Term> replacers = new ArrayList<Term>();
	//
	// Set<BoogieVar> inAndOutVars = new HashSet<BoogieVar>();
	// inAndOutVars.addAll(transFormula.getOutVars().keySet());
	// inAndOutVars.addAll(transFormula.getInVars().keySet());
	//
	// for (BoogieVar var : inAndOutVars) {
	// TermVariable outVar = transFormula.getOutVars().get(var);
	// TermVariable inVar = transFormula.getInVars().get(var);
	//
	// if (var.isGlobal()) {
	// if (var.isOldvar()) {
	// BoogieVar nonOldVar = boogie2smt.getSmt2Boogie().
	// getGlobals().get(var.getIdentifier());
	// TermVariable nonOldVarTv;
	// // We use the TermVariable of the nonOld invar.
	// // If the nonOld BoogieVar does not occur we use a fresh
	// // TermVariable
	// if (inVars.containsKey(nonOldVar)) {
	// nonOldVarTv = inVar;
	// } else {
	// nonOldVarTv = getFreshVariable(boogie2smt,var, outVar.getSort());
	// }
	// if (transFormula.getInVars().containsKey(var)) {
	// replacees.add(inVar);
	// replacers.add(nonOldVarTv);
	// assert (outVar == null || outVar == inVar) :
	// "oldvar can not be modified";
	// } else {
	// assert transFormula.getOutVars().containsKey(var);
	// replacees.add(outVar);
	// replacers.add(nonOldVarTv);
	// }
	// // Since oldvars may not be modified it is safe to add the
	// // TermVariable only as inVar.
	// assert (!inVars.containsKey(nonOldVar) ||
	// inVars.get(nonOldVarTv) == nonOldVarTv) :
	// "oldVar should have been replaced by nonOldVar";
	// inVars.put(var, nonOldVarTv);
	// } else {
	// if (transFormula.getInVars().containsKey(var)) {
	// inVars.put(var, inVar);
	// }
	// if (transFormula.getOutVars().containsKey(var)) {
	// outVars.put(var, outVar);
	// }
	// }
	// } else {
	// if (outVar != null) {
	// if (outResult.contains(var)) {
	// assert (transFormula.getOutVars().containsKey(var));
	// outVars.put(var, outVar);
	// } else {
	// if (outVar == inVar && inArgument.contains(var)) {
	// // do nothing. special case where outVar does not
	// // become auxVar
	// } else {
	// auxVars.add(outVar);
	// }
	// }
	// }
	// if (inVar != null) {
	// if (inArgument.contains(var) && inVar != null) {
	// assert (transFormula.getInVars().containsKey(var));
	// inVars.put(var, inVar);
	// } else {
	// if (inVar == outVar && outResult.contains(var)) {
	// // do nothing. special case where inVar does not
	// // become
	// // auxVar
	// } else {
	// auxVars.add(inVar);
	// }
	// }
	// }
	// }
	// }
	//
	// for (TermVariable auxVar : transFormula.getAuxVars()) {
	// TermVariable newAuxVar = getFreshAuxVariable(boogie2smt,
	// auxVar.getName(), auxVar.getSort());
	// replacees.add(auxVar);
	// replacers.add(newAuxVar);
	// auxVars.add(newAuxVar);
	// }
	// //TODO: These have to be renamed?!?
	// //newBranchEncoders.addAll(transFormula.getBranchEncoders());
	//
	//
	// TermVariable[] vars = replacees.toArray(new
	// TermVariable[replacees.size()]);
	// Term[] values = replacers.toArray(new Term[replacers.size()]);
	// Term formula = script.let( vars , values, transFormula.getFormula());
	// //formula = new FormulaUnLet().unlet(formula);
	//
	//
	// formula = new FormulaUnLet().unlet(formula);
	// formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
	// removesuperfluousVariables(inVars, outVars, auxVars, formula);
	//
	// NaiveDestructiveEqualityResolution der =
	// new NaiveDestructiveEqualityResolution(script);
	// formula = der.eliminate(auxVars, formula);
	// formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
	// removesuperfluousVariables(inVars, outVars, auxVars, formula);
	//
	// LBool isSat = Util.checkSat(script, formula);
	// if (isSat == LBool.UNSAT) {
	// s_Logger.warn("CodeBlock already infeasible");
	// formula = script.term("false");
	// }
	// Infeasibility infeasibility;
	// if (formula == script.term("false")) {
	// infeasibility = Infeasibility.INFEASIBLE;
	// } else {
	// infeasibility = Infeasibility.UNPROVEABLE;
	// }
	//
	// Term closedFormula = computeClosedFormula(formula,
	// inVars, outVars, auxVars, boogie2smt);
	// TransFormula result = new TransFormula(formula, inVars, outVars,
	// auxVars, newBranchEncoders, infeasibility, closedFormula);
	//
	// // assert allVarsContainsFreeVars(allVars, formula);
	// assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, auxVars,
	// newBranchEncoders);
	// return result;
	//
	// }
	//

	private void removeOutVar(final IProgramVar var, final VariableManager variableManager) {
		assert mOutVars.containsKey(var) : "illegal to remove variable not that is contained";
		final TermVariable inVar = mInVars.get(var);
		final TermVariable outVar = mOutVars.get(var);
		mOutVars.remove(var);
		if (inVar != outVar) {
			// outVar does not occurs already as inVar, we have to add outVar
			// to auxVars
			final Term newAuxVarConst = variableManager.constructFreshConstant(outVar); 
			mAuxVars.put(outVar, newAuxVarConst);
			final boolean removed = mAssignedVars.remove(var);
			assert (removed);
		} else {
			assert !mAssignedVars.contains(var);
		}
	}

	private void removeInVar(final IProgramVar var, final VariableManager variableManager) {
		assert mInVars.containsKey(var) : "illegal to remove variable not that is contained";
		final TermVariable inVar = mInVars.get(var);
		final TermVariable outVar = mOutVars.get(var);
		mInVars.remove(var);
		if (inVar != outVar) {
			// inVar does not occurs already as outVar, we have to add inVar
			// to auxVars
			final Term newAuxVarConst = variableManager.constructFreshConstant(inVar); 
			mAuxVars.put(inVar, newAuxVarConst);
			assert outVar == null || mAssignedVars.contains(var);
		} else {
			assert !mAssignedVars.contains(var);
			if (outVar != null) {
				mAssignedVars.add(var);
			}
		}
	}

	// /**
	// * Replace all oldVars that occur in inVars or outVars by corresponding
	// * non-old global Var. The corresponding non-old Var is the one that
	// * occurs in the inVars. If inVars does not contain such a variable
	// * we construct it.
	// */
	// private static Term replaceOldVarsByInVars(Boogie2SMT boogie2smt,
	// Map<BoogieVar,TermVariable> inVars, Map<BoogieVar,TermVariable> outVars,
	// Term formula) {
	// ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
	// ArrayList<Term> replacers = new ArrayList<Term>();
	//
	// Set<BoogieVar> inAndOutVars = new HashSet<BoogieVar>();
	// inAndOutVars.addAll(outVars.keySet());
	// inAndOutVars.addAll(inVars.keySet());
	//
	// for (BoogieVar var : inAndOutVars) {
	// if (var.isGlobal()) {
	// if (var.isOldvar()) {
	// TermVariable outVar = outVars.get(var);
	// TermVariable inVar = inVars.get(var);
	// BoogieVar nonOldVar = boogie2smt.getSmt2Boogie()
	// .getGlobals().get(var.getIdentifier());
	// TermVariable nonOldVarTv;
	// // We use the TermVariable of the nonOld invar.
	// // If the nonOld BoogieVar does not occur we use a fresh
	// // TermVariable
	// if (inVars.containsKey(nonOldVar)) {
	// nonOldVarTv = inVar;
	// } else {
	// nonOldVarTv = getFreshVariable(boogie2smt, var,
	// outVar.getSort());
	// }
	// if (inVars.containsKey(var)) {
	// replacees.add(inVar);
	// replacers.add(nonOldVarTv);
	// assert (outVar == null || outVar == inVar) :
	// "oldvar can not be modified";
	// } else {
	// assert outVars.containsKey(var);
	// replacees.add(outVar);
	// replacers.add(nonOldVarTv);
	// }
	// }
	// }
	// }
	// TermVariable[] vars = replacees.toArray(new
	// TermVariable[replacees.size()]);
	// Term[] values = replacers.toArray(new Term[replacers.size()]);
	// Term result = boogie2smt.getScript().let( vars , values, formula);
	// return result;
	// }

	/**
	 * Returns TransFormula that describes a sequence of code blocks that
	 * contains a pending call. Note the the scope of inVars and outVars is
	 * different. Do not compose the result with the default/intraprocedural
	 * composition.
	 * 
	 * @param beforeCall
	 *            TransFormula that describes transition relation before the
	 *            call.
	 * @param callTf
	 *            TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment
	 *            TransFormula that assigns to oldVars of modifiable globals the
	 *            value of the global var.
	 * @param afterCall
	 *            TransFormula that describes the transition relation after the
	 *            call.
	 * @param logger
	 * @param services
	 * @param modifiableGlobalsOfEndProcedure
	 * 			  Set of variables that are modifiable globals in the procedure
	 * 	          in which the afterCall TransFormula ends. 
	 */
	public static TransFormula sequentialCompositionWithPendingCall(final Boogie2SMT boogie2smt, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final List<TransFormula> beforeCall, final TransFormula callTf,
			final TransFormula oldVarsAssignment, final TransFormula afterCall, final ILogger logger, final IUltimateServiceProvider services, 
			final Set<IProgramVar> modifiableGlobalsOfEndProcedure, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		logger.debug("sequential composition (pending call) with" + (simplify ? "" : "out") + " formula simplification");
		TransFormula callAndBeforeTF;
		{
			final List<TransFormula> callAndBeforeList = new ArrayList<TransFormula>(beforeCall);
			callAndBeforeList.add(callTf);
			final TransFormula[] callAndBeforeArray = callAndBeforeList.toArray(new TransFormula[callAndBeforeList.size()]);
			callAndBeforeTF = sequentialComposition(logger, services, boogie2smt, simplify, extPqe, transformToCNF,
					xnfConversionTechnique, simplificationTechnique, callAndBeforeArray);

			// remove outVars that relate to scope of caller
			// - local vars that are no inParams of callee
			// - oldVars of variables that can be modified by callee
			final List<IProgramVar> varsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : callAndBeforeTF.getOutVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar() && oldVarsAssignment.getOutVars().containsKey(bv)) {
						varsToRemove.add(bv);
					}
				} else {
					if (!callTf.getOutVars().containsKey(bv)) {
						// bv is local but not inParam of called procedure
						varsToRemove.add(bv);
					}
				}
			}
			for (final IProgramVar bv : varsToRemove) {
				callAndBeforeTF.removeOutVar(bv, boogie2smt.getVariableManager());
			}
		}

		TransFormula oldAssignAndAfterTF;
		{
			final List<TransFormula> oldAssignAndAfterList = new ArrayList<TransFormula>(Arrays.asList(afterCall));
			oldAssignAndAfterList.add(0, oldVarsAssignment);
			final TransFormula[] oldAssignAndAfterArray = oldAssignAndAfterList.toArray(new TransFormula[0]);
			oldAssignAndAfterTF = sequentialComposition(logger, services, boogie2smt, simplify, extPqe, transformToCNF,
					xnfConversionTechnique, simplificationTechnique, oldAssignAndAfterArray);

			// remove inVars that relate to scope of callee
			// - local vars that are no inParams of callee
			// - oldVars of variables that can be modified by callee
			final List<IProgramVar> inVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : oldAssignAndAfterTF.getInVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar() && oldVarsAssignment.getOutVars().containsKey(bv)) {
						inVarsToRemove.add(bv);
					}
				} else {
					if (!callTf.getOutVars().containsKey(bv)) {
						// bv is local but not inParam of called procedure
						inVarsToRemove.add(bv);
					}
				}
			}
			for (final IProgramVar bv : inVarsToRemove) {
				oldAssignAndAfterTF.removeInVar(bv, boogie2smt.getVariableManager());
			}
			
			final List<IProgramVar> outVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : oldAssignAndAfterTF.getOutVars().keySet()) {
				if (bv instanceof IProgramOldVar) {
					final IProgramNonOldVar nonOld = ((IProgramOldVar) bv).getNonOldVar();
					if (modifiableGlobalsOfEndProcedure.contains(nonOld)) {
						// do nothing - bv should be outVar
					} else {
						outVarsToRemove.add(bv);
					}
				}
			}
			for (final IProgramVar bv : outVarsToRemove) {
				oldAssignAndAfterTF.removeOutVar(bv, boogie2smt.getVariableManager());
			}
		}

		final TransFormula result = sequentialComposition(logger, services, boogie2smt, simplify, 
				extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique,
				callAndBeforeTF, oldAssignAndAfterTF);
		return result;
	}

	/**
	 * Returns a TransFormula that can be seen as procedure summary.
	 * 
	 * @param callTf
	 *            TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment
	 *            TransFormula that assigns to oldVars of modifiable globals the
	 *            value of the global var.
	 * @param procedureTf
	 *            TransFormula that describes the procedure.
	 * @param returnTf
	 *            TransFormula that assigns the result of the procedure call.
	 * @param logger
	 * @param services
	 */
	public static TransFormula sequentialCompositionWithCallAndReturn(final Boogie2SMT boogie2smt, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final TransFormula callTf, 
			final TransFormula oldVarsAssignment, final TransFormula globalVarsAssignment,
			final TransFormula procedureTf, final TransFormula returnTf, final ILogger logger, 
			final IUltimateServiceProvider services, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		logger.debug("sequential composition (call/return) with" + (simplify ? "" : "out") + " formula simplification");
		final TransFormula result = sequentialComposition(logger, services, boogie2smt, 
				simplify, extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique,
				callTf, oldVarsAssignment, globalVarsAssignment, procedureTf, returnTf);
		{
			final List<IProgramVar> inVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : result.getInVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar() && oldVarsAssignment.getOutVars().containsKey(bv)) {
						inVarsToRemove.add(bv);
					}
				} else {
					if (!callTf.getInVars().containsKey(bv)) {
						// bv is local but not argument of procedure call
						inVarsToRemove.add(bv);
					}
				}
			}
			for (final IProgramVar bv : inVarsToRemove) {
				result.removeInVar(bv, boogie2smt.getVariableManager());
			}
		}
		{
			final List<IProgramVar> outVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : result.getOutVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar() && oldVarsAssignment.getOutVars().containsKey(bv)) {
						outVarsToRemove.add(bv);
					}
				} else {
					if (!returnTf.getOutVars().containsKey(bv)) {
						// bv is local but not result of procedure call
						outVarsToRemove.add(bv);
					}
				}
			}
			for (final IProgramVar bv : outVarsToRemove) {
				result.removeOutVar(bv, boogie2smt.getVariableManager());
			}
		}
		{
			for (final Entry<IProgramVar, TermVariable> entry : callTf.getInVars().entrySet()) {
				if (!result.getOutVars().containsKey(entry.getKey())) {
					final TermVariable inVar = result.getInVars().get(entry.getKey());
					if (inVar == null) {
						// do nothing, not in formula any more
					} else {
						result.mOutVars.put(entry.getKey(), inVar);
					}
				}
			}
		}
		// // Add all inVars (bv,tv) of the call to outVars of the result except
		// // if there already an outVar (bv,tv').
		// // (Because in this case the variable bv was reassigned by the
		// summary,
		// // e.g. in the case where bv is a global variable that can be
		// modified
		// // by the procedure or is bv is a variable that is assigned by the
		// // call.
		// {
		// for (BoogieVar bv : callTf.getInVars().keySet()) {
		// if (!result.getOutVars().containsKey(bv)) {
		// TermVariable inVar = result.getInVars().get(bv);
		// if (inVar == null) {
		// // do nothing,
		// // this inVar was removed by a simplification
		// } else {
		// result.mOutVars.put(bv, inVar);
		// }
		// }
		//
		// }
		// }
		assert SmtUtils.neitherKeyNorValueIsNull(result.mOutVars) : "sequentialCompositionWithCallAndReturn introduced null entries";
		assert (isIntraprocedural(result));
		return result;
	}

	/**
	 * Returns true iff all local variables in tf belong to a single procedure.
	 */
	static boolean isIntraprocedural(final TransFormula tf) {
		final Set<String> procedures = new HashSet<String>();
		for (final IProgramVar bv : tf.getInVars().keySet()) {
			if (!bv.isGlobal()) {
				procedures.add(bv.getProcedure());
			}
		}
		for (final IProgramVar bv : tf.getOutVars().keySet()) {
			if (!bv.isGlobal()) {
				procedures.add(bv.getProcedure());
			}
		}
		return procedures.size() <= 1;
	}
	
	
	private static TransFormula computeGuard(final TransFormula tf, final Boogie2SMT boogie2smt) {
		final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = tf.getInVars(); // yes! outVars are inVars of input
		final Set<TermVariable> auxVars = new HashSet<TermVariable>();
		auxVars.addAll(tf.getAuxVars().keySet());
		for (final IProgramVar bv : tf.getAssignedVars()) {
			final TermVariable outVar = tf.getOutVars().get(bv);
			if (Arrays.asList(tf.getFormula().getFreeVars()).contains(outVar)) {
				auxVars.add(outVar);
			}
		}
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		final Set<TermVariable> branchEncoders = tf.getBranchEncoders();
		final Infeasibility infeasibility = tf.isInfeasible();
		final Term formula = tf.getFormula();
		final Map<TermVariable, Term> auxVar2Const = TransFormula.constructAuxVarMapping(auxVars, boogie2smt.getVariableManager());
		final Term closedFormula = computeClosedFormula(formula, inVars, outVars, auxVar2Const, boogie2smt);
		final TransFormula result = new TransFormula(formula, inVars, outVars, auxVar2Const, branchEncoders, infeasibility, closedFormula);
		return result;
	}
	
	private static TransFormula negate(final TransFormula tf, final Boogie2SMT boogie2smt, final IUltimateServiceProvider services, 
			final ILogger logger,final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		final Set<TermVariable> branchEncoders = tf.getBranchEncoders();
		final Infeasibility infeasibility = tf.isInfeasible();
		Term formula = tf.getFormula();
		formula = PartialQuantifierElimination.quantifier(services, logger, 
				boogie2smt.getScript(), boogie2smt.getVariableManager(), simplificationTechnique, xnfConversionTechnique, QuantifiedFormula.EXISTS, 
				tf.getAuxVars().keySet(), formula, new Term[0]);
		final Set<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		freeVars.retainAll(tf.getAuxVars().keySet());
		if (!freeVars.isEmpty()) {
			throw new UnsupportedOperationException("cannot negate if there are auxVars");
		}
		formula = SmtUtils.not(boogie2smt.getScript(), formula);
		final Map<TermVariable, Term> auxVars = Collections.emptyMap();
		
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>(tf.getInVars());
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>(tf.getOutVars());
		TransFormula.removeSuperfluousVars(formula, inVars, outVars, auxVars.keySet());
		

		//FIXME: Filter inVars and outVars to tv that occur in formula
//		formula = SmtUtils.quantifier(boogie2smt.getScript(), QuantifiedFormula.EXISTS, tf.getAuxVars(), formula);
		final Term closedFormula = computeClosedFormula(formula, inVars, outVars, auxVars, boogie2smt);
		final TransFormula result = new TransFormula(formula, inVars, outVars, auxVars, branchEncoders, infeasibility, closedFormula);
		return result;
	}
	
	public static TransFormula computeMarkhorTransFormula(final TransFormula tf, 
			final Boogie2SMT boogie2smt, final IUltimateServiceProvider services, 
			final ILogger logger, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		final TransFormula guard = computeGuard(tf, boogie2smt);
		final TransFormula negGuard = negate(guard, boogie2smt, services, logger, xnfConversionTechnique, simplificationTechnique);
		final TransFormula markhor = parallelComposition(logger, services, tf.hashCode(), boogie2smt, null, false, xnfConversionTechnique, tf, negGuard);
		return markhor;
	}
	
	/**
	 * Given a set of auxVars, construct a map that assigns to auxVar
	 * a fresh constant. 
	 */
	public static Map<TermVariable, Term> constructAuxVarMapping(final Set<TermVariable> auxVars, final VariableManager varManager) {
		final Map<TermVariable,Term> result = new HashMap<>();
		for (final TermVariable auxVar : auxVars) {
			final Term auxVarConst = varManager.constructFreshConstant(auxVar);
			result.put(auxVar, auxVarConst);
		}
		return result;
	}

}
