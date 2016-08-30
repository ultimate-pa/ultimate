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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions;

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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Unmodifiable variant of {@link TransFormula}
 * @author heizmann@informatik.uni-freiburg.de
 */
public class UnmodifiableTransFormula extends TransFormula implements Serializable {
	private static final long serialVersionUID = 7058102586141801399L;
	final Term mFormula;
	private final Set<IProgramVar> mAssignedVars;
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

	/**
	 * This constructor is package-private use {@link TransFormulaBuilder}
	 * to construct TransFormulas. 
	 */
	UnmodifiableTransFormula(final Term formula, 
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Set<TermVariable> auxVars, final Set<TermVariable> branchEncoders, 
			final Infeasibility infeasibility, final ManagedScript script) {
		super(inVars, outVars, auxVars);
		mFormula = formula;
		mBranchEncoders = branchEncoders;
		mInfeasibility = infeasibility;
		mClosedFormula = computeClosedFormula(formula, mInVars, mOutVars, mAuxVars, script);
		assert SmtUtils.neitherKeyNorValueIsNull(inVars) : "null in inVars";
		assert SmtUtils.neitherKeyNorValueIsNull(outVars) : "null in outVars";
		assert (branchEncoders.size() > 0 || mClosedFormula.getFreeVars().length == 0);
		// mVars = new
		// HashSet<TermVariable>(Arrays.asList(mFormula.getFreeVars()));
		assert allSubsetInOutAuxBranch() : "unexpected vars in TransFormula";
		assert inAuxSubsetAll(false) : "superfluous vars in TransFormula";
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
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> auxVars,
			final ManagedScript script) {
		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
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
		for (final TermVariable auxVarTv : auxVars) {
			final Term auxVarConst = SmtUtils.termVariable2constant(script.getScript(), auxVarTv, true);
			substitutionMapping.put(auxVarTv, auxVarConst);
		}
		final Term closedTerm = (new Substitution(script, substitutionMapping)).transform(formula);
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
			result &= (mInVars.values().contains(tv) || mOutVars.values().contains(tv) || mAuxVars.contains(tv) || mBranchEncoders
					.contains(tv));
			assert result : "unexpected variable in formula";
		}
		for (final TermVariable tv : mAuxVars) {
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
		for (final TermVariable tv : mAuxVars) {
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

	public Set<ApplicationTerm> getConstants() {
		return Collections.unmodifiableSet(mConstants);
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
		return "Formula: " + mFormula + "  InVars " + mInVars + "  OutVars" + mOutVars + "  AuxVars" + mAuxVars
				+ "  AssignedVars" + mAssignedVars;
	}

	public Infeasibility isInfeasible() {
		return mInfeasibility;
	}

	/**
	 * @param services
	 * @return the relational composition (concatenation) of transformula1 und
	 *         transformula2
	 */
	public static UnmodifiableTransFormula sequentialComposition(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean simplify, final boolean extPqe, final boolean tranformToCNF, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique,
			final UnmodifiableTransFormula... transFormula) {
		logger.debug("sequential composition with" + (simplify ? "" : "out") + " formula simplification");
		final Script script = mgdScript.getScript();
		final Set<TermVariable> auxVars = new HashSet<TermVariable>();
		Term formula = mgdScript.getScript().term("true");
		
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, false, null, false);

		final Map<Term, Term> subsitutionMapping = new HashMap<Term, Term>();
		for (int i = transFormula.length - 1; i >= 0; i--) {
			for (final IProgramVar var : transFormula[i].getOutVars().keySet()) {

				final TermVariable outVar = transFormula[i].getOutVars().get(var);
				TermVariable newOutVar;
				if (tfb.containsInVar(var)) {
					newOutVar = tfb.getInVar(var);
				} else {
					newOutVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(), var.getTermVariable().getSort());
				}
				subsitutionMapping.put(outVar, newOutVar);
				// add to outvars if var is not outvar
				if (!tfb.containsOutVar(var)) {
					tfb.addOutVar(var, newOutVar);
				}
				final TermVariable inVar = transFormula[i].getInVars().get(var);
				if (inVar == null) {
					// case: var is assigned without reading or havoced
					if (tfb.getOutVar(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
					tfb.removeInVar(var);
				} else if (inVar == outVar) {
					// case: var is not modified
					tfb.addInVar(var, newOutVar);
				} else {
					// case: var is read and written
					final TermVariable newInVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(), var.getTermVariable().getSort());
					subsitutionMapping.put(inVar, newInVar);
					tfb.addInVar(var, newInVar);
					if (tfb.getOutVar(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
				}
			}
			auxVars.addAll(transFormula[i].getAuxVars());
			tfb.addBranchEncoders(transFormula[i].getBranchEncoders());

			for (final IProgramVar var : transFormula[i].getInVars().keySet()) {
				if (transFormula[i].getOutVars().containsKey(var)) {
					// nothing do to, this var was already considered above
				} else {
					// case var occurs only as inVar: var is not modfied.
					final TermVariable inVar = transFormula[i].getInVars().get(var);
					TermVariable newInVar;
					if (tfb.containsInVar(var)) {
						newInVar = tfb.getInVar(var);
					} else {
						newInVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(), var.getTermVariable().getSort());
						tfb.addInVar(var, newInVar);
					}
					subsitutionMapping.put(inVar, newInVar);
				}
			}
			final Term originalFormula = transFormula[i].getFormula();
			final Term updatedFormula = (new SubstitutionWithLocalSimplification(mgdScript, subsitutionMapping)).transform(originalFormula);
			formula = Util.and(script, formula, updatedFormula);
		}

		formula = new FormulaUnLet().unlet(formula);
		if (simplify) {
			try {
				final Term simplified = SmtUtils.simplify(mgdScript, formula, services, simplificationTechnique);
				formula = simplified;
			} catch (final ToolchainCanceledException tce) {
				throw new ToolchainCanceledException(UnmodifiableTransFormula.class, tce.getRunningTaskInfo() + 
						" while doing sequential composition of " + transFormula.length + " TransFormulas");
			}
		}

		if (extPqe) {
			final Term eliminated = PartialQuantifierElimination.elim(mgdScript, QuantifiedFormula.EXISTS, auxVars, formula,
					services, logger, simplificationTechnique, xnfConversionTechnique);
			logger.debug(new DebugMessage("DAG size before PQE {0}, DAG size after PQE {1}",
					new DagSizePrinter(formula), new DagSizePrinter(eliminated)));
			formula = eliminated;
		} else {
			final XnfDer xnfDer = new XnfDer(mgdScript, services);
			formula = Util.and(script, xnfDer.tryToEliminate(QuantifiedFormula.EXISTS, SmtUtils.getConjuncts(formula), auxVars));
		}
		if (simplify) {
			formula = SmtUtils.simplify(mgdScript, formula, services, simplificationTechnique);
		} else {
			final LBool isSat = Util.checkSat(script, formula);
			if (isSat == LBool.UNSAT) {
				logger.warn("CodeBlock already infeasible");
				formula = script.term("false");
			}
		}

		Infeasibility infeasibility;
		if (formula == script.term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}

		if (tranformToCNF) {
			final Term cnf = SmtUtils.toCnf(services, mgdScript, formula, xnfConversionTechnique);
			formula = cnf;
		}

		tfb.setFormula(formula);
		tfb.setInfeasibility(infeasibility);
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, mgdScript);
		return tfb.finishConstruction(mgdScript);
	}

	private static void reportTimeoutResult(final IUltimateServiceProvider services) {
		final String timeOutMessage = "Timeout during computation of TransFormula";
		final TimeoutResult timeOutRes = new TimeoutResult(ModelCheckerUtils.PLUGIN_ID, timeOutMessage);
		services.getResultService().reportResult(ModelCheckerUtils.PLUGIN_ID, timeOutRes);
	}



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
	public static UnmodifiableTransFormula parallelComposition(final ILogger logger, final IUltimateServiceProvider services, final int serialNumber,
			final ManagedScript mgdScript, final TermVariable[] branchIndicators, final boolean tranformToCNF, final XnfConversionTechnique xnfConversionTechnique,
			final UnmodifiableTransFormula... transFormulas) {
		logger.debug("parallel composition");
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
		final TransFormulaBuilder tfb; 
		if (useBranchEncoders) {
			tfb = new TransFormulaBuilder(null, null, false, Arrays.asList(branchIndicators), false);
		} else {
			tfb = new TransFormulaBuilder(null, null, true, null, false);
		}

		final Map<IProgramVar, Sort> assignedInSomeBranch = new HashMap<IProgramVar, Sort>();
		for (final UnmodifiableTransFormula tf : transFormulas) {
			for (final IProgramVar bv : tf.getInVars().keySet()) {
				if (!tfb.containsInVar(bv)) {
					final Sort sort = tf.getInVars().get(bv).getSort();
					final String inVarName = bv.getIdentifier() + "_In" + serialNumber;
					tfb.addInVar(bv, mgdScript.variable(inVarName, sort));
				}
			}
			for (final IProgramVar bv : tf.getOutVars().keySet()) {

				// vars which are assigned in some but not all branches must
				// also occur as inVar
				// We can omit this step in the special case where the
				// variable is assigned in all branches.
				if (!tfb.containsInVar(bv) && !assignedInAll(bv, transFormulas)) {
					final Sort sort = tf.getOutVars().get(bv).getSort();
					final String inVarName = bv.getIdentifier() + "_In" + serialNumber;
					tfb.addInVar(bv, mgdScript.variable(inVarName, sort));
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
				tfb.addOutVar(bv, tfb.getInVar(bv));
			}
		}

		// overwrite (see comment above) the outvars if the outvar does not
		// coincide with the invar in some of the transFormulas
		for (final IProgramVar bv : assignedInSomeBranch.keySet()) {
			final Sort sort = assignedInSomeBranch.get(bv);
			final String outVarName = bv.getIdentifier() + "_Out" + serialNumber;
			tfb.addOutVar(bv, mgdScript.variable(outVarName, sort));
		}

		final Set<TermVariable> auxVars = new HashSet<>();
		for (int i = 0; i < transFormulas.length; i++) {
			tfb.addBranchEncoders(transFormulas[i].getBranchEncoders());
			auxVars.addAll(transFormulas[i].getAuxVars());
			final Map<Term, Term> subsitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar bv : transFormulas[i].getInVars().keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				subsitutionMapping.put(inVar, tfb.getInVar(bv));
			}
			for (final IProgramVar bv : transFormulas[i].getOutVars().keySet()) {
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);

				final boolean isAssignedVar = (inVar != outVar);
				if (isAssignedVar) {
					subsitutionMapping.put(outVar, tfb.getOutVar(bv));
				} else {
					assert subsitutionMapping.containsKey(outVar);
					assert subsitutionMapping.containsValue(tfb.getInVar(bv));
				}
			}
			final Term originalFormula = transFormulas[i].getFormula();
			renamedFormulas[i] = (new SubstitutionWithLocalSimplification(mgdScript, subsitutionMapping)).transform(originalFormula);

			for (final IProgramVar bv : assignedInSomeBranch.keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				if (inVar == null && outVar == null) {
					// bv does not occur in transFormula
					assert tfb.getInVar(bv) != null;
					assert tfb.getOutVar(bv) != null;
					final Term equality = mgdScript.getScript().term("=", tfb.getInVar(bv), tfb.getOutVar(bv));
					renamedFormulas[i] = Util.and(mgdScript.getScript(), renamedFormulas[i], equality);
				} else if (inVar == outVar) {
					// bv is not modified in transFormula
					assert tfb.getInVar(bv) != null;
					assert tfb.getOutVar(bv) != null;
					final Term equality = mgdScript.getScript().term("=", tfb.getInVar(bv), tfb.getOutVar(bv));
					renamedFormulas[i] = Util.and(mgdScript.getScript(), renamedFormulas[i], equality);
				}
			}

			if (useBranchEncoders) {
				renamedFormulas[i] = Util.implies(mgdScript.getScript(), branchIndicators[i], renamedFormulas[i]);
			}
		}

		Term resultFormula;
		if (useBranchEncoders) {
			resultFormula = Util.and(mgdScript.getScript(), renamedFormulas);
			final Term atLeastOneBranchTaken = Util.or(mgdScript.getScript(), branchIndicators);
			resultFormula = Util.and(mgdScript.getScript(), resultFormula, atLeastOneBranchTaken);
		} else {
			resultFormula = Util.or(mgdScript.getScript(), renamedFormulas);
		}
		final LBool termSat = Util.checkSat(mgdScript.getScript(), resultFormula);
		Infeasibility inFeasibility;
		if (termSat == LBool.UNSAT) {
			inFeasibility = Infeasibility.INFEASIBLE;
		} else {
			inFeasibility = Infeasibility.UNPROVEABLE;
		}
		if (tranformToCNF) {
			resultFormula = SmtUtils.toCnf(services, mgdScript, resultFormula, xnfConversionTechnique);
		}

		tfb.setFormula(resultFormula);
		tfb.setInfeasibility(inFeasibility);
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, mgdScript);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * Return true iff bv is assigned in all transFormulas.
	 */
	private static boolean assignedInAll(final IProgramVar bv, final UnmodifiableTransFormula... transFormulas) {
		for (final UnmodifiableTransFormula tf : transFormulas) {
			if (!tf.getAssignedVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}


	private void removeOutVar(final IProgramVar var) {
		assert mOutVars.containsKey(var) : "illegal to remove variable not that is contained";
		final TermVariable inVar = mInVars.get(var);
		final TermVariable outVar = mOutVars.get(var);
		mOutVars.remove(var);
		if (inVar != outVar) {
			// outVar does not occurs already as inVar, we have to add outVar
			// to auxVars
			mAuxVars.add(outVar);
			final boolean removed = mAssignedVars.remove(var);
			assert (removed);
		} else {
			assert !mAssignedVars.contains(var);
		}
	}

	private void removeInVar(final IProgramVar var) {
		assert mInVars.containsKey(var) : "illegal to remove variable not that is contained";
		final TermVariable inVar = mInVars.get(var);
		final TermVariable outVar = mOutVars.get(var);
		mInVars.remove(var);
		if (inVar != outVar) {
			// inVar does not occurs already as outVar, we have to add inVar
			// to auxVars
			mAuxVars.add(inVar);
			assert outVar == null || mAssignedVars.contains(var);
		} else {
			assert !mAssignedVars.contains(var);
			if (outVar != null) {
				mAssignedVars.add(var);
			}
		}
	}


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
	public static UnmodifiableTransFormula sequentialCompositionWithPendingCall(final ManagedScript mgdScript, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final List<UnmodifiableTransFormula> beforeCall, final UnmodifiableTransFormula callTf,
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula afterCall, final ILogger logger, final IUltimateServiceProvider services, 
			final Set<IProgramVar> modifiableGlobalsOfEndProcedure, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		logger.debug("sequential composition (pending call) with" + (simplify ? "" : "out") + " formula simplification");
		UnmodifiableTransFormula callAndBeforeTF;
		{
			final List<UnmodifiableTransFormula> callAndBeforeList = new ArrayList<UnmodifiableTransFormula>(beforeCall);
			callAndBeforeList.add(callTf);
			final UnmodifiableTransFormula[] callAndBeforeArray = callAndBeforeList.toArray(new UnmodifiableTransFormula[callAndBeforeList.size()]);
			callAndBeforeTF = sequentialComposition(logger, services, mgdScript, simplify, extPqe, transformToCNF,
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
				callAndBeforeTF.removeOutVar(bv);
			}
		}

		UnmodifiableTransFormula oldAssignAndAfterTF;
		{
			final List<UnmodifiableTransFormula> oldAssignAndAfterList = new ArrayList<UnmodifiableTransFormula>(Arrays.asList(afterCall));
			oldAssignAndAfterList.add(0, oldVarsAssignment);
			final UnmodifiableTransFormula[] oldAssignAndAfterArray = oldAssignAndAfterList.toArray(new UnmodifiableTransFormula[0]);
			oldAssignAndAfterTF = sequentialComposition(logger, services, mgdScript, simplify, extPqe, transformToCNF,
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
				oldAssignAndAfterTF.removeInVar(bv);
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
				oldAssignAndAfterTF.removeOutVar(bv);
			}
		}

		final UnmodifiableTransFormula result = sequentialComposition(logger, services, mgdScript, simplify, 
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
	public static UnmodifiableTransFormula sequentialCompositionWithCallAndReturn(final ManagedScript mgdScript, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final UnmodifiableTransFormula callTf, 
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment,
			final UnmodifiableTransFormula procedureTf, final UnmodifiableTransFormula returnTf, final ILogger logger, 
			final IUltimateServiceProvider services, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		logger.debug("sequential composition (call/return) with" + (simplify ? "" : "out") + " formula simplification");
		final UnmodifiableTransFormula result = sequentialComposition(logger, services, mgdScript, 
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
				result.removeInVar(bv);
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
				result.removeOutVar(bv);
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
		assert SmtUtils.neitherKeyNorValueIsNull(result.mOutVars) : "sequentialCompositionWithCallAndReturn introduced null entries";
		assert (isIntraprocedural(result));
		return result;
	}

	/**
	 * Returns true iff all local variables in tf belong to a single procedure.
	 */
	static boolean isIntraprocedural(final UnmodifiableTransFormula tf) {
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
	
	
	private static UnmodifiableTransFormula computeGuard(final UnmodifiableTransFormula tf, final ManagedScript script) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(tf.getInVars(), tf.getInVars(), true, null, false);
		final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
		for (final IProgramVar bv : tf.getAssignedVars()) {
			final TermVariable outVar = tf.getOutVars().get(bv);
			if (Arrays.asList(tf.getFormula().getFreeVars()).contains(outVar)) {
				auxVars.add(outVar);
			}
		}
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		// yes! outVars of result are indeed the inVars of input

		tfb.setFormula(tf.getFormula());
		tfb.setInfeasibility(tf.isInfeasible());
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, script);
		return tfb.finishConstruction(script);
	}
	
	private static UnmodifiableTransFormula negate(final UnmodifiableTransFormula tf, final ManagedScript maScript, final IUltimateServiceProvider services, 
			final ILogger logger,final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		Term formula = tf.getFormula();
		formula = PartialQuantifierElimination.quantifier(services, logger, 
				maScript, simplificationTechnique, xnfConversionTechnique, QuantifiedFormula.EXISTS, tf.getAuxVars(), 
				formula, new Term[0]);
		final Set<TermVariable> freeVars = new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		freeVars.retainAll(tf.getAuxVars());
		if (!freeVars.isEmpty()) {
			throw new UnsupportedOperationException("cannot negate if there are auxVars");
		}
		formula = SmtUtils.not(maScript.getScript(), formula);
		
		final TransFormulaBuilder tfb = new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(), 
				false, tf.getBranchEncoders(), true);
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(maScript);
	}
	
	public static UnmodifiableTransFormula computeMarkhorTransFormula(final UnmodifiableTransFormula tf, 
			final ManagedScript maScript, final IUltimateServiceProvider services, 
			final ILogger logger, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique) {
		final UnmodifiableTransFormula guard = computeGuard(tf, maScript);
		final UnmodifiableTransFormula negGuard = negate(guard, maScript, services, logger, xnfConversionTechnique, simplificationTechnique);
		final UnmodifiableTransFormula markhor = parallelComposition(logger, services, tf.hashCode(), maScript, null, false, xnfConversionTechnique, tf, negGuard);
		return markhor;
	}
	
//	/**
//	 * Given a set of auxVars, construct a map that assigns to auxVar
//	 * a fresh constant. 
//	 */
//	public static Map<TermVariable, Term> constructAuxVarMapping(final Set<TermVariable> auxVars, final Script script) {
//		final Map<TermVariable,Term> result = new HashMap<>();
//		for (final TermVariable auxVar : auxVars) {
//			final Term auxVarConst = SmtUtils.termVariable2constant(script, auxVar);
//			result.put(auxVar, auxVarConst);
//		}
//		return result;
//	}

}
