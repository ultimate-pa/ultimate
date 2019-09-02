/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2012-2017 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ConstantFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SMTPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Static auxiliary methods for {@link TransFormula}s
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public final class TransFormulaUtils {

	public static final String TRANS_FORMULA_OF_RETURN_MUST_NOT_CONTAIN_AUX_VARS = "TransFormula of return must not contain auxVars";
	public static final String OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS = "oldVarAssignments must not contain auxVars";
	public static final String GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS = "globalVarsAssignments must not contain auxVars";

	private TransFormulaUtils() {
		// do not instantiate utility class
	}

	/**
	 * compute the assigned/updated variables. A variable is updated by this transition if it occurs as outVar and - it
	 * does not occur as inVar - or the inVar is represented by a different TermVariable
	 */
	public static Set<IProgramVar> computeAssignedVars(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars) {
		final HashSet<IProgramVar> assignedVars = new HashSet<>();
		for (final Entry<IProgramVar, TermVariable> entry : outVars.entrySet()) {
			assert entry.getValue() != null;
			if (entry.getValue() != inVars.get(entry.getKey())) {
				assignedVars.add(entry.getKey());
			}
		}
		return assignedVars;
	}

	/**
	 * @param services
	 * @param tryAuxVarElimination
	 *            Apply our partial quantifier elimination and try to eliminate auxVars. This is a postprocessing that
	 *            we apply to the resulting formula which produces an equivalent formula with less auxvars.
	 * @return the relational composition (concatenation) of transformula1 and transformula2
	 */
	public static UnmodifiableTransFormula sequentialComposition(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final boolean simplify,
			final boolean tryAuxVarElimination, final boolean tranformToCNF,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique,
			final List<UnmodifiableTransFormula> transFormula) {
		if (logger.isDebugEnabled()) {
			logger.debug("sequential composition with" + (simplify ? "" : "out") + " formula simplification");
		}
		final Script script = mgdScript.getScript();
		final Set<TermVariable> auxVars = new HashSet<>();
		Term formula = mgdScript.getScript().term("true");

		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, false, null, false, null, false);
		final Set<IProgramConst> nonTheoryConsts = new HashSet<>();

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (int i = transFormula.size() - 1; i >= 0; i--) {
			for (final IProgramVar var : transFormula.get(i).getOutVars().keySet()) {

				final TermVariable outVar = transFormula.get(i).getOutVars().get(var);
				TermVariable newOutVar;
				if (tfb.containsInVar(var)) {
					newOutVar = tfb.getInVar(var);
				} else {
					newOutVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(),
							var.getTermVariable().getSort());
				}
				substitutionMapping.put(outVar, newOutVar);
				// add to outvars if var is not outvar
				if (!tfb.containsOutVar(var)) {
					tfb.addOutVar(var, newOutVar);
				}
				final TermVariable inVar = transFormula.get(i).getInVars().get(var);
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
					final TermVariable newInVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(),
							var.getTermVariable().getSort());
					substitutionMapping.put(inVar, newInVar);
					tfb.addInVar(var, newInVar);
					if (tfb.getOutVar(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
				}
			}
			for (final TermVariable oldAuxVar : transFormula.get(i).getAuxVars()) {
				final TermVariable newAuxVar = mgdScript.constructFreshCopy(oldAuxVar);
				substitutionMapping.put(oldAuxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
			tfb.addBranchEncoders(transFormula.get(i).getBranchEncoders());

			for (final IProgramVar var : transFormula.get(i).getInVars().keySet()) {
				if (transFormula.get(i).getOutVars().containsKey(var)) {
					// nothing do to, this var was already considered above
				} else {
					// case var occurs only as inVar: var is not modfied.
					final TermVariable inVar = transFormula.get(i).getInVars().get(var);
					TermVariable newInVar;
					if (tfb.containsInVar(var)) {
						newInVar = tfb.getInVar(var);
					} else {
						newInVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(),
								var.getTermVariable().getSort());
						tfb.addInVar(var, newInVar);
					}
					substitutionMapping.put(inVar, newInVar);
				}
			}
			final Term originalFormula = transFormula.get(i).getFormula();
			final Term updatedFormula =
					new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(originalFormula);
			nonTheoryConsts.addAll(transFormula.get(i).getNonTheoryConsts());
			formula = SmtUtils.and(script, formula, updatedFormula);
		}

		assert !new SubtermPropertyChecker(a -> a instanceof LetTerm)
				.isPropertySatisfied(formula) : "formula contains LetTerm";

		if (simplify) {
			try {
				final Term simplified = SmtUtils.simplify(mgdScript, formula, services, simplificationTechnique);
				formula = simplified;
			} catch (final ToolchainCanceledException tce) {
				final String taskDescription =
						"doing sequential composition of " + transFormula.size() + " TransFormulas";
				tce.addRunningTaskInfo(new RunningTaskInfo(PartialQuantifierElimination.class, taskDescription));
				throw tce;
			}
		}

		if (tryAuxVarElimination) {
			final Term eliminated = PartialQuantifierElimination.elim(mgdScript, QuantifiedFormula.EXISTS, auxVars,
					formula, services, logger, simplificationTechnique, xnfConversionTechnique);
			logger.debug(new DebugMessage("DAG size before PQE {0}, DAG size after PQE {1}",
					new DagSizePrinter(formula), new DagSizePrinter(eliminated)));
			formula = eliminated;
		} else {
			final XnfDer xnfDer = new XnfDer(mgdScript, services);
			formula = SmtUtils.and(script,
					xnfDer.tryToEliminate(QuantifiedFormula.EXISTS, SmtUtils.getConjuncts(formula), auxVars));
		}
		if (simplify) {
			formula = SmtUtils.simplify(mgdScript, formula, services, simplificationTechnique);
		} else {
			final LBool isSat = Util.checkSat(script, formula);
			if (isSat == LBool.UNSAT) {
				if (logger.isDebugEnabled()) {
					logger.debug("CodeBlock already infeasible");
				}
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

		TransFormulaUtils.addConstantsIfInFormula(tfb, formula, nonTheoryConsts);
		tfb.setFormula(formula);
		tfb.setInfeasibility(infeasibility);
		for (final TermVariable auxVar : auxVars) {
			tfb.addAuxVar(auxVar);
		}
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * The parallel composition of transFormulas is the disjunction of the underlying relations. If we check
	 * satisfiability of a path which contains this transFormula we want know one disjuncts that is satisfiable. We use
	 * additional boolean variables called branchIndicators to encode this disjunction. Example: Assume we have two
	 * TransFormulas tf1 and tf2. Instead of the Formula tf1 || tf2 we use the following formula. (BI1 -> tf1) && (BI2
	 * -> tf2) && (BI1 || BI2) The following holds
	 * <ul>
	 * <li>tf1 || tf2 is satisfiable iff (BI1 -> tf1) && (BI2 -> tf2) && (BI1 || BI2) is satisfiable.
	 * <li>in a satisfying assignment BIi can only be true if tfi is true for i \in {1,2}
	 *
	 * @param logger
	 * @param services
	 * @param xnfConversionTechnique
	 */
	public static UnmodifiableTransFormula parallelComposition(final ILogger logger,
			final IUltimateServiceProvider services, final int serialNumber, final ManagedScript mgdScript,
			final TermVariable[] branchIndicators, final boolean tranformToCNF,
			final XnfConversionTechnique xnfConversionTechnique, final UnmodifiableTransFormula... transFormulas) {
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
			tfb = new TransFormulaBuilder(null, null, false, null, false, Arrays.asList(branchIndicators), false);
		} else {
			tfb = new TransFormulaBuilder(null, null, false, null, true, null, false);
		}
		final Set<IProgramConst> nonTheoryConsts = new HashSet<>();

		final Map<IProgramVar, Sort> assignedInSomeBranch = new HashMap<>();
		for (final UnmodifiableTransFormula tf : transFormulas) {
			for (final IProgramVar bv : tf.getInVars().keySet()) {
				if (!tfb.containsInVar(bv)) {
					final Sort sort = tf.getInVars().get(bv).getSort();
					final String inVarName = bv.getGloballyUniqueId() + "_In" + serialNumber;
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
					final String inVarName = bv.getGloballyUniqueId() + "_In" + serialNumber;
					tfb.addInVar(bv, mgdScript.variable(inVarName, sort));
				}

				final TermVariable outVar = tf.getOutVars().get(bv);
				final TermVariable inVar = tf.getInVars().get(bv);
				final boolean isAssignedVar = outVar != inVar;
				if (isAssignedVar) {
					final Sort sort = tf.getOutVars().get(bv).getSort();
					assignedInSomeBranch.put(bv, sort);
				}
				// auxilliary step, add all invars. Some will be overwritten by
				// outvars
				tfb.addOutVar(bv, tfb.getInVar(bv));
			}
			nonTheoryConsts.addAll(tf.getNonTheoryConsts());
		}

		// overwrite (see comment above) the outvars if the outvar does not
		// coincide with the invar in some of the transFormulas
		for (final Entry<IProgramVar, Sort> entry : assignedInSomeBranch.entrySet()) {
			final IProgramVar bv = entry.getKey();
			final Sort sort = entry.getValue();
			final String outVarName = bv.getGloballyUniqueId() + "_Out" + serialNumber;
			tfb.addOutVar(bv, mgdScript.variable(outVarName, sort));
		}

		final Set<TermVariable> auxVars = new HashSet<>();
		for (int i = 0; i < transFormulas.length; i++) {
			tfb.addBranchEncoders(transFormulas[i].getBranchEncoders());
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final IProgramVar bv : transFormulas[i].getInVars().keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				substitutionMapping.put(inVar, tfb.getInVar(bv));
			}
			for (final IProgramVar bv : transFormulas[i].getOutVars().keySet()) {
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);

				final boolean isAssignedVar = inVar != outVar;
				if (isAssignedVar) {
					substitutionMapping.put(outVar, tfb.getOutVar(bv));
				} else {
					assert substitutionMapping.containsKey(outVar);
					assert substitutionMapping.containsValue(tfb.getInVar(bv));
				}
			}
			for (final TermVariable oldAuxVar : transFormulas[i].getAuxVars()) {
				final TermVariable newAuxVar = mgdScript.constructFreshCopy(oldAuxVar);
				substitutionMapping.put(oldAuxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
			final Term originalFormula = transFormulas[i].getFormula();
			renamedFormulas[i] =
					new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(originalFormula);

			for (final IProgramVar bv : assignedInSomeBranch.keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				if ((inVar == null && outVar == null) || inVar == outVar) {
					// bv does not occur in transFormula or bv is not modified in transFormula
					final TermVariable termInVar = tfb.getInVar(bv);
					final TermVariable termOutVar = tfb.getOutVar(bv);
					assert termInVar != null;
					assert termOutVar != null;
					final Term equality = mgdScript.getScript().term("=", termInVar, termOutVar);
					renamedFormulas[i] = SmtUtils.and(mgdScript.getScript(), renamedFormulas[i], equality);
				}
			}

			if (useBranchEncoders) {
				renamedFormulas[i] = Util.implies(mgdScript.getScript(), branchIndicators[i], renamedFormulas[i]);
			}
		}

		Term resultFormula;
		if (useBranchEncoders) {
			resultFormula = SmtUtils.and(mgdScript.getScript(), renamedFormulas);
			final Term atLeastOneBranchTaken = SmtUtils.or(mgdScript.getScript(), branchIndicators);
			resultFormula = SmtUtils.and(mgdScript.getScript(), resultFormula, atLeastOneBranchTaken);
		} else {
			resultFormula = SmtUtils.or(mgdScript.getScript(), renamedFormulas);
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

		TransFormulaUtils.addConstantsIfInFormula(tfb, resultFormula, nonTheoryConsts);
		tfb.setFormula(resultFormula);
		tfb.setInfeasibility(inFeasibility);
		for (final TermVariable auxVar : auxVars) {
			tfb.addAuxVar(auxVar);
		}
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

	/**
	 * Returns TransFormula that describes a sequence of code blocks that contains a pending call. Note the the scope of
	 * inVars and outVars is different. Do not compose the result with the default/intraprocedural composition.
	 *
	 * @param beforeCall
	 *            TransFormula that describes transition relation before the call.
	 * @param callTf
	 *            TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment
	 *            TransFormula that assigns to oldVars of modifiable globals the value of the global var.
	 * @param globalVarsAssignment
	 *            TODO
	 * @param afterCall
	 *            TransFormula that describes the transition relation after the call.
	 * @param logger
	 * @param services
	 * @param modifiableGlobalsOfEndProcedure
	 *            Set of variables that are modifiable globals in the procedure in which the afterCall TransFormula
	 *            ends.
	 * @param symbolTable
	 */
	public static UnmodifiableTransFormula sequentialCompositionWithPendingCall(final ManagedScript mgdScript,
			final boolean simplify, final boolean extPqe, final boolean transformToCNF,
			final List<UnmodifiableTransFormula> beforeCall, final UnmodifiableTransFormula callTf,
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment,
			final UnmodifiableTransFormula afterCall, final ILogger logger, final IUltimateServiceProvider services,
			final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable, final String procAtStart, final String procBeforeCall,
			final String procAfterCall, final String procAtEnd, final ModifiableGlobalsTable modifiableGlobalsTable) {
		assert procAtStart != null : "proc at start must not be null";
		if (!procAtStart.equals(procBeforeCall)) {
			throw new UnsupportedOperationException("proc change before call");
		}

		logger.debug(
				"sequential composition (pending call) with" + (simplify ? "" : "out") + " formula simplification");
		final UnmodifiableTransFormula callAndBeforeTF;
		{
			final List<UnmodifiableTransFormula> callAndBefore = new ArrayList<>(beforeCall);
			callAndBefore.add(callTf);
			callAndBefore.add(oldVarsAssignment);
			final UnmodifiableTransFormula composition = sequentialComposition(logger, services, mgdScript, simplify,
					extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique, callAndBefore);

			// remove outVars that are not "interface variables"
			// see isInterfaceVariable()
			final List<IProgramVar> outVarsToRemove = new ArrayList<>();
			for (final IProgramVar bv : composition.getOutVars().keySet()) {
				final boolean isInterfaceVariable =
						isInterfaceVariable(bv, callTf, oldVarsAssignment, procBeforeCall, procAfterCall, true, false);
				if (isInterfaceVariable) {
					// keep variable
				} else {
					outVarsToRemove.add(bv);
				}
			}

			final Map<IProgramVar, TermVariable> varsToHavoc = new HashMap<>();
			// we havoc all oldvars that are modifiable by the caller
			// but not modifiable y the callee
			final Set<IProgramNonOldVar> modifiableByCaller =
					modifiableGlobalsTable.getModifiedBoogieVars(procBeforeCall);
			for (final IProgramNonOldVar modifiable : modifiableByCaller) {
				final IProgramOldVar oldVar = modifiable.getOldVar();
				final boolean modifiableByCallee = oldVarsAssignment.getAssignedVars().contains(oldVar);
				if (!modifiableByCallee) {
					varsToHavoc.put(oldVar, mgdScript.constructFreshCopy(oldVar.getTermVariable()));
				}
			}

			// we havoc all local variables of the caller (unless they are inparams of callee)
			final Set<ILocalProgramVar> locals = symbolTable.getLocals(procBeforeCall);
			for (final ILocalProgramVar localVar : locals) {
				final boolean isInParamOfCallee = callTf.getAssignedVars().contains(localVar);
				if (!isInParamOfCallee) {
					varsToHavoc.put(localVar, mgdScript.constructFreshCopy(localVar.getTermVariable()));
				}
			}

			callAndBeforeTF = TransFormulaBuilder.constructCopy(mgdScript, composition, Collections.emptySet(),
					outVarsToRemove, varsToHavoc);

		}

		final UnmodifiableTransFormula globalVarAssignAndAfterTF;
		{
			final List<UnmodifiableTransFormula> oldAssignAndAfterList = new ArrayList<>(Arrays.asList(afterCall));
			oldAssignAndAfterList.add(0, globalVarsAssignment);
			final UnmodifiableTransFormula composition = sequentialComposition(logger, services, mgdScript, simplify,
					extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique, oldAssignAndAfterList);

			// remove inVars that are not "interface variables"
			// see isInterfaceVariable()
			final List<IProgramVar> inVarsToRemove = new ArrayList<>();
			for (final IProgramVar bv : composition.getInVars().keySet()) {
				final boolean isInterfaceVariable =
						isInterfaceVariable(bv, callTf, oldVarsAssignment, procBeforeCall, procAfterCall, false, true);
				if (isInterfaceVariable) {
					// keep variable
				} else {
					inVarsToRemove.add(bv);
				}
			}

			globalVarAssignAndAfterTF = TransFormulaBuilder.constructCopy(mgdScript, composition, inVarsToRemove,
					Collections.emptySet(), Collections.emptyMap());
		}

		final UnmodifiableTransFormula preliminaryResult = sequentialComposition(logger, services, mgdScript, simplify,
				extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique,
				Arrays.asList(new UnmodifiableTransFormula[] { callAndBeforeTF, globalVarAssignAndAfterTF }));

		// If the procedure does not change after the call, we already have
		// the result. Otherwise we have to remove the inparams since they
		// do not have the scope of the procedure at the end
		// Note that in case of recursive procedure calls we do not have to
		// remove anything. If the after-call-formula was build correctly
		// it ensures that the inparam instances are not outvars after the
		// composition above.
		final UnmodifiableTransFormula result;
		if (procAfterCall.equals(procAtEnd)) {
			result = preliminaryResult;
		} else {
			final List<IProgramVar> outVarsToRemove = new ArrayList<>();
			// remove inparams of callee that are still in the outvars
			for (final IProgramVar pv : preliminaryResult.getOutVars().keySet()) {
				if (callTf.getAssignedVars().contains(pv)) {
					// pv is inparam, we have to remove it
					outVarsToRemove.add(pv);
				}
			}
			if (outVarsToRemove.isEmpty()) {
				// nothing to remove
				result = preliminaryResult;
			} else {
				result = TransFormulaBuilder.constructCopy(mgdScript, preliminaryResult, Collections.emptySet(),
						outVarsToRemove, Collections.emptyMap());
			}
		}

		assert !result.getBranchEncoders().isEmpty()
				|| predicateBasedResultCheck(services, mgdScript, xnfConversionTechnique, simplificationTechnique,
						beforeCall, callTf, oldVarsAssignment, globalVarsAssignment, afterCall, result, symbolTable,
						modifiableGlobalsOfEndProcedure) : "sequentialCompositionWithPendingCall - incorrect result";
		return result;
	}

	/**
	 * Check if {@link IProgramVar} is variable at the interface between caller and callee. This is used for
	 * interprocedural sequential compositions with pending calls. We say that a variable is an interface variable if it
	 * is either - an inparam of the callee (local variable) - an oldvar that is in the callee's set of modifiable
	 * variables - an non-old global variable that is not in the callee's set of modifiable variables.
	 */
	private static boolean isInterfaceVariable(final IProgramVar bv, final UnmodifiableTransFormula callTf,
			final UnmodifiableTransFormula oldVarsAssignment, final String procBeforeCall, final String procAfterCall,
			final boolean tolerateLocalVarsOfCaller, final boolean tolerateLocalVarsOfCallee) {
		final boolean isInterfaceVariable;
		if (bv.isGlobal()) {
			if (bv.isOldvar()) {
				if (oldVarsAssignment.getOutVars().containsKey(bv)) {
					// is a modifiable oldvar
					isInterfaceVariable = true;
				} else {
					// has to be renamed to non-old var
					throw new AssertionError("oldvars not yet implemented");
				}
			} else {
				if (oldVarsAssignment.getInVars().containsKey(bv)) {
					isInterfaceVariable = false;
				} else {
					// global and not modified by procedure
					isInterfaceVariable = true;
				}
			}
		} else {
			if (bv.getProcedure().equals(procAfterCall)) {
				if (callTf.getAssignedVars().contains(bv)) {
					// is an inparam
					isInterfaceVariable = true;
				} else {
					if (tolerateLocalVarsOfCallee) {
						// no AssertionError
					} else {
						if (procBeforeCall.equals(procAfterCall) && tolerateLocalVarsOfCaller) {
							// no AssertionError
						} else {
							throw new AssertionError("local var of callee is no inparam " + bv);
						}
					}
					isInterfaceVariable = false;
				}
			} else if (bv.getProcedure().equals(procBeforeCall)) {
				if (!tolerateLocalVarsOfCaller) {
					throw new AssertionError("local var of caller " + bv);
				}
				isInterfaceVariable = false;
			} else {
				throw new AssertionError("local var neither from caller nor callee " + bv);
			}
		}
		return isInterfaceVariable;
	}

	private static boolean predicateBasedResultCheck(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique, final List<UnmodifiableTransFormula> beforeCall,
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula oldVarsAssignment,
			final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula afterCallTf,
			final UnmodifiableTransFormula result, final IIcfgSymbolTable symbolTable,
			final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure) {
		assert result.getBranchEncoders().isEmpty() : "result check not applicable with branch encoders";
		final PredicateTransformer<Term, IPredicate, TransFormula> pt =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(services, mgdScript));
		final BasicPredicateFactory bpf = new BasicPredicateFactory(services, mgdScript, symbolTable);
		final IPredicate truePredicate = bpf.newPredicate(mgdScript.getScript().term("true"));
		Term resultComposition = pt.strongestPostcondition(truePredicate, result);
		resultComposition =
				new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(resultComposition);
		final IPredicate resultCompositionPredicate = bpf.newPredicate(resultComposition);
		IPredicate beforeCallPredicate = truePredicate;
		for (final UnmodifiableTransFormula tf : beforeCall) {
			final Term tmp = pt.strongestPostcondition(beforeCallPredicate, tf);
			beforeCallPredicate = bpf.newPredicate(tmp);
		}
		final Term afterCallTerm = pt.strongestPostconditionCall(beforeCallPredicate, callTf, globalVarsAssignment,
				oldVarsAssignment, modifiableGlobalsOfEndProcedure);
		final IPredicate afterCallPredicate = bpf.newPredicate(afterCallTerm);
		Term endTerm = pt.strongestPostcondition(afterCallPredicate, afterCallTf);
		endTerm = new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(endTerm);
		final IPredicate endPredicate = bpf.newPredicate(endTerm);
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final Validity check1 = mic.checkImplication(endPredicate, false, resultCompositionPredicate, false);
		final Validity check2 = mic.checkImplication(resultCompositionPredicate, false, endPredicate, false);
		assert check1 != Validity.INVALID
				&& check2 != Validity.INVALID : "sequentialCompositionWithPendingCall - incorrect result";
		return check1 != Validity.INVALID && check2 != Validity.INVALID;
	}

	/**
	 * Returns a TransFormula that can be seen as procedure summary.
	 *
	 * @param callTf
	 *            TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment
	 *            TransFormula that assigns to oldVars of modifiable globals the value of the global var.
	 * @param procedureTf
	 *            TransFormula that describes the procedure.
	 * @param returnTf
	 *            TransFormula that assigns the result of the procedure call.
	 * @param logger
	 * @param services
	 * @param symbolTable
	 * @param modifiableGlobalsOfCallee
	 */
	public static UnmodifiableTransFormula sequentialCompositionWithCallAndReturn(final ManagedScript mgdScript,
			final boolean simplify, final boolean extPqe, final boolean transformToCNF,
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula oldVarsAssignment,
			final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula procedureTf,
			final UnmodifiableTransFormula returnTf, final ILogger logger, final IUltimateServiceProvider services,
			final XnfConversionTechnique xnfConversionTechnique, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable, final Set<IProgramNonOldVar> modifiableGlobalsOfCallee) {
//		if (!callTf.getAuxVars().isEmpty()) {
//			throw new UnsupportedOperationException(TransFormulaUtils.AUX_VARS_IN_CALL_TF);
//		}
		if (!returnTf.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.TRANS_FORMULA_OF_RETURN_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarsAssignment.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!globalVarsAssignment.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}


		logger.debug("sequential composition (call/return) with" + (simplify ? "" : "out") + " formula simplification");
		final UnmodifiableTransFormula composition =
				sequentialComposition(logger, services, mgdScript, simplify, extPqe, transformToCNF,
						xnfConversionTechnique, simplificationTechnique, Arrays.asList(new UnmodifiableTransFormula[] {
								callTf, oldVarsAssignment, globalVarsAssignment, procedureTf, returnTf }));

		// remove invars except for
		// local vars that occur in arguments of the call
		// oldvars that are modifiable by the callee unless they occur in
		// arguments of the call
		final List<IProgramVar> inVarsToRemove = new ArrayList<>();
		for (final IProgramVar bv : composition.getInVars().keySet()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					final boolean isModifiableByCallee = oldVarsAssignment.getAssignedVars().contains(bv);
					if (isModifiableByCallee) {
						final boolean occursInArguments = callTf.getInVars().containsKey(bv);
						if (occursInArguments) {
							// keep, invar instance refers to start of caller
						} else {
							// remove, invar instance refers to start of callee
							inVarsToRemove.add(bv);
						}
					} else {
						// keep, invar instance refers to start of caller
					}
				} else {
					// keep, invar instance's scope is caller or before
					// (because for the modifiables the oldvarsassignment
					// introduced a new instance
				}
			} else {
				final boolean occursInArguments = callTf.getInVars().containsKey(bv);
				if (occursInArguments) {
					// keep, invar instance's scope is caller
				} else {
					// remove, this is a local variables of callee
					inVarsToRemove.add(bv);
				}
			}
		}

		// remove outvars except for
		// local vars that are outvars of return
		// oldvars that are modifiable by the callee
		// note that it is not possible that return assigns an oldvar
		final List<IProgramVar> outVarsToRemove = new ArrayList<>();
		for (final IProgramVar bv : composition.getOutVars().keySet()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					final boolean isModifiableByCallee = oldVarsAssignment.getAssignedVars().contains(bv);
					if (isModifiableByCallee) {
						// remove, outvar instance refers to instance at beginning of calleee
						outVarsToRemove.add(bv);
					} else {
						// keep, outvar instance refers to start of caller
					}
				} else {
					// keep
				}
			} else {
				if (!returnTf.getOutVars().containsKey(bv)) {
					// bv is local var of callee
					outVarsToRemove.add(bv);
				}
			}
		}
		// our composition might have introduced arguments of the caller as
		// inVars, they should not count as havoced, we have to add them to
		// outvars
		final Map<IProgramVar, TermVariable> additionalOutVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : callTf.getInVars().entrySet()) {
			// we add the invar as outvar if there is not yet an outvar,
			// or we remove the outvar (e.g., in recursive programs in can
			// happen that the outvar instance does not coincide with
			// the invar but the outvar instance belongs to the caller
			if (!composition.getOutVars().containsKey(entry.getKey()) || outVarsToRemove.contains(entry.getKey())) {
				final TermVariable inVar = composition.getInVars().get(entry.getKey());
				if (inVar == null) {
					// do nothing, not in formula any more
				} else {
					additionalOutVars.put(entry.getKey(), inVar);
				}
			}
		}
		final UnmodifiableTransFormula result = TransFormulaBuilder.constructCopy(mgdScript, composition,
				inVarsToRemove, outVarsToRemove, additionalOutVars);

		assert SmtUtils.neitherKeyNorValueIsNull(
				result.getOutVars()) : "sequentialCompositionWithCallAndReturn introduced null entries";
		assert isIntraprocedural(result);
		assert !result.getBranchEncoders().isEmpty() || predicateBasedResultCheck(services, logger, mgdScript,
				xnfConversionTechnique, simplificationTechnique, callTf, oldVarsAssignment, globalVarsAssignment,
				procedureTf, returnTf, result, symbolTable,
				modifiableGlobalsOfCallee) : "sequentialCompositionWithCallAndReturn - incorrect result";
		return result;
	}

	private static boolean predicateBasedResultCheck(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique, final UnmodifiableTransFormula callTf,
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment,
			final UnmodifiableTransFormula procedureTf, final UnmodifiableTransFormula returnTf,
			final UnmodifiableTransFormula result, final IIcfgSymbolTable symbolTable,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		assert result.getBranchEncoders().isEmpty() : "result check not applicable with branch encoders";
		final PredicateTransformer<Term, IPredicate, TransFormula> pt =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(services, mgdScript));
		final BasicPredicateFactory bpf = new BasicPredicateFactory(services, mgdScript, symbolTable);
		final IPredicate truePredicate = bpf.newPredicate(mgdScript.getScript().term("true"));
		Term resultComposition = pt.strongestPostcondition(truePredicate, result);
		resultComposition =
				new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(resultComposition);
		final IPredicate resultCompositionPredicate = bpf.newPredicate(resultComposition);
		final Term afterCallTerm = pt.strongestPostconditionCall(truePredicate, callTf, globalVarsAssignment,
				oldVarsAssignment, modifiableGlobals);
		final IPredicate afterCallPredicate = bpf.newPredicate(afterCallTerm);
		final Term beforeReturnTerm = pt.strongestPostcondition(afterCallPredicate, procedureTf);
		final IPredicate beforeReturnPredicate = bpf.newPredicate(beforeReturnTerm);
		Term afterReturnTerm = pt.strongestPostconditionReturn(beforeReturnPredicate, truePredicate, returnTf, callTf,
				oldVarsAssignment, modifiableGlobals);
		afterReturnTerm =
				new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(afterReturnTerm);
		final IPredicate afterReturnPredicate = bpf.newPredicate(afterReturnTerm);
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final Validity check1 = mic.checkImplication(afterReturnPredicate, false, resultCompositionPredicate, false);
		final Validity check2 = mic.checkImplication(resultCompositionPredicate, false, afterReturnPredicate, false);
		assert check1 != Validity.INVALID
				&& check2 != Validity.INVALID : "sequentialCompositionWithCallAndReturn - incorrect result";
		if (check1 == Validity.UNKNOWN || check2 == Validity.UNKNOWN) {
			logger.warn("predicate-based correctness check returned UNKNOWN, "
					+ "hence correctness of interprocedural sequential composition was not checked.");
		}
		return check1 != Validity.INVALID && check2 != Validity.INVALID;
	}

	/**
	 * Returns true iff all local variables in tf belong to a single procedure.
	 */
	static boolean isIntraprocedural(final UnmodifiableTransFormula tf) {
		final Set<String> procedures = new HashSet<>();
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

	public static UnmodifiableTransFormula computeGuard(final UnmodifiableTransFormula tf,
			final ManagedScript mgdScript, final IUltimateServiceProvider services, final ILogger logger) {
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

		final Pair<Term, Set<TermVariable>> termAndAuxVars =
				tryToEliminateAuxVars(services, logger, mgdScript, tf.getFormula(), auxVars);

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(tf.getInVars(), tf.getInVars(), tf.getNonTheoryConsts().isEmpty(),
						tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(), true, null, false);
		tfb.setFormula(termAndAuxVars.getFirst());
		tfb.setInfeasibility(tf.isInfeasible());
		tfb.addAuxVarsButRenameToFreshCopies(termAndAuxVars.getSecond(), mgdScript);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * The "guarded havoc" is the transition relation in which we keep the guard
	 * (for all inVars) but havoc all variables that are updated.
	 * <p>
	 * TODO Matthias 2018-12-22: This could be improved to a result where we keep
	 * also guards on outVars. E.g., the forumula that corresponds to the sequence
	 * <code>x := 0 havoc y; assume y>=0</code> would be translated to 'true'.
	 * However since only outVars are affected we would like to keep this
	 * information. This could be achieved by taking the conjunction of the current
	 * implementation together with a copy of this formula in which all inVars have
	 * been existentially quantified.
	 * <p>
	 * We would afterwards change the documentation as follows.
	 * The idea of this method is to provide an {@link UnmodifiableTransFormula} in
	 * which all information about the connection between inVars and outVars is
	 * dropped, with one exception: the information that a variable does not changes
	 * its value may be kept. (We cannot guarantee that this information is kept
	 * because the equality of two variables might be hidden in complicated formula
	 * and we cannot detect the equality without using an SMT solver.
	 */
	public static UnmodifiableTransFormula computeGuardedHavoc(final UnmodifiableTransFormula tf,
			final ManagedScript mgdScript, final IUltimateServiceProvider services, final ILogger logger,
			final boolean cellPrecisionForArrays) {
		final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar bv : tf.getAssignedVars()) {
			if (cellPrecisionForArrays && SmtSortUtils.isArraySort(bv.getTermVariable().getSort())) {
				final Set<ApplicationTerm> stores =
						new ApplicationTermFinder("store", false).findMatchingSubterms(tf.getFormula());
				for (final ApplicationTerm appTerm : stores) {
					final Term storedValue = appTerm.getParameters()[2];
					if (!SmtSortUtils.isArraySort(storedValue.getSort())) {
						final TermVariable aux = mgdScript.constructFreshTermVariable("rosehip", storedValue.getSort());
						final Term array = appTerm.getParameters()[0];
						final Term index = appTerm.getParameters()[1];
						final Term newSelect = SmtUtils.store(mgdScript.getScript(), array, index, aux);
						substitutionMapping.put(appTerm, newSelect);
						auxVars.add(aux);
					}
				}
			} else {
				final TermVariable outVar = tf.getOutVars().get(bv);
				final TermVariable aux = mgdScript.constructFreshCopy(outVar);
				substitutionMapping.put(outVar, aux);
				auxVars.add(aux);
			}
		}
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		final Term term = new Substitution(mgdScript, substitutionMapping).transform(tf.getFormula());
		final Pair<Term, Set<TermVariable>> termAndAuxVars =
				tryToEliminateAuxVars(services, logger, mgdScript, term, auxVars);

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(), tf.getNonTheoryConsts().isEmpty(),
						tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(), true, null, false);
		tfb.setFormula(termAndAuxVars.getFirst());
		tfb.setInfeasibility(tf.isInfeasible());
		tfb.addAuxVarsButRenameToFreshCopies(termAndAuxVars.getSecond(), mgdScript);
		return tfb.finishConstruction(mgdScript);
	}

	public static UnmodifiableTransFormula negate(final UnmodifiableTransFormula tf, final ManagedScript maScript,
			final IUltimateServiceProvider services, final ILogger logger,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new AssertionError("I think this does not make sense with branch enconders");
		}
		final Pair<Term, Set<TermVariable>> termAndAuxVars =
				tryToEliminateAuxVars(services, logger, maScript, tf.getFormula(), tf.getAuxVars());
		if (!termAndAuxVars.getSecond().isEmpty()) {
			throw new UnsupportedOperationException("cannot negate if there are auxVars");
		}
		final Term formula = SmtUtils.not(maScript.getScript(), termAndAuxVars.getFirst());

		final TransFormulaBuilder tfb = new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(),
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(),
				false, tf.getBranchEncoders(), true);
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(maScript);
	}

	/**
	 * Given the return of a {@link Transformula} try to eliminate auxvars.
	 *
	 * @return new term and set of remaining auxvars.
	 */
	private static Pair<Term, Set<TermVariable>> tryToEliminateAuxVars(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript maScript, final Term formula,
			final Set<TermVariable> oldAuxVars) {
		final Term resultTerm = PartialQuantifierElimination.quantifier(services, logger, maScript,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				QuantifiedFormula.EXISTS, oldAuxVars, formula);
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(resultTerm.getFreeVars()));
		freeVars.retainAll(oldAuxVars);
		final Pair<Term, Set<TermVariable>> result = new Pair<>(resultTerm, freeVars);
		return result;
	}

	public static UnmodifiableTransFormula computeMarkhorTransFormula(final UnmodifiableTransFormula tf,
			final ManagedScript maScript, final IUltimateServiceProvider services, final ILogger logger,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		final UnmodifiableTransFormula guard = computeGuard(tf, maScript, services, logger);
		final UnmodifiableTransFormula negGuard =
				negate(guard, maScript, services, logger, xnfConversionTechnique, simplificationTechnique);
		final UnmodifiableTransFormula markhor = parallelComposition(logger, services, tf.hashCode(), maScript, null,
				false, xnfConversionTechnique, tf, negGuard);
		return markhor;
	}

	public static UnmodifiableTransFormula computeEncodedBranchFormula(final UnmodifiableTransFormula tf,
			final UnmodifiableTransFormula altPath, final ManagedScript maScript,
			final IUltimateServiceProvider services, final ILogger logger,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {

		final UnmodifiableTransFormula blockEnoded = parallelComposition(logger, services, tf.hashCode(), maScript,
				null, false, xnfConversionTechnique, tf, altPath);
		return blockEnoded;

	}

	/**
	 * Add all elements of progConsts to tfb that occur in formula, ignore the those that do not occur in the formula.
	 */
	public static <T extends IProgramConst> void addConstantsIfInFormula(final TransFormulaBuilder tfb,
			final Term formula, final Set<T> progConsts) {
		final Set<ApplicationTerm> constsInFormula = new ConstantFinder().findConstants(formula, false);
		for (final IProgramConst progConst : progConsts) {
			if (constsInFormula.contains(progConst.getDefaultConstant())) {
				tfb.addProgramConst(progConst);
			}
		}
	}

	public static <V, K> Map<V, K> constructReverseMapping(final Map<K, V> map) {
		return map.entrySet().stream().collect(Collectors.toMap(Entry::getValue, Entry::getKey));
	}

	public static Map<TermVariable, TermVariable> constructInvarsToDefaultvarsMap(final TransFormula tf) {
		return tf.getInVars().entrySet().stream()
				.collect(Collectors.toMap(Entry::getValue, x -> x.getKey().getTermVariable()));
	}

	public static Map<TermVariable, TermVariable> constructOutvarsToDefaultvarsMap(final TransFormula tf) {
		return tf.getOutVars().entrySet().stream()
				.collect(Collectors.toMap(Entry::getValue, x -> x.getKey().getTermVariable()));
	}

	public static Map<TermVariable, TermVariable> constructInvarsToOutvarsMap(final TransFormula tf) {
		return tf.getInVars().entrySet().stream().filter(x -> tf.getOutVars().containsKey(x.getKey()))
				.collect(Collectors.toMap(Entry::getValue, x -> tf.getOutVars().get(x.getKey())));
	}

	public static Map<TermVariable, TermVariable> constructOutvarsToInvarsMap(final TransFormula tf) {
		return tf.getOutVars().entrySet().stream().filter(x -> tf.getInVars().containsKey(x.getKey()))
				.collect(Collectors.toMap(Entry::getValue, x -> tf.getInVars().get(x.getKey())));
	}

	public static boolean eachFreeVarIsInvar(final TransFormula tf, final Term term) {
		final Set<TermVariable> inVars = tf.getInVars().entrySet().stream().map(x -> x.getValue())
				.collect(Collectors.toSet());
		return Arrays.stream(term.getFreeVars()).allMatch(inVars::contains);
	}

	public static boolean eachFreeVarIsOutvar(final TransFormula tf, final Term term) {
		final Set<TermVariable> outVars = tf.getOutVars().entrySet().stream().map(x -> x.getValue())
				.collect(Collectors.toSet());
		return Arrays.stream(term.getFreeVars()).allMatch(outVars::contains);
	}

	public static Term renameInvarsToDefaultVars(final TransFormula tf, final ManagedScript mgdScript,
			final Term term) {
		final Map<TermVariable, TermVariable> map = constructInvarsToDefaultvarsMap(tf);
		return new Substitution(mgdScript, map).transform(term);
	}

	public static Term renameOutvarsToDefaultVars(final TransFormula tf, final ManagedScript mgdScript,
			final Term term) {
		final Map<TermVariable, TermVariable> map = constructOutvarsToDefaultvarsMap(tf);
		return new Substitution(mgdScript, map).transform(term);
	}

	public static UnmodifiableTransFormula constructHavoc(final TransFormula tf, final ManagedScript mgdScript) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(), false,
				tf.getNonTheoryConsts(), true, null, false);
		tfb.setFormula(mgdScript.getScript().term("true"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * This method first computes the guards of the input {@link UnmodifiableTransFormula}s. It then returns a
	 * {@link UnmodifiableTransFormula} that is satisfied for some input variables iff none of the guards is satisfied.
	 * The output variables of the result are simply set to the input variables.
	 *
	 * This method will not always work: in case the disjunction contains auxvars that cannot be eliminated this method
	 * will throw an Exception.
	 *
	 *
	 * TODO 2017-08-07 Matthias: Get rid of serial number in parallel composition.
	 *
	 * @param logger
	 * @param services
	 * @param serialNumber
	 *            Use a different number in each call. This is an ugly workaround and will be removed in the future.
	 * @param mgdScript
	 * @param transFormulas
	 *            The other TransFormulas.
	 * @return A TransFormula in guard form.
	 */
	public static UnmodifiableTransFormula constructRemainderGuard(final ILogger logger,
			final IUltimateServiceProvider services, final int serialNumber, final ManagedScript mgdScript,
			final UnmodifiableTransFormula... transFormulas) {
		final UnmodifiableTransFormula disjunction = parallelComposition(logger, services, serialNumber, mgdScript,
				null, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, transFormulas);
		final UnmodifiableTransFormula guardOfDisjunction = computeGuard(disjunction, mgdScript, services, logger);
		return negate(guardOfDisjunction, mgdScript, services, logger,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA);
	}

	/**
	 * Substitutes TermVariables in the given TransFormula by other given TermVariables.
	 *
	 * @param tf
	 *            The TransFormula
	 * @param mgdScript
	 *            A ManagedScript
	 * @param mapping
	 *            A map from the to be replaced variables to their replacements.
	 * @return A new UnmodifiableTransFormula where the variables have been substituted.
	 */
	public static UnmodifiableTransFormula substituteTermVars(final TransFormula tf, final ManagedScript mgdScript,
			final Map<TermVariable, TermVariable> mapping) {
		final Map<IProgramVar, TermVariable> inVars = tf.getInVars().entrySet().stream()
				.collect(Collectors.toMap(Entry::getKey, e -> mapping.getOrDefault(e.getValue(), e.getValue())));
		final Map<IProgramVar, TermVariable> outVars = tf.getOutVars().entrySet().stream()
				.collect(Collectors.toMap(Entry::getKey, e -> mapping.getOrDefault(e.getValue(), e.getValue())));
		final Set<TermVariable> auxVars = new HashSet<>();
		for (final TermVariable auxVar : tf.getAuxVars()) {
			auxVars.add(mapping.getOrDefault(auxVar, auxVar));
		}

		final Map<Term, Term> substitutionMapping = new HashMap<>(mapping);
		final Term term = new Substitution(mgdScript, substitutionMapping).transform(tf.getFormula());
		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, false);
		builder.setFormula(term);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		builder.addAuxVarsButRenameToFreshCopies(auxVars, mgdScript);
		return builder.finishConstruction(mgdScript);
	}


	/**
	 * Checks if for a pair of {@link UnmodifiableTransFormula}s (lhs,rhs) if lhs
	 * implies rhs, i.e., if the relation represented by lhs is a subset of the
	 * relation by rhs.
	 *
	 * FIXME 20190902 Matthias: WARNING this method does not yet provide correct
	 * results! I will fix the method in the next days.
	 *
	 * @param mgdScript
	 *            {@link ManagedScript} that is not locked.
	 * @return UNSAT if the implication holds, SAT if the implication does not hold,
	 *         UNKNOWN if the SMT solver was unable to check satisfiability.
	 */
	public static LBool checkImplication(final UnmodifiableTransFormula lhs, final UnmodifiableTransFormula rhs,
			final ManagedScript mgdScript) {
		if (!lhs.getAuxVars().isEmpty()) {
			throw new UnsupportedOperationException();
		}
		if (!rhs.getAuxVars().isEmpty()) {
			throw new UnsupportedOperationException();
		}
		mgdScript.lock(lhs);
		mgdScript.push(lhs, 1);
		mgdScript.assertTerm(lhs, lhs.getClosedFormula());
		mgdScript.assertTerm(lhs, SmtUtils.not(mgdScript.getScript(), rhs.getClosedFormula()));
		final LBool result = mgdScript.checkSat(lhs);
		mgdScript.pop(lhs, 1);
		mgdScript.unlock(lhs);
		return result;
	}

	/**
	 * Attempts to find the IProgramVarOrConst that corresponds to the given term in the given TransFormula.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @param tf
	 * @param term
	 * @return The IProgramVarOrConst that corresponds to term in tf. Null if there is none.
	 */
	public static IProgramVarOrConst getProgramVarOrConstForTerm(final TransFormula tf, final Term term) {
		if (term instanceof TermVariable) {
			return getProgramVarForTerm(tf, (TermVariable) term);
		} else if (term instanceof ApplicationTerm) {
			for (final IProgramConst ntc : tf.getNonTheoryConsts()) {
				if (ntc.getDefaultConstant().equals(term)) {
					return ntc;
				}
			}
		}
		return null;
	}

	/**
	 * Attempts to find the IProgramVar that corresponds to the given term in the given TransFormula.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @param tf
	 * @param tv
	 * @return The IProgramVar that corresponds to tv in tf. Null if there is none.
	 */
	public static IProgramVarOrConst getProgramVarForTerm(final TransFormula tf, final TermVariable tv) {
		for (final Entry<IProgramVar, TermVariable> en : tf.getInVars().entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		for (final Entry<IProgramVar, TermVariable> en : tf.getOutVars().entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		return null;
	}

	/**
	 * Pretty print a TransFormula by adding some line breaks to its normal {@link Object#toString()} representation.
	 * Uses some simple heuristics like "align equality constraints which are argument to the same and/or by the same
	 * indentation".
	 *
	 * @param tf
	 * @return
	 */
	public static String prettyPrint(final TransFormula tf) {
		final StringBuilder sb = new StringBuilder();

		// pretty print formula
		final String prettyPrintedFormula = new SMTPrettyPrinter(tf.getFormula()).toString();
		sb.append(prettyPrintedFormula);
		sb.append("\n");

		sb.append("Invars:\n");
		sb.append(tf.getInVars());
		sb.append("\n");

		sb.append("Outvars:\n");
		sb.append(tf.getOutVars());

		return sb.toString();
	}
}
