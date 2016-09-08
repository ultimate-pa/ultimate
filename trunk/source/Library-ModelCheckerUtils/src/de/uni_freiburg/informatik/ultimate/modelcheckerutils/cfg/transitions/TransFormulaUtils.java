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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Static auxiliary methods for {@link TransFormula}s
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TransFormulaUtils {

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

		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (int i = transFormula.length - 1; i >= 0; i--) {
			for (final IProgramVar var : transFormula[i].getOutVars().keySet()) {

				final TermVariable outVar = transFormula[i].getOutVars().get(var);
				TermVariable newOutVar;
				if (tfb.containsInVar(var)) {
					newOutVar = tfb.getInVar(var);
				} else {
					newOutVar = mgdScript.constructFreshTermVariable(var.getGloballyUniqueId(), var.getTermVariable().getSort());
				}
				substitutionMapping.put(outVar, newOutVar);
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
					substitutionMapping.put(inVar, newInVar);
					tfb.addInVar(var, newInVar);
					if (tfb.getOutVar(var) != newOutVar) {
						// add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
				}
			}
			for (final TermVariable oldAuxVar : transFormula[i].getAuxVars()) {
				final TermVariable newAuxVar = mgdScript.constructFreshCopy(oldAuxVar);
				substitutionMapping.put(oldAuxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
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
					substitutionMapping.put(inVar, newInVar);
				}
			}
			final Term originalFormula = transFormula[i].getFormula();
			final Term updatedFormula = (new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping)).transform(originalFormula);
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
		for (final TermVariable auxVar : auxVars) {
			tfb.addAuxVar(auxVar);
		}
		return tfb.finishConstruction(mgdScript);
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
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar bv : transFormulas[i].getInVars().keySet()) {
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);
				substitutionMapping.put(inVar, tfb.getInVar(bv));
			}
			for (final IProgramVar bv : transFormulas[i].getOutVars().keySet()) {
				final TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				final TermVariable inVar = transFormulas[i].getInVars().get(bv);

				final boolean isAssignedVar = (inVar != outVar);
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
			renamedFormulas[i] = (new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping)).transform(originalFormula);

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
	 * Returns TransFormula that describes a sequence of code blocks that
	 * contains a pending call. Note the the scope of inVars and outVars is
	 * different. Do not compose the result with the default/intraprocedural
	 * composition.
	 * @param beforeCall
	 *            TransFormula that describes transition relation before the
	 *            call.
	 * @param callTf
	 *            TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment
	 *            TransFormula that assigns to oldVars of modifiable globals the
	 *            value of the global var.
	 * @param globalVarsAssignment TODO
	 * @param afterCall
	 *            TransFormula that describes the transition relation after the
	 *            call.
	 * @param logger
	 * @param services
	 * @param modifiableGlobalsOfEndProcedure
	 * 			  Set of variables that are modifiable globals in the procedure
	 * 	          in which the afterCall TransFormula ends. 
	 * @param symbolTable 
	 */
	public static UnmodifiableTransFormula sequentialCompositionWithPendingCall(final ManagedScript mgdScript, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final List<UnmodifiableTransFormula> beforeCall, final UnmodifiableTransFormula callTf,
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula afterCall, final ILogger logger, 
			final IUltimateServiceProvider services, 
			final Set<IProgramVar> modifiableGlobalsOfEndProcedure, 
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique, 
			final Boogie2SmtSymbolTable symbolTable,
			final String procAtStart, final String procBeforeCall, final String procAfterCall, final String procAtEnd,
			final ModifiableGlobalVariableManager modGlobVarManager) {
		assert procAtStart != null : "proc at start must not be null";
		if (!procAtStart.equals(procBeforeCall)) {
			throw new UnsupportedOperationException("proc change before call");
		}
		final boolean recursiveProcedureChange =  (procBeforeCall.equals(procAtEnd));
		
		logger.debug("sequential composition (pending call) with" + (simplify ? "" : "out") + " formula simplification");
		final UnmodifiableTransFormula callAndBeforeTF;
		{
			final List<UnmodifiableTransFormula> callAndBeforeList = new ArrayList<UnmodifiableTransFormula>(beforeCall);
			callAndBeforeList.add(callTf);
			callAndBeforeList.add(oldVarsAssignment);
			final UnmodifiableTransFormula[] callAndBeforeArray = callAndBeforeList.toArray(new UnmodifiableTransFormula[callAndBeforeList.size()]);
			final UnmodifiableTransFormula composition = sequentialComposition(logger, services, mgdScript, simplify, extPqe, transformToCNF,
					xnfConversionTechnique, simplificationTechnique, callAndBeforeArray);

			// remove outVars that relate to scope of caller
			// remove all but the following
			// - in params of called procedure
			// - oldVars that are modified by called procedure
			// - non-oldVars of variables that are not modified by the called procedure
			// additionally, we have to replace oldVars that are not modified by the 
			// called procedure by the corresponding non-oldVars
			final List<IProgramVar> outVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : composition.getOutVars().keySet()) {
				final boolean isInterfaceVariable = isInterfaceVariable(bv, callTf, oldVarsAssignment, procBeforeCall, procAfterCall, true, false);
				if (isInterfaceVariable) {
					// keep variable
				} else {
					outVarsToRemove.add(bv);
				}
				
			}
			callAndBeforeTF = TransFormulaBuilder.constructCopy(composition, Collections.emptySet(), outVarsToRemove, mgdScript);
			// now we havoc all oldvars that are modifiable by the caller 
			// but not modifiable y the callee
			final Set<IProgramVar> modifiableByCaller = modGlobVarManager.getOldVarsAssignment(procBeforeCall).getAssignedVars();
			for (final IProgramVar oldVar : modifiableByCaller) {
				if (!oldVarsAssignment.getAssignedVars().contains(oldVar)) {
					callAndBeforeTF.mOutVars.put(oldVar, mgdScript.constructFreshCopy(oldVar.getTermVariable()));
				}
			}
			
			// we have to havoc all local variables of the caller
			final Map<String, LocalBoogieVar> locals = symbolTable.getLocals(procBeforeCall);
			for (final Entry<String, LocalBoogieVar> entry : locals.entrySet()) {
				callAndBeforeTF.mOutVars.put(entry.getValue(), mgdScript.constructFreshCopy(entry.getValue().getTermVariable()));
		
			}
			
//			// now we havoc all oldvars that are not modified by the callee
//			// TODO: Rename the ones that are not modified by the caller
//			for (final Entry<String, IProgramVar> entry : symbolTable.getOldVars().entrySet()) {
//				if (!oldVarsAssignment.getAssignedVars().contains(entry.getValue())) {
//					callAndBeforeTF.mOutVars.put(entry.getValue(), mgdScript.constructFreshCopy(entry.getValue().getTermVariable()));
//				}
//			}
		}

		final UnmodifiableTransFormula globalVarAssignAndAfterTF;
		{
			final List<UnmodifiableTransFormula> oldAssignAndAfterList = new ArrayList<UnmodifiableTransFormula>(Arrays.asList(afterCall));
			oldAssignAndAfterList.add(0, globalVarsAssignment);
			final UnmodifiableTransFormula[] globalVarAssignAndAfterArray = oldAssignAndAfterList.toArray(new UnmodifiableTransFormula[0]);
			final UnmodifiableTransFormula composition = sequentialComposition(logger, services, mgdScript, simplify, extPqe, transformToCNF,
					xnfConversionTechnique, simplificationTechnique, globalVarAssignAndAfterArray);

			// remove inVars that relate to scope of callee
			final List<IProgramVar> inVarsToRemove = new ArrayList<IProgramVar>();
			for (final IProgramVar bv : composition.getInVars().keySet()) {
				final boolean isInterfaceVariable = isInterfaceVariable(bv, callTf, oldVarsAssignment, procBeforeCall, procAfterCall, false, true);
				if (isInterfaceVariable) {
					// keep variable
				} else {
					inVarsToRemove.add(bv);
				}
				
			}
			
			
//			// remove inVars that relate to scope of callee
//			// - local vars that are no inParams of callee
//			// - oldVars of variables that can be modified by callee
//			final List<IProgramVar> inVarsToRemove = new ArrayList<IProgramVar>();
//			for (final IProgramVar bv : composition.getInVars().keySet()) {
//				if (bv.isGlobal()) {
//					if (bv.isOldvar() && oldVarsAssignment.getOutVars().containsKey(bv)) {
//						inVarsToRemove.add(bv);
//					}
//				} else {
//					if (!callTf.getOutVars().containsKey(bv)) {
//						// bv is local but not inParam of called procedure
//						inVarsToRemove.add(bv);
//					}
//				}
//			}
			


			
//			for (final IProgramVar bv : composition.getOutVars().keySet()) {
//				if (bv instanceof IProgramOldVar) {
//					final IProgramNonOldVar nonOld = ((IProgramOldVar) bv).getNonOldVar();
//					if (modifiableGlobalsOfEndProcedure.contains(nonOld)) {
//						// do nothing - bv should be outVar
//					} else {
//						outVarsToRemove.add(bv);
//					}
//				}
//			}
			globalVarAssignAndAfterTF = TransFormulaBuilder.constructCopy(composition, inVarsToRemove, Collections.emptySet(), mgdScript);
		}
		
		

		final UnmodifiableTransFormula tmpresult = sequentialComposition(logger, services, mgdScript, simplify, 
				extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique,
				callAndBeforeTF, globalVarAssignAndAfterTF);
		
		final UnmodifiableTransFormula result;
		if (procAfterCall.equals(procAtEnd)) {
			result = tmpresult;
		} else {
			final List<IProgramVar> outVarsToRemove = new ArrayList<IProgramVar>();
			// remove inparams of callee that are still in the outvars
			for (final IProgramVar pv : tmpresult.getOutVars().keySet()) {
				if (callTf.getAssignedVars().contains(pv)) {
					// pv is inparam, we have to remove it
					outVarsToRemove.add(pv);
				}
			}
			if (outVarsToRemove.isEmpty()) {
				// nothing to remove
				result = tmpresult;
			} else {
				result = TransFormulaBuilder.constructCopy(tmpresult, Collections.emptySet(), outVarsToRemove, mgdScript);
			}
		}
		

		
//		if (recursiveProcedureChange) {
//			// we have to havoc all local variables that do not yet occur
//			final Map<String, LocalBoogieVar> locals = symbolTable.getLocals(procAtEnd);
//			for (final Entry<String, LocalBoogieVar> entry : locals.entrySet()) {
//				if (!result.getInVars().containsKey(entry.getValue()) &&
//						!result.getOutVars().containsKey(entry.getValue())) {
//					result.mOutVars.put(entry.getValue(), mgdScript.constructFreshCopy(entry.getValue().getTermVariable()));
//				}
//				
//			}
//		}
		assert !result.getBranchEncoders().isEmpty() || predicateBasedResultCheck(services, mgdScript, 
				xnfConversionTechnique, simplificationTechnique, 
				beforeCall,
				callTf, oldVarsAssignment, globalVarsAssignment, afterCall, result, symbolTable, modifiableGlobalsOfEndProcedure) : 
					"sequentialCompositionWithPendingCall - incorrect result";
		return result;
	}


	/**
	 * Check if {@link IProgramVar} is variable at the interface between 
	 * caller and callee. This is used for interprocedural sequential
	 * compositions with pending calls.
	 * We say that a variable is an interface variable if it is either
	 * - an inparam of the callee (local variable)
	 * - an oldvar that is in the callee's set of modifiable variables
	 * - an non-old global variable that is not in the callee's set of modifiable
	 * variables.
	 */
	private static boolean isInterfaceVariable(final IProgramVar bv, 
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula oldVarsAssignment, 
			final String procBeforeCall, final String procAfterCall,
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
	
	
	private static boolean predicateBasedResultCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique,
			final List<UnmodifiableTransFormula> beforeCall,
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula oldVarsAssignment,
			final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula afterCallTf,
			final UnmodifiableTransFormula result, 
			final Boogie2SmtSymbolTable symbolTable, final Set<IProgramVar> modifiableGlobals) {
		assert result.getBranchEncoders().isEmpty() : "result check not applicable with branch encoders";
		final PredicateTransformer pt = new PredicateTransformer(services, mgdScript, simplificationTechnique, xnfConversionTechnique);
		final BasicPredicateFactory bpf = new BasicPredicateFactory(services, mgdScript, symbolTable, simplificationTechnique, xnfConversionTechnique);
		final IPredicate truePredicate = bpf.newPredicate(mgdScript.getScript().term("true"));
		Term resultComposition = pt.strongestPostcondition(truePredicate, result);
		resultComposition = new QuantifierPusher(mgdScript, services).transform(resultComposition);
		final IPredicate resultCompositionPredicate = bpf.newPredicate(resultComposition);
		IPredicate beforeCallPredicate = truePredicate;
		for (final UnmodifiableTransFormula tf : beforeCall) {
			final Term tmp = pt.strongestPostcondition(beforeCallPredicate, tf);
			beforeCallPredicate = bpf.newPredicate(tmp);
		}
		final Term afterCallTerm = pt.strongestPostconditionCall(beforeCallPredicate, callTf, globalVarsAssignment, oldVarsAssignment, modifiableGlobals);
		final IPredicate afterCallPredicate = bpf.newPredicate(afterCallTerm);
		Term endTerm = pt.strongestPostcondition(afterCallPredicate, afterCallTf);
		endTerm = new QuantifierPusher(mgdScript, services).transform(endTerm);
		final IPredicate endPredicate = bpf.newPredicate(endTerm);
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final Validity check1 = mic.checkImplication(endPredicate, false, resultCompositionPredicate, false);
		final Validity check2 = mic.checkImplication(resultCompositionPredicate, false, endPredicate, false);
		assert check1 != Validity.UNKNOWN && check2 != Validity.UNKNOWN : "SMT solver too weak for correctness check";
		assert check1 == Validity.VALID && check2 == Validity.VALID : "sequentialCompositionWithPendingCall - incorrect result";
		return check1 == Validity.VALID && check2 == Validity.VALID;
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
	 * @param symbolTable 
	 * @param modifiableGlobalsOfCallee 
	 */
	public static UnmodifiableTransFormula sequentialCompositionWithCallAndReturn(final ManagedScript mgdScript, final boolean simplify,
			final boolean extPqe, final boolean transformToCNF, final UnmodifiableTransFormula callTf, 
			final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment,
			final UnmodifiableTransFormula procedureTf, final UnmodifiableTransFormula returnTf, final ILogger logger, 
			final IUltimateServiceProvider services, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique, 
			final Boogie2SmtSymbolTable symbolTable, final Set<IProgramVar> modifiableGlobalsOfCallee) {
		logger.debug("sequential composition (call/return) with" + (simplify ? "" : "out") + " formula simplification");
		final UnmodifiableTransFormula composition = sequentialComposition(logger, services, mgdScript, 
				simplify, extPqe, transformToCNF, xnfConversionTechnique, simplificationTechnique,
				callTf, oldVarsAssignment, globalVarsAssignment, procedureTf, returnTf);
		final List<IProgramVar> inVarsToRemove = new ArrayList<IProgramVar>();
		for (final IProgramVar bv : composition.getInVars().keySet()) {
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

		final List<IProgramVar> outVarsToRemove = new ArrayList<IProgramVar>();
		for (final IProgramVar bv : composition.getOutVars().keySet()) {
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
		final UnmodifiableTransFormula result = TransFormulaBuilder.constructCopy(composition, inVarsToRemove, outVarsToRemove, mgdScript);
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
		assert !result.getBranchEncoders().isEmpty() || predicateBasedResultCheck(services, mgdScript, 
				xnfConversionTechnique, simplificationTechnique, 
				callTf, oldVarsAssignment, globalVarsAssignment, procedureTf, returnTf, result, symbolTable, modifiableGlobalsOfCallee) : 
					"sequentialCompositionWithCallAndReturn - incorrect result";
		return result;
	}
	
	
	private static boolean predicateBasedResultCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique,
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula oldVarsAssignment,
			final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula procedureTf,
			final UnmodifiableTransFormula returnTf, final UnmodifiableTransFormula result, 
			final Boogie2SmtSymbolTable symbolTable, final Set<IProgramVar> modifiableGlobals) {
		assert result.getBranchEncoders().isEmpty() : "result check not applicable with branch encoders";
		final PredicateTransformer pt = new PredicateTransformer(services, mgdScript, simplificationTechnique, xnfConversionTechnique);
		final BasicPredicateFactory bpf = new BasicPredicateFactory(services, mgdScript, symbolTable, simplificationTechnique, xnfConversionTechnique);
		final IPredicate truePredicate = bpf.newPredicate(mgdScript.getScript().term("true"));
		Term resultComposition = pt.strongestPostcondition(truePredicate, result);
		resultComposition = new QuantifierPusher(mgdScript, services).transform(resultComposition);
		final IPredicate resultCompositionPredicate = bpf.newPredicate(resultComposition); 
		final Term afterCallTerm = pt.strongestPostconditionCall(truePredicate, callTf, globalVarsAssignment, oldVarsAssignment, modifiableGlobals);
		final IPredicate afterCallPredicate = bpf.newPredicate(afterCallTerm);
		final Term beforeReturnTerm = pt.strongestPostcondition(afterCallPredicate, procedureTf);
		final IPredicate beforeReturnPredicate = bpf.newPredicate(beforeReturnTerm);
		Term afterReturnTerm = pt.strongestPostcondition(beforeReturnPredicate, truePredicate, returnTf, callTf, globalVarsAssignment, oldVarsAssignment);
		afterReturnTerm = new QuantifierPusher(mgdScript, services).transform(afterReturnTerm);
		final IPredicate afterReturnPredicate = bpf.newPredicate(afterReturnTerm);
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final Validity check1 = mic.checkImplication(afterReturnPredicate, false, resultCompositionPredicate, false);
		final Validity check2 = mic.checkImplication(resultCompositionPredicate, false, afterReturnPredicate, false);
		assert check1 != Validity.UNKNOWN && check2 != Validity.UNKNOWN : "SMT solver too weak for correctness check";
		assert check1 == Validity.VALID && check2 == Validity.VALID : "sequentialCompositionWithCallAndReturn - incorrect result";
		return check1 == Validity.VALID && check2 == Validity.VALID;
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
	
}
