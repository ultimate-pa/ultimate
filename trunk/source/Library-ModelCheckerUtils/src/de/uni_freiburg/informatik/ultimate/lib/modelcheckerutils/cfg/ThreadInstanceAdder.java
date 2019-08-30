/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier.ProcedureErrorType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Adds thread instances to an ICFG
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ThreadInstanceAdder {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public ThreadInstanceAdder(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
	}

	// public BoogieIcfgContainer connectThreadInstances(final BoogieIcfgContainer
	// icfg,
	public IIcfg<IcfgLocation> connectThreadInstances(final IIcfg<IcfgLocation> icfg,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinCurrentThreads,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> threadInstanceMap2,
			final BlockEncodingBacktranslator backtranslator, final boolean addThreadInUseViolationEdges) {
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fct : forkCurrentThreads) {
			final ThreadInstance ti = threadInstanceMap2.get(fct);

			addForkOtherThreadTransition(fct, ti.getErrorLocation(), ti.getIdVars(), ti.getInUseVar(), icfg,
					ti.getThreadInstanceName(), backtranslator, addThreadInUseViolationEdges);
		}

		// For each implemented procedure, add a JoinOtherThreadTransition from the exit
		// location of the procedure
		// to all target locations of each JoinCurrentThreadEdge
		for (final IIcfgJoinTransitionThreadCurrent<IcfgLocation> jot : joinCurrentThreads) {
			// if (mBoogieDeclarations.getProcImplementation().containsKey(procName)) {
			for (final ThreadInstance ti : threadInstanceMap2.values()) {
				final boolean threadIdCompatible = isThreadIdCompatible(ti.getIdVars(),
						jot.getJoinSmtArguments().getThreadIdArguments().getTerms());
				final boolean returnValueCompatible =
						isReturnValueCompatible(jot.getJoinSmtArguments().getAssignmentLhs(),
								icfg.getCfgSmtToolkit().getOutParams().get(ti.getThreadInstanceName()));
				if (threadIdCompatible && returnValueCompatible) {
					addJoinOtherThreadTransition(jot, ti.getThreadInstanceName(), ti.getIdVars(), ti.getInUseVar(),
							icfg, backtranslator, addThreadInUseViolationEdges);
				}
			}

			// }
		}
		return icfg;
	}

	/**
	 * @return true iff
	 *         <ul>
	 *         <li>assignmentLhs is empty (which means that we do not care about the return value of this thread) and
	 *         <li>both list have same length and
	 *         <li>all Sorts are pairwise equivalent
	 *         </ul>
	 */
	private static boolean isReturnValueCompatible(final List<IProgramVar> assignmentLhs,
			final List<ILocalProgramVar> outParams) {
		if (assignmentLhs.isEmpty()) {
			return true;
		}
		if (assignmentLhs.size() != outParams.size()) {
			return false;
		}
		for (int i = 0; i < assignmentLhs.size(); i++) {
			if (!assignmentLhs.get(i).getTerm().getSort().equals(outParams.get(i).getTerm().getSort())) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @return true iff
	 *         <ul>
	 *         <li>both arrays have same length and
	 *         <li>all Sorts are pairwise equivalent
	 *         </ul>
	 */
	private static boolean isThreadIdCompatible(final IProgramNonOldVar[] idVars, final Term[] terms) {
		if (idVars.length != terms.length) {
			return false;
		}
		for (int i = 0; i < idVars.length; i++) {
			if (!idVars[i].getTerm().getSort().equals(terms[i].getSort())) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Add ForkOtherThreadEdge from the ForkCurrentThreadEdge source to the entry location of the forked procedure.
	 *
	 * @param backtranslator
	 * @param addThreadInUseViolationEdges
	 * @param string
	 *
	 * @param edge
	 *            that points to the next step in the current thread.
	 */
	private void addForkOtherThreadTransition(final IIcfgForkTransitionThreadCurrent<IcfgLocation> fct,
			final IcfgLocation errorNode, final IProgramNonOldVar[] threadIdVars,
			final IProgramNonOldVar threadInUseVar, final IIcfg<? extends IcfgLocation> icfg,
			final String threadInstanceName, final BlockEncodingBacktranslator backtranslator,
			final boolean addThreadInUseViolationEdges) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags

		assert icfg.getProcedureEntryNodes().containsKey(threadInstanceName) : "Thread instance " + threadInstanceName
				+ " missing.";

		// Add fork transition from callerNode to procedures entry node.
		final IcfgLocation callerNode = fct.getSource();
		final IcfgLocation calleeEntryLoc = icfg.getProcedureEntryNodes().get(threadInstanceName);

		final ForkSmtArguments fsa = fct.getForkSmtArguments();

		final IcfgEdgeFactory ef = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		final UnmodifiableTransFormula forkTransformula;
		{
			final List<UnmodifiableTransFormula> conjuncts;
			final UnmodifiableTransFormula parameterAssignment = fsa.constructInVarsAssignment(
					icfg.getCfgSmtToolkit().getSymbolTable(), icfg.getCfgSmtToolkit().getManagedScript(),
					icfg.getCfgSmtToolkit().getInParams().get(threadInstanceName));
			final UnmodifiableTransFormula threadIdAssignment = fsa.constructThreadIdAssignment(
					icfg.getCfgSmtToolkit().getSymbolTable(), icfg.getCfgSmtToolkit().getManagedScript(),
					Arrays.asList(threadIdVars));
			if (addThreadInUseViolationEdges) {
				final UnmodifiableTransFormula threadInUseAssignment = constructForkInUseAssignment(threadInUseVar,
						icfg.getCfgSmtToolkit().getManagedScript());
				conjuncts = Arrays.asList(parameterAssignment, threadIdAssignment, threadInUseAssignment);
			} else {
				conjuncts = Arrays.asList(parameterAssignment, threadIdAssignment);
			}
			forkTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
					conjuncts);
		}

		final IcfgForkThreadOtherTransition forkThreadOther =
				ef.createForkThreadOtherTransition(callerNode, calleeEntryLoc, null, forkTransformula, fct);
		callerNode.addOutgoing(forkThreadOther);
		calleeEntryLoc.addIncoming(forkThreadOther);

		// hack to get the original fork
		final IIcfgTransition<IcfgLocation> originalEdge = getOriginalEdge(fct, backtranslator);
		backtranslator.mapEdges(forkThreadOther, originalEdge);
		if (addThreadInUseViolationEdges) {
			// Add the assume statement for the error location and construct the
			final UnmodifiableTransFormula forkErrorTransFormula =
					constructThreadInUseViolationAssumption(threadInUseVar, icfg.getCfgSmtToolkit().getManagedScript());
			final IcfgInternalTransition errorTransition =
					ef.createInternalTransition(callerNode, errorNode, null, forkErrorTransFormula);
			callerNode.addOutgoing(errorTransition);
			errorNode.addIncoming(errorTransition);
		}

		// TODO Matthias 2018-09-15: Set overapproximations for both edges
		final Map<String, ILocation> overapproximations = new HashMap<>();
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(fct);
		}
	}

	private IIcfgTransition<IcfgLocation> getOriginalEdge(final IIcfgTransition<IcfgLocation> newEdge,
			final BlockEncodingBacktranslator backtranslator) {
		final List<IIcfgTransition<IcfgLocation>> transRes =
				backtranslator.translateTrace(Collections.singletonList(newEdge));
		if (transRes.size() != 1) {
			throw new IllegalStateException();
		}
		return transRes.get(0);
	}

	/**
	 * Add JoinOtherThreadEdge from
	 *
	 * @param backtranslator
	 *
	 * @param edge
	 */
	private void addJoinOtherThreadTransition(final IIcfgJoinTransitionThreadCurrent<IcfgLocation> jot,
			final String threadInstanceName, final IProgramNonOldVar[] threadIdVars,
			final IProgramNonOldVar threadInUseVar, final IIcfg<? extends IcfgLocation> icfg,
			final BlockEncodingBacktranslator backtranslator,
			final boolean addThreadInUseViolationEdges) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags
		final IcfgLocation exitNode = icfg.getProcedureExitNodes().get(threadInstanceName);
		final IcfgLocation callerNode = jot.getTarget();

		final JoinSmtArguments jsa = jot.getJoinSmtArguments();

		final IcfgEdgeFactory ef = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		final UnmodifiableTransFormula joinTransformula;
		{

			final UnmodifiableTransFormula threadIdAssumption =
					jsa.constructThreadIdAssumption(icfg.getCfgSmtToolkit().getSymbolTable(),
							icfg.getCfgSmtToolkit().getManagedScript(), Arrays.asList(threadIdVars));

			final UnmodifiableTransFormula resultAssignment;
			if (jsa.getAssignmentLhs().isEmpty()) {
				// no result assignment
				resultAssignment =
						TransFormulaBuilder.getTrivialTransFormula(icfg.getCfgSmtToolkit().getManagedScript());
			} else {
				resultAssignment = jsa.constructResultAssignment(icfg.getCfgSmtToolkit().getManagedScript(),
						icfg.getCfgSmtToolkit().getOutParams().get(threadInstanceName));
			}
			final List<UnmodifiableTransFormula> conjuncts;
			if (addThreadInUseViolationEdges) {
				final UnmodifiableTransFormula threadInUseAssignment =
						constructThreadNotInUseAssingment(threadInUseVar, icfg.getCfgSmtToolkit().getManagedScript());
				conjuncts = Arrays.asList(resultAssignment, threadIdAssumption, threadInUseAssignment);
			} else {
				conjuncts = Arrays.asList(resultAssignment, threadIdAssumption);
			}
			joinTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
					conjuncts);
		}

		final IcfgJoinThreadOtherTransition joinThreadOther =
				ef.createJoinThreadOtherTransition(exitNode, callerNode, null, joinTransformula, jot);
		exitNode.addOutgoing(joinThreadOther);
		callerNode.addIncoming(joinThreadOther);

		// hack to get the original fork
		final IIcfgTransition<IcfgLocation> originalEdge = getOriginalEdge(jot, backtranslator);
		backtranslator.mapEdges(joinThreadOther, originalEdge);

		final Map<String, ILocation> overapproximations = new HashMap<>();
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(jot);
		}
	}

	/**
	 * TODO Concurrent Boogie:
	 *
	 * @param mgdScript
	 */
	private static UnmodifiableTransFormula constructForkInUseAssignment(final IProgramNonOldVar threadInUseVar,
			final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> outVars =
				Collections.singletonMap(threadInUseVar, threadInUseVar.getTermVariable());
		final TransFormulaBuilder tfb = new TransFormulaBuilder(Collections.emptyMap(), outVars, true,
				Collections.emptySet(), true, Collections.emptySet(), true);
		tfb.setFormula(threadInUseVar.getTermVariable());
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * TODO Concurrent Boogie:
	 *
	 * @param mgdScript
	 * @return A {@link TransFormula} that represents the assume statement {@code var == true}.
	 */
	private static UnmodifiableTransFormula constructThreadInUseViolationAssumption(
			final IProgramNonOldVar threadInUseVar, final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> inVars =
				Collections.singletonMap(threadInUseVar, threadInUseVar.getTermVariable());
		final Map<IProgramVar, TermVariable> outVars = inVars;
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, Collections.emptySet(), true,
				Collections.emptySet(), true);
		tfb.setFormula(threadInUseVar.getTermVariable());
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * TODO Concurrent Boogie:
	 *
	 * @param mgdScript
	 * @return A {@link TransFormula} that represents the assignment statement {@code var := false}.
	 */
	private static UnmodifiableTransFormula constructThreadNotInUseAssingment(final IProgramNonOldVar threadInUseVar,
			final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> outVars =
				Collections.singletonMap(threadInUseVar, threadInUseVar.getTermVariable());
		final TransFormulaBuilder tfb = new TransFormulaBuilder(Collections.emptyMap(), outVars, true,
				Collections.emptySet(), true, Collections.emptySet(), true);
		tfb.setFormula(SmtUtils.not(mgdScript.getScript(), threadInUseVar.getTermVariable()));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * Construct the {@link ThreadInstance} objects but does not yet add
	 * {@link IProgramVar}s and error locations to the {@link IIcfg}.
	 */
	public Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> constructThreadInstances(
			final IIcfg<? extends IcfgLocation> icfg,
			final List<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forkCurrentThreads,
			final boolean addThreadInUseViolationVariablesAndErrorLocation) {
		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> result = new HashMap<>();
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		int i = 0;
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : forkCurrentThreads) {
			final String procedureName = fork.getNameOfForkedProcedure();
			final String threadInstanceId = generateThreadInstanceId(i, procedureName);
			final BoogieNonOldVar threadInUseVar;
			if (addThreadInUseViolationVariablesAndErrorLocation) {
				threadInUseVar = constructThreadInUseVariable(threadInstanceId, mgdScript);
			} else {
				threadInUseVar = null;
			}
			final BoogieNonOldVar[] threadIdVars = constructThreadIdVariable(threadInstanceId, mgdScript,
					fork.getForkSmtArguments().getThreadIdArguments().getTerms());

			final IcfgLocation errorLocation;
			if (addThreadInUseViolationVariablesAndErrorLocation) {
				final DebugIdentifier debugIdentifier = new ProcedureErrorDebugIdentifier(fork.getPrecedingProcedure(),
						i, ProcedureErrorType.INUSE_VIOLATION);
				errorLocation = new IcfgLocation(debugIdentifier, fork.getPrecedingProcedure());
				ModelUtils.copyAnnotations(fork, errorLocation);
				// 2018-09-28 Matthias: Questionable if this is an assert. Maybe we should
				// introduce an InUseViolation.
				final Check check = new Check(Spec.ASSERT);
				check.annotate(errorLocation);
			} else {
				errorLocation = null;
			}
			final ThreadInstance ti =
					new ThreadInstance(threadInstanceId, procedureName, threadIdVars, threadInUseVar, errorLocation);
			result.put(fork, ti);
			i++;
		}
		return result;
	}

	private String generateThreadInstanceId(final int i, final String procedureName) {
		return "Thread" + i + "_" + procedureName;
	}

	private static BoogieNonOldVar constructThreadInUseVariable(final String threadInstanceId,
			final ManagedScript mgdScript) {
		final Sort booleanSort = SmtSortUtils.getBoolSort(mgdScript);
		final BoogieNonOldVar threadInUseVar =
				constructThreadAuxiliaryVariable(threadInstanceId + "_inUse", booleanSort, mgdScript);
		return threadInUseVar;
	}

	private static BoogieNonOldVar[] constructThreadIdVariable(final String threadInstanceId,
			final ManagedScript mgdScript, final Term[] threadIdArguments) {
		final BoogieNonOldVar[] threadIdVars = new BoogieNonOldVar[threadIdArguments.length];
		int i = 0;
		for (final Term forkId : threadIdArguments) {
			threadIdVars[i] =
					constructThreadAuxiliaryVariable(threadInstanceId + "_thidvar" + i, forkId.getSort(), mgdScript);
			i++;
		}
		return threadIdVars;
	}

	/**
	 * TODO Concurrent Boogie:
	 */
	private static BoogieNonOldVar constructThreadAuxiliaryVariable(final String id, final Sort sort,
			final ManagedScript mgdScript) {
		mgdScript.lock(id);
		final BoogieNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(id, sort, mgdScript, id);
		mgdScript.unlock(id);
		return var;
	}

	CfgSmtToolkit constructNewToolkit(final CfgSmtToolkit cfgSmtToolkit,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, ThreadInstance> threadInstanceMap,
			final Collection<IIcfgJoinTransitionThreadCurrent<IcfgLocation>> joinTransitions,
			final boolean addThreadInUseViolationVariables) {
		final DefaultIcfgSymbolTable newSymbolTable =
				new DefaultIcfgSymbolTable(cfgSmtToolkit.getSymbolTable(), cfgSmtToolkit.getProcedures());
		final HashRelation<String, IProgramNonOldVar> proc2Globals =
				new HashRelation<>(cfgSmtToolkit.getModifiableGlobalsTable().getProcToGlobals());
		for (final ThreadInstance ti : threadInstanceMap.values()) {
			if (addThreadInUseViolationVariables) {
				addVar(ti.getInUseVar(), newSymbolTable, proc2Globals, cfgSmtToolkit.getProcedures());
			}
			for (final IProgramNonOldVar idVar : ti.getIdVars()) {
				addVar(idVar, newSymbolTable, proc2Globals, cfgSmtToolkit.getProcedures());
			}
		}
		newSymbolTable.finishConstruction();
		final ConcurrencyInformation concurrencyInformation = new ConcurrencyInformation(threadInstanceMap,
				joinTransitions);
		return new CfgSmtToolkit(new ModifiableGlobalsTable(proc2Globals), cfgSmtToolkit.getManagedScript(),
				newSymbolTable, cfgSmtToolkit.getProcedures(), cfgSmtToolkit.getInParams(),
				cfgSmtToolkit.getOutParams(), cfgSmtToolkit.getIcfgEdgeFactory(), concurrencyInformation,
				cfgSmtToolkit.getSmtFunctionsAndAxioms());
	}

	private static void addVar(final IProgramNonOldVar var, final DefaultIcfgSymbolTable newSymbolTable,
			final HashRelation<String, IProgramNonOldVar> proc2Globals, final Set<String> allProcedures) {
		newSymbolTable.add(var);
		for (final String proc : allProcedures) {
			proc2Globals.addPair(proc, var);
		}
	}

	static void addInUseErrorLocations(final BasicIcfg<IcfgLocation> result,
			final Collection<ThreadInstance> threadInstances) {
		for (final ThreadInstance ti : threadInstances) {
			result.addLocation(ti.getErrorLocation(), false, true, false, false, false);
		}

	}

}
