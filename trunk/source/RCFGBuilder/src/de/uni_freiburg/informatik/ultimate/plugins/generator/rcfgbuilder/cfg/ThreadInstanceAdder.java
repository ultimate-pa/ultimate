/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitzke (lars.nitzke@outlook.com)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.ProcedureErrorDebugIdentifier.ProcedureErrorType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
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
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	// public BoogieIcfgContainer connectThreadInstances(final BoogieIcfgContainer
	// icfg,
	public IIcfg<? extends IcfgLocation> connectThreadInstances(final IIcfg<? extends IcfgLocation> icfg,
			final List<IIcfgForkTransitionThreadCurrent> forkCurrentThreads,
			final List<IIcfgJoinTransitionThreadCurrent> joinCurrentThreads,
			final Collection<String> forkedProcedureNames, final Map<String, ThreadInstance> threadInstanceMap) {
		for (final IIcfgForkTransitionThreadCurrent fct : forkCurrentThreads) {
			final ThreadInstance ti = threadInstanceMap.get(fct.getNameOfForkedProcedure());

			addForkOtherThreadTransition(fct, ti.getErrorLocation(), ti.getIdVars(), ti.getInUseVar(), icfg);
		}

		// For each implemented procedure, add a JoinOtherThreadTransition from the exit
		// location of the procedure
		// to all target locations of each JoinCurrentThreadEdge
		for (final IIcfgJoinTransitionThreadCurrent jot : joinCurrentThreads) {
			// if (mBoogieDeclarations.getProcImplementation().containsKey(procName)) {
			for (final String procName : forkedProcedureNames) {
				final ThreadInstance ti = threadInstanceMap.get(procName);
				final boolean threadIdCompatible = isThreadIdCompatible(ti.getIdVars(),
						jot.getJoinSmtArguments().getThreadIdArguments().getTerms());
				final boolean returnValueCompatible = isReturnValueCompatible(
						jot.getJoinSmtArguments().getAssignmentLhs(),
						icfg.getCfgSmtToolkit().getOutParams().get(procName));
				if (threadIdCompatible && returnValueCompatible) {
					addJoinOtherThreadTransition(jot, procName, ti.getIdVars(), ti.getInUseVar(), icfg);
				}
			}
			// }
		}
		return icfg;
	}

	/**
	 * @return true iff
	 *         <ul>
	 *         <li>assignmentLhs is empty (which means that we do not care about the
	 *         return value of this thread) and
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
		} else {
			for (int i = 0; i < assignmentLhs.size(); i++) {
				if (!assignmentLhs.get(i).getTerm().getSort().equals(outParams.get(i).getTerm().getSort())) {
					return false;
				}
			}
			return true;
		}
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
		} else {
			for (int i = 0; i < idVars.length; i++) {
				if (!idVars[i].getTerm().getSort().equals(terms[i].getSort())) {
					return false;
				}
			}
			return true;
		}
	}

	/**
	 * Add ForkOtherThreadEdge from the ForkCurrentThreadEdge source to the entry
	 * location of the forked procedure.
	 *
	 * @param edge
	 *            that points to the next step in the current thread.
	 */
	private void addForkOtherThreadTransition(final IIcfgForkTransitionThreadCurrent fct, final IcfgLocation errorNode,
			final IProgramNonOldVar[] threadIdVars, final IProgramNonOldVar threadInUseVar,
			final IIcfg<? extends IcfgLocation> icfg) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags

		final String forkedProcedure = fct.getNameOfForkedProcedure();
		assert icfg.getProcedureEntryNodes().containsKey(forkedProcedure) : "Source code contains" + " fork of "
				+ forkedProcedure + " but no such procedure.";

		// Add fork transition from callerNode to procedures entry node.
		final IcfgLocation callerNode = fct.getSource();
		final IcfgLocation calleeEntryLoc = icfg.getProcedureEntryNodes().get(forkedProcedure);

		final ForkSmtArguments fsa = fct.getForkSmtArguments();

		final IcfgEdgeFactory ef = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		final UnmodifiableTransFormula forkTransformula;
		{
			final UnmodifiableTransFormula parameterAssignment = fsa.constructInVarsAssignment(
					icfg.getCfgSmtToolkit().getSymbolTable(), icfg.getCfgSmtToolkit().getManagedScript(),
					icfg.getCfgSmtToolkit().getInParams().get(forkedProcedure));
			final UnmodifiableTransFormula threadIdAssignment = fsa.constructThreadIdAssignment(
					icfg.getCfgSmtToolkit().getSymbolTable(), icfg.getCfgSmtToolkit().getManagedScript(),
					Arrays.asList(threadIdVars));
			final UnmodifiableTransFormula threadInUseAssignment = constructForkInUseAssignment(threadInUseVar,
					icfg.getCfgSmtToolkit().getManagedScript());
			forkTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
					Arrays.asList(parameterAssignment, threadIdAssignment, threadInUseAssignment));
		}

		final IcfgForkThreadOtherTransition forkThreadOther = ef.createForkThreadOtherTransition(callerNode,
				calleeEntryLoc, null, forkTransformula, fct);
		callerNode.addOutgoing(forkThreadOther);
		calleeEntryLoc.addIncoming(forkThreadOther);

		// Add the assume statement for the error location and construct the
		final UnmodifiableTransFormula forkErrorTransFormula = constructThreadInUseViolationAssumption(threadInUseVar,
				icfg.getCfgSmtToolkit().getManagedScript());
		final IcfgInternalTransition errorTransition = ef.createInternalTransition(callerNode, errorNode, null,
				forkErrorTransFormula);
		callerNode.addOutgoing(errorTransition);
		errorNode.addIncoming(errorTransition);

		// TODO Matthias 2018-09-15: Set overapproximations for both edges
		final Map<String, ILocation> overapproximations = new HashMap<>();
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(fct);
		}
	}

	/**
	 * Add JoinOtherThreadEdge from
	 *
	 * @param edge
	 */
	private void addJoinOtherThreadTransition(final IIcfgJoinTransitionThreadCurrent jot, final String procName,
			final IProgramNonOldVar[] threadIdVars, final IProgramNonOldVar threadInUseVar,
			final IIcfg<? extends IcfgLocation> icfg) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags
		final IcfgLocation exitNode = icfg.getProcedureExitNodes().get(procName);
		final IcfgLocation callerNode = jot.getTarget();

		final JoinSmtArguments jsa = jot.getJoinSmtArguments();

		final IcfgEdgeFactory ef = icfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		final UnmodifiableTransFormula joinTransformula;
		{

			final UnmodifiableTransFormula threadIdAssumption = jsa.constructThreadIdAssumption(
					icfg.getCfgSmtToolkit().getSymbolTable(), icfg.getCfgSmtToolkit().getManagedScript(),
					Arrays.asList(threadIdVars));

			final UnmodifiableTransFormula parameterAssignment = jsa.constructResultAssignment(
					icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getOutParams().get(procName));

			final UnmodifiableTransFormula threadInUseAssignment = constructThreadNotInUseAssingment(threadInUseVar,
					icfg.getCfgSmtToolkit().getManagedScript());
			joinTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
					icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
					Arrays.asList(parameterAssignment, threadIdAssumption, threadInUseAssignment));
		}

		final IcfgJoinThreadOtherTransition joinThreadOther = ef.createJoinThreadOtherTransition(exitNode, callerNode,
				null, joinTransformula, jot);
		exitNode.addOutgoing(joinThreadOther);
		callerNode.addIncoming(joinThreadOther);

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
		final Map<IProgramVar, TermVariable> outVars = Collections.singletonMap(threadInUseVar,
				threadInUseVar.getTermVariable());
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
	 * @return A {@link TransFormula} that represents the assume statement
	 *         {@code var == true}.
	 */
	private UnmodifiableTransFormula constructThreadInUseViolationAssumption(final IProgramNonOldVar threadInUseVar,
			final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> inVars = Collections.singletonMap(threadInUseVar,
				threadInUseVar.getTermVariable());
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
	 * @return A {@link TransFormula} that represents the assignment statement
	 *         {@code var := false}.
	 */
	private static UnmodifiableTransFormula constructThreadNotInUseAssingment(final IProgramNonOldVar threadInUseVar,
			final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> outVars = Collections.singletonMap(threadInUseVar,
				threadInUseVar.getTermVariable());
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
	public Map<String, ThreadInstance> constructTreadInstances(final IIcfg<? extends IcfgLocation> icfg,
			final List<IIcfgForkTransitionThreadCurrent> forkCurrentThreads) {
		final Map<String, ThreadInstance> result = new HashMap<>();
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		int i = 0;
		for (final IIcfgForkTransitionThreadCurrent fork : forkCurrentThreads) {
			final String procedureName = fork.getNameOfForkedProcedure();
			final String threadInstanceId = procedureName + " lol";
			if (result.containsKey(procedureName)) {
				// workaround
				continue;
			}
			final BoogieNonOldVar threadInUseVar = constructThreadInUseVariable(threadInstanceId, mgdScript);
			final BoogieNonOldVar[] threadIdVars = constructThreadIdVariable(threadInstanceId, mgdScript,
					fork.getForkSmtArguments().getThreadIdArguments().getTerms());

			final DebugIdentifier debugIdentifier = new ProcedureErrorDebugIdentifier(fork.getPrecedingProcedure(), i,
					ProcedureErrorType.INUSE_VIOLATION);
			final IcfgLocation errorLocation = new IcfgLocation(debugIdentifier, fork.getPrecedingProcedure());
			ModelUtils.copyAnnotations(fork, errorLocation);
			// 2018-09-28 Matthias: Questionable if this is an assert. Maybe we should introduce an InUseViolation.
			final Check check = new Check(Spec.ASSERT);
			check.annotate(errorLocation);
			final ThreadInstance ti = new ThreadInstance(threadInstanceId, procedureName, threadIdVars, threadInUseVar,
					errorLocation);
			result.put(procedureName, ti);
			i++;
		}
		return result;
	}

	public static BoogieNonOldVar constructThreadInUseVariable(final String threadInstanceId,
			final ManagedScript mgdScript) {
		final Sort booleanSort = SmtSortUtils.getBoolSort(mgdScript);
		final BoogieNonOldVar threadInUseVar = constructThreadAuxiliaryVariable("th_" + threadInstanceId + "_inUse",
				booleanSort, mgdScript);
		return threadInUseVar;
	}

	public static BoogieNonOldVar[] constructThreadIdVariable(final String threadInstanceId,
			final ManagedScript mgdScript, final Term[] threadIdArguments) {
		final BoogieNonOldVar[] threadIdVars = new BoogieNonOldVar[threadIdArguments.length];
		int i = 0;
		for (final Term forkId : threadIdArguments) {
			threadIdVars[i] = constructThreadAuxiliaryVariable("thidvar" + i + "_" + threadInstanceId, forkId.getSort(),
					mgdScript);
			i++;
		}
		return threadIdVars;
	}

	/**
	 * TODO Concurrent Boogie:
	 */
	public static BoogieNonOldVar constructThreadAuxiliaryVariable(final String id, final Sort sort,
			final ManagedScript mgdScript) {
		mgdScript.lock(id);
		final BoogieNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(id, sort, mgdScript, id);
		mgdScript.unlock(id);
		return var;
	}

	public CfgSmtToolkit constructNewToolkit(final CfgSmtToolkit cfgSmtToolkit, final Map<String, ThreadInstance> threadInstanceMap2) {
		final DefaultIcfgSymbolTable newSymbolTable = new DefaultIcfgSymbolTable(cfgSmtToolkit.getSymbolTable(), cfgSmtToolkit.getProcedures());
		final HashRelation<String, IProgramNonOldVar> proc2Globals = new HashRelation<>(cfgSmtToolkit.getModifiableGlobalsTable().getProcToGlobals());
		for (final ThreadInstance ti : threadInstanceMap2.values()) {
			addVar(ti.getInUseVar(), newSymbolTable, proc2Globals, cfgSmtToolkit.getProcedures());
						for (final IProgramNonOldVar idVar : ti.getIdVars()) {
				addVar(idVar, newSymbolTable, proc2Globals, cfgSmtToolkit.getProcedures());
			}
		}
		newSymbolTable.finishConstruction();
		final ConcurrencyInformation concurrencyInformation = new ConcurrencyInformation(threadInstanceMap2);
		return new CfgSmtToolkit(new ModifiableGlobalsTable(proc2Globals), cfgSmtToolkit.getManagedScript(),
				newSymbolTable, cfgSmtToolkit.getAxioms(), cfgSmtToolkit.getProcedures(), cfgSmtToolkit.getInParams(),
				cfgSmtToolkit.getOutParams(), cfgSmtToolkit.getIcfgEdgeFactory(),
				concurrencyInformation);
	}

	private void addVar(final IProgramNonOldVar var, final DefaultIcfgSymbolTable newSymbolTable,
			final HashRelation<String, IProgramNonOldVar> proc2Globals, final Set<String> allProcedures) {
		newSymbolTable.add(var);
		for (final String proc : allProcedures) {
			proc2Globals.addPair(proc, var);
		}
	}

	public void addInUseErrorLocations(final BasicIcfg<IcfgLocation> result,
			final Collection<ThreadInstance> threadInstances) {
		for (final ThreadInstance ti : threadInstances) {
			result.addLocation(ti.getErrorLocation(), false, true, false, false, false);
		}


	}

}
