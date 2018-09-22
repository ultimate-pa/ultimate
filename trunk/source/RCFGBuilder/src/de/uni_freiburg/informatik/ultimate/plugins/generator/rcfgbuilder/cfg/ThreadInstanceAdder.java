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

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Adds thread instances to an ICFG
 *
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ThreadInstanceAdder {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;


	public ThreadInstanceAdder(final IUltimateServiceProvider services)  {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}


	public BoogieIcfgContainer connectThreadInstances(final BoogieIcfgContainer icfg,
			final Collection<ForkThreadCurrent> forkCurrentThreads,
			final Collection<JoinThreadCurrent> joinCurrentThreads, final Collection<String> forkedProcedureNames,
			final Map<String, ThreadInstance> threadInstanceMap, final CodeBlockFactory cbf) {
		for (final ForkThreadCurrent fct : forkCurrentThreads) {
			final ThreadInstance ti = threadInstanceMap.get(fct.getForkStatement().getProcedureName());

			addForkOtherThreadTransition(fct, (BoogieIcfgLocation) ti.getErrorLocation(), ti.getIdVars(), ti.getInUseVar(), icfg, cbf);
		}

		// For each implemented procedure, add a JoinOtherThreadTransition from the exit
		// location of the procedure
		// to all target locations of each JoinCurrentThreadEdge
		for (final JoinThreadCurrent jot : joinCurrentThreads) {
			// if (mBoogieDeclarations.getProcImplementation().containsKey(procName)) {
			for (final String procName : forkedProcedureNames) {
				final ThreadInstance ti = threadInstanceMap.get(procName);
				addJoinOtherThreadTransition(jot, procName, ti.getIdVars(), ti.getInUseVar(), icfg, cbf);
			}
			// }
		}

		return icfg;
	}


	/**
	 * Add ForkOtherThreadEdge from the ForkCurrentThreadEdge source to the entry
	 * location of the forked procedure.
	 * @param edge
	 *            that points to the next step in the current thread.
	 */
	private void addForkOtherThreadTransition(final ForkThreadCurrent forkEdgeCurrent,
			final BoogieIcfgLocation errorNode, final IProgramNonOldVar[] threadIdVars,
			final IProgramNonOldVar threadInUseVar, final BoogieIcfgContainer icfg, final CodeBlockFactory cbf) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags

		final ForkStatement st = forkEdgeCurrent.getForkStatement();
		final String callee = st.getProcedureName();
		assert icfg.getProcedureEntryNodes().containsKey(callee) : "Source code contains" + " fork of " + callee
				+ " but no such procedure.";

		// Add fork transition from callerNode to procedures entry node.
		final BoogieIcfgLocation callerNode = (BoogieIcfgLocation) forkEdgeCurrent.getSource();
		final BoogieIcfgLocation calleeEntryLoc = icfg.getProcedureEntryNodes().get(callee);

		final ForkSmtArguments fsa = forkEdgeCurrent.getForkSmtArguments();

		final ForkThreadOther fork = cbf.constructForkOtherThread(callerNode, calleeEntryLoc, st, forkEdgeCurrent);
		final UnmodifiableTransFormula parameterAssignment = fsa.constructInVarsAssignment(icfg.getSymboltable(),
				icfg.getBoogie2SMT().getManagedScript(),
				icfg.getCfgSmtToolkit().getInParams().get(st.getProcedureName()));

		final UnmodifiableTransFormula threadIdAssignment = fsa.constructThreadIdAssignment(icfg.getSymboltable(),
				icfg.getBoogie2SMT().getManagedScript(), Arrays.asList(threadIdVars));
		final UnmodifiableTransFormula threadInUseAssignment = constructForkInUseAssignment(threadInUseVar,
				icfg.getCfgSmtToolkit().getManagedScript());
		final UnmodifiableTransFormula forkTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
				icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
				Arrays.asList(parameterAssignment, threadIdAssignment, threadInUseAssignment));
		fork.setTransitionFormula(forkTransformula);

		// Add the assume statement for the error location and construct the
		final ILocation forkLocation = st.getLocation();
		final UnmodifiableTransFormula forkErrorTransFormula = constructThreadInUseViolationAssumption(threadInUseVar,
				icfg.getCfgSmtToolkit().getManagedScript());
		final Expression formula = icfg.getBoogie2SMT().getTerm2Expression()
				.translate(forkErrorTransFormula.getFormula());
		final AssumeStatement assumeError = new AssumeStatement(forkLocation, formula);
		final StatementSequence errorStatement = cbf.constructStatementSequence(callerNode, errorNode, assumeError);
		errorStatement.setTransitionFormula(forkErrorTransFormula);

		// TODO Matthias 2018-09-15: Set overapproximations for both edges
		final Map<String, ILocation> overapproximations = new HashMap<>();
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(forkEdgeCurrent);
		}
	}





	/**
	 * Add JoinOtherThreadEdge from
	 * @param edge
	 */
	private void addJoinOtherThreadTransition(final JoinThreadCurrent joinEdgeCurrent, final String procName,
			final IProgramNonOldVar[] threadIdVars, final IProgramNonOldVar threadInUseVar,
			final BoogieIcfgContainer icfg, final CodeBlockFactory cbf) {
		// FIXME Matthias 2018-08-17: check method, especially for terminology and
		// overapproximation flags
		final JoinStatement st = joinEdgeCurrent.getJoinStatement();
		final BoogieIcfgLocation exitNode = icfg.getProcedureExitNodes().get(procName);
		final BoogieIcfgLocation callerNode = (BoogieIcfgLocation) joinEdgeCurrent.getTarget();


		final JoinSmtArguments jsa = joinEdgeCurrent.getJoinSmtArguments();

		// TODO Matthias 2018-08-16: IssueId:Feldberg
		//
		// use the following list and the jsa to do a comparison
		// based on sorts (instead of types)
		final List<ILocalProgramVar> outParams = icfg.getCfgSmtToolkit().getOutParams().get(procName);
		//
		//

		if (threadIdVars.length != st.getThreadID().length) {
			return;
		} else {
			int offset = 0;
			for (final IProgramNonOldVar threadId : threadIdVars) {
				if (st.getThreadID()[offset].getType() != icfg.getBoogie2SMT().getTypeSortTranslator()
						.getType(threadId.getSort())) {
					return;
				}
				offset++;
			}
		}

		final String caller = callerNode.getProcedure();

		// Create JoinOtherThread object and add TransFormulas.
		final JoinThreadOther joinOtherThread = cbf.constructJoinOtherThread(exitNode, callerNode, st,
				joinEdgeCurrent);

		final UnmodifiableTransFormula threadIdAssumption = jsa.constructThreadIdAssumption(icfg.getSymboltable(),
				icfg.getBoogie2SMT().getManagedScript(), Arrays.asList(threadIdVars));

		final UnmodifiableTransFormula parameterAssignment = jsa.constructResultAssignment(
				icfg.getBoogie2SMT().getManagedScript(), icfg.getCfgSmtToolkit().getOutParams().get(procName));

		final UnmodifiableTransFormula threadInUseAssignment = constructThreadNotInUseAssingment(threadInUseVar,
				icfg.getCfgSmtToolkit().getManagedScript());
		final UnmodifiableTransFormula joinTransformula = TransFormulaUtils.sequentialComposition(mLogger, mServices,
				icfg.getCfgSmtToolkit().getManagedScript(), false, false, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.NONE,
				Arrays.asList(parameterAssignment, threadIdAssumption, threadInUseAssignment));
		joinOtherThread.setTransitionFormula(joinTransformula);

		final Map<String, ILocation> overapproximations = new HashMap<>();
		if (!overapproximations.isEmpty()) {
			new Overapprox(overapproximations).annotate(joinEdgeCurrent);
		}
	}



	/**
	 * TODO Concurrent Boogie:
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
	 * @param mgdScript
	 * @return A {@link TransFormula} that represents the assume statement {@code var == true}.
	 */
	private UnmodifiableTransFormula constructThreadInUseViolationAssumption(final IProgramNonOldVar threadInUseVar,
			final ManagedScript mgdScript) {
		final Map<IProgramVar, TermVariable> inVars = Collections.singletonMap(threadInUseVar,
				threadInUseVar.getTermVariable());
		final Map<IProgramVar, TermVariable> outVars = inVars;
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true,
				Collections.emptySet(), true, Collections.emptySet(), true);
		tfb.setFormula(threadInUseVar.getTermVariable());
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}


	/**
	 * TODO Concurrent Boogie:
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


}
