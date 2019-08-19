/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 */
public class RcfgVariableProvider<STATE extends IAbstractState<STATE>> implements IVariableProvider<STATE, IcfgEdge> {

	private final CfgSmtToolkit mCfgSmt;
	private final IIcfgSymbolTable mSymbolTable;
	private final ILogger mLogger;

	public RcfgVariableProvider(final CfgSmtToolkit toolkit, final IUltimateServiceProvider services) {
		this(toolkit, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
	}

	public RcfgVariableProvider(final CfgSmtToolkit toolkit, final ILogger logger) {
		assert toolkit != null;
		assert logger != null;
		mCfgSmt = toolkit;
		mSymbolTable = toolkit.getSymbolTable();
		mLogger = logger;
	}

	@Override
	public STATE defineInitialVariables(final IcfgEdge current, final STATE state) {
		assert current != null : "edge is null";
		assert state != null : "state is null";

		final Set<IProgramVarOrConst> vars = getPreVariables(current);
		if (vars.isEmpty()) {
			return state;
		}
		return state.addVariables(vars);
	}

	@Override
	public STATE defineVariablesAfter(final IcfgEdge action, final STATE localPreState,
			final STATE hierachicalPreState) {
		assert action != null;
		assert localPreState != null;

		// we assume that state has all variables except the ones that would be
		// introduced or removed by this edge
		// so, only call or return can do this
		if (action instanceof IIcfgCallTransition<?>) {
			return defineVariablesAfterCall(action, localPreState);
		} else if (action instanceof IIcfgReturnTransition<?, ?>) {
			final String sourceProc = action.getPrecedingProcedure();
			final String targetProc = action.getSucceedingProcedure();
			return defineVariablesAfterReturn(localPreState, hierachicalPreState, sourceProc, targetProc);
		} else if (action instanceof Summary) {
			final Summary sum = (Summary) action;
			if (sum.calledProcedureHasImplementation()) {
				// this summary is used because we have pre/poststate from our summary map
				final String sourceProc = sum.getCallStatement().getMethodName();
				final String targetProc = action.getSucceedingProcedure();
				return defineVariablesAfterReturn(localPreState, hierachicalPreState, sourceProc, targetProc);
			}
		}

		// nothing changes
		return localPreState;
	}

	@Override
	public STATE createValidPostOpStateAfterLeaving(final IcfgEdge action, final STATE stateLin,
			final STATE stateHier) {
		final Set<IProgramVarOrConst> preVars = getPreVariables(action);
		final STATE synchronizedPreLin = AbsIntUtil.synchronizeVariables(stateLin, preVars);
		return defineVariablesAfter(action, synchronizedPreLin, stateHier);
	}

	@Override
	public STATE createValidPostOpStateBeforeLeaving(final IcfgEdge action, final STATE stateHier) {
		final Set<IProgramVarOrConst> preVars = getPreVariables(action);
		return AbsIntUtil.synchronizeVariables(stateHier, preVars);
	}

	private STATE defineVariablesAfterReturn(final STATE localPreState, final STATE hierachicalPreState,
			final String sourceProc, final String targetProc) {
		// if the action is a return, we have to:
		// - remove all currently local variables
		// - keep all unmasked globals
		// - add old locals from the scope we are returning to
		// - add globals that were masked by this scope from the scope we are returning to

		final Set<IProgramVarOrConst> varsNeededFromOldScope = new HashSet<>();
		if (sourceProc != null) {
			// we need masked globals from the old scope, so we have to determine which globals are masked
			varsNeededFromOldScope.addAll(getMaskedGlobalsVariables(sourceProc));
			// but we need to keep all global variables in the target scope
			varsNeededFromOldScope.addAll(getOldVars());
		}
		if (targetProc != null) {
			// we also need oldlocals from the old scope; if the old scope also masks global variables, this will
			// mask them again
			varsNeededFromOldScope.addAll(getLocalVariables(targetProc));
		}

		STATE rtr = localPreState;
		// in any case, we have to remove all local variables from the state
		rtr = removeLocals(rtr, sourceProc);

		if (varsNeededFromOldScope.isEmpty()) {
			// we do not need information from the old scope, so we are finished
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
						.append(" No vars needed from old scope"));
			}
			return rtr;
		}

		// the program state that has to be used to obtain the values of the old scope
		// (old locals, unmasked globals) is the pre state of the call
		STATE preCallState = hierachicalPreState;
		assert preCallState != null : "There is no abstract state before the call that corresponds to this return";
		// we determine which variables are not needed ...
		final Set<IProgramVarOrConst> toberemoved = new HashSet<>();
		for (final IProgramVarOrConst entry : preCallState.getVariables()) {
			if (!varsNeededFromOldScope.contains(entry)) {
				toberemoved.add(entry);
			}
		}

		if (!toberemoved.isEmpty()) {
			// ... and remove them if there are any
			preCallState = preCallState.removeVariables(toberemoved);
		}
		// now we combine the state after returning from this method with the one from before we entered the method.
		rtr = rtr.patch(preCallState);
		return rtr;
	}

	private STATE defineVariablesAfterCall(final IcfgEdge action, final STATE localPreState) {
		// if we call we just need to update all local variables, i.e., remove all the ones from the current scope
		// and add all the ones from the new scope (thus also automatically masking globals)
		final String remove = action.getPrecedingProcedure();
		final String add = action.getSucceedingProcedure();

		// remove current locals
		STATE rtr = removeLocals(localPreState, remove);

		// TODO: replace old old variables with fresh ones

		// remove globals that will be masked by the new scope
		final Set<IProgramVarOrConst> masked = getMaskedGlobalsVariables(add);
		if (!masked.isEmpty()) {
			rtr = rtr.removeVariables(masked);
		}
		// add locals of new scope
		rtr = applyLocals(rtr, add, rtr::addVariables);
		return rtr;
	}

	private STATE removeLocals(final STATE state, final String procedure) {
		return applyLocals(state, procedure, state::removeVariables);
	}

	private STATE applyLocals(final STATE state, final String procedure,
			final Function<Set<IProgramVarOrConst>, STATE> fun) {
		if (procedure == null) {
			return state;
		}

		final Set<IProgramVarOrConst> locals = getLocalVariables(procedure);
		if (locals.isEmpty()) {
			return state;
		}

		return fun.apply(locals);
	}

	/**
	 * Get all global variables that are masked by the specified procedure.
	 *
	 * @param procedure
	 *            the name of the masking procedure.
	 * @return A map from variable name to {@link IProgramVarOrConst}.
	 */
	private Set<IProgramVarOrConst> getMaskedGlobalsVariables(final String procedure) {
		assert procedure != null;
		final Set<IProgramVarOrConst> globals = getGlobalScopeVarAndConsts();
		final Set<IProgramVarOrConst> locals = getLocalVariables(procedure);
		final Set<IProgramVarOrConst> rtr = new HashSet<>();

		for (final IProgramVarOrConst local : locals) {
			if (globals.contains(local)) {
				rtr.add(local);
			}
		}

		return rtr;
	}

	private Set<IProgramVarOrConst> getPreVariables(final IcfgEdge current) {
		final Set<IProgramVarOrConst> vars = getGlobalScopeVarAndConsts();

		// add locals if applicable, thereby overriding globals
		final String procedure = current.getPrecedingProcedure();
		if (procedure != null) {
			vars.addAll(getLocalVariables(procedure));
		}
		return vars;
	}

	private Set<IProgramVarOrConst> getGlobalScopeVarAndConsts() {
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		for (final IProgramNonOldVar globalNonOld : mSymbolTable.getGlobals()) {
			vars.add(globalNonOld);
			vars.add(globalNonOld.getOldVar());
		}
		for (final IProgramConst pc : mSymbolTable.getConstants()) {
			vars.add(pc);
		}
		return vars;
	}

	private Set<IProgramVarOrConst> getOldVars() {
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		for (final IProgramNonOldVar globalNonOld : mSymbolTable.getGlobals()) {
			vars.add(globalNonOld.getOldVar());
		}
		return vars;
	}

	private Set<IProgramVarOrConst> getLocalVariables(final String procedure) {
		assert procedure != null;
		final Set<IProgramVarOrConst> rtr =
				mSymbolTable.getLocals(procedure).stream().map(a -> (IProgramVarOrConst) a).collect(Collectors.toSet());
		return rtr;
	}

	@Override
	public IVariableProvider<STATE, IcfgEdge> createNewVariableProvider(final CfgSmtToolkit toolkit) {
		return new RcfgVariableProvider<>(toolkit, mLogger);
	}

	@Override
	public Set<IProgramVarOrConst> getRequiredVars(final IcfgEdge act) {
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		if (act instanceof IInternalAction) {
			addTfVars(act.getTransformula(), vars);
		} else if (act instanceof ICallAction) {
			final ICallAction callAct = (ICallAction) act;
			addTfVars(callAct.getLocalVarsAssignment(), vars);
			addTfVars(mCfgSmt.getOldVarsAssignmentCache().getOldVarsAssignment(callAct.getSucceedingProcedure()), vars);
		} else if (act instanceof IReturnAction) {
			final IReturnAction retAct = (IReturnAction) act;
			addTfVars(retAct.getAssignmentOfReturn(), vars);
		} else {
			throw new UnsupportedOperationException();
		}
		return vars;
	}

	private static void addTfVars(final UnmodifiableTransFormula tf, final Set<IProgramVarOrConst> vars) {
		tf.getNonTheoryConsts().forEach(a -> vars.add(a));
		tf.getInVars().entrySet().stream().forEach(a -> vars.add(a.getKey()));
		tf.getOutVars().entrySet().stream().forEach(a -> vars.add(a.getKey()));
	}

}
