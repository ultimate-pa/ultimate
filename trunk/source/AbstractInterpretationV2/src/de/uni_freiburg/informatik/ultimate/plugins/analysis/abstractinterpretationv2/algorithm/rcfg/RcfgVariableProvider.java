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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
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
public class RcfgVariableProvider<STATE extends IAbstractState<STATE, IBoogieVar>>
		implements IVariableProvider<STATE, IcfgEdge, IBoogieVar> {

	private final IIcfgSymbolTable mSymbolTable;
	private final ILogger mLogger;

	public RcfgVariableProvider(final IIcfgSymbolTable symbolTable, final IUltimateServiceProvider services) {
		this(symbolTable, services.getLoggingService().getLogger(Activator.PLUGIN_ID));
	}

	public RcfgVariableProvider(final IIcfgSymbolTable symbolTable, final ILogger logger) {
		assert symbolTable != null;
		assert logger != null;
		mSymbolTable = symbolTable;
		mLogger = logger;
	}

	@Override
	public STATE defineInitialVariables(final IcfgEdge current, final STATE state) {
		assert current != null;
		assert state != null;
		assert state.isEmpty();

		final Set<IBoogieVar> vars = getPreVariables(current);
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
	public STATE synchronizeVariables(final STATE template, final STATE toSynchronize) {
		if (toSynchronize == null) {
			return null;
		}
		if (template == null) {
			return toSynchronize;
		}
		final STATE rtr = synchronizeVariables(toSynchronize, template.getVariables());
		assert !toSynchronize.isBottom() || rtr.isBottom() : "Bottom is lost";
		return rtr;
	}

	@Override
	public STATE createValidPostOpStateAfterLeaving(final IcfgEdge action, final STATE stateLin,
			final STATE stateHier) {
		final Set<IBoogieVar> preVars = getPreVariables(action);
		final STATE synchronizedPreLin = synchronizeVariables(stateLin, preVars);
		return defineVariablesAfter(action, synchronizedPreLin, stateHier);
	}

	@Override
	public STATE createValidPostOpStateBeforeLeaving(final IcfgEdge action, final STATE stateHier) {
		final Set<IBoogieVar> preVars = getPreVariables(action);
		return synchronizeVariables(stateHier, preVars);
	}

	private STATE synchronizeVariables(final STATE state, final Set<IBoogieVar> shouldVars) {
		final Set<IBoogieVar> definedVariables = state.getVariables();

		final Set<IBoogieVar> toRemove = AbsIntUtil.difference(definedVariables, shouldVars);
		final Set<IBoogieVar> toAdd = AbsIntUtil.difference(shouldVars, definedVariables);

		if (toRemove.isEmpty() && toAdd.isEmpty()) {
			return state;
		}
		if (toRemove.isEmpty()) {
			return state.addVariables(toAdd);
		}
		if (toAdd.isEmpty()) {
			return state.removeVariables(toRemove);
		}
		return state.removeVariables(toRemove).addVariables(toAdd);
	}

	private STATE defineVariablesAfterReturn(final STATE localPreState, final STATE hierachicalPreState,
			final String sourceProc, final String targetProc) {
		// if the action is a return, we have to:
		// - remove all currently local variables
		// - keep all unmasked globals
		// - add old locals from the scope we are returning to
		// - add globals that were masked by this scope from the scope we are returning to

		final Set<IBoogieVar> varsNeededFromOldScope = new HashSet<>();
		if (sourceProc != null) {
			// we need masked globals from the old scope, so we have to determine which globals are masked
			varsNeededFromOldScope.addAll(getMaskedGlobalsVariables(sourceProc));
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
		final Set<IBoogieVar> toberemoved = new HashSet<>();
		for (final IBoogieVar entry : preCallState.getVariables()) {
			if (!varsNeededFromOldScope.contains(entry)) {
				toberemoved.add(entry);
			}
		}

		if (!toberemoved.isEmpty()) {
			// ... and remove them if there are any
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageRemoveLocalsPreCall(preCallState, toberemoved));
			}
			preCallState = preCallState.removeVariables(toberemoved);
		} else if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageNoRemoveLocalsPreCall(preCallState));
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
		final Set<IBoogieVar> masked = getMaskedGlobalsVariables(add);
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

	private STATE applyLocals(final STATE state, final String procedure, final Function<Set<IBoogieVar>, STATE> fun) {
		if (procedure == null) {
			return state;
		}

		final Set<IBoogieVar> locals = getLocalVariables(procedure);
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
	 * @return A map from variable name to {@link IBoogieVar}.
	 */
	private Set<IBoogieVar> getMaskedGlobalsVariables(final String procedure) {
		assert procedure != null;
		final Set<IBoogieVar> globals = new HashSet<>();
		for (final IProgramNonOldVar global : mSymbolTable.getGlobals()) {
			globals.add((IBoogieVar) global);
		}
		for (final IProgramConst pc : mSymbolTable.getConstants()) {
			globals.add((IBoogieVar) pc);
		}

		final Set<IBoogieVar> locals = new HashSet<>();
		locals.addAll(getLocalVariables(procedure));

		final Set<IBoogieVar> rtr = new HashSet<>();

		for (final IBoogieVar local : locals) {
			if (globals.contains(local)) {
				rtr.add(local);
			}
		}

		return rtr;
	}

	private Set<IBoogieVar> getPreVariables(final IcfgEdge current) {
		final Set<IBoogieVar> vars = getGlobalScopeVarAndConsts();

		// add locals if applicable, thereby overriding globals
		final String procedure = current.getPrecedingProcedure();
		if (procedure != null) {
			vars.addAll(getLocalVariables(procedure));
		}
		return vars;
	}

	private Set<IBoogieVar> getGlobalScopeVarAndConsts() {
		final Set<IBoogieVar> vars = new HashSet<>();
		for (final IProgramNonOldVar globalNonOld : mSymbolTable.getGlobals()) {
			vars.add((IBoogieVar) globalNonOld);
			vars.add((IBoogieVar) globalNonOld.getOldVar());
		}
		for (final IProgramConst pc : mSymbolTable.getConstants()) {
			vars.add((IBoogieVar) pc);
		}
		return vars;
	}

	private Set<IBoogieVar> getLocalVariables(final String procedure) {
		assert procedure != null;
		final Set<IBoogieVar> rtr =
				mSymbolTable.getLocals(procedure).stream().map(a -> (IBoogieVar) a).collect(Collectors.toSet());
		return rtr;
	}

	private StringBuilder getLogMessageRemoveLocalsPreCall(final STATE state, final Set<IBoogieVar> toberemoved) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" removing vars from pre-call state [")
				.append(state.hashCode()).append("] ").append(state.toLogString()).append(": ").append(toberemoved);
	}

	private StringBuilder getLogMessageNoRemoveLocalsPreCall(final STATE state) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" using unchanged pre-call state [")
				.append(state.hashCode()).append("] ").append(state.toLogString());
	}

	@Override
	public IVariableProvider<STATE, IcfgEdge, IBoogieVar> createNewVariableProvider(final IIcfgSymbolTable table) {
		return new RcfgVariableProvider<>(table, mLogger);
	}

}
