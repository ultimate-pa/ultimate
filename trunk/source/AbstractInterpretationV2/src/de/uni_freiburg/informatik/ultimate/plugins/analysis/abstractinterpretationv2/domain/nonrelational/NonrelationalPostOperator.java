/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * The post operator of the interval domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public abstract class NonrelationalPostOperator<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		implements IAbstractPostOperator<STATE, CodeBlock, IBoogieVar> {

	private final ILogger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final NonrelationalStatementProcessor<STATE, V> mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;
	private final int mParallelStates;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;

	protected NonrelationalPostOperator(final ILogger logger, final BoogieSymbolTable symbolTable,
			final Boogie2SmtSymbolTable bpl2smtSymbolTable,
			final NonrelationalStatementProcessor<STATE, V> statementProcessor, final int parallelStates) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mBoogie2SmtSymbolTable = bpl2smtSymbolTable;
		mStatementProcessor = statementProcessor;
		mSymbolTable = symbolTable;
		mParallelStates = parallelStates;
	}

	@Override
	public List<STATE> apply(final STATE oldstate, final CodeBlock transition) {
		assert oldstate != null;
		assert !oldstate.isBottom() : "You should not need to calculate post of a bottom state";
		assert transition != null;

		List<STATE> currentStates = new ArrayList<>();
		currentStates.add(oldstate);
		final List<Statement> statements = mStatementExtractor.process(transition);

		for (final Statement stmt : statements) {
			final List<STATE> afterProcessStates = new ArrayList<>();
			for (final STATE currentState : currentStates) {
				final List<STATE> processed = mStatementProcessor.process(currentState, stmt);
				for (final STATE s : processed) {
					if (!s.isBottom()) {
						afterProcessStates.add(s);
					}
				}
			}
			currentStates = afterProcessStates;
		}

		if (currentStates.isEmpty()) {
			if (!oldstate.getVariables().isEmpty()) {
				currentStates.add(oldstate.bottomState());
			}
			return currentStates;
		}

		return NonrelationalUtils.mergeStatesIfNecessary(currentStates, mParallelStates);
	}

	@Override
	public List<STATE> apply(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final CodeBlock transition) {
		assert transition instanceof Call
				|| transition instanceof Return : "Cannot calculate hierachical post for non-hierachical transition";

		final List<STATE> returnList = new ArrayList<>();

		if (transition instanceof Call) {
			final Call call = (Call) transition;
			final CallStatement callStatement = call.getCallStatement();
			final Expression[] args = callStatement.getArguments();

			// If there are no arguments, we don't need to rewrite states.
			if (args.length == 0) {
				returnList.add(stateAfterLeaving);
				return returnList;
			}

			final Map<Integer, String> tmpParamNames = getArgumentTemporaries(args.length, stateBeforeLeaving);
			final List<LeftHandSide> idents = new ArrayList<>();
			final Map<LeftHandSide, IBoogieVar> tmpVarUses = new HashMap<>();
			final Map<String, IBoogieVar> tmpParamVars = new HashMap<>();
			final ILocation loc = callStatement.getLocation();
			for (int i = 0; i < args.length; i++) {
				final String name = tmpParamNames.get(i);
				final IBoogieVar boogieVar = BoogieUtil.createTemporaryIBoogieVar(name, args[i].getType());
				final VariableLHS lhs = new VariableLHS(loc, name);
				tmpParamVars.put(name, boogieVar);
				tmpVarUses.put(lhs, boogieVar);
				idents.add(lhs);
			}

			final AssignmentStatement assign = new AssignmentStatement(callStatement.getLocation(),
					idents.toArray(new LeftHandSide[idents.size()]), args);
			final STATE interimState = stateBeforeLeaving.addVariables(tmpParamVars.values());
			final List<STATE> result = mStatementProcessor.process(interimState, assign, tmpVarUses);
			if (result.isEmpty()) {
				throw new UnsupportedOperationException("The assingment operation resulted in 0 states.");
			}

			final Procedure procedure = getProcedure(callStatement.getMethodName());
			assert procedure != null;
			final VarList[] inParams = procedure.getInParams();
			final List<IBoogieVar> realParamVars = new ArrayList<>();

			for (final VarList varlist : inParams) {
				for (final String var : varlist.getIdentifiers()) {
					realParamVars.add(mBoogie2SmtSymbolTable.getBoogieVar(var, callStatement.getMethodName(), true));
				}
			}

			if (args.length != realParamVars.size()) {
				throw new UnsupportedOperationException(
						"The number of the expressions in the call statement arguments does not correspond to the length of the number of arguments in the symbol table.");
			}

			for (final STATE resultState : result) {
				STATE returnState = stateAfterLeaving.createCopy();

				for (int i = 0; i < realParamVars.size(); i++) {
					final String tempName = tmpParamNames.get(i);
					final IBoogieVar realVar = realParamVars.get(i);
					final IBoogieVar tempVar = tmpParamVars.get(tempName);

					if (tempVar.getIType() instanceof PrimitiveType) {
						final PrimitiveType primitiveType = (PrimitiveType) tempVar.getIType();

						if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
							returnState = returnState.setBooleanValue(realVar, resultState.getBooleanValue(tempVar));
						} else {
							returnState = returnState.setValue(realVar, resultState.getValue(tempVar));
						}
					} else if (tempVar.getIType() instanceof ArrayType) {
						// TODO:
						// We treat Arrays as normal variables for the time being.
						returnState = returnState.setValue(realVar, resultState.getValue(tempVar));
					} else {
						mLogger.warn("The IBoogieVar type " + tempVar.getIType()
								+ " cannot be handled. Assuming normal variable type.");
						returnState = returnState.setValue(realVar, resultState.getValue(tempVar));
					}
				}

				returnList.add(returnState);
			}

			return NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates);
		} else if (transition instanceof Return) {
			final Return ret = (Return) transition;
			final CallStatement correspondingCall = ret.getCallStatement();

			final List<V> vals = getOutParamValues(correspondingCall.getMethodName(), stateBeforeLeaving);
			final VariableLHS[] lhs = correspondingCall.getLhs();

			if (vals.size() != lhs.length) {
				throw new UnsupportedOperationException("The expected number of return variables (" + lhs.length
						+ ") is different from the function's number of return variables (" + vals.size() + ").");
			}

			final List<IBoogieVar> updateVarNames = new ArrayList<>();
			for (final VariableLHS varLhs : lhs) {
				final BoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(varLhs.getIdentifier(),
						varLhs.getDeclarationInformation(), false);
				updateVarNames.add(boogieVar);
			}

			final STATE returnState =
					stateAfterLeaving.setValues(updateVarNames.toArray(new IBoogieVar[updateVarNames.size()]),
							vals.toArray(stateAfterLeaving.getArray(vals.size())));

			returnList.add(returnState);
			return NonrelationalUtils.mergeStatesIfNecessary(returnList, mParallelStates);
		} else {
			throw new UnsupportedOperationException(
					"IntervalDomain does not support context switches other than Call and Return (yet)");
		}
	}

	/**
	 * Creates a map of Integers -&gt; Identifiers for a given desired number of variables. The created identifiers are
	 * unique temporary variable identifiers. It is ensured that the created identifiers do not already occur in the
	 * current state.
	 *
	 * @param argNum
	 *            The number of temporary variables to create.
	 * @param state
	 *            The current state.
	 * @return A map containing for each index of the call statement's argument
	 */
	private Map<Integer, String> getArgumentTemporaries(final int argNum, final STATE state) {
		final Map<Integer, String> returnMap = new HashMap<>();

		String paramPrefix = "param_";
		final Set<String> varNames =
				state.getVariables().stream().map(a -> a.getGloballyUniqueId()).collect(Collectors.toSet());
		boolean uniqueFound = false;

		while (!uniqueFound) {
			for (int i = 0; i < argNum; i++) {
				final StringBuilder sb = new StringBuilder();
				sb.append(paramPrefix).append(i);
				final String currentParamName = sb.toString();
				if (varNames.contains(currentParamName)) {
					final StringBuilder paramBuilder = new StringBuilder();
					paramBuilder.append(paramPrefix).append('_');
					paramPrefix = paramBuilder.toString();
					break;
				}
			}
			uniqueFound = true;
		}

		for (int i = 0; i < argNum; i++) {
			final StringBuilder sb = new StringBuilder();
			sb.append(paramPrefix).append(i);
			returnMap.put(i, sb.toString());
		}

		return returnMap;
	}

	private Procedure getProcedure(final String procedureName) {
		return mSymbolTable.getFunctionOrProcedureDeclaration(procedureName).stream()
				.filter(decl -> decl instanceof Procedure).map(decl -> (Procedure) decl)
				.filter(proc -> proc.getBody() != null).findFirst().get();
	}

	private List<V> getOutParamValues(final String procedureName, final STATE stateBeforeLeaving) {
		// functions are already inlined and if there are procedure and implementation declaration for a proc, we know
		// that we only get the implementation from the FXPE
		final Procedure procedure = getProcedure(procedureName);

		final List<V> vals = new ArrayList<>();
		for (final VarList list : procedure.getOutParams()) {
			for (final String s : list.getIdentifiers()) {
				final BoogieVar boogieVar = mBoogie2SmtSymbolTable.getBoogieVar(s, procedure.getIdentifier(), false);
				vals.add(stateBeforeLeaving.getValue(boogieVar));
			}
		}
		return vals;
	}
}
