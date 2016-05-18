/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IType;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class RcfgProgramExecutionBuilder {

	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final NestedWord<CodeBlock> m_Trace;
	private final Map<BoogieVar, Map<Integer, Expression>> m_var2pos2value;
	private final RelevantVariables m_RelevantVariables;
	private RcfgProgramExecution m_RcfgProgramExecution;
	private final Map<TermVariable, Boolean>[] m_BranchEncoders;
	private final Boogie2SmtSymbolTable m_SymbolTable;

	public RcfgProgramExecutionBuilder(ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			NestedWord<CodeBlock> trace, RelevantVariables relevantVariables, Boogie2SmtSymbolTable symbolTable) {
		super();
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_Trace = trace;
		m_var2pos2value = new HashMap<BoogieVar, Map<Integer, Expression>>();
		m_RelevantVariables = relevantVariables;
		m_BranchEncoders = new Map[m_Trace.length()];
		m_RcfgProgramExecution = null;
		m_SymbolTable = symbolTable;
	}

	public RcfgProgramExecution getRcfgProgramExecution() {
		if (m_RcfgProgramExecution == null) {
			m_RcfgProgramExecution = computeRcfgProgramExecution();
		}
		return m_RcfgProgramExecution;
	}

	private boolean isReAssigned(BoogieVar bv, int position) {
		boolean result;
		if (m_Trace.isInternalPosition(position) || m_Trace.isReturnPosition(position)) {
			TransFormula tf = m_Trace.getSymbolAt(position).getTransitionFormula();
			result = tf.getAssignedVars().contains(bv);
		} else if (m_Trace.isCallPosition(position)) {
			Call call = (Call) m_Trace.getSymbolAt(position);
			String callee = call.getCallStatement().getMethodName();
			if (bv.isGlobal()) {
				Set<BoogieVar> modGlobals = m_ModifiableGlobalVariableManager.getGlobalVarsAssignment(callee)
						.getOutVars().keySet();
				Set<BoogieVar> modOldGlobals = m_ModifiableGlobalVariableManager.getOldVarsAssignment(callee)
						.getOutVars().keySet();
				result = modGlobals.contains(bv) || modOldGlobals.contains(bv);
			} else {
				// TransFormula locVarAssign =
				// m_Trace.getSymbolAt(position).getTransitionFormula();
				// result = locVarAssign.getAssignedVars().contains(bv);
				result = (callee.equals(bv.getProcedure()));
			}
		} else {
			throw new AssertionError();
		}
		return result;
	}

	void addValueAtVarAssignmentPosition(BoogieVar bv, int index, Expression value) {
		assert index >= -1;
		assert index == -1 || isReAssigned(bv, index) : "oldVar in procedure where it is not modified?";
		Map<Integer, Expression> pos2value = m_var2pos2value.get(bv);
		if (pos2value == null) {
			pos2value = new HashMap<Integer, Expression>();
			m_var2pos2value.put(bv, pos2value);
		}
		assert !pos2value.containsKey(index);
		pos2value.put(index, value);
	}

	public void setBranchEncoders(int i, Map<TermVariable, Boolean> beMapping) {
		m_BranchEncoders[i] = beMapping;
	}

	private int indexWhereVarWasAssignedTheLastTime(BoogieVar bv, int pos) {
		assert pos >= -1;
		if (pos == -1) {
			return -1;
		}
		if (isReAssigned(bv, pos)) {
			return pos;
		}
		if (m_Trace.isInternalPosition(pos) || m_Trace.isCallPosition(pos)) {
			return indexWhereVarWasAssignedTheLastTime(bv, pos - 1);
		} else if (m_Trace.isReturnPosition(pos)) {
			if (bv.isGlobal() && !bv.isOldvar()) {
				return indexWhereVarWasAssignedTheLastTime(bv, pos - 1);
			} else {
				int callPos = m_Trace.getCallPosition(pos);
				return indexWhereVarWasAssignedTheLastTime(bv, callPos - 1);
			}
		} else {
			throw new AssertionError();
		}

	}

	public Map<BoogieVar, Expression> varValAtPos(int position) {
		Map<BoogieVar, Expression> result = new HashMap<BoogieVar, Expression>();
		Set<BoogieVar> vars = m_RelevantVariables.getForwardRelevantVariables()[position + 1];
		for (BoogieVar bv : vars) {
			if (bv.getTermVariable().getSort().isNumericSort()
					|| bv.getTermVariable().getSort().getRealSort().getName().equals("Bool")
					|| bv.getTermVariable().getSort().getRealSort().getName().equals("BitVec")) {
				int assignPos = indexWhereVarWasAssignedTheLastTime(bv, position);
				Expression value = m_var2pos2value.get(bv).get(assignPos);
				assert value != null;
				result.put(bv, value);
			}
		}
		return result;
	}

	private RcfgProgramExecution computeRcfgProgramExecution() {
		Map<Integer, ProgramState<Expression>> partialProgramStateMapping = 
				new HashMap<Integer, ProgramState<Expression>>();
		for (int i = 0; i < m_Trace.length(); i++) {
			Map<BoogieVar, Expression> varValAtPos = varValAtPos(i);
			Map<Expression, Collection<Expression>> variable2Values = 
					new HashMap<Expression, Collection<Expression>>();
			for (Entry<BoogieVar, Expression> entry : varValAtPos.entrySet()) {
				BoogieVar bv = entry.getKey();
				ILocation loc = m_SymbolTable.getAstNode(bv).getLocation();
				DeclarationInformation declInfo = 
						m_SymbolTable.getDeclarationInformation(bv);
				IType iType = entry.getKey().getIType();
				IdentifierExpression idExpr = new IdentifierExpression(
						loc, iType, entry.getKey().getIdentifier(), declInfo);
				Expression expr;
				if (bv instanceof BoogieOldVar) {
					expr = new UnaryExpression(loc, iType, UnaryExpression.Operator.OLD, idExpr);
				} else {
					expr = idExpr;
				}
				variable2Values.put(expr, Collections.singleton(entry.getValue()));
			}
			ProgramState<Expression> pps = new ProgramState<Expression>(variable2Values);
			partialProgramStateMapping.put(i, pps);
		}
		return new RcfgProgramExecution(m_Trace.lettersAsList(), partialProgramStateMapping, m_BranchEncoders);

	}

}
