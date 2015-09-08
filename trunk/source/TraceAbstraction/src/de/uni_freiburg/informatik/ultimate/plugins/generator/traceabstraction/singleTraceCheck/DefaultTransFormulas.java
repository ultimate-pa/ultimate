/*
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

import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class DefaultTransFormulas extends NestedFormulas<TransFormula, IPredicate> {
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final boolean m_WithBranchEncoders;
	
	
	
	public ModifiableGlobalVariableManager getModifiableGlobalVariableManager() {
		return m_ModifiableGlobalVariableManager;
	}

	public DefaultTransFormulas(NestedWord<CodeBlock> nestedWord, 
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			boolean withBranchEncoders) {
		super(nestedWord, pendingContexts);
		super.setPrecondition(precondition);
		super.setPostcondition(postcondition);
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_WithBranchEncoders = withBranchEncoders;
	}
	
	public boolean hasBranchEncoders() {
		return m_WithBranchEncoders;
	}
	
	@Override
	protected TransFormula getFormulaFromValidNonCallPos(int i) {
		CodeBlock cb = super.getTrace().getSymbolAt(i);
		if (m_WithBranchEncoders) {
			return cb.getTransitionFormulaWithBranchEncoders();
		} else {
			return cb.getTransitionFormula();
		}
	}

	@Override
	protected TransFormula getLocalVarAssignmentFromValidPos(int i) {
		CodeBlock cb = super.getTrace().getSymbolAt(i);
		assert ((cb instanceof Call) || (cb instanceof InterproceduralSequentialComposition)); 
		return cb.getTransitionFormula();
	}

	@Override
	protected TransFormula getGlobalVarAssignmentFromValidPos(int i) {
		String calledProcedure = getCalledProcedure(i);
		return m_ModifiableGlobalVariableManager.getGlobalVarsAssignment(calledProcedure);

	}

	@Override
	protected TransFormula getOldVarAssignmentFromValidPos(int i) {		
		String calledProcedure = getCalledProcedure(i);
		return m_ModifiableGlobalVariableManager.getOldVarsAssignment(calledProcedure);
	}
	
	/**
	 * TODO: return set of all pending calls in case of InterproceduralSequentialComposition
	 */
	private String getCalledProcedure(int i) {
		CodeBlock cb = super.getTrace().getSymbolAt(i);
		assert ((cb instanceof Call) || (cb instanceof InterproceduralSequentialComposition) 
				|| (cb instanceof Return)); 
		if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException("not yet implemented");
			// collect all pending calls use modifiable globals of all
		}
		
		Call call;
		if (cb instanceof Return) {
			call = ((Return) cb).getCorrespondingCall();
		} else if (cb instanceof Call) {
			call = (Call) cb;
		} else {
			throw new UnsupportedOperationException("neither call nor return");
		}
		String calledProcedure = call.getCallStatement().getMethodName();
		return calledProcedure;
	}


}
