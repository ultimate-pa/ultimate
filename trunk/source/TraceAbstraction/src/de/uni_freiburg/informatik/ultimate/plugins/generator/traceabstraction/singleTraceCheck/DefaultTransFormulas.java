package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class DefaultTransFormulas extends TraceWithFormulas<TransFormula, IPredicate> {
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final Set<Integer> m_CallPositions;
	private final boolean m_WithBranchEncoders;
	
	public DefaultTransFormulas(NestedWord<CodeBlock> nestedWord, 
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			boolean withBranchEncoders) {
		super(nestedWord, precondition, postcondition, pendingContexts);
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_CallPositions = super.getTrace().getCallPositions();
		m_WithBranchEncoders = withBranchEncoders;
	}
	
	public boolean hasBranchEncoders() {
		return m_WithBranchEncoders;
	}
	
	@Override
	public Set<Integer> callPositions() {
		return m_CallPositions;
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
