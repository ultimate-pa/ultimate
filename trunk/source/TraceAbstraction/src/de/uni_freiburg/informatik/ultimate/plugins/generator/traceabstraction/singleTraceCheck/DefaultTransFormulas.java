package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class DefaultTransFormulas extends TraceWithFormulas<TransFormula, IPredicate> {
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	private final Set<Integer> m_CallPositions;
	
	public DefaultTransFormulas(NestedWord<CodeBlock> nestedWord, 
			IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager) {
		super(nestedWord, precondition, postcondition, pendingContexts);
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		m_CallPositions = super.getTrace().computeCallPositions();
	}
	
	@Override
	public Set<Integer> callPositions() {
		return m_CallPositions;
	}

	@Override
	protected TransFormula getFormulaFromValidNonCallPos(int i) {
		CodeBlock cb = super.getTrace().getSymbolAt(i); 
		return cb.getTransitionFormula();
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
		assert ((cb instanceof Call) || (cb instanceof InterproceduralSequentialComposition)); 
		if (cb instanceof InterproceduralSequentialComposition) {
			throw new UnsupportedOperationException("not yet implemented");
			// collect all pending calls use modifiable globals of all
		}
		String calledProcedure = ((Call) cb).getCallStatement().getMethodName();
		return calledProcedure;
	}



	



}
