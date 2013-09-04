package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class UnsatCore2Conjuncts extends TraceWithFormulas<Map<Term,Term>> {

	public UnsatCore2Conjuncts(NestedWord<CodeBlock> nestedWord) {
		super(nestedWord);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Set<Integer> callPositions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Map<Term, Term> getFormulaFromValidNonCallPos(int i) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Map<Term, Term> getLocalVarAssignmentFromValidPos(int i) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Map<Term, Term> getGlobalVarAssignmentFromValidPos(int i) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Map<Term, Term> getOldVarAssignmentFromValidPos(int i) {
		// TODO Auto-generated method stub
		return null;
	}
	

}
