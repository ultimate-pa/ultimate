package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.DestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class AnnotateAndAsserterConjuncts extends AnnotateAndAsserter {
	
	TraceWithFormulas<TransFormula, IPredicate> m_Original;

	public AnnotateAndAsserterConjuncts(SmtManager smtManager, NestedSsa nestedSSA, 
			NestedWord<CodeBlock> trace) {
		super(smtManager, nestedSSA, trace);
	}

	@Override
	protected Term annotateAndAssertPrecondition() {
		Term original = m_Original.getPrecondition().getFormula();
		Term[] originalConjuncts = DestructiveEqualityResolution.getConjuncts(original);
		Term indexed = m_SSA.getPrecondition();
		Term[] indexedConjuncts = DestructiveEqualityResolution.getConjuncts(indexed);
		assert originalConjuncts.length == indexedConjuncts.length;
		for (int i=0; i<originalConjuncts.length; i++) {
			//TODO:
		}
		return null;
	}

	@Override
	protected Term annotateAndAssertPostcondition() {
		// TODO Auto-generated method stub
		return super.annotateAndAssertPostcondition();
	}

	@Override
	protected Term annotateAndAssertNonCall(int position) {
		// TODO Auto-generated method stub
		return super.annotateAndAssertNonCall(position);
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntCall(int position) {
		// TODO Auto-generated method stub
		return super.annotateAndAssertLocalVarAssignemntCall(position);
	}

	@Override
	protected Term annotateAndAssertGlobalVarAssignemntCall(int position) {
		// TODO Auto-generated method stub
		return super.annotateAndAssertGlobalVarAssignemntCall(position);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntCall(int position) {
		// TODO Auto-generated method stub
		return super.annotateAndAssertOldVarAssignemntCall(position);
	}

	@Override
	protected Term annotateAndAssertPendingContext(int positionOfPendingContext) {
		// TODO Auto-generated method stub
		return super.annotateAndAssertPendingContext(positionOfPendingContext);
	}

	@Override
	protected Term annotateAndAssertLocalVarAssignemntPendingContext(
			int positionOfPendingReturn) {
		// TODO Auto-generated method stub
		return super
				.annotateAndAssertLocalVarAssignemntPendingContext(positionOfPendingReturn);
	}

	@Override
	protected Term annotateAndAssertOldVarAssignemntPendingContext(
			int positionOfPendingReturn) {
		// TODO Auto-generated method stub
		return super
				.annotateAndAssertOldVarAssignemntPendingContext(positionOfPendingReturn);
	}
	
	

}
