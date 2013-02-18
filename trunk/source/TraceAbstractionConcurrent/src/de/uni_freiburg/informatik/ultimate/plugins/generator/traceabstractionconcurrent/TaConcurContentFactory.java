package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TaConcurContentFactory extends PredicateFactory {

	public TaConcurContentFactory(Map<String, Map<String, ProgramPoint>> locNodes,
			AbstractCegarLoop abstractCegarLoop, SmtManager theory,
			TAPreferences taPrefs,
			boolean hoareAnnotation,
			boolean interprocedural) {
		super(theory, taPrefs);
		// TODO Auto-generated constructor stub
	}
	
	
	@Override
	public IPredicate getContentOnConcurrentProduct(IPredicate c1,
			IPredicate c2) {
		
		List<IPredicate> programPoints = new ArrayList<IPredicate>();
		ProdState result = ((ConcurrentSmtManager) m_SmtManager).getNewProdState(programPoints);
		if (c1 instanceof ProdState) {
			ProdState ps1 = (ProdState) c1;
			programPoints.addAll(ps1.getPredicates());
		}
		else {
			programPoints.add(c1);
		}
		if (((SPredicate) c2).getProgramPoint() == null) {
			assert (c2.getFormula() != null);
//			result.and(m_Theory, (Predicate) c2);
		}
		programPoints.add(c2); 
		return result;
	}



	@Override
	public IPredicate getContentOnPetriNet2FiniteAutomaton(
			Marking<?, IPredicate> marking) {
		LinkedList<IPredicate> programPoints = new LinkedList<IPredicate>();
		for (Place<?, IPredicate> place : marking) {
			programPoints.add(place.getContent());
		}
		return ((ConcurrentSmtManager) m_SmtManager).getNewProdState(programPoints);
	}
	



	@Override
	public IPredicate finitePrefix2net(Condition<?, IPredicate> c) {
		ProgramPoint pp = ((ISLPredicate) c.getPlace().getContent()).getProgramPoint();
		return super.m_SmtManager.newDontCarePredicate(pp);
	}
	

}
