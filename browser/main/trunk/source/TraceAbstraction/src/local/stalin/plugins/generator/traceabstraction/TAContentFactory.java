package local.stalin.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.Pair;
import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Theory;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.RStateFormula;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;

public class TAContentFactory extends ContentFactory<IProgramState> {
	
	protected Map<String,Map<String,LocNode>> m_locNodes;
	protected CegarLoop m_CegarLoop;
	protected Theory m_Theory;
	final protected TAPreferences m_TaPref;
 	
	public TAContentFactory(Map<String,Map<String,LocNode>> locNodes,
							CegarLoop cegarLoop,
							Theory theory,
							TAPreferences taPrefs,
							boolean hoareAnnotation,
							boolean interprocedural) {
		m_locNodes = locNodes;
		m_CegarLoop = cegarLoop;
		m_TaPref = taPrefs;
		m_Theory = theory;
	}
	

	
	public IProgramState createContentOnIntersection(IProgramState c1, IProgramState c2) {
		if (m_TaPref.computeHoareAnnotation()) {
			if (m_TaPref.interprocedural()) {
				if (c2.isTrue()) {
					return c1;
				}
				else {
					RStateFormula sf1 = (RStateFormula) c1;
					RStateFormula sf2 = (RStateFormula) c2;
					RStateFormula sf = sf1.and(m_Theory, sf2);
					sf.createIterationFormulas(sf1.getIterationFormulas());
//					assert (!sf2.getFormulas().keySet().isEmpty());
					sf.getIterationFormulas().put(m_CegarLoop.m_Iteration, sf2.getFormulas());
					return sf;
				}
			}
			else {
				StateFormula sf1 = (StateFormula) c1;
				StateFormula sf2 = (StateFormula) c2;
				return sf1.and(m_Theory, sf2);
			}
		}
		else {
			return c1;
		}
	}
			
			
//		Map<StateFormula, Set<StateFormula>> oldStatePairConjunction = 
//				oldAbstraction.getStatePairConjunction();
//		
//		if (m_TaPref.interprocedural()) {
//			RState detInterpolantAutomaton = (RState) c2;
//		Map<StateFormula, Set<StateFormula>> iAStatePairConjunction = 
//				detInterpolantAutomaton.getStatePairConjunction();
//		for (StateFormula caller : oldStatePairConjunction.keySet()) {
//			for (StateFormula callee : oldStatePairConjunction.get(caller)) {
//				newAbstraction.addPair(caller, callee);
//			}
//		}
//		for (StateFormula caller : iAStatePairConjunction.keySet()) {
//			for (StateFormula callee : iAStatePairConjunction.get(caller)) {
//				newAbstraction.addPair(caller, callee);
//			}
//		}
//		}

	
	
	public IProgramState createContentOnDeterminization(Collection<Pair<IProgramState, IProgramState>> cPairList) {
		if (m_TaPref.computeHoareAnnotation()) {
			if (m_TaPref.interprocedural()) {
				RStateFormula conjunction = new RStateFormula(m_Theory);
				for (Pair<IProgramState, IProgramState> pair : cPairList) {
					IProgramState caller = pair.fst;
					assert (caller != null);
					IProgramState current = pair.snd;
					assert (current != null);
					conjunction.add(m_Theory, caller, current);
				}
//				FIXME: This was wrong - use false instead?
				if (cPairList.isEmpty()) {
					conjunction.add(m_Theory, 
							StateFormula.trueStateFormula(), 
							StateFormula.trueStateFormula());
				}
				return conjunction;
			}
			else {
				StateFormula conjunction = new StateFormula(null);
				for (Pair<IProgramState, IProgramState> pair : cPairList) {
					StateFormula sf = (StateFormula) pair.snd;
					conjunction = conjunction.and(m_Theory, sf);
				}
				return conjunction;
			}
		}
		else {
			return null;
		}
	}
	
	public IProgramState createSinkStateContent() {

		if (m_TaPref.computeHoareAnnotation()) {
			if (m_TaPref.interprocedural()) {
				return StateFormula.trueStateFormula();
			}
			else {
			 	return StateFormula.trueStateFormula();
			}
		}
		else {
			return null;
		}
	}
	
	@Override
	public IProgramState createEmptyStackContent(){
		if (m_TaPref.computeHoareAnnotation()) {
			Formula emptyStack = 
				m_Theory.atom(m_Theory.createFormulaVariable("emptyStack"));
			return new StateFormula(emptyStack,new HashSet(0),new HashSet(0));

		}
		else {
			return null;
		}
	}
}
