package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

public abstract class StateFactory<STATE> {
	
	public STATE intersection(STATE s1, STATE s2) {
		return null;
	}
	
	public STATE intersectBuchi(STATE s1, STATE s2, int track) {
		return intersection(s1, s2);
	}
	
	public STATE determinize(Map<STATE,Set<STATE>> down2up) {
		return null;
	}
	
	public STATE createSinkStateContent() {
		return null;
	}
	
	public STATE createEmptyStackState() {
		return null;
	}

	public STATE getContentOnPetriNet2FiniteAutomaton(
			Marking<?, STATE> marking) {
		return null;
	}
	
	public STATE getContentOnConcurrentProduct(STATE c1, STATE c2) {
		return intersection(c1, c2);
	}
	
	public STATE getWhiteContent(STATE c) {
		return c;
	}
	
	public STATE getBlackContent(STATE c) {
		return c;
	}
	
	public STATE buchiComplementFKV(BuchiComplementFKV<?, STATE>.LevelRankingState compl) {
		return null;
	}
	
	public STATE complementBuchiDeterministicNonFinal(STATE c) {
		return null;
	}
	
	public STATE complementBuchiDeterministicFinal(STATE c) {
		return null;
	}
	
//	public void annouceNwaStateRemoval(INestedWordAutomaton<?, Content> nwa, Content down, Content up) {
//		
//	}
	
	public STATE minimize(Collection<STATE> states) {
		return null;	
	}

	public STATE createDoubleDeckerContent(STATE down, STATE up) {
		return null;
	}
	
	public STATE constructBuchiSVWState(Integer stateNb, Integer tmaNb) {
		return null;
	}
	
	public STATE finitePrefix2net(Condition<?, STATE> c) {
		return null;
	}
	
	public STATE senwa(STATE entry, STATE state) {
		return null;
	}

}
