package local.stalin.automata.nfalibrary;

import java.util.Set;
import java.util.TreeSet;

public class NFAtest_VM {
	
	public NFA_VM<Character, StateName> getSomeNFA(){
		NFA_VM<Character, StateName> nfa = getMinimizedTest();
		nfa.minimize();
		//NFA_VM<Character, StateName> nfa = getDeterminizeTest();
		//nfa.determinize();
		//NFA_VM<Character, StateName> nfa = getI3U2A1NFA();
		//NFA_VM<Character, StateName> nfa = getI3U2A1NFA().intersect(getI3U3A2NFA());
		
		return nfa;
	}
	
	//Returns the automaton of Aufgabe 1 from the following exercise sheet.
	//http://swt.informatik.uni-freiburg.de/teaching/winter-term-2009/informatik-iii-theoretische-informatik/ubungsaufgaben/uebung02.pdf
	public NFA_VM<Character, StateName> getI3U2A1NFA() {
		// Accepts words with an 'a' as 3rd character from the right
		
		NFA_VM<Character,StateName> nfa = new NFA_VM<Character, StateName>(new StateNameFactory());
		
		NFAstate_VM<Character, StateName> q0 = nfa.addState(true, false, new StateName("q0"));
		NFAstate_VM<Character, StateName> q1 = nfa.addState(false, false, new StateName("q1"));
		NFAstate_VM<Character, StateName> q2 = nfa.addState(false, false, new StateName("q2"));
		NFAstate_VM<Character, StateName> q3 = nfa.addState(false, true, new StateName("q3"));
		
		nfa.addTransition(q0, 'a', q0);
		nfa.addTransition(q0, 'b', q0);
		nfa.addTransition(q0, 'a', q1);
		nfa.addTransition(q1, 'a', q2);
		nfa.addTransition(q1, 'b', q2);
		nfa.addTransition(q2, 'a', q3);
		nfa.addTransition(q2, 'b', q3);
		
		return nfa;
	}
	
	//Returns the automaton of Aufgabe 2 from the following exercise sheet.
	//http://swt.informatik.uni-freiburg.de/teaching/winter-term-2009/informatik-iii-theoretische-informatik/ubungsaufgaben/uebung03.pdf
	public NFA_VM<Character, StateName> getI3U3A2NFA() {
		// Accepts words that don't end with an odd number of 'b's
		
		NFA_VM<Character,StateName> nfa = new NFA_VM<Character, StateName>(new StateNameFactory());
		
		NFAstate_VM<Character, StateName> q1 = nfa.addState(true, true, new StateName("q1"));
		NFAstate_VM<Character, StateName> q2 = nfa.addState(false, false, new StateName("q2"));
		
		nfa.addTransition(q1, 'a', q1);
		nfa.addTransition(q1, 'b', q2);
		nfa.addTransition(q2, 'a', q1);
		nfa.addTransition(q2, 'b', q1);
		
		return nfa;
	}
	
	public NFA_VM<Character, StateName> getMinimizedTest(){
		NFAstate_VM<Character, StateName> q0, q1, q2, q3, q4;
		
		q0 = new NFAstate_VM<Character, StateName>();
		q0.content = new StateName("qo");
		q1 = new NFAstate_VM<Character, StateName>();
		q1.content = new StateName("q1");
		q2 = new NFAstate_VM<Character, StateName>();
		q2.content = new StateName("q2");
		q3 = new NFAstate_VM<Character, StateName>();
		q3.content = new StateName("q3");
		q4 = new NFAstate_VM<Character, StateName>();
		q4.content = new StateName("q4");
		q4.isAccepting = true;
		
		q0.addTransition('0', q1);
		q0.addTransition('1', q2);
		q1.addTransition('0', q4);
		q1.addTransition('1', q2);
		q2.addTransition('0', q3);
		q2.addTransition('1', q2);
		q3.addTransition('0', q4);
		q3.addTransition('1', q0);
		q4.addTransition('0', q4);
		q4.addTransition('1', q4);
		
		Set<Character> alphabet = new TreeSet<Character>();
		alphabet.add('0');
		alphabet.add('1');
		
		NFA_VM<Character, StateName> nfa = new NFA_VM<Character, StateName>(new StateNameFactory(), alphabet);
		
		nfa.initialStates.add(q0);
		nfa.allStates.add(q0);
		nfa.allStates.add(q1);
		nfa.allStates.add(q2);
		nfa.allStates.add(q3);
		nfa.allStates.add(q4);
		
		return nfa;
	}
	
	public NFA_VM<Character, StateName> getDeterminizeTest(){
		NFAstate_VM<Character, StateName> q0,q1,q2,q3;
		
		q0 = new NFAstate_VM<Character, StateName>();
		q0.content = new StateName("q0");
		q1 = new NFAstate_VM<Character, StateName>();
		q1.content = new StateName("q1");
		q2 = new NFAstate_VM<Character, StateName>();
		q2.content = new StateName("q2");
		q3 = new NFAstate_VM<Character, StateName>();
		q3.content = new StateName("q3");
		q3.isAccepting = true;
		
		q0.addTransition('a', q0);
		q0.addTransition('a', q1);
		q0.addTransition('b', q0);
		q0.addTransition('c', q0);
		q1.addTransition('b', q2);
		q2.addTransition('a', q3);
		q3.addTransition('a', q3);
		q3.addTransition('b', q3);
		q3.addTransition('c', q3);
		
		Set<Character> alphabet = new TreeSet<Character>();
		alphabet.add('a');
		alphabet.add('b');
		alphabet.add('c');
		
		NFA_VM<Character, StateName> nfa = new NFA_VM<Character, StateName>(new StateNameFactory(), alphabet);
		
		nfa.initialStates.add(q0);
		nfa.allStates.add(q0);
		nfa.allStates.add(q1);
		nfa.allStates.add(q2);
		nfa.allStates.add(q3);
		
		return nfa;
	}
	
}
