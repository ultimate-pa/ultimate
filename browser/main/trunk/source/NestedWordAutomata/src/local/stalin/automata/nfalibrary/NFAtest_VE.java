package local.stalin.automata.nfalibrary;

import java.util.ArrayList;

import local.stalin.automata.nfalibrary.NFA_VE;
import local.stalin.automata.nfalibrary.NFAedge;
import local.stalin.automata.nfalibrary.NFAstate_VE;
import local.stalin.automata.nfalibrary.StateName;

public class NFAtest_VE {
	
	public NFA_VE<Character, StateName> getSomeNFA(){
		//return getI3U3A2NFA();
		return getMyNFADeterminizationTest().determinize();
	}
	
	public NFA_VE<Character, StateName> getMyNFADeterminizationTest()
	{
		StateName q1name = new StateName("q1");
		NFAstate_VE<Character, StateName> q1 = new NFAstate_VE<Character, StateName>();
		q1.content = q1name;
		q1.isAccepting = false;
		
		StateName q2name = new StateName("q2");
		NFAstate_VE<Character, StateName> q2 = new NFAstate_VE<Character, StateName>();
		q2.content = q2name;
		q2.isAccepting = false;
		
		StateName q3name = new StateName("q3");
		NFAstate_VE<Character, StateName> q3 = new NFAstate_VE<Character, StateName>();
		q3.content = q3name;
		q3.isAccepting = true;
		
		NFAedge<Character, StateName> q1_q2 = new NFAedge<Character, StateName>();
		q1_q2.predecessor = q1;
		q1_q2.successor = q2;
		q1_q2.symbol = '0';
		
		NFAedge<Character, StateName> q1_q3 = new NFAedge<Character, StateName>();
		q1_q3.predecessor = q1;
		q1_q3.successor = q3;
		q1_q3.symbol = '0';
		
		q1.edges.add(q1_q2);
		q2.edges.add(q1_q2);
		q1.edges.add(q1_q3);
		q3.edges.add(q1_q3);
		
		ArrayList<Character> alphabet = new ArrayList<Character>();
		alphabet.add('0');
		alphabet.add('1');
		
		ArrayList<NFAstate_VE<Character, StateName>> initials = new ArrayList<NFAstate_VE<Character, StateName>>();
		initials.add(q1);
		
		ArrayList<NFAstate_VE<Character, StateName>> states = new ArrayList<NFAstate_VE<Character, StateName>>();
		states.add(q1);
		states.add(q2);
		states.add(q3);
		
		NFA_VE<Character, StateName> nfa = new NFA_VE<Character, StateName>();
		nfa.alphabet = alphabet;
		nfa.initialStates = initials;
		nfa.states = states;
		nfa.contentFactory = new StateNameFactory();
		
		//NFArun<Character, StateName> run = nfa.getAcceptingRun();
		
		return nfa;
		
	}
	
	//Returns the automaton of Aufgabe 2 from the following exercise sheet.
	//http://swt.informatik.uni-freiburg.de/teaching/winter-term-2009/informatik-iii-theoretische-informatik/ubungsaufgaben/uebung03.pdf
	public NFA_VE<Character, StateName> getI3U3A2NFA(){
		
		StateName q1name = new StateName("q1");
		NFAstate_VE<Character, StateName> q1 = new NFAstate_VE<Character, StateName>();
		q1.content = q1name;
		q1.isAccepting = true;
		
		StateName q2name = new StateName("q2");
		NFAstate_VE<Character, StateName> q2 = new NFAstate_VE<Character, StateName>();
		q2.content = q2name;
		
		NFAedge<Character, StateName> q1_a_q1 = new NFAedge<Character, StateName>();
		q1_a_q1.symbol = 'a';
		q1_a_q1.predecessor = q1;
		q1_a_q1.successor = q1;
		q1.edges.add(q1_a_q1);
		
		NFAedge<Character, StateName> q1_b_q2 = new NFAedge<Character, StateName>();
		q1_b_q2.symbol = 'b';
		q1_b_q2.predecessor = q2;
		q1_b_q2.successor = q2;
		q1.edges.add(q1_b_q2);
		
		NFAedge<Character, StateName> q2_a_q1 = new NFAedge<Character, StateName>();
		q2_a_q1.symbol = 'a';
		q2_a_q1.predecessor = q1;
		q2_a_q1.successor = q1;
		q2.edges.add(q2_a_q1);		

		NFAedge<Character, StateName> q2_b_q1 = new NFAedge<Character, StateName>();
		q2_b_q1.symbol = 'b';
		q2_b_q1.predecessor = q1;
		q2_b_q1.successor = q1;
		q2.edges.add(q2_b_q1);		
		
		ArrayList<Character> alphabet = new ArrayList<Character>();
		alphabet.add('a');
		alphabet.add('b');
		
		ArrayList<NFAstate_VE<Character, StateName>> initialStates = new ArrayList<NFAstate_VE<Character, StateName>>();
		initialStates.add(q1);
		
		NFA_VE<Character, StateName> nfa = new NFA_VE<Character,StateName>();
		nfa.alphabet = alphabet;
		nfa.contentFactory = new StateNameFactory();
		nfa.initialStates = initialStates;

		return nfa;
	}
}
