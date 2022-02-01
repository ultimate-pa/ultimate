package de.uni_freiburg.informatik.ultimate.automata.nestedword;

//in order to represent generalized Buchi nested word automata
public interface IGeneralizedNestedWordAutomaton<LETTER, STATE> 
         extends INestedWordAutomaton<LETTER, STATE>, IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE>{

}
