package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public interface IPetriNet<S,C> extends IAutomaton<S,C> {
	
	public Set<S> getAlphabet(); 
	public StateFactory<C> getStateFactory();
	
	public Collection<Place<S,C>> getPlaces();
	public Collection<ITransition<S,C>> getTransitions();
	
	public Marking<S,C> getInitialMarking();
	public Collection<Collection<Place<S,C>>> getAcceptingMarkings();
	
	public boolean isAccepting(Marking<S,C> marking);
	
	public boolean accepts(Word<S> word);
	
	public String sizeInformation();

}
