package local.stalin.automata.petrinet;

import java.util.Collection;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.NestedWord;

public interface IPetriNet<S,C> {
	
	public Collection<S> getAlphabet(); 
	public ContentFactory<C> getContentFactory();
	
	public Collection<Place<S,C>> getPlaces();
	public Collection<ITransition<S,C>> getTransitions();
	
	public Collection<Place<S,C>> getInitialMarking();
	public Collection<Collection<Place<S,C>>> getAcceptingMarkings();
	
	public boolean isAccepting(Collection<Place<S,C>> marking);
	
	public boolean accepts(NestedWord<S> word);

}
