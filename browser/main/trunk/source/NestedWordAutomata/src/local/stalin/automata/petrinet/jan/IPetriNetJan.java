package local.stalin.automata.petrinet.jan;

import java.util.Collection;
import java.util.List;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.petrinet.IPetriNet;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;

public interface IPetriNetJan<Symbol, Content> extends IPetriNet<Symbol, Content> {
	
	public Place<Symbol, Content> addPlace(Content content);
	public void addTransition(Transition<Symbol, Content> transition);
	public void setInitialMarking(Collection<Place<Symbol, Content>> 
		initialMarking);
	public void setAcceptingMarkings(
		Collection<Collection<Place<Symbol, Content>>> acceptingMarkings);
	
	public Collection<Symbol> getAlphabet();
	public Collection<Place<Symbol, Content>> getPlaces();
	public Collection<Place<Symbol, Content>> getInitialMarking();
	public Collection<Collection<Place<Symbol, Content>>> 
		getAcceptingMarkings();
	public Collection<ITransition<Symbol, Content>> getTransitions();
	public ContentFactory<Content> getContentFactory();
	
	public boolean accepts(NestedWord<Symbol> word);
	public IPetriNetJan<Symbol, Content> concurrentProduct(
		INestedWordAutomaton<Symbol, Content> nwa); 
	/**
	 * @return An accepting run or null of no one exists.
	 */
	public List<Collection<Place<Symbol, Content>>> getAcceptedRun();
	/**
	 * @return The complete finite prefix.
	 */
	public IOccurrenceNet<Symbol,Content> getFinitePrefix();
}
