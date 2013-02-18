package local.stalin.automata.petrinet.jan;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.Place;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class PetriNet<Symbol, Content> implements IPetriNetJan<Symbol, Content>{

	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private Collection<Symbol> m_alphabet;
	private Collection<Place<Symbol, Content>> m_places;
	private Collection<Transition<Symbol, Content>> m_transitions;
	private Collection<Place<Symbol, Content>> m_initialMarking;
	private Collection<Collection<Place<Symbol, Content>>> m_acceptingMarkings;
	private ContentFactory<Content> m_contentFactory;

	/**
	 * Copy constructor.
	 * 
	 * @param petriNet The instance of PetriNet to copy.
	 */
	public PetriNet(IPetriNetJan<Symbol, Content> petriNet){
		
		this.m_contentFactory = petriNet.getContentFactory();
		
		this.m_alphabet = new HashSet<Symbol>(petriNet.getAlphabet());
		
		this.m_places = 
			//new HashSet<Place<Symbol, Content>>(petriNet.getPlaces());
			new HashSet<Place<Symbol, Content>>();
		HashMap<Place<Symbol, Content>, Place<Symbol, Content>> 
		oldPlace2newPlace = 
			new HashMap<Place<Symbol, Content>, Place<Symbol, Content>>();
		for(Place<Symbol, Content> oldPlace : petriNet.getPlaces()){
			
			oldPlace2newPlace.put(
					oldPlace, 
					new Place<Symbol, Content>(oldPlace.getContent()));
		}
			
		
		this.m_transitions =
//			= new HashSet<ITransition<Symbol, Content>>(
//					petriNet.getTransitions());
			new HashSet<Transition<Symbol, Content>>();
		HashMap<ITransition<Symbol, Content>, Transition<Symbol, Content>>
		oldTransition2newTransition = 
			new HashMap<ITransition<Symbol, Content>, 
						Transition<Symbol, Content>>();
		for(ITransition<Symbol, Content> oldTransition : 
			petriNet.getTransitions()){
			
			oldTransition2newTransition.put(oldTransition, 
					new Transition<Symbol, Content>(oldTransition.getSymbol()));
		}
		
		for(Place<Symbol, Content> oldPlace : petriNet.getPlaces()){
			
			for(ITransition<Symbol, Content> oldSucc : 
				oldPlace.getSuccessors()){
				
				oldPlace2newPlace.get(oldPlace).addSuccessor(
						oldTransition2newTransition.get(oldSucc));
			}
			
			for(ITransition<Symbol, Content> oldPre :
				oldPlace.getPredecessors()){
				
				oldPlace2newPlace.get(oldPlace).addPredecessor(
						oldTransition2newTransition.get(oldPre));
			}
		}
		
		for(ITransition<Symbol, Content> oldTransition : 
			petriNet.getTransitions()){
			
			for(Place<Symbol, Content> oldSucc : 
				oldTransition.getSuccessors()){
				
				oldTransition2newTransition.get(oldTransition).
				addSuccessorPlace(oldPlace2newPlace.get(oldSucc));
			}
			
			for(Place<Symbol, Content> oldPre :
				oldTransition.getPredecessors()){
				
				oldTransition2newTransition.get(oldTransition).
				addPredecessorPlace(oldPlace2newPlace.get(oldPre));
			}
		}
		
		for(Place<Symbol, Content> keyForNewPlace : oldPlace2newPlace.keySet()){
		
			m_places.add(oldPlace2newPlace.get(keyForNewPlace));
		}
		
		for(ITransition<Symbol, Content> keyForNewTransition : 
			oldTransition2newTransition.keySet()){
			
			m_transitions.add(
					oldTransition2newTransition.get(keyForNewTransition));
		}
		
		this.m_initialMarking = 
			//new HashSet<Place<Symbol, Content>>(petriNet.getInitialMarking());
			new HashSet<Place<Symbol, Content>>();
		for(Place<Symbol, Content> initialPlace : 
			petriNet.getInitialMarking()){
			
			m_initialMarking.add(oldPlace2newPlace.get(initialPlace));
		}
			
		
		this.m_acceptingMarkings = 
			new HashSet<Collection<Place<Symbol, Content>>>();
		for(Collection<Place<Symbol, Content>> acceptingMarking : 
				petriNet.getAcceptingMarkings()){
			
//			this.m_acceptingMarkings.add(new HashSet<Place<Symbol, Content>>(
//					acceptingMarking));
			HashSet<Place<Symbol, Content>> newAcceptingMarking =
				new HashSet<Place<Symbol, Content>>();
			for(Place<Symbol, Content> acceptingPlace : acceptingMarking)
				newAcceptingMarking.add(oldPlace2newPlace.get(acceptingPlace));
			
			this.m_acceptingMarkings.add(newAcceptingMarking);
		}
	}
	
	/**
	 * Takes an implementation of a nested word automaton and creates a 
	 * petri net which accepts the same language.
	 * 
	 * @param nwa An implementation of a nested word automaton.
	 */
	public PetriNet(INestedWordAutomaton<Symbol, Content> nwa, 
					ContentFactory<Content> contentFactory){
		
		this(new HashSet<Symbol>(nwa.getInternalAlphabet()), contentFactory);
			
		//add all places
		HashMap<Content, Place<Symbol, Content>> name2place = 
			new HashMap<Content, Place<Symbol, Content>>();
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			
			name2place.put(state.getContent(), addPlace(state.getContent()));
		}
			
		//add the initial marking
		m_initialMarking = new HashSet<Place<Symbol, Content>>();
		for(IState<Symbol, Content> state : nwa.getInitialStates()){
		
			m_initialMarking.add(name2place.get(state.getContent()));
		}
		
		//add the accepting markings
		m_acceptingMarkings = 
			new HashSet<Collection<Place<Symbol, Content>>>();
		HashSet<Place<Symbol, Content>> acceptingMarking = new 
			HashSet<Place<Symbol, Content>>();
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			
			if(state.isFinal()){
				
				acceptingMarking.add(name2place.get(state.getContent()));
			}
			m_acceptingMarkings.add(acceptingMarking);
		}
		
		//Add transitions
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			
			for(Symbol symbol : nwa.getInternalAlphabet()){
				
				if(state.getInternalSucc(symbol).size() > 0){
					
					Transition<Symbol, Content> transition = 
						new Transition<Symbol, Content>(symbol);
					transition.addPredecessorPlace(name2place.get(
							state.getContent()));
					
					for(IState<Symbol, Content> succ :
						state.getInternalSucc(symbol)){
						
						transition.addSuccessorPlace(name2place.get(
								succ.getContent()));
					}
					addTransition(transition);
				}
			}
		}
	}
	
	/**
	 * Creates a new petri net with the given alphabet.
	 * 
	 * @param alphabet The alphabet of the petri net.
	 */
	public PetriNet(Collection<Symbol> alphabet, 
					ContentFactory<Content> contentFactory){
		
		this.m_contentFactory = contentFactory;
		this.m_alphabet = alphabet;
		this.m_places = new HashSet<Place<Symbol,Content>>();
		this.m_transitions = new HashSet<Transition<Symbol,Content>>();
	}
	
	/**
	 *	Tests weather the petri net accepts a given word.
	 * 
	 * @param word The word.
	 * @return Weather the word is accepted or not.
	 */
	@Override
	public boolean accepts(NestedWord<Symbol> word) {

		return acceptsHelper(word, 
					new HashSet<Place<Symbol, Content>>(m_initialMarking), 0);
	}
	
	private boolean acceptsHelper(NestedWord<Symbol> word, 
			Collection<Place<Symbol, Content>> marking, int position){
		
		if(position < word.length()){
			
			Symbol symbol = word.getSymbolAt(position);

			if(!m_alphabet.contains(symbol)){
				
				return false;
			}
			
			HashSet<ITransition<Symbol, Content>> 
			activeTransitionsWithTheSymbol = 
				new HashSet<ITransition<Symbol, Content>>();
			
			//get all active transitions which are labeled with the next symbol
			for(Place<Symbol, Content> place : marking)
				for(ITransition<Symbol, Content> transition : 
					place.getSuccessors())
					if(isTransitionActivated(transition, marking) && 
							transition.getSymbol().equals(symbol))
						activeTransitionsWithTheSymbol.add(transition);
			
			// create next marking and call method recursively for every
			// transition 
			Collection<Place<Symbol, Content>> nextMarking;
			position++;
			boolean result = false;
			for(ITransition<Symbol, Content> transition : 
				activeTransitionsWithTheSymbol){
				
				//nextMarking = fireTransition(transition, marking);
				nextMarking = new HashSet<Place<Symbol, Content>>(marking);
				nextMarking = fireTransition(transition, nextMarking);
				
				if(acceptsHelper(word, nextMarking, position))
					result = true;
			}
			return result;
		}
		else{
			if(m_acceptingMarkings.contains(marking))
				return true;
			else
				return false;
		}
	}
	
	private Collection<Place<Symbol, Content>> 
		fireTransition(ITransition<Symbol, Content> transition, 
						Collection<Place<Symbol, Content>> marking){
		
		marking.removeAll(transition.getPredecessors());
		marking.addAll(transition.getSuccessors());
		
		return marking;
	}
	
	private boolean isTransitionActivated(ITransition<Symbol, 
			Content> transition, Collection<Place<Symbol, Content>> marking){
		
		return marking.containsAll(transition.getPredecessors());
	}
	
	//TODO concurrentProduct from two PetriNets

	/**
	 * Constructs a petri net which accepts the concurrent product of the 
	 * languages of this and a gives nested word automata with respect to a 
	 * set of synchronisation symbols.
	 * 
	 * @param nwa The nested word automata
	 */
	@Override
	public PetriNet<Symbol, Content> concurrentProduct(
			INestedWordAutomaton<Symbol, Content> nwa){
		
		if(nwa.getInitialStates().size() != 1)
			throw new IllegalArgumentException(
					"NWA must have exactly one initial state.");
		
		PetriNet<Symbol, Content> newNet = 
			new PetriNet<Symbol, Content>(this);
		
		//specify the intersection of the alphabets of the petri net and the
		//nwa as the set of synchronisation symbols
		Collection<Symbol> synchronisationSymbols = 
			new HashSet<Symbol>();
		synchronisationSymbols.addAll(m_alphabet);
		synchronisationSymbols.retainAll(nwa.getInternalAlphabet());		
		
		//Add the symbols of the nwa to the alphabet
		newNet.getAlphabet().addAll(nwa.getInternalAlphabet());
		
		//Add for every state in the nwa a place to the petri net
		HashMap<Content, Place<Symbol, Content>> name2place = 
			new HashMap<Content, Place<Symbol, Content>>();
		for(IState<Symbol, Content> state : nwa.getAllStates())
			name2place.put(state.getContent(), newNet.addPlace(state.getContent()));
		
		//Change the accepting markings
		HashSet<Collection<Place<Symbol, Content>>> newAcceptingMarkings = 
			new HashSet<Collection<Place<Symbol, Content>>>();
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			if(state.isFinal()){
				for(Collection<Place<Symbol, Content>> marking :
					newNet.getAcceptingMarkings()){
					HashSet<Place<Symbol, Content>> newMarking =
						new HashSet<Place<Symbol, Content>>(marking);
					newMarking.add(name2place.get(state.getContent()));
					newAcceptingMarkings.add(newMarking);
				}
			}
		}
		newNet.setAcceptingMarkings(newAcceptingMarkings);
		
		//FIXME Support concurrent product from nwa with more than one initial
		//state.
		
		//Change initial marking
		for(IState<Symbol, Content> state : nwa.getInitialStates())
			newNet.getInitialMarking().add(name2place.get(state.getContent()));
		
		//Add the transitions
		for(Symbol symbol : nwa.getInternalAlphabet()){
			
			//For every transitions with a symbol not in the synchronisation set 				
			for(IState<Symbol, Content> state : nwa.getAllStates()){
				for(IState<Symbol, Content> nextState : 
					state.getInternalSucc(symbol)){
					if(!synchronisationSymbols.contains(symbol) ||
							!(nwa.getInternalAlphabet().contains(symbol) &&
								newNet.getAlphabet().contains(symbol))){

						Transition<Symbol, Content> transition = 
							new Transition <Symbol, Content>(symbol);
						transition.addPredecessorPlace(
								name2place.get(state.getContent()));
						transition.addSuccessorPlace(
								name2place.get(nextState.getContent()));
						newNet.addTransition(transition);
					}
					else{
						HashSet<Transition<Symbol, Content>> newTransitions =
							new HashSet<Transition<Symbol, Content>>();
						for(ITransition<Symbol, Content> transition : 
							newNet.getTransitions()){
							if(transition.getSymbol().equals(symbol)){
								newTransitions.add((Transition<Symbol, Content>) transition);
							}
						}
						newNet.getTransitions().removeAll(newTransitions);
						for(Transition<Symbol, Content> transition : 
							newTransitions){
							transition.addPredecessorPlace(
									name2place.get(state.getContent()));
							transition.addSuccessorPlace(
									name2place.get(nextState.getContent()));
							name2place.get(
									nextState.getContent()).
									addPredecessor(transition);
							name2place.get(
									state.getContent()).
									addSuccessor(transition);
						}
						newNet.getTransitions().addAll(newTransitions);
					}
				}
			}
		}
		return newNet;
	}
	
	
	
	
	public void prefixProduct(INestedWordAutomaton<Symbol, Content> nwa){
		
		if(nwa.getInitialStates().size() != 1)
			throw new IllegalArgumentException(
					"NWA must have exactly one initial state.");
		
		//specify the intersection of the alphabets of the petri net and the
		//nwa as the set of synchronisation symbols
		Collection<Symbol> synchronisationSymbols = 
			new HashSet<Symbol>();
		synchronisationSymbols.addAll(m_alphabet);
		synchronisationSymbols.retainAll(nwa.getInternalAlphabet());		
		
		//Add the symbols of the nwa to the alphabet
		this.m_alphabet.addAll(nwa.getInternalAlphabet());
		
		HashSet<Place<Symbol, Content>> originalNetPlace = 
			new HashSet<Place<Symbol,Content>>(this.getPlaces());
		
		
		//Add for every state in the nwa a place to the petri net
		HashMap<Content, Place<Symbol, Content>> name2place = 
			new HashMap<Content, Place<Symbol, Content>>();
		for(IState<Symbol, Content> state : nwa.getAllStates())
			name2place.put(state.getContent(), addPlace(state.getContent()));
		
		//Change the accepting markings
		HashSet<Collection<Place<Symbol, Content>>> newAcceptingMarkings
			= new HashSet<Collection<Place<Symbol, Content>>>();
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			for(Collection<Place<Symbol, Content>> marking :
				m_acceptingMarkings){
				HashSet<Place<Symbol, Content>> newAcceptingMarking = 
					new HashSet<Place<Symbol, Content>>(marking);
				newAcceptingMarking.add(name2place.get(state.getContent()));
				newAcceptingMarkings.add(newAcceptingMarking);
			}
		}
		for(IState<Symbol, Content> state : nwa.getAllStates()){
			if(state.isFinal()){
				for (Place<Symbol,Content> place : originalNetPlace) {
					HashSet<Place<Symbol, Content>> newAcceptingMarking = 
						new HashSet<Place<Symbol, Content>>();
					newAcceptingMarking.add(place);
					newAcceptingMarking.add(name2place.get(state.getContent()));
					newAcceptingMarkings.add(newAcceptingMarking);
				}
			}
		}
		m_acceptingMarkings = newAcceptingMarkings;
		
		//FIXME Support concurrent product from nwa with more than one initial
		//state.
		
		//Change initial marking
		for(IState<Symbol, Content> state : nwa.getInitialStates())
			m_initialMarking.add(name2place.get(state.getContent()));
		
		//Add the transition 
		for(Symbol symbol : nwa.getInternalAlphabet()){
			
			//For every transitions with a symbol not in the synchronisation set 				
			for(IState<Symbol, Content> state : nwa.getAllStates()){
				for(IState<Symbol, Content> nextState : 
					state.getInternalSucc(symbol)){
					if(!synchronisationSymbols.contains(symbol) ||
							!(nwa.getInternalAlphabet().contains(symbol) &&
								this.m_alphabet.contains(symbol))){

						Transition<Symbol, Content> transition = 
							new Transition <Symbol, Content>(symbol);
						transition.addPredecessorPlace(
								name2place.get(state.getContent()));
						transition.addSuccessorPlace(
								name2place.get(nextState.getContent()));
						addTransition(transition);
					}
					else{
						for(Transition<Symbol, Content> transition : 
							this.m_transitions){
							if(transition.getSymbol().equals(symbol)){
								transition.addPredecessorPlace(
										name2place.get(state.getContent()));
								transition.addSuccessorPlace(
										name2place.get(nextState.getContent()));
								name2place.get(
										nextState.getContent()).
										addPredecessor(transition);
								name2place.get(
										state.getContent()).
										addSuccessor(transition);
							}
						}
					}
				}
			}
		}
	}
	
	
	public NestedRun<Symbol, Content> getAcceptedWord(){
		
		List<Collection<Place<Symbol, Content>>> run = 
			new ArrayList<Collection<Place<Symbol, Content>>>();
		
		NestedRun<Symbol, Content> nr = new NestedRun<Symbol, Content>(null);
		
		if(m_acceptingMarkings.contains(m_initialMarking)){
			
			run.add(m_initialMarking);
			return nr;
		}
		
		OccurrenceNet<Symbol, Content> finitePrefix = 
			(OccurrenceNet<Symbol, Content>) createFinitePrefix(false); 
		
		run = 
			finitePrefix.getAcceptingRun();
		nr = finitePrefix.getAcceptedWord();
		
		if(run == null)
			return null;
		
		return nr;
	}
	
	
	
	
	
	
	
	
	/**
	 * Adds a place with a given content to the petri net and returnes the 
	 * added place.
	 * Consider that the edges are given by the added transitions.
	 * 
	 * @param content The content of the place.
	 * @return The created place. 
	 */
	@Override
	public Place<Symbol, Content> addPlace(Content content) {
		
		Place<Symbol, Content> place = new Place<Symbol, Content>(content); 
		this.m_places.add(place);
		return place;
	}

	/**
	 * Adds a transition to the petri net and updates the edges of the places
	 * with respect to the edges given by the transition.
	 * 
	 * @param transition The transition to be added.
	 */
	@Override
	public void addTransition(Transition<Symbol, Content> transition) {
		
		this.m_transitions.add(transition);
		updatePlaces();
	}
	
	private void updatePlaces(){
		
		for(ITransition<Symbol, Content> trans : m_transitions){
		
			for(Place<Symbol, Content> pre : trans.getPredecessors()){
			
				pre.addSuccessor(trans);
			}
			for(Place<Symbol, Content> succ : trans.getSuccessors()){

				succ.addPredecessor(trans);
			}
		}
	}

	/**
	 * Sets the set of accepting markings
	 * 
	 * @param acceptingMarkings The set of accepting markings.
	 */
	@Override
	public void setAcceptingMarkings(
			Collection<Collection<Place<Symbol, Content>>> acceptingMarkings) {
		
		this.m_acceptingMarkings = acceptingMarkings;	
	}

	/**
	 * Sets the initial marking.
	 * 
	 * @param initialMarking The initial marking.
	 */
	@Override
	public void setInitialMarking(Collection<Place<Symbol, Content>> 
			initialMarking) {
		
		this.m_initialMarking = initialMarking;
	}
	
	/**
	 * Getter method for the initial marking.
	 * 
	 * @return The initial marking.
	 */
	@Override
	public Collection<Place<Symbol, Content>> getInitialMarking(){
		
		return m_initialMarking;
	}
	
	/**
	 * Getter method for the set of accepting markings.
	 * 
	 * @return The set of accepting markings.
	 */
	@Override
	public Collection<Collection<Place<Symbol, Content>>> 
			getAcceptingMarkings(){
		
		return m_acceptingMarkings;
	}

	/**
	 * Getter method for the alphabet.
	 * 
	 * @return The alphabet.
	 */
	@Override
	public Collection<Symbol> getAlphabet() {
		
		return m_alphabet;
	}

	/**
	 * Getter method for the places.
	 * 
	 * @return The places.
	 */
	@Override
	public Collection<Place<Symbol, Content>> getPlaces() {
		
		return m_places;
	}

	/**
	 * Getter method for the transitions.
	 * 
	 * @return The transitions.
	 */
	@Override
	public Collection<ITransition<Symbol, Content>> getTransitions() {
		ArrayList<ITransition<Symbol,Content>> result =
			new ArrayList<ITransition<Symbol,Content>>();
		result.addAll(m_transitions);
		return result;
	}
	
	/**
	 * Tests weather the petri net has an accepting run.
	 * 
	 * @return An accepted word or null if the petri net has no accepting run.
	 */
	@Override
	public List<Collection<Place<Symbol, Content>>> getAcceptedRun(){
		
		List<Collection<Place<Symbol, Content>>> run = 
			new ArrayList<Collection<Place<Symbol, Content>>>();
		
		if(m_acceptingMarkings.contains(m_initialMarking)){
			
			run.add(m_initialMarking);
			return run;
		}
		
		IOccurrenceNet<Symbol, Content> finitePrefix = 
			createFinitePrefix(false); 
		
		run = 
			finitePrefix.getAcceptingRun();
		
		if(run == null)
			return null;
		
		return run;
	}
	
	private IOccurrenceNet<Symbol, Content> createFinitePrefix(
			boolean createFullPrefix){

		//The queue which events can be added.
		PriorityQueue<IEvent<Symbol, Content>> queue = 
			new PriorityQueue<IEvent<Symbol, Content>>();
		
		//The resulting branching process.
		IOccurrenceNet<Symbol, Content> branchingProcess =
			new OccurrenceNet<Symbol, Content>(); 
		
		//Saves the just added Conditions.
		HashSet<ICondition<Symbol, Content>> justCreatedConditions = 
			new HashSet<ICondition<Symbol, Content>>();
		
		//Create conditions for the initial marking.
		for(Place<Symbol, Content> place : m_initialMarking)
			justCreatedConditions.add(branchingProcess.addCondition(place));
		branchingProcess.setInitialConditions(justCreatedConditions);
		
		queue.addAll(getPossibleExtensions(justCreatedConditions, 
										   branchingProcess));

		boolean done = false;
		if(m_acceptingMarkings.contains(m_initialMarking) && !createFullPrefix)
			done = true;
		else 
			done = false;
		
		while(!queue.isEmpty() && !done){
			
			IEvent<Symbol, Content> event = queue.poll();
			
			boolean conjunctionEmpty = true;
			
			Collection<IEvent<Symbol, Content>> localConfiguration = 
				event.getLocalConfiguration();
			
			for(IEvent<Symbol, Content> eventOfLocalCoEvent : 
				localConfiguration)
				if(branchingProcess.isCutOffEvent(eventOfLocalCoEvent))
					conjunctionEmpty = false;
			
			for(IEvent<Symbol, Content> cutOffEvent : 
				branchingProcess.getCutOffEvents())
				if(localConfiguration.contains(cutOffEvent))
					conjunctionEmpty = false;
			
			if(conjunctionEmpty){
				
				justCreatedConditions.clear();
				
				for(Place<Symbol, Content> place : 
					event.getTransition().getSuccessors())
					justCreatedConditions.add(
							branchingProcess.addCondition(place));

				for(ICondition<Symbol, Content> successor : 
					justCreatedConditions)
					event.addSuccessorCondition(successor);
				
				event.calculateRepresentedMarking();
				
				branchingProcess.addEvent(event);
		
				event.leadsToRepresentationOfAcceptingMarking(
						getRepresentationOfAcceptingMarking(
								event, 
								branchingProcess));

				if(event.getRepresentatedOfAcceptingMarking() != null && 
				   !createFullPrefix){
					
					branchingProcess.
						setToRepresentationOfAcceptingMarkingLeadingEvent(
								event);
					done = true;
				}
				
				//queue = queue U pe
				queue.addAll(getPossibleExtensions(justCreatedConditions,  
												   branchingProcess));
			}
		}
		
		return branchingProcess;
	}	
	
	/**
	 * Calculates the possible extensions of a given branching process.
	 * 
	 * @param justCreatedConditions The last conditions which have been created.
	 * @param place2Conditions A mapping which maps places of a petri net to 
	 * 						   conditions of its branching process. 
	 * @param branchingProcess The (incomplete) branching process.
	 * @return The possible extensions
	 */
	private Collection<IEvent<Symbol, Content>> getPossibleExtensions(
		Collection<ICondition<Symbol, Content>> justCreatedConditions,
		IOccurrenceNet<Symbol, Content> branchingProcess){
				
		Collection<IEvent<Symbol, Content>> possibleExtensions = 
			new HashSet<IEvent<Symbol, Content>>();
		
		Collection<ITransition<Symbol, Content>> possibleTransitions =
			new HashSet<ITransition<Symbol, Content>>();
		for(ICondition<Symbol, Content> condition : justCreatedConditions)
			for(ITransition<Symbol, Content> transition : 
				condition.getPlace().getSuccessors())
				possibleTransitions.add(transition);
		
		for(ITransition<Symbol, Content> transition : possibleTransitions){
			
			List<List<ICondition<Symbol, Content>>> possibleConditions = 
				new ArrayList<List<ICondition<Symbol, Content>>>();
			
			
			for(Place<Symbol, Content> place : 
				transition.getPredecessors()){
		
				if(branchingProcess.getPlace2Conditions().get(place) == null){

//					possibleExtensions.clear();TODO
//					return possibleExtensions;
					break;
				}
				
				possibleConditions.add(
						new ArrayList<ICondition<Symbol, Content>>(
						branchingProcess.getPlace2Conditions().get(place)));
			}
			if(possibleConditions.size() != transition.getPredecessors().size())
				continue;
			
			Collection<Collection<ICondition<Symbol, Content>>> coSets = 
				getCoSets(possibleConditions, branchingProcess);
			
			for(Collection<ICondition<Symbol, Content>> coSet : coSets){
				
				IEvent<Symbol, Content> possibeExtension = 
					new Event<Symbol, Content>(transition, coSet);
				
				if(!branchingProcess.isInOccurenceNet(possibeExtension)){
					
					possibleExtensions.add(possibeExtension);
				}
			}
		}
		
		return possibleExtensions;
	}
	
	private Collection<Collection<ICondition<Symbol, Content>>> getCoSets(
			List<List<ICondition<Symbol, Content>>> conditions,
			IOccurrenceNet<Symbol, Content> branchingProcess){
		
		Collection<Collection<ICondition<Symbol, Content>>> coSets = 
			new HashSet<Collection<ICondition<Symbol, Content>>>();

		int[] counter = new int[conditions.size()];
		int[] sizeOfCollections = new int[conditions.size()];
		
		for(int i = 0; i < conditions.size(); i++){
			
			counter[i] = 0;
			sizeOfCollections[i] = conditions.get(i).size();
		}
		
		Collection<ICondition<Symbol, Content>> checkedConditionSet;
		
		while(counter != null){
			
			checkedConditionSet = new HashSet<ICondition<Symbol, Content>>();
			
			for(int i = 0; i < counter.length; i++){
				
				checkedConditionSet.add(
						conditions.get(i).get(counter[i]));
			}
			
			if(isCoSet(checkedConditionSet, branchingProcess)){
				
				coSets.add(checkedConditionSet);
			}
	
			counter = increaseCounter(sizeOfCollections, counter);
		}
		
		return coSets;
	}
	
	/**
	 * Calculates if an event, labeled with a given transition leads to the
	 * representation of an accepting marking of the corresponding petri net.
	 * Returns the set of condition if an accepting one exists or null 
	 * otherwise.
	 */
	private Collection<ICondition<Symbol, Content>> 
		getRepresentationOfAcceptingMarking(
			IEvent<Symbol, Content> event,
			IOccurrenceNet<Symbol, Content> branchingProcess){
		
		Collection<Collection<Place<Symbol, Content>>> possibleMarkings =
			getForEventPossibleAcceptingMarkings(event, branchingProcess);
		
		possibleMarkings = getSetOfAllPlacesRepresentedMarkings(
				possibleMarkings, branchingProcess);
		
		for(Collection<Place<Symbol, Content>> marking : possibleMarkings){
			
			List<List<ICondition<Symbol, Content>>> possibleConditions = 
				getPossibleAcceptingConditionLists(marking, branchingProcess);	
			
			Collection<Collection<ICondition<Symbol, Content>>> 
				acceptingMarkingRepresentingConditionSet = 
					getCoSets(possibleConditions, branchingProcess);
			
			if(!acceptingMarkingRepresentingConditionSet.isEmpty()){
				
				Collection<ICondition<Symbol, Content>> result =  
					new HashSet<ICondition<Symbol, Content>>();
				
				for(Collection<ICondition<Symbol, Content>> coSet : 
					acceptingMarkingRepresentingConditionSet){
					
					result = coSet;
					
				}
				
				return result;
			}
		}
		
		return null;
	}
	
	/*
	 * Returns the for a given event the accepting markings which contain a
	 * place represented by a successor condition of the event.  
	 */
	private Collection<Collection<Place<Symbol, Content>>>
	getForEventPossibleAcceptingMarkings(IEvent<Symbol, Content> event, 
									 IOccurrenceNet<Symbol, Content> 
									 branchingProcess){
		
		Collection<Collection<Place<Symbol, Content>>> possibleMarkings = 
			new HashSet<Collection<Place<Symbol, Content>>>();
		
		for(Collection<Place<Symbol, Content>> marking : m_acceptingMarkings){
			
			for(Place<Symbol, Content> place : 
				event.getTransition().getSuccessors()){
			
				if(marking.contains(place)){
					possibleMarkings.add(marking);
				}
			}
		}
		
		return possibleMarkings;
	}
	
	/**
	 * Returns for a given set of accepting markings the set of accepting 
	 * markings where for every place in every marking a condition in the given
	 * branching process exists which represents the place.   
	 */
	private Collection<Collection<Place<Symbol, Content>>>
		getSetOfAllPlacesRepresentedMarkings(
			Collection<Collection<Place<Symbol, Content>>> possibleMarkings, 
			IOccurrenceNet<Symbol, Content> branchingProcess){
		
		//buffer to prevent CurrentModificationException
		Collection<Collection<Place<Symbol, Content>>> markingsToRemove = 
			new HashSet<Collection<Place<Symbol, Content>>>();
		
		for(Collection<Place<Symbol, Content>> marking : possibleMarkings){
			
			for(Place<Symbol, Content> place : marking){
				
				if(branchingProcess.getPlace2Conditions().get(place) == null){
					
					markingsToRemove.add(marking);
				}
			}
		}
		
		possibleMarkings.removeAll(markingsToRemove);
		
		return possibleMarkings;
	}
	
	/**
	 * Returns a list of lists of conditions where every list is the appearance 
	 * of a corresponding condition in the branching process.  
	 */
	private List<List<ICondition<Symbol, Content>>>
		getPossibleAcceptingConditionLists(
			Collection<Place<Symbol, Content>> possibleMarking, 
			IOccurrenceNet<Symbol, Content> branchingProcess){
		
		List<List<ICondition<Symbol, Content>>> conditionLists = 
			new ArrayList<List<ICondition<Symbol, Content>>>();
		
		List<ICondition<Symbol, Content>> conditionList;
		
		for(Place<Symbol, Content> place : possibleMarking){
			
			conditionList = new ArrayList<ICondition<Symbol, Content>>();

			if(branchingProcess.getPlace2Conditions().get(place) != null){
				
				conditionList.addAll(
						branchingProcess.getPlace2Conditions().get(place));
			}
			
			conditionLists.add(conditionList);
		}
		return conditionLists;
	}
	
	/*
	 * Increases a counter consisting of an array of integer.
	 * Returns null if the counter can´t be increased.
	 */
	private int[] increaseCounter(
			int[] sizeOfCollections,
			int[] counter){
		
		assert sizeOfCollections.length == counter.length : 
			"The arrays \"sizeOfCollections\" and \"counter\" must have the " +
			"same length.";
		
		for(int i = sizeOfCollections.length-1; i >= 0; i--){
			if(counter[i] < sizeOfCollections[i] - 1){
				counter[i]++;
				return counter;
			}
			else{
				counter[i] = 0;
			}
		}
		
		return null;
	}	

	private boolean isCoSet(Collection<ICondition<Symbol, Content>> set,
							IOccurrenceNet<Symbol, Content> branchingProcess){
		
		boolean result = true;
	
		for(ICondition<Symbol, Content> condition1 : set)
			for(ICondition<Symbol, Content> condition2 : set)
				if(!branchingProcess.inCoRelation(condition1, condition2))
					result = false;
		
	return result;
	}
		
	@Override
	public String toString() {		
		
		return "Petri Net " + "\n" +
			"Places: " + m_places + "\n" + 
			"Transitions: " + m_transitions + "\n" + 
			"Initial marking: " + m_initialMarking + "\n" + 
			"Accepting marking: " + m_acceptingMarkings;
	}

	@Override
	public IOccurrenceNet<Symbol, Content> getFinitePrefix() {
		
		return createFinitePrefix(false);
	}

	@Override
	public ContentFactory<Content> getContentFactory() {

		return m_contentFactory;
	}

	@Override
	public boolean isAccepting(Collection<Place<Symbol, Content>> marking) {
		if (getAcceptingMarkings().contains(marking)) {
			return true;
		}
		else {
			return false;
		}
	}
}