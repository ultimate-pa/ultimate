package local.stalin.automata.nfalibrary;

import java.util.List;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.HashMap;

public class NFA_VE<Symbol, Content extends StateContent> {
	List<Symbol> alphabet;
	List<NFAstate_VE<Symbol,Content>> states;
	public List<NFAstate_VE<Symbol,Content>> initialStates;
	IStateContentFactory<Content> contentFactory;
	
	public NFA_VE()
	{
		alphabet = new ArrayList<Symbol>();
		states = new ArrayList<NFAstate_VE<Symbol,Content>>();
		initialStates = new ArrayList<NFAstate_VE<Symbol,Content>>();
	}
	
	private NFA_VE(NFA_VE<Symbol, Content> other){}
	
	public boolean accepts(List<Symbol> inputWord)
	{
		for(NFAstate_VE<Symbol,Content> beginning : initialStates)
		{
			if(accepts(inputWord, beginning))
				return true;
		}
		return false;
	}
	
	private boolean accepts(List<Symbol> inputWord, NFAstate_VE<Symbol,Content> beginning)
	{
		//wenn wir das komplette eingabewort verarbeitet haben, kann trivial entschieden werden,
		//ob das Wort akzeptiert wird oder nicht
		if(inputWord.size() == 0 && beginning.isAccepting())
			return true;
		else if(inputWord.size() == 0)
			return false;
		
		//ansonsten gehen wir f�r das erste Symbol aus dem Wort in einen Folgezustand und
		//schauen ob es f�r den Folgezustand und das Restwort ein Pfad zu einem
		//akzeptierenden Zustand gefunden werden kann (rekursiv)
		for(NFAedge<Symbol, Content> edge : beginning.edges)
		{
			if(edge.predecessor.equals(beginning) && inputWord.get(0).equals(edge.symbol))
			{
				inputWord.remove(0);
				if(accepts(inputWord ,edge.successor))
					return true;
			}
		}
		return false;
	}

	public NFArun<Symbol, Content> getAcceptingRun()
	{
		ArrayList<NFAstate_VE<Symbol,Content>> visited = new ArrayList<NFAstate_VE<Symbol,Content>>();
		ArrayList<NFAstate_VE<Symbol,Content>> toVisit = new ArrayList<NFAstate_VE<Symbol,Content>>();
		HashMap<NFAstate_VE<Symbol,Content>, NFAstate_VE<Symbol,Content>> wasExpandedBy = new HashMap<NFAstate_VE<Symbol,Content>, NFAstate_VE<Symbol,Content>>();
		NFAstate_VE<Symbol,Content> acceptingState = null;
		
		//F�ge alle Anfangszust�nde auf die zu Besuchen Liste hinzu
		
		for(NFAstate_VE<Symbol,Content> state : initialStates)
		{
			toVisit.add(state);
			for(NFAedge<Symbol, Content> edge : state.edges)
			{
				if(edge.predecessor.equals(state))
				{
					wasExpandedBy.put(edge.successor, edge.predecessor);
				}
			}
		}
		
		//geh solange die zu Besuchen Liste mit Breadth First Search durch, bis du einen akzeptierenden Zustand findest
		
		for(NFAstate_VE<Symbol,Content> state : toVisit)
		{
			visited.add(state);
			if(state.isAccepting())
			{
				acceptingState = state;
				break;
			}
			else
			{
				for(NFAedge<Symbol, Content> edge : state.edges)
				{
					if(edge.predecessor.equals(state))
					{
						if(!visited.contains(edge.successor))
						{
							toVisit.add(edge.successor);
							wasExpandedBy.put(edge.successor, edge.predecessor);
						}
					}
				}
			}
		}
		
		ArrayDeque<Symbol> newWord = new ArrayDeque<Symbol>();
		ArrayDeque<NFAstate_VE<Symbol,Content>> newStates = new ArrayDeque<NFAstate_VE<Symbol,Content>>();
		NFAstate_VE<Symbol,Content> current = acceptingState;
		
		//konstruiere den Run r�ckw�rts
		
		if(current == null)
			return null;
		
		if(initialStates.contains(current))
		{
			newStates.add(current);
		}
		
		while(!initialStates.contains(current))
		{
			newStates.addFirst(current);
			NFAstate_VE<Symbol,Content> pre = wasExpandedBy.get(current);
			for(NFAedge<Symbol, Content> edge : current.edges)
			{
				if(edge.predecessor.equals(pre) && edge.successor.equals(current))
				{
					newWord.addFirst(edge.symbol);
					break;
				}
			}
			current = pre;
		}
		
		ArrayList<Symbol> x1 = new ArrayList<Symbol>();
		ArrayList<INFAstate<Symbol,Content>> x2 = new ArrayList<INFAstate<Symbol,Content>>();
		
		for(Symbol s : newWord)
		{
			x1.add(s);
		}
		
		for(NFAstate_VE<Symbol,Content> s : newStates)
		{
			x2.add(s);
		}
		
		return new NFArun<Symbol, Content>(x1, x2);
	}
	
	NFA_VE<Symbol, Content> intersect(NFA_VE<Symbol, Content> automaton)
	{
		NFA_VE<Symbol, Content> result = this.minimize();

		for(Symbol s : automaton.alphabet)
			if(!result.alphabet.contains(s))
				result.alphabet.add(s);
		
		result.complement();
		automaton.complement();
		
		result.states.addAll(automaton.states);
		result.initialStates.addAll(automaton.initialStates);
		
		result.complement();
		
		result.minimize();
		return result;
	}
	
	NFA_VE<Symbol, Content> determinize()
	{
		
		ArrayList<NFAstate_VE<Symbol, Content>> toVisit = new ArrayList<NFAstate_VE<Symbol, Content>>();
		ArrayList<NFAstate_VE<Symbol, Content>> newStates = new ArrayList<NFAstate_VE<Symbol, Content>>();
		ArrayList<NFAstate_VE<Symbol, Content>> newInitials = new ArrayList<NFAstate_VE<Symbol, Content>>();
		ArrayList<NFAstate_VE<Symbol, Content>> newAccepting = new ArrayList<NFAstate_VE<Symbol, Content>>();
		//TreeMap<HashSet<NFAstate_VE<Symbol, Content>>, NFAstate_VE<Symbol, Content>> alreadyCreated = new TreeMap<HashSet<NFAstate_VE<Symbol, Content>>, NFAstate_VE<Symbol, Content>>(); 
		HashMap<HashSet<NFAstate_VE<Symbol, Content>>, NFAstate_VE<Symbol, Content>> alreadyCreated = new HashMap<HashSet<NFAstate_VE<Symbol, Content>>, NFAstate_VE<Symbol, Content>>(); 
		
		
		//Zuerst alle anfangszust�nde zu einem Zustand zusammenf�gen:
		
		NFAstate_VE<Symbol, Content> beginning = new NFAstate_VE<Symbol, Content>();
		ArrayList<Content> initial = new ArrayList<Content>();
		boolean accepting = false;
		for(NFAstate_VE<Symbol, Content> state : initialStates)
		{
			initial.add(state.getContent());
			if(state.isAccepting())
				accepting = true;
			for(NFAedge<Symbol, Content> edge : state.edges)
			{
				if(edge.predecessor.equals(state))
				{
					NFAedge<Symbol, Content> newEdge = new NFAedge<Symbol, Content>();
					newEdge.predecessor = beginning;
					newEdge.successor = edge.successor;
					newEdge.symbol = edge.symbol;
					beginning.edges.add(newEdge);
				}
			}
		}
		beginning.content = contentFactory.createContentOnDeterminization(initial);
		beginning.isAccepting = accepting;
		if(accepting)
			newAccepting.add(beginning);
		newInitials.add(beginning);
		
		toVisit.add(beginning);
		
		while(toVisit.size() != 0)
		{
			NFAstate_VE<Symbol, Content> current = toVisit.get(0);
			TreeMap<Symbol, ArrayList<NFAstate_VE<Symbol, Content>>> map = new TreeMap<Symbol, ArrayList<NFAstate_VE<Symbol, Content>>>();
			newStates.add(current);
			
			//Suche dir alle Folgezust�nde von current heraus und sortiere sie nach
			//den Symbolen, an den verbindenden Kanten
			for(NFAedge<Symbol, Content> edge : current.edges)
			{
				if(edge.predecessor.equals(current))
				{
					if(map.containsKey(edge.symbol))
					{
						map.get(edge.symbol).add(edge.successor);
					}
					else
					{
						map.put(edge.symbol, new ArrayList<NFAstate_VE<Symbol, Content>>());
						map.get(edge.symbol).add(edge.successor);
					}
				}
			}
			
			current.edges.clear();
			
			//F�ge alle Zust�nde, die von current aus durch das selbe Symbol erreicht werden
			//zu einem neuen Zustand zusammen
			for(Symbol symbol : map.keySet())
			{
				ArrayList<NFAstate_VE<Symbol, Content>> states = map.get(symbol);
				HashSet<NFAstate_VE<Symbol, Content>> stateList = new HashSet<NFAstate_VE<Symbol, Content>>(states);
				if(alreadyCreated.containsKey(stateList))
				{
					NFAstate_VE<Symbol, Content> nextState = alreadyCreated.get(stateList);
					NFAedge<Symbol, Content> tempEdge = new NFAedge<Symbol, Content>();
					tempEdge.predecessor = current;
					tempEdge.successor = nextState;
					tempEdge.symbol = symbol;
					
					nextState.edges.add(tempEdge);
					current.edges.add(tempEdge);
				}
				else
				{
					NFAstate_VE<Symbol, Content> newState = new NFAstate_VE<Symbol, Content>();
					ArrayList<Content> contents = new ArrayList<Content>();
					boolean accepting2 = false; 
					for(NFAstate_VE<Symbol, Content> state : states)
					{
						contents.add(state.getContent());
						if(state.isAccepting())
							accepting2 = true;
						for(NFAedge<Symbol, Content> edge : state.edges)
						{
							if(edge.predecessor.equals(state))
							{
								NFAedge<Symbol, Content> tempedge = new NFAedge<Symbol, Content>();
								tempedge.predecessor = newState;
								tempedge.successor = edge.successor;
								tempedge.symbol = edge.symbol;
								newState.edges.add(tempedge);
							}
						}
					}
					newState.content = contentFactory.createContentOnDeterminization(contents);
					newState.isAccepting = accepting2;
					
					NFAedge<Symbol, Content> tempEdge = new NFAedge<Symbol, Content>();
					tempEdge.predecessor = current;
					tempEdge.successor = newState;
					tempEdge.symbol = symbol;
					
					newState.edges.add(tempEdge);
					current.edges.add(tempEdge);
					
					newStates.add(newState);
					if(accepting2)
						newAccepting.add(newState);
				}
			}
			
			toVisit.remove(current);
		}
		
		NFA_VE<Symbol, Content> result = new NFA_VE<Symbol, Content>();
		result.alphabet = alphabet;
		result.initialStates = newInitials;
		result.states = newStates;
		result.contentFactory = contentFactory;
		return result; 
	}
	
	NFA_VE<Symbol, Content> complement()
	{
		NFA_VE <Symbol, Content> result = this.determinize();
		
		for(NFAstate_VE<Symbol, Content> state : result.states)
			state.isAccepting = !state.isAccepting;
		
		return result;
	}
	
	NFA_VE<Symbol, Content> minimize()
	{
		class Pair{
			NFAstate_VE<Symbol, Content> s1;
			NFAstate_VE<Symbol, Content> s2;
			boolean marked;
		}		
		ArrayList<Pair> pairs = new ArrayList<Pair>();
		
		NFA_VE <Symbol, Content> result = this.determinize();
	
		Pair pair = new Pair();
		for(NFAstate_VE<Symbol, Content> state : result.states){
		
			pair.s1 = state;

			//Ein Zustandspaar wird erzeugt 
			for(NFAstate_VE<Symbol, Content> state2 : result.states){
				if(pair.s1 != state2)
					pair.s2 = state2;
			}
		
			//Alle Zustandspaare {z,z'} werden markiert wo z exor z' ==  Startzustand
			if((pair.s1.isAccepting && !pair.s2.isAccepting) || (!pair.s1.isAccepting && pair.s2.isAccepting))
				pair.marked = true;
			else
				pair.marked = false;

			//Hinzuf�gen zur Liste der Zustandspaare
			pairs.add(pair);

		}
		
		//Markiere jedes Paar, wo ein Folgezustand f�r ein Symbol shcon markiert ist
		boolean changed = true;
		while(changed){
			changed = false;
			for(Pair p : pairs)
				for(NFAedge<Symbol, Content> edge : p.s1.edges)
					for(Pair p2 : pairs)
						if(edge.successor == p2.s1 || edge.successor == p2.s2)
							if(p2.marked){
								p.marked = true;
								changed = true;
							}
		}
		
		//Verschmelze alle nicht markierten Zust�nde.
		ArrayList<NFAstate_VE<Symbol, Content>> toMerge = new ArrayList<NFAstate_VE<Symbol, Content>>();
		result.alphabet = alphabet;
		result.contentFactory = contentFactory;
		result.states = null;
		result.initialStates = null;
		changed = true;
		for(Pair p : pairs){
			if(!p.marked){
				toMerge.add(p.s1);
				toMerge.add(p.s2);
				while(changed){
					changed = false;
					for(NFAstate_VE<Symbol, Content> state : toMerge)
						for(Pair p2 : pairs)
							if(!p2.marked && (p2.s1 == state || p2.s2 == state)){
								if(!toMerge.contains(p2.s1)){
									toMerge.add(p2.s1);
									changed = true;
								}
								if(!toMerge.contains(p2.s2)){
									toMerge.add(p2.s2);
									changed = true;
								}
								//geht das???
								pairs.remove(p2);
							}
				}
				NFAstate_VE<Symbol, Content> state = new NFAstate_VE<Symbol, Content>();
				ArrayList<Content> commonContent = new ArrayList<Content>();
				boolean initialState = false;
				for(NFAstate_VE<Symbol, Content> s : toMerge){
					if(s.isAccepting)
						state.isAccepting = true;
					
					for(NFAedge<Symbol, Content> edge : s.edges)
						state.edges.add(edge);
					
					if(initialStates.contains(s))
						initialState = true;
					
					commonContent.add(s.content);
				}
			
				state.content = contentFactory.createContentOnMinimization(commonContent);

				if(initialState)
					result.initialStates.add(state);
			
				result.states.add(state);
			}
		}
		
		return result;
	}
}