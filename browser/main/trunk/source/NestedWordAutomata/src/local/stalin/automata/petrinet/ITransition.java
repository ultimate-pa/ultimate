package local.stalin.automata.petrinet;

import java.util.Collection;


public interface ITransition<S,C> {
	public S getSymbol();
	public Collection<Place<S,C>> getPredecessors();
	public Collection<Place<S,C>> getSuccessors();
	
//	public 
//	
//	public interface Successors extends Iterable<IPlace> {
//		
//	}
}
