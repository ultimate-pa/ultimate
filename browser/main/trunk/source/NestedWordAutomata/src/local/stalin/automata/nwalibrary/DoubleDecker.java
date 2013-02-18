package local.stalin.automata.nwalibrary;

/**
 * Part of a NestedWordAutomatons configuration. up is the state in which
 * the automaton is. down is the state before the last call transition
 * that the automaton has taken.
 * <p>
 * For many algorithms (e.g. determinization) we do not have to use 
 * configurations (current state + stack) of the automaton, the DoubleDeckers
 * are sufficient. In 
 * "JACM2009 - Alur,Madhusudan - Adding nesting structure to words"
 * a DoubleDeckers is called "summary state", but to avoid clashes in variable
 * names I decided to use this name.
 *  
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class DoubleDecker<S,C> {
	private final IState<S,C> down;
	private final IState<S,C> up;
	private final int hashCode;
	
	public DoubleDecker(IState<S,C> down, IState<S,C> up) {
		this.down = down;
		this.up = up;
		this.hashCode = 
			3 * down.hashCode() + 5 * up.hashCode(); 
	}
	
	public IState<S, C> getDown() {
		return down;
	}


	public IState<S, C> getUp() {
		return up;
	}



	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof DoubleDecker) {
			DoubleDecker<S,C> summaryState = (DoubleDecker<S,C>) obj;
			return up.equals(summaryState.up) && 
							down.equals(summaryState.down);
		}
		else {
			return false;
		}
	}
	
	@Override
	public int hashCode() {
		return hashCode;
	}

	@Override
	public String toString() {
		return "Basement: " + down + "  Upstairs: " + up;
	}
	
}
