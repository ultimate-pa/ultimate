/**
 * Basic Vertex.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.old.vertex;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @date 10.12.2011
 */
public class Vertex<LETTER,STATE> {
    /*_______________________________________________________________________*\
    \* FIELDS / ATTRIBUTES                                                   */
	
    /**
     * The label of the first Buchi automaton state.
     */
    private STATE q0;
    /**
     * The label of the second Buchi automaton state.
     */
    private STATE q1;
	
    /*_______________________________________________________________________*\
    \* CONSTRUCTORS                                                          */
    
    /**
     * Constructor.
	 * 
     * @param q0
     *            the label of the first Buchi automaton state
     * @param q1
     *            the label of the second Buchi automaton state
     */
    public Vertex(STATE q0, STATE q1) {
        this.q0 = q0;
        this.q1 = q1;
    }
    
    /*_______________________________________________________________________*\
    \* METHODS                                                               */
    
    /*_______________________________________________________________________*\
    \* OVERRIDDEN METHODS                                                    */
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<(").append(getQ0()).append(",").append(getQ1());
        sb.append(")>");
        return sb.toString();
    }
    
    /*_______________________________________________________________________*\
    \* GETTERS AND SETTERS                                                     */
    
    /**
     * Getter for the label of the first Buchi automaton state.
     * 
     * @return the label of the first Buchi automaton state
     */
    public STATE getQ0() {
        return q0;
    }

    /**
     * Getter for the label of the first Buchi automaton state.
     * 
     * @return the label of the first Buchi automaton state
     */
    public STATE getQ1() {
        return q1;
    }
}
