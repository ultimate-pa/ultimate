package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices;

/**
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 16.01.2012
 */
public class Player0Vertex<LETTER,STATE> extends Vertex<LETTER, STATE> {
    /**
     * The label of the edge in the buchi automaton.
     */
    private LETTER a;

    /**
     * Vertex constructor.
     * 
     * @param priority
     *            priority of this vertex
     * @param b
     *            extra bit b
     * @param q0
     *            label of the first Buchi automaton state
     * @param q1
     *            label of the second Buchi automaton state
     * @param a
     *            label of the Buchi automaton edge
     */
    public Player0Vertex(byte priority, boolean b, STATE q0, STATE q1, LETTER a) {
        super(priority, b, q0, q1);
        this.a = a;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("<").append(isB()).append(",(").append(getQ0()).append(",");
        sb.append(getQ1()).append(",").append(a).append("),p:");
        sb.append(getPriority()).append(",pm:").append(pm);
        sb.append(">");
        return sb.toString();
    }
}