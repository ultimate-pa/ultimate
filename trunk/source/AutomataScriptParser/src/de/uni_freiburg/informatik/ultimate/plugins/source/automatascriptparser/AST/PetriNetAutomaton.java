/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetAutomaton extends Automaton {

	/**
	 * 
	 */
	private static final long serialVersionUID = -3606354736361896683L;
	private List<String> m_alphabet;
	private List<String> m_places;
	
	private List<PetriNetTransition> m_transitions;
	private PetriNetMarkingList m_initialMarkings;
	private PetriNetMarkingList m_acceptingMarkings;
	private List<String> m_acceptingPlaces;
	private boolean m_isPetriNetJulianDefinition;
	
	
	public PetriNetAutomaton() {
		m_transitions = new ArrayList<PetriNetTransition>();
		m_initialMarkings = new PetriNetMarkingList();
		m_acceptingMarkings = new PetriNetMarkingList();
		m_acceptingPlaces = new ArrayList<String>();
	}
	
	public PetriNetAutomaton(String name) {
		this();
		m_Name = name;
	}
	
	public PetriNetAutomaton(String name, boolean isPetriNetJulian) {
		this(name);
		m_isPetriNetJulianDefinition  = isPetriNetJulian;
	}
	

	public List<String> getAlphabet() {
		return m_alphabet;
	}

	public void setAlphabet(List<String> m_alphabet) {
		this.m_alphabet = m_alphabet;
	}

	public List<String> getPlaces() {
		return m_places;
	}

	public void setPlaces(List<String> m_places) {
		this.m_places = m_places;
	}

	public List<PetriNetTransition> getTransitions() {
		return m_transitions;
	}

	public void setTransitions(List<PetriNetTransition> m_transitions) {
		this.m_transitions = m_transitions;
	}

	public PetriNetMarkingList getInitialMarkings() {
		return m_initialMarkings;
	}

	public void setInitialMarkings(PetriNetMarkingList m_initialMarkings) {
		this.m_initialMarkings = m_initialMarkings;
	}

	public PetriNetMarkingList getAcceptingMarkings() {
		return m_acceptingMarkings;
	}

	public void setAcceptingMarkings(PetriNetMarkingList m_acceptingMarkings) {
		this.m_acceptingMarkings = m_acceptingMarkings;
	}

	public List<String> getAcceptingPlaces() {
		return m_acceptingPlaces;
	}

	public void setAcceptingPlaces(List<String> m_acceptingPlaces) {
		this.m_acceptingPlaces = m_acceptingPlaces;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("PetriNet(" + m_Name + ") "+ "[Size of alphabet: ");
		builder.append(m_alphabet.size());
		builder.append(" Num of places: ");
		builder.append(m_places.size());
		builder.append(" Num of transitions: ");
		builder.append(m_transitions.size());
		builder.append("]");
		return builder.toString();
	}

	public boolean isPetriNetJulianDefinition() {
		return m_isPetriNetJulianDefinition;
	}

}
