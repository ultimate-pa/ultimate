package local.stalin.automata.parser.astAnnotations.petrinet;
import java.util.ArrayList;

import local.stalin.model.AbstractAnnotations;


public class PetriNetJulianDefinition extends AbstractAnnotations {

	private static final long serialVersionUID = -2644386589944130013L;
	private final String name;
	private final ArrayList<String> alphabet;
	private final ArrayList<String> places;
	private final ArrayList<String> initialMarking;
	private final ArrayList<String> acceptingPlaces;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"name", "alphabet", "places", "initialMarking", "acceptingPlaces"};
	


	public PetriNetJulianDefinition(String name, ArrayList<String> alphabet,
			ArrayList<String> places, ArrayList<String> initialMarking,
			ArrayList<String> acceptingPlaces) {
		this.name = name;
		this.alphabet = alphabet;
		this.places = places;
		this.initialMarking = initialMarking;
		this.acceptingPlaces = acceptingPlaces;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "name")
			return name;
		else if (field == "alphabet")
			return alphabet;
		else if (field == "places")
			return places;
		else if (field == "initialMarking")
			return initialMarking;
		else if (field == "acceptingPlaces")
			return acceptingPlaces;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * 
	 * @return the alphabet
	 */
	public ArrayList<String> getAlphabet(){
		return alphabet;
	}

	/**
	 * 
	 * @return the places
	 */
	public ArrayList<String> getPlaces(){
		return places;
	}
	
	/**
	 * 
	 * @return the initial marking
	 */
	public ArrayList<String> getInitialMarking(){
		return initialMarking;
	}
	
	/**
	 * 
	 * @return the accepting markings
	 */
	public ArrayList<String> getAcceptingPlaces(){
		return acceptingPlaces;
	}
}