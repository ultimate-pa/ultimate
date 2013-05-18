package de.uni_freiburg.informatik.ultimate.automata;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * 
 * 
 * @author haettigj@informatik.uni-freiburg.de
 * 
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the
 *            automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of
 *            automata. In many cases you want to use String as STATE and your
 *            states are labeled e.g. with "q0", "q1", ...
 */
public class AutomatonEpimorphism<STATE> {

	// For status output
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private HashMap<STATE, STATE> m_epimorphism;

	public AutomatonEpimorphism() {
		m_epimorphism = new HashMap<STATE, STATE>();
	}

	/**
	 * Creates the epimorphism for two automatons from a1 to a2. The Labels of
	 * a1 have to be of type string and have to be of the following scheme:
	 * "<l1>_<l2>", where "<l1>" is the actual label of the state and <l2> is
	 * the label of the node of a2, which it is epimorph to
	 * 
	 * @param a1
	 *            automaton where the epimorphism to to is encoded in the labels
	 * @param a2
	 *            automaton where the epimorphism maps to
	 * @return an epimorphism structure from a1 to a2
	 */
	public static AutomatonEpimorphism<String> GetFromAutomatonLabels(
			INestedWordAutomatonOldApi<String, String> a1,
			INestedWordAutomatonOldApi<String, String> a2) {
		AutomatonEpimorphism<String> epimorphism = new AutomatonEpimorphism<String>();

		// traversing the states
		for (String state1 : a1.getStates()) {
			if (state1.contains("_")) {

				// check that "_" is not the last char in the string
				if (state1.indexOf("_") + 1 == state1.length()) {
					s_Logger.error("Invalid state name: " + state1);
				}

				// get the name of the epimorph state
				String epimorphState = state1
						.substring(state1.indexOf("_") + 1);

				// check that "_" does not occur multiple times
				if (epimorphState.indexOf("_") != -1) {
					s_Logger.error("Invalid state name: " + state1);
				}

				// search the state in a2
				String state2 = null;
				for (String s : a2.getStates()) {
					if (s.equals(epimorphState)) {
						state2 = s;
					}
				}

				// if it is not found, error
				if (state2 == null) {
					s_Logger.error("Missing epimorphism partner for: " + state1);
				}

				// set the mapping from state1 to state2
				epimorphism.m_epimorphism.put(state1, state2);
			}
		}

		return epimorphism;
	}
	
	/**
	 * Returns the state, where the epimorphism points to
	 * @param s
	 */
	public STATE GetMapping(STATE s)
	{
		return m_epimorphism.get(s);
	}
}
