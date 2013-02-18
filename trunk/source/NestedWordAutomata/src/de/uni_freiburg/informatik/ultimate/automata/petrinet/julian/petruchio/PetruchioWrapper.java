package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.petruchio;

import java.util.IdentityHashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import petruchio.interfaces.petrinet.Place;
import petruchio.interfaces.petrinet.Transition;
import petruchio.pn.PetriNet;
import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Wraps the Petri net representation used in Tim Straznys Petruchio.
 * Use a PetriNetJulian to construct a Petruchio petri net.
 * Stores mapping for transitions and places of both representations. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Type of alphabet symbols
 * @param <C> Type of place labeling
 */

public class PetruchioWrapper<S,C> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	
	final PetriNetJulian<S,C> m_NetJulian;
	final PetriNet m_NetPetruchio = new PetriNet();
	
	// Maps each place of m_NetJulian to the corresponding place in m_NetPetruchio
	final Map<de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S,C>, Place> pJulian2pPetruchio = 
		new IdentityHashMap<de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S,C>,Place>();

	// Maps each transition of m_NetPetruchio to the corresponding transition in m_NetJulian	
	final Map<Transition, ITransition<S,C>> tPetruchio2tJulian = 
		new IdentityHashMap<Transition, ITransition<S,C>>();

	
	public PetruchioWrapper(PetriNetJulian<S,C> net) {
		m_NetJulian = net;
		constructNetPetruchio();
	}
	
	/**
	 * Given a NetJulian Petri net m_NetJulian, construct
	 *  <ul>
	 * <li> the corresponding Petruchio Petri net representation m_NetPetruchio
	 * <li> the Julian -> Petruchio place mapping plMap
	 * <li> the Petruchio -> Julian place mapping trMap
	 * </ul>
	 */
	private void constructNetPetruchio() {
		//construct a Petruchio place for each NetJulian place
		for(de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S,C> pJulian : m_NetJulian.getPlaces()) {
			Place pPetruchio;
			String pLabel = "";
			pLabel += pJulian.getContent();
			pLabel += String.valueOf(pJulian.getContent().hashCode());
			if (m_NetJulian.getInitialMarking().contains(pJulian)) {
				pPetruchio = m_NetPetruchio.addPlace(pLabel, 1);
			}
			else {
				pPetruchio = m_NetPetruchio.addPlace(pLabel, 0);
			}
			// 1-sicheres Netz, Info hilft Petruchio/BW
			pPetruchio.setBound(1); 
			pJulian2pPetruchio.put(pJulian, pPetruchio);
		}
		//construct a Petruchio transition for each NetJulian transition
		for(ITransition<S,C> tJulian : m_NetJulian.getTransitions()) {
			Transition transitionPetruchio = m_NetPetruchio.addTransition(tJulian.toString());
			tPetruchio2tJulian.put(transitionPetruchio, tJulian);
			// PTArcs kopieren
			for(final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S,C> pJulian : tJulian.getSuccessors()) {
				m_NetPetruchio.addArc(transitionPetruchio, pJulian2pPetruchio.get(pJulian), 1); // 1-sicheres Netz
			}
			// TPArcs kopieren
			for(final de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S,C> p : tJulian.getPredecessors()) {
				m_NetPetruchio.addArc(pJulian2pPetruchio.get(p), transitionPetruchio, 1); // 1-sicheres Netz
			}
		}
	}
	

	/**
	 * Write Petri Net to file by using Petruchio. The ending of the filename
	 * determines how the Petri net is encoded (e.g., .spec, .lola, etc.)
	 * @param filename
	 */
	public void writeToFile(String filename) {
		s_Logger.debug("Writing net to file " + filename);
		petruchio.pn.Converter.writeNet(m_NetPetruchio, filename);
		s_Logger.info("Accepting places: " + m_NetJulian.getAcceptingPlaces());
	}

	public Map<de.uni_freiburg.informatik.ultimate.automata.petrinet.Place<S, C>, Place> getpJulian2pPetruchio() {
		return pJulian2pPetruchio;
	}

	public Map<Transition, ITransition<S, C>> gettPetruchio2tJulian() {
		return tPetruchio2tJulian;
	}

	public PetriNet getNet() {
		return m_NetPetruchio;
	}
		

	


}
