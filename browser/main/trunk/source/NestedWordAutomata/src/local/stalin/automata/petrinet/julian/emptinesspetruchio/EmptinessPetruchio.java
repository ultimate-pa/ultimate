package local.stalin.automata.petrinet.julian.emptinesspetruchio;

import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Map;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.automata.petrinet.ITransition;
import local.stalin.automata.petrinet.julian.PetriNetJulian;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

import petruchio.cov.Backward;
import petruchio.cov.SimpleList;
import petruchio.interfaces.petrinet.Place;
import petruchio.interfaces.petrinet.Transition;
import petruchio.pn.PetriNet;

/**
 * Check if a PetriNetJulian has an accepting run.
 * The emptiness check uses Tim Straznys Petruchio.
 * A marking of a PetriNetJulian is accepting if the marking contains an 
 * accepting place.
 * EmptinessPetruchio checks if any (singleton) marking {p} such that p is an
 * accepting place can be covered.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Type of alphabet symbols
 * @param <C> Type of place labeling
 */

public class EmptinessPetruchio<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	final PetriNetJulian<S,C> m_NetJulian;
	final PetriNet m_NetPetruchio = new PetriNet();
	
	// Maps each place of m_NetJulian to the corresponding place in m_NetPetruchio
	final Map<local.stalin.automata.petrinet.Place<S,C>, Place> pJulian2pPetruchio = 
		new IdentityHashMap<local.stalin.automata.petrinet.Place<S,C>,Place>();

	// Maps each transition of m_NetPetruchio to the corresponding transition in m_NetJulian	
	final Map<Transition, ITransition<S,C>> tPetruchio2tJulian = 
		new IdentityHashMap<Transition, ITransition<S,C>>();

	
	NestedRun<S,C> m_AcceptedRun = null;
	
	public EmptinessPetruchio(PetriNetJulian<S,C> net) {
		m_NetJulian = net;
		constructNetPetruchio();
		m_AcceptedRun = constructAcceptingRun();
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
		for(local.stalin.automata.petrinet.Place<S,C> pJulian : m_NetJulian.getPlaces()) {
			Place pPetruchio;
			if (m_NetJulian.getInitialMarking().contains(pJulian)) {
				pPetruchio = m_NetPetruchio.addPlace(pJulian.getContent().toString(), 1);
			}
			else {
				pPetruchio = m_NetPetruchio.addPlace(pJulian.getContent().toString(), 0);
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
			for(final local.stalin.automata.petrinet.Place<S,C> pJulian : tJulian.getSuccessors()) {
				m_NetPetruchio.addArc(transitionPetruchio, pJulian2pPetruchio.get(pJulian), 1); // 1-sicheres Netz
			}
			// TPArcs kopieren
			for(final local.stalin.automata.petrinet.Place<S,C> p : tJulian.getPredecessors()) {
				m_NetPetruchio.addArc(pJulian2pPetruchio.get(p), transitionPetruchio, 1); // 1-sicheres Netz
			}
		}
	}
	
	
	/**
	 * 
	 * @return Some accepting run if the Petri net has an accepting run, null
	 * otherwise. 
	 * Note: A run should be an interleaved sequence of markings and symbols.
	 * Here each marking will be null instead. 
	 */
	private NestedRun<S,C> constructAcceptingRun() {
		s_Logger.debug("Net has "+m_NetJulian.getPlaces().size()+ " Places");
		s_Logger.debug("Net has "+m_NetJulian.getTransitions().size()+ " Transitions");
		
		// construct single invariant p_1 + ... + p_n where p_i \in places
		Collection<Map<Place, Integer>> invariants = new ArrayList<Map<Place, Integer>>(1);
		Map<Place, Integer> theInvariant = 
			new IdentityHashMap<Place, Integer>(m_NetPetruchio.getPlaces().size());
		for(Place pPetruchio : m_NetPetruchio.getPlaces()) {
		   theInvariant.put(pPetruchio, Integer.valueOf(1));
		}
		invariants.add(theInvariant);
		
		// construct the following target:
		// at least one of { {p_j} | p_j \in Paccepting } is coverable
		Collection<Map<Place, Integer>> targets = new ArrayList<Map<Place, Integer>>();
		for(local.stalin.automata.petrinet.Place<S,C> pAcceptingJulian : m_NetJulian.getAcceptingPlaces()) {
			// construct single target pAccepting >= 1
			Place pAcceptingPetruchio = pJulian2pPetruchio.get(pAcceptingJulian);
			Map<Place, Integer> placeWithOneToken = new IdentityHashMap<Place, Integer>();
			placeWithOneToken.put(pAcceptingPetruchio,1);
			targets.add(placeWithOneToken);
		}
		
		s_Logger.debug("Check coverability of " + m_NetJulian.getAcceptingPlaces().toString());
//		petruchio.pn.Converter.writeNet(m_NetPetruchio, "/mnt/storage/qYv/uni/stalin/trunk/glotterNeu.spec");
		SimpleList<Transition> tracePetruchio = 
			Backward.checkCoverability(m_NetPetruchio, targets, invariants);
		s_Logger.debug("done");
		
		if (tracePetruchio == null) {
			return null;
			
		}
		else {
			return tracePetruchio2run(tracePetruchio);
		}
		
	}
		


	/**
	 * Translate sequence of Petruchio transitions to run of PetriNet
	 * @param tracePetruchio
	 * @return
	 */
	private NestedRun<S,C> tracePetruchio2run(SimpleList<Transition> tracePetruchio) {
		
		NestedRun<S,C> result = new NestedRun<S,C>(null);
		for(Transition tPetruchio : tracePetruchio) {
			S symbol = tPetruchio2tJulian.get(tPetruchio).getSymbol();
			NestedRun<S,C> oneStepSubrun = 
				new NestedRun<S,C>(null, symbol,NestedWord.INTERNAL_POSITION, null);
			result = result.concatenate(oneStepSubrun);
		}
		return result;
	}
	
	
	public NestedRun<S,C> getResult() {
		return m_AcceptedRun;
	}

}
