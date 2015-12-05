package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.delayed;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 * @param <STATE>
 */
public final class DelayedGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	
	protected final Logger m_Logger;
	
	public DelayedGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi)
					throws OperationCanceledException {
		super(services);
		m_Buechi = buechi;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		generateGameGraphFromBuechi();
	}
	
	private int getAmountOfBitsForSpoilerVertix(final STATE q0, final STATE q1) {
    	int amount = 0;
    	
    	if (getSpoilerVertex(q0, q1, false) != null) {
    		amount++;
    	}
    	
    	if (getSpoilerVertex(q0, q1, true) != null) {
    		amount++;
    	}
    	
    	return amount;
    }
	
    @Override
    protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph()
    		throws OperationCanceledException {
        // determine which states to merge
        ArrayList<STATE> states = new ArrayList<STATE>();
        states.addAll(m_Buechi.getStates());
        boolean[][] table = new boolean[states.size()][states.size()];
        for (SpoilerVertex<LETTER,STATE> v : getSpoilerVertices()) {
            // all the states we need are in V1...
            if ((m_Buechi.isFinal(v.getQ0()) && m_Buechi.isFinal(v.getQ1()))
                    ^ v.isB() ^ m_Buechi.isFinal(v.getQ0())) {
                // skip all elements that not fulfill:
                // letting b=1 if q0 in F and q1 not in F, and b=0 else
                continue;
            }
            if (v.getPM(null,getGlobalInfinity()) < getGlobalInfinity()) {
                table[states.indexOf(v.getQ0())][states.indexOf(v.getQ1())] = true;
            }
        }

        if (m_Services.getProgressMonitorService() != null
        		&& !m_Services.getProgressMonitorService().continueProcessing()) {
            m_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
            throw new OperationCanceledException(this.getClass());
        }

        // merge states
        boolean[] marker = new boolean[states.size()];
        Set<STATE> temp = new HashSet<STATE>();
        HashMap<STATE,STATE> oldSNames2newSNames = new HashMap<STATE,STATE>();
        @SuppressWarnings("unchecked")
        StateFactory<STATE> snf = (StateFactory<STATE>) new StringFactory();
        NestedWordAutomaton<LETTER,STATE> result = new NestedWordAutomaton<LETTER,STATE>(
        		m_Services, m_Buechi.getInternalAlphabet(), null, null, snf);
        for (int i = 0; i < states.size(); i++) {
            if (marker[i]) continue;
            temp.clear();
            temp.add(states.get(i));
            marker[i] = true;
            boolean isFinal = m_Buechi.isFinal(states.get(i));
            boolean isInitial = m_Buechi.isInitial(states.get(i));
            for (int j = i; j < states.size(); j++) {
                if (table[i][j] && table[j][i] && !marker[j]) {
                    temp.add(states.get(j));
                    marker[j] = true;
                    if (m_Buechi.isFinal(states.get(j))) isFinal = true;
                    if (m_Buechi.isInitial(states.get(j))) isInitial = true;
                }
            }
            STATE minimizedStateName = snf.minimize(temp);
            for (STATE c : temp) oldSNames2newSNames.put(c, minimizedStateName);
            result.addState(isInitial, isFinal, minimizedStateName);
            marker[i] = true;
        }

        if (m_Services.getProgressMonitorService() != null
        		&& !m_Services.getProgressMonitorService().continueProcessing()) {
            m_Logger.debug("Stopped in generateBuchiAutomaton/states added to result BA");
            throw new OperationCanceledException(this.getClass());
        }

        // add edges
        for (STATE c : m_Buechi.getStates())
            for (LETTER s : m_Buechi.getInternalAlphabet())
                for (STATE succ : m_Buechi.succInternal(c, s)) {
                    STATE newPred = oldSNames2newSNames.get(c);
                    STATE newSucc = oldSNames2newSNames.get(succ);
                    result.addInternalTransition(newPred, s, newSucc);
                }
        
        return result;
    }
    
    @Override
    protected void generateGameGraphFromBuechi() throws OperationCanceledException {
        // Calculate v1 [paper ref 10]
        for (STATE q0 : m_Buechi.getStates()) {
            for (STATE q1 : m_Buechi.getStates()) {
                SpoilerVertex<LETTER,STATE> v1e = new SpoilerVertex<LETTER, STATE>(
                        0, false, q0, q1);
                addSpoilerVertex(v1e);
                if (!m_Buechi.isFinal(q1)) {
                    v1e = new SpoilerVertex<LETTER,STATE>(1, true, q0, q1);
                    addSpoilerVertex(v1e);
                    increaseGlobalInfinity();
                }
            }
            if (m_Services.getProgressMonitorService() != null &&
            		!m_Services.getProgressMonitorService().continueProcessing()) {
                m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException(this.getClass());
            }
        }
        // Calculate v0 and edges [paper ref 10, 11, 12]
        for (STATE q0 : m_Buechi.getStates()) {
            for (STATE q1 : m_Buechi.getStates()) {
                for (LETTER s : m_Buechi.lettersInternalIncoming(q0)) {
                    if (m_Buechi.predInternal(q0, s).iterator().hasNext()) {
                        DuplicatorVertex<LETTER,STATE> v0e = new DuplicatorVertex<LETTER, STATE>(
                                2, false, q0, q1, s);
                        addDuplicatorVertex(v0e);
                        // V0 -> V1 edges [paper ref 11]
                        for (STATE q2 : m_Buechi.succInternal(q1, s))
                            addEdge(v0e, getSpoilerVertex(q0, q2, false));
                        // V1 -> V0 edges [paper ref 11]
                        for (STATE q2 : m_Buechi.predInternal(q0, s))
                            if (!m_Buechi.isFinal(q0))
                                addEdge(getSpoilerVertex(q2, q1, false), v0e);
                        v0e = new DuplicatorVertex<LETTER,STATE>(2, true, q0, q1, s);
                        addDuplicatorVertex(v0e);
                        // V0 -> V1 edges [paper ref 11]
                        for (STATE q2 : m_Buechi.succInternal(q1, s)) {
                            if (!m_Buechi.isFinal(q2)
                            		&& getAmountOfBitsForSpoilerVertix(q0, q2) > 1) {
                            	addEdge(v0e, getSpoilerVertex(q0, q2, true));
                            } else {
                            	addEdge(v0e, getSpoilerVertex(q0, q2, false));
                            }
                        }
                        // V1 -> V0 edges [paper ref 11]
                        for (STATE q2 : m_Buechi.predInternal(q0, s)) {
                            if (getAmountOfBitsForSpoilerVertix(q2, q1) > 1)
                            	addEdge(getSpoilerVertex(q2, q1, true), v0e);
                            if (m_Buechi.isFinal(q0))
                                addEdge(getSpoilerVertex(q2, q1, false), v0e);
                        }
                    }
                }
            }
            if (m_Services.getProgressMonitorService() != null
            		&& !m_Services.getProgressMonitorService().continueProcessing()) {
                m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException(this.getClass());
            }
        }
        increaseGlobalInfinity(); // global infinity = (# of pr==1 nodes) + 1
        if (m_Logger.isDebugEnabled()) {
            m_Logger.debug("Infinity is " + getGlobalInfinity());
            m_Logger.debug("Number of vertices in game graph: "
                    + (getDuplicatorVertices().size() + getSpoilerVertices().size()));
            m_Logger.debug("Number of vertices in v0: " + getDuplicatorVertices().size());
            m_Logger.debug("Number of vertices in v1: " + getSpoilerVertices().size());
            int edges = 0;
            for (Set<Vertex<LETTER,STATE>> hs : getSuccessorGroups()) {
                edges += hs.size();
            }
            m_Logger.debug("Number of edges in game graph: " + edges);
        }
    }
}
