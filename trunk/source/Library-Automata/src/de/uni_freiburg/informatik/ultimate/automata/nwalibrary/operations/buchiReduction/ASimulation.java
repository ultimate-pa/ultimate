/*
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Buchi automata state space reduction algorithm based on the following paper:
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 * 
 * Algorithm optimized to work using strongly connected components.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 */
public abstract class ASimulation<LETTER,STATE> {
	
	protected final Logger m_Logger;
	
	protected NestedWordAutomaton<LETTER, STATE> m_Result;
	
    protected SccComputation<Vertex<LETTER, STATE>,
		StronglyConnectedComponent<Vertex<LETTER, STATE>>> m_SccComp;
    
    protected DefaultStronglyConnectedComponentFactory<Vertex<LETTER,STATE>> m_SccFactory;
    
    protected final IUltimateServiceProvider m_Services;

    protected final StateFactory<STATE> m_StateFactory;
	
	protected GameGraphSuccessorProvider<LETTER, STATE> m_SuccProvider;

	protected final boolean m_UseSCCs;

	protected ArrayList<Vertex<LETTER, STATE>> m_WorkingList;
    
    public ASimulation(final IUltimateServiceProvider services,
    		final boolean useSCCs, final StateFactory<STATE> stateFactory)
    				throws OperationCanceledException {
    	m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_UseSCCs = useSCCs;
        m_StateFactory = stateFactory;
		
		m_SccComp = null;
		m_SccFactory = null;
		m_SuccProvider = null;
    }
    
    public NestedWordAutomaton<LETTER, STATE> getResult() {
		return m_Result;
	}
    
	protected int calcBestNghbMeasure(final Vertex<LETTER, STATE> vertex,
			final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		boolean isDuplicatorVertex = vertex.isDuplicatorVertex();

		// If there are no successors the corresponding player looses
		if (!getGameGraph().hasSuccessors(vertex)) {
			if (isDuplicatorVertex) {
				return getGameGraph().getGlobalInfinity();
			} else {
				return 0;
			}
		}

		int optimum;
		if (isDuplicatorVertex) {
			optimum = getGameGraph().getGlobalInfinity();
		} else {
			optimum = 0;
		}
		
		for (Vertex<LETTER, STATE> succ : getGameGraph().getSuccessors(vertex)) {
			int progressMeasure = succ.getPM(scc, getGameGraph().getGlobalInfinity());
			if (isDuplicatorVertex) {
				if (progressMeasure < optimum) {
					optimum = progressMeasure;
				}
			} else {
				if (progressMeasure > optimum) {
					optimum = progressMeasure;
				}
			}
		}

		return decreaseVector(vertex.getPriority(), optimum, localInfinity);
	}
    
	protected int calcNghbCounter(final Vertex<LETTER, STATE> vertex,
			final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		// If there are no successors
		if (!getGameGraph().hasSuccessors(vertex)) {
			return 0;
		}
		int counter = 0;
		for (Vertex<LETTER, STATE> succ : getGameGraph().getSuccessors(vertex))
			if (decreaseVector(vertex.getPriority(), succ.getPM(scc,
					getGameGraph().getGlobalInfinity()), localInfinity) == vertex.getBEff()) {
				counter++;
			}
		return counter;
	}
    
	protected int calculateInfinityOfSCC(final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		int localInfinity = 0;
		for (Vertex<LETTER, STATE> vertex : scc.getNodes()) {
			if (vertex.getPriority() == 1) {
				localInfinity++;
			}
		}
		localInfinity++;
		return localInfinity;
	}
    
	protected void clear() {
		getGameGraph().clear();
		m_WorkingList.clear();
		m_Result = null;
		m_SccComp = null;
		m_SccFactory = null;
		m_SuccProvider = null;
	}
    
	protected int decreaseVector(final int index, final int vector,
			final int localInfinity) {
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 0) {
			return 0;
		} else {
			return vector;
		}
	}
    
	protected void doSimulation() throws OperationCanceledException {
    	long startTime = System.currentTimeMillis();
        if(m_UseSCCs) { // calculate reduction with SCC
        	m_SccFactory = new DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>>();
			m_SuccProvider = new GameGraphSuccessorProvider<LETTER, STATE>(getGameGraph());
			m_SccComp = new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_Logger, m_SuccProvider,
					m_SccFactory, getGameGraph().getSize(), getGameGraph().getVertices());
			
            Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter =
            		new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(m_SccComp.getSCCs()).iterator();
            while(iter.hasNext()) {
            	StronglyConnectedComponent<Vertex<LETTER, STATE>> scc = iter.next();
                iter.remove();
                efficientLiftingAlgorithm(calculateInfinityOfSCC(scc), scc.getNodes());
            }
        } else { // calculate reduction w/o SCCs
            efficientLiftingAlgorithm(getGameGraph().getGlobalInfinity(), null);
        }
        m_Result = getGameGraph().generateBuchiAutomatonFromGraph();
        clear();
        long duration = System.currentTimeMillis() - startTime;
        m_Logger.info((this.m_UseSCCs ? "SCC version" : "nonSCC version") + 
        		" took " + duration + " milliseconds.");
    }
    
	protected void efficientLiftingAlgorithm(final int l_inf,
			final Set<Vertex<LETTER,STATE>> scc) throws OperationCanceledException {
        // init STATE in all vertices and create the working list
		AGameGraph<LETTER, STATE> game = getGameGraph();
		int globalInfinity = game.getGlobalInfinity();
		
        m_WorkingList = new ArrayList<Vertex<LETTER, STATE>>();
        if(m_UseSCCs) {
          HashSet<Vertex<LETTER,STATE>> notDeadEnd = new HashSet<Vertex<LETTER, STATE>>();
          for (Vertex<LETTER,STATE> v : scc) {
              if (v.getPM(scc, globalInfinity) != update(v, l_inf, scc)) {
                  if (!game.hasSuccessors(v)) m_WorkingList.add(v);
                  else notDeadEnd.add(v);
                  v.setInWL(true);
              }
              v.setC(calcNghbCounter(v, l_inf, scc));
          }
          m_WorkingList.addAll(notDeadEnd);
        } else {
            HashSet<Vertex<LETTER,STATE>> notDeadEnd = new HashSet<Vertex<LETTER, STATE>>();
            for (DuplicatorVertex<LETTER,STATE> v : game.getDuplicatorVertices()) {
                if (v.getPM(scc, globalInfinity) != update(v, l_inf, scc)) {
                    if (!game.hasSuccessors(v)) m_WorkingList.add(v);
                    else notDeadEnd.add(v);
                    v.setInWL(true);
                }
                if (game.hasSuccessors(v)) v.setC(game.getSuccessors(v).size());
            }
            for (SpoilerVertex<LETTER,STATE> v : game.getSpoilerVertices()) {
                if (v.getPM(scc, globalInfinity) != update(v, l_inf, scc)) {
                    if (!game.hasSuccessors(v)) m_WorkingList.add(v);
                    else notDeadEnd.add(v);
                    v.setInWL(true);
                }
                if (game.hasSuccessors(v)) v.setC(game.getSuccessors(v).size());
            }
            m_WorkingList.addAll(notDeadEnd);
        }
        while (!m_WorkingList.isEmpty()) {
            Vertex<LETTER,STATE> v = m_WorkingList.remove(m_WorkingList.size() - 1);
            v.setInWL(false);
            int t = v.getPM(scc, globalInfinity);
            v.setBEff(calcBestNghbMeasure(v, l_inf, scc));
            v.setC(calcNghbCounter(v, l_inf, scc));
            v.setPM(increaseVector(v.getPriority(), v.getBEff(), l_inf));
            if (!game.hasPredecessors(v)) continue;
            for (Vertex<LETTER,STATE> w : game.getPredecessors(v)) {
                if(m_UseSCCs && !scc.contains(w)) continue;
                // for each predecessor w of v
                if (!w.isInWL()
                        && decreaseVector(w.getPriority(), v.getPM(scc, globalInfinity), l_inf) > w.getBEff()) {
                    /* w in L && <p(v)>_w > B(w) means: for each predecessor w
                     * of v which is not in L */
                    if (w.isDuplicatorVertex()
                            && decreaseVector(w.getPriority(), t, l_inf) == w.getBEff()) {
                        /* w in v0 && <l>_w==w.getB() */
                        if (w.getC() == 1) {
                        	m_WorkingList.add(w);
                            w.setInWL(true);
                        }
                        if (w.getC() > 1) w.setC(w.getC() - 1);
                    } else if (w.isSpoilerVertex()) {
                    	m_WorkingList.add(w);
                        w.setInWL(true);
                    }
                }
            }
            
            if (m_Services.getProgressMonitorService() != null
            		&& !m_Services.getProgressMonitorService().continueProcessing()) {
                m_Logger.debug("Stopped in efficientLiftingAlgorithm");
                throw new OperationCanceledException(this.getClass());
            }
        }
    }
    
	protected abstract AGameGraph<LETTER, STATE> getGameGraph();
	
	protected int increaseVector(final int index, final int vector,
			final int localInfinity) {
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 1) {
			int tempVector = vector + 1;
			if (tempVector == localInfinity) {
				return getGameGraph().getGlobalInfinity();
			}
			return tempVector;
		} else {
			return decreaseVector(index, vector, localInfinity);
		}
	}
    
    protected int update(final Vertex<LETTER,STATE> v, final int l_inf,
			final Set<Vertex<LETTER, STATE>> scc) {
        return increaseVector(v.getPriority(), calcBestNghbMeasure(v, l_inf, scc), l_inf);
    }
}
