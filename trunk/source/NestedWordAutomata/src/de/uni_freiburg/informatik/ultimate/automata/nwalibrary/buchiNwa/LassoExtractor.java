/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class LassoExtractor<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private final INestedWordAutomatonSimple<LETTER, STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private List<NestedLassoWord<LETTER>> m_NestedLassoWords;

	public LassoExtractor(INestedWordAutomatonSimple<LETTER, STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		if (m_Operand instanceof NestedWordAutomatonReachableStates) {
			m_Reach = (NestedWordAutomatonReachableStates<LETTER, STATE>) m_Operand;
		} else {
			m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Operand);
		}
		NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents sccs = 
				m_Reach.getOrComputeStronglyConnectedComponents();
		m_NestedLassoRuns = sccs.getAllNestedLassoRuns();
		m_NestedLassoWords = new ArrayList<NestedLassoWord<LETTER>>(m_NestedLassoRuns.size());
		if (m_NestedLassoRuns.isEmpty() && sccs.getNestedLassoRun() == null) {
			assert (new BuchiIsEmpty<LETTER, STATE>(m_Reach)).getResult();
		} else {
			for (NestedLassoRun<LETTER, STATE> nlr  : m_NestedLassoRuns) {
				m_NestedLassoWords.add(nlr.getNestedLassoWord());
			}
		}
		s_Logger.info(exitMessage());
	}

	@Override
	public List<NestedLassoWord<LETTER>> getResult() throws OperationCanceledException {
		return m_NestedLassoWords;
	}

	@Override
	public String operationName() {
		return "getSomeAcceptedLassoRuns";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Found " + 
					m_NestedLassoRuns.size() + " examples of accepted words.";
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
