/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE MSO Library package.
 *
 * The ULTIMATE MSO Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSO Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSO Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSO Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSO Library package library grant you additional permission
 * to convey the resulting work.
 */

/*
 * ApplicationTerm		:= function symbols
 * ConstantTerm			:= literals
 * QuantifiedFormula	:= 
 * TermVariable			:= quantified variables
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class MoNatDiffScript extends NoopScript {
	
	
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataLibraryServices;
	private final ILogger mLogger;

	public MoNatDiffScript(IUltimateServiceProvider services, ILogger logger) {
		mServices = services;
		mAutomataLibraryServices = new AutomataLibraryServices(services);
		mLogger = logger;
	}

	@Override
	public void setLogic(String logic) throws UnsupportedOperationException, SMTLIBException {
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mLogger.info("hello world, logic set to " + logic);
		super.setLogic(logic);
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}
	
	
	private void constructAutomaton() {
		Set<Integer> alphabet = null;
		VpAlphabet<Integer> vpAlphabet = new VpAlphabet<Integer>(alphabet);
		IEmptyStackStateFactory stateFactory = new StringFactory();
		NestedWordAutomaton<Integer, String> automaton = new NestedWordAutomaton<Integer, String>(
				mAutomataLibraryServices, vpAlphabet, stateFactory);
		
		// add some initial state
		automaton.addState(true, false, "q_0");
		// add some accepting state
		automaton.addState(false, true, "q_1");
		// connect both states via transition that is labeled by letter 23
		automaton.addInternalTransition("q_0", 23, "q_1");
		
		
	}
}
