/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetHandle;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class BuchiInterpolantAutomatonWithHandle extends
		BuchiInterpolantAutomaton {
	
	private NestedRun<CodeBlock, IPredicate> m_Handle;
	private int m_Position = 0;
	
	
	

	public BuchiInterpolantAutomatonWithHandle(SmtManager smtManager,
			EdgeChecker edgeChecker, boolean emptyStem, IPredicate precondition,
			Set<IPredicate> stemInterpolants, IPredicate hondaPredicate,
			Set<IPredicate> loopInterpolants, CodeBlock hondaEntererStem,
			CodeBlock hondaEntererLoop,
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			boolean scroogeNondeterminismStem,
			boolean scroogeNondeterminismLoop, boolean hondaBouncerStem,
			boolean hondaBouncerLoop, PredicateFactoryForInterpolantAutomata predicateFactory, Logger logger, IUltimateServiceProvider  services) {
		super(smtManager, edgeChecker, emptyStem, precondition, stemInterpolants,
				hondaPredicate, loopInterpolants, hondaEntererStem,
				hondaEntererLoop, abstraction, scroogeNondeterminismStem,
				scroogeNondeterminismLoop, hondaBouncerStem, hondaBouncerLoop,  	predicateFactory ,logger, services);
		GetHandle<CodeBlock, IPredicate> gh;
		try {
			gh = new GetHandle<CodeBlock, IPredicate>(new AutomataLibraryServices(services), abstraction);
			m_Handle = gh.getResult();
		} catch (OperationCanceledException e) {
			throw new AssertionError();
		}
	}



	@Override
	protected boolean mayEnterHondaFromStem(CodeBlock letter) {
		if (m_Handle != null && m_Position < m_Handle.getLength() - 1) {
			assert letter.equals(m_Handle.getWord().getSymbolAt(m_Position));
			m_Position++;
			return false;
		} else {
			return super.mayEnterHondaFromStem(letter);
		}
	}
	
	

}
