/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PrefixProduct;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class Cfg2NetJulian extends CFG2Automaton {

	private PetriNetJulian<CodeBlock, IPredicate> mResult;
	
	public Cfg2NetJulian(final RootNode rootNode,
			final IStateFactory<IPredicate> contentFactory, final SmtManager smtManager, final IUltimateServiceProvider services, final XnfConversionTechnique xnfConversionTechnique, final SimplicationTechnique simplificationTechnique)
					throws AutomataLibraryException {
		super(rootNode, contentFactory, smtManager, services, simplificationTechnique, xnfConversionTechnique);
		
		constructProcedureAutomata();
		mResult = new PetriNetJulian<CodeBlock,IPredicate>(new AutomataLibraryServices(services), mAutomata.get(0));
//		new TestFileWriter<TransAnnot, Predicate>(mAutomata.get(0), true);
		for (int i=1; i<mAutomata.size(); i++) {
			mResult = (new PrefixProduct<CodeBlock,IPredicate>(
					new AutomataLibraryServices(services), mResult, mAutomata.get(i)).getResult());
//			new TestFileWriter<TransAnnot, Predicate>(mAutomata.get(i), true);
		}
	}

	@Override
	public PetriNetJulian<CodeBlock,IPredicate> getResult() {
		return mResult;
	}

}
