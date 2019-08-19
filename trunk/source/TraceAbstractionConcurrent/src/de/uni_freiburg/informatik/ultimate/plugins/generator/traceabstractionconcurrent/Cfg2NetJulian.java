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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Automaton2Net;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PrefixProduct;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public final class Cfg2NetJulian<LETTER extends IIcfgTransition<?>>
		extends CFG2Automaton<LETTER, BoundedPetriNet<LETTER, IPredicate>> {
	private final BoundedPetriNet<LETTER, IPredicate> mResult;

	public Cfg2NetJulian(final IIcfg<?> rootNode, final IPetriNetAndAutomataInclusionStateFactory<IPredicate> contentFactory,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IUltimateServiceProvider services, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) throws AutomataLibraryException {
		super(rootNode, contentFactory, csToolkit, predicateFactory, services, simplificationTechnique,
				xnfConversionTechnique);

		constructProcedureAutomata();
		final Automaton2Net<LETTER, IPredicate> automaton2Net = new Automaton2Net<>(new AutomataLibraryServices(services), mAutomata.get(0));
		BoundedPetriNet result = (BoundedPetriNet) automaton2Net.getResult();
		assert automaton2Net.checkResult(contentFactory);
		for (int i = 1; i < mAutomata.size(); i++) {
			result = new PrefixProduct<>(new AutomataLibraryServices(services), result, mAutomata.get(i)).getResult();
		}
		mResult = result;
	}

	@Override
	public BoundedPetriNet<LETTER, IPredicate> getResult() {
		return mResult;
	}
}
