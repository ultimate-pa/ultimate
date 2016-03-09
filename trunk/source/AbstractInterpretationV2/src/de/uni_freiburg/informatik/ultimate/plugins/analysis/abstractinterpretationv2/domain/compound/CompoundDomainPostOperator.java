/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Post operator of the {@link CompoundDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "rawtypes", "unchecked" })
public class CompoundDomainPostOperator implements IAbstractPostOperator<CompoundDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;

	protected CompoundDomainPostOperator(Logger logger) {
		mLogger = logger;
	}

	@Override
	public List<CompoundDomainState> apply(CompoundDomainState oldstate, CodeBlock transition) {
		final List<CompoundDomainState> returnStates = new ArrayList<>();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> states = oldstate.getAbstractStatesList();
		final List<IAbstractDomain> domains = oldstate.getDomainList();
		assert domains.size() == states.size();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> resultingStates = new ArrayList<>();

		for (int i = 0; i < domains.size(); i++) {
			final List<IAbstractState> result = applyInternally(states.get(i), domains.get(i).getPostOperator(),
			        transition);
			
			if (result.size() == 0) {
				return new ArrayList<>();
			}
			
			IAbstractState state = result.get(0);
			for (int j = 1; j < result.size(); j++) {
				state = applyMergeInternally(state, result.get(j), domains.get(i).getMergeOperator());
			}

			resultingStates.add(state);
		}

		assert resultingStates.size() == domains.size();
		returnStates.add(new CompoundDomainState(mLogger, domains, resultingStates));

		return returnStates;
	}

	@Override
	public List<CompoundDomainState> apply(CompoundDomainState stateBeforeLeaving,
	        CompoundDomainState stateAfterLeaving, CodeBlock transition) {
		final List<CompoundDomainState> returnStates = new ArrayList<>();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> beforeStates = stateBeforeLeaving.getAbstractStatesList();
		final List<IAbstractState<?, CodeBlock, IBoogieVar>> afterStates = stateAfterLeaving.getAbstractStatesList();
		final List<IAbstractDomain> domainsBefore = stateBeforeLeaving.getDomainList();
		final List<IAbstractDomain> domainsAfter = stateAfterLeaving.getDomainList();

		assert domainsBefore.size() == domainsAfter.size();
		assert beforeStates.size() == afterStates.size();
		assert domainsBefore.size() == beforeStates.size();

		final List<IAbstractState<?, CodeBlock, IBoogieVar>> resultingStates = new ArrayList<>();
		
		for (int i = 0; i < domainsBefore.size(); i++) {
			final List<IAbstractState> result = applyInternally(beforeStates.get(i), afterStates.get(i),
			        domainsBefore.get(i).getPostOperator(), transition);
			
			if (result.size() == 0) {
				return new ArrayList<>();
			}
			
			IAbstractState state = result.get(0);
			for (int j = 1; j < result.size(); j++) {
				state = applyMergeInternally(state, result.get(j), domainsBefore.get(i).getMergeOperator());
			}
			
			if (state.isBottom()) {
				return new ArrayList<>();
			}
			resultingStates.add(state);
		}
		
		assert resultingStates.size() == domainsBefore.size();
		returnStates.add(new CompoundDomainState(mLogger, domainsBefore, resultingStates));

		return returnStates;
	}

	private static List<IAbstractState> applyInternally(final IAbstractState<?, CodeBlock, IBoogieVar> currentState,
	        final IAbstractPostOperator postOperator, final CodeBlock transition) {
		return postOperator.apply(currentState, transition);
	}

	private List<IAbstractState> applyInternally(final IAbstractState<?, CodeBlock, IBoogieVar> first,
	        final IAbstractState<?, CodeBlock, IBoogieVar> second, final IAbstractPostOperator postOperator,
	        final CodeBlock transition) {
		return postOperator.apply(first, second, transition);
	}

	private static <T extends IAbstractState, M extends IAbstractStateBinaryOperator<T>> T applyMergeInternally(T first,
	        T second, M mergeOperator) {
		return mergeOperator.apply(first, second);
	}

}
