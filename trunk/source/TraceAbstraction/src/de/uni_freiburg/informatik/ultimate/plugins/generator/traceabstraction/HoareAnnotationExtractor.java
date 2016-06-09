/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

/**
 * Extract an interprocedural Hoare annotation from an abstraction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationExtractor extends DoubleDeckerVisitor<CodeBlock, IPredicate> {

	Set<DoubleDecker<IPredicate>> mReportedDoubleDeckers = new HashSet<DoubleDecker<IPredicate>>();

	private final HoareAnnotationFragments mHoareAnnotation;

	public HoareAnnotationExtractor(IUltimateServiceProvider services, INestedWordAutomatonOldApi<CodeBlock, IPredicate> abstraction,
			HoareAnnotationFragments haf) {
		super(new AutomataLibraryServices(services));
		mTraversedNwa = abstraction;
		mHoareAnnotation = haf;

		try {
			traverseDoubleDeckerGraph();
		} catch (final AutomataOperationCanceledException e) {
			mLogger.warn("Computation of Hoare annotation canceled.");
		}
	}

	private void addContext(DoubleDecker<IPredicate> doubleDecker) {
		if (!mReportedDoubleDeckers.contains(doubleDecker)) {
			final IPredicate state = doubleDecker.getUp();
			final IPredicate context = doubleDecker.getDown();
			mHoareAnnotation.addDoubleDecker(context, state, mTraversedNwa.getEmptyStackState());
			mReportedDoubleDeckers.add(doubleDecker);
		}

	}

	@Override
	protected Collection<IPredicate> getInitialStates() {
		final Collection<IPredicate> result = mTraversedNwa.getInitialStates();
		if (result.size() == 1) {
			// case where automaton is emtpy minimized and contains only one
			// dummy state.
			final IPredicate p = result.iterator().next();
			if (!(p instanceof SPredicate)) {
				throw new AssertionError("No State Automaton would be ok");
				// result = new ArrayList<Predicate>(0);
			}
		}
		return result;
	}

	@Override
	protected Collection<IPredicate> visitAndGetInternalSuccessors(DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		final IPredicate state = doubleDecker.getUp();
		final ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		for (final CodeBlock symbol : mTraversedNwa.lettersInternal(state)) {
			for (final IPredicate succ : mTraversedNwa.succInternal(state, symbol)) {
				succs.add(succ);
			}
		}
		return succs;
	}

	@Override
	protected Collection<IPredicate> visitAndGetCallSuccessors(DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		final IPredicate state = doubleDecker.getUp();
		final ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		final Collection<CodeBlock> symbolsCall = mTraversedNwa.lettersCall(state);
		if (symbolsCall.size() > 1) {
			throw new UnsupportedOperationException("Several outgoing calls not supported");
		}
		for (final CodeBlock symbol : symbolsCall) {
			final Iterable<IPredicate> succCall = mTraversedNwa.succCall(state, symbol);
			final Iterator<IPredicate> calls = succCall.iterator();
			calls.next();
			if (calls.hasNext()) {
				throw new UnsupportedOperationException("Several outgoing calls not supported");
			}
			for (final IPredicate succ : succCall) {
				mHoareAnnotation.addContextEntryPair(state, succ);
				succs.add(succ);
			}
		}
		return succs;
	}

	@Override
	protected Collection<IPredicate> visitAndGetReturnSuccessors(DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		final IPredicate state = doubleDecker.getUp();
		final IPredicate context = doubleDecker.getDown();
		final ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		if (context == mTraversedNwa.getEmptyStackState()) {
			return succs;
		}
		for (final CodeBlock symbol : mTraversedNwa.lettersReturn(state)) {
			for (final IPredicate succ : mTraversedNwa.succReturn(state, context, symbol)) {
				succs.add(succ);
			}
		}
		return succs;
	}
}
