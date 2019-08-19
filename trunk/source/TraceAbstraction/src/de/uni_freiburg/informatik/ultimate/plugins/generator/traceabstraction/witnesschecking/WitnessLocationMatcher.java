/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class WitnessLocationMatcher<LETTER extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final Set<WitnessEdge> mPureAnnotationEdges = new HashSet<>();
	private final HashRelation<Integer, WitnessEdge> mLineNumber2WitnessLetter = new HashRelation<>();
	private final HashRelation<ILocation, WitnessEdge> mSingleLineLocation2WitnessLetters = new HashRelation<>();
	private final HashRelation<WitnessEdge, ILocation> mWitnessLetters2SingleLineLocations = new HashRelation<>();
	private final Set<ILocation> mMultiLineLocations = new HashSet<>();
	private final ILogger mLogger;
	private final ArrayList<WitnessEdge> mUnmatchedWitnessLetters;

	public WitnessLocationMatcher(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> controlFlowAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		partitionEdges(witnessAutomaton.getVpAlphabet().getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getVpAlphabet().getInternalAlphabet());
		matchLocations(controlFlowAutomaton.getVpAlphabet().getCallAlphabet());
		matchLocations(controlFlowAutomaton.getVpAlphabet().getReturnAlphabet());
		mUnmatchedWitnessLetters = new ArrayList<>(witnessAutomaton.getVpAlphabet().getInternalAlphabet());
		mUnmatchedWitnessLetters.removeAll(mWitnessLetters2SingleLineLocations.getDomain());
		// for (WitnessEdge witnessLetter : mUnmatchedWitnessLetters) {
		// mLogger.info("Unmatched witness edge: " + witnessLetter);
		// }
		mLogger.info(witnessAutomaton.getVpAlphabet().getInternalAlphabet().size() + " witness edges");
		mLogger.info(mPureAnnotationEdges.size() + " pure annotation edges");
		mLogger.info(mUnmatchedWitnessLetters.size() + " unmatched witness edges");
		mLogger.info(mWitnessLetters2SingleLineLocations.getDomain().size() + " matched witness edges");
		mLogger.info(mSingleLineLocation2WitnessLetters.getDomain().size() + " single line locations");
		mLogger.info(mMultiLineLocations.size() + " multi line locations");
	}

	public boolean isMatchedWitnessEdge(final WitnessEdge wal) {
		return mWitnessLetters2SingleLineLocations.getDomain().contains(wal);
	}

	public boolean isCompatible(final ILocation loc, final WitnessEdge wal) {
		return mSingleLineLocation2WitnessLetters.containsPair(loc, wal);
	}

	public Set<ILocation> getCorrespondingLocations(final WitnessEdge wal) {
		return mWitnessLetters2SingleLineLocations.getImage(wal);
	}

	private void partitionEdges(final Set<WitnessEdge> internalAlphabet) {
		for (final WitnessEdge we : internalAlphabet) {
			final int startline = we.getLocation().getStartLine();
			mLineNumber2WitnessLetter.addPair(startline, we);
		}
	}

	private void matchLocations(final Set<? extends IIcfgTransition<?>> internalAlphabet) {
		for (final IIcfgTransition<?> cb : internalAlphabet) {
			matchLocations(cb);
		}

	}

	private void matchLocations(final IIcfgTransition<?> cb) {
		if (cb instanceof Call) {
			final Call call = (Call) cb;
			matchLocations(call);
		} else if (cb instanceof ParallelComposition) {
			final ParallelComposition pc = (ParallelComposition) cb;
			matchLocations(pc);
		} else if (cb instanceof Return) {
			final Return ret = (Return) cb;
			matchLocations(ret);
		} else if (cb instanceof SequentialComposition) {
			final SequentialComposition sc = (SequentialComposition) cb;
			matchLocations(sc);
		} else if (cb instanceof StatementSequence) {
			final StatementSequence ss = (StatementSequence) cb;
			matchLocations(ss);
		} else if (cb instanceof Summary) {
			final Summary sum = (Summary) cb;
			matchLocations(sum.getCallStatement());
		} else {
			throw new AssertionError("unknown type of CodeBlock");
		}
	}

	private void matchLocations(final Call call) {
		matchLocations(call.getCallStatement());
	}

	private void matchLocations(final ParallelComposition pc) {
		for (final CodeBlock cb : pc.getCodeBlocks()) {
			matchLocations(cb);
		}
	}

	private void matchLocations(final Return ret) {
		matchLocations(ILocation.getAnnotation(ret));
	}

	private void matchLocations(final SequentialComposition sc) {
		for (final CodeBlock cb : sc.getCodeBlocks()) {
			matchLocations(cb);
		}
	}

	private void matchLocations(final StatementSequence ss) {
		for (final Statement st : ss.getStatements()) {
			matchLocations(st);
		}
	}

	private void matchLocations(final Statement st) {
		if (st instanceof AssumeStatement) {
			matchLocations(((AssumeStatement) st).getFormula().getLocation());
		} else {
			matchLocations(st.getLocation());
		}
	}

	private void matchLocations(final ILocation location) {
		if (location.getStartLine() == location.getEndLine()) {
			final Set<WitnessEdge> witnessLetters = mLineNumber2WitnessLetter.getImage(location.getStartLine());
			if (witnessLetters != null) {
				for (final WitnessEdge wal : witnessLetters) {
					mSingleLineLocation2WitnessLetters.addPair(location, wal);
					mWitnessLetters2SingleLineLocations.addPair(wal, location);
				}
			}
		} else {
			mMultiLineLocations.add(location);
		}
	}

}
