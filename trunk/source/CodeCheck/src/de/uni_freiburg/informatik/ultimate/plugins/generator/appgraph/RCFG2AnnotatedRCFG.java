/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class RCFG2AnnotatedRCFG {

	private HashMap<BoogieIcfgLocation, AnnotatedProgramPoint> mOldPpTonew;
	private final ILogger mLogger;
	private final PredicateFactory mPredicateFactory;
	private final IPredicate mTruePredicate;
	private final Map<IcfgLocation, Term> mInitialPredicates;
	private final boolean mUseInitialPredicates;

	public RCFG2AnnotatedRCFG(final CfgSmtToolkit smtMan, final PredicateFactory predicateFactory, final ILogger logger,
			final IPredicate truePredicate, final Map<IcfgLocation, Term> initialPredicates) {
		mLogger = logger;
		mPredicateFactory = predicateFactory;
		mTruePredicate = truePredicate;
		mInitialPredicates = initialPredicates;
		mUseInitialPredicates = initialPredicates != null;
	}

	public ImpRootNode convert(final IUltimateServiceProvider services, final IIcfg<BoogieIcfgLocation> oldRoot) {
		final ImpRootNode newRoot = new ImpRootNode();

		final Deque<BoogieIcfgLocation> openNodes = new ArrayDeque<>();
		mOldPpTonew = new HashMap<>();

		for (final Entry<String, BoogieIcfgLocation> entry : oldRoot.getProcedureEntryNodes().entrySet()) {
			final BoogieIcfgLocation oldNode = entry.getValue();
			final AnnotatedProgramPoint newNode = createAnnotatedProgramPoint(oldNode);

			newRoot.connectOutgoing(new DummyCodeBlock(mLogger), newNode);
			openNodes.add(oldNode);
			mOldPpTonew.put(oldNode, newNode);
		}

		/*
		 * collect all Nodes and create AnnotatedProgramPoints
		 */
		while (!openNodes.isEmpty()) {
			final BoogieIcfgLocation currentNode = openNodes.pollFirst();

			for (final IcfgEdge outEdge : currentNode.getOutgoingEdges()) {
				final BoogieIcfgLocation newNode = (BoogieIcfgLocation) outEdge.getTarget();
				if (mOldPpTonew.containsKey(newNode)) {
					continue;
				}
				mOldPpTonew.put(newNode, createAnnotatedProgramPoint(newNode));
				openNodes.add(newNode);
				if (outEdge instanceof Return) {
					final BoogieIcfgLocation hier = ((Return) outEdge).getCallerProgramPoint();
					if (mOldPpTonew.containsKey(hier)) {
						continue;
					}
					mOldPpTonew.put(hier, createAnnotatedProgramPoint(hier));
					openNodes.add(hier);
				}
			}
		}

		/*
		 * put edges into annotated program points
		 */
		for (final Entry<BoogieIcfgLocation, AnnotatedProgramPoint> entry : mOldPpTonew.entrySet()) {
			for (final IcfgEdge outEdge : entry.getKey().getOutgoingEdges()) {
				final AnnotatedProgramPoint annotatedTarget = mOldPpTonew.get(outEdge.getTarget());

				if (outEdge instanceof Return) {
					final AnnotatedProgramPoint callPred = mOldPpTonew.get(((Return) outEdge).getCallerProgramPoint());
					entry.getValue().connectOutgoingReturn(callPred, (Return) outEdge, annotatedTarget);
				} else {
					entry.getValue().connectOutgoing((CodeBlock) outEdge, annotatedTarget);
				}
			}
		}
		return newRoot;
	}

	/**
	 * Creates an AnnotatedProgramPoint from a ProgramPoint. The annotation is an IPredicate. If we have a Term from
	 * AbstractInterpretation for that ProgramPoint, we annotate it with the corresponding Predicate. Otherwise the
	 * annotation is "true".
	 */
	private AnnotatedProgramPoint createAnnotatedProgramPoint(final BoogieIcfgLocation pp) {
		if (mUseInitialPredicates) {
			final Term aiTerm = mInitialPredicates.get(pp);
			IPredicate aiPredicate;
			if (aiTerm != null) {
				aiPredicate = mPredicateFactory.newPredicate(aiTerm);
			} else {
				aiPredicate = mTruePredicate;
			}
			return new AnnotatedProgramPoint(aiPredicate, pp);
		}
		return new AnnotatedProgramPoint(mTruePredicate, pp);
	}

	public HashMap<BoogieIcfgLocation, AnnotatedProgramPoint> getOldPpTonew() {
		return mOldPpTonew;
	}
}
