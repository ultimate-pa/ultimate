/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;

public abstract class CodeChecker {

	private final CodeCheckSettings mGlobalSettings;

	protected IIcfg<IcfgLocation> mOriginalRoot;
	protected CfgSmtToolkit mCfgToolkit;
	protected final ImpRootNode mGraphRoot;

	protected IHoareTripleChecker mEdgeChecker;
	protected IPredicateUnifier mPredicateUnifier;

	protected GraphWriter mGraphWriter;

	protected final ILogger mLogger;

	public CodeChecker(final CfgSmtToolkit csToolkit, final IIcfg<IcfgLocation> originalRoot,
			final ImpRootNode graphRoot, final GraphWriter graphWriter, final IHoareTripleChecker edgeChecker,
			final IPredicateUnifier predicateUnifier, final ILogger logger, final CodeCheckSettings globalSettings) {
		mLogger = logger;
		mCfgToolkit = csToolkit;
		mOriginalRoot = originalRoot;
		mGraphRoot = graphRoot;
		mEdgeChecker = edgeChecker;
		mPredicateUnifier = predicateUnifier;
		mGraphWriter = graphWriter;
		mGlobalSettings = globalSettings;
	}

	public abstract boolean codeCheck(NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> errorRun,
			IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot);

	/**
	 * Given 2 predicates, return a predicate which is the conjunction of both.
	 *
	 * @param a
	 *            : The first Predicate.
	 * @param b
	 *            : The second Predicate.
	 */
	protected IPredicate conjugatePredicates(final IPredicate a, final IPredicate b) {
		final Set<IPredicate> preds = new HashSet<>(2, 1.0f);
		preds.add(mPredicateUnifier.getOrConstructPredicate(a));
		preds.add(mPredicateUnifier.getOrConstructPredicate(b));
		return mPredicateUnifier.getOrConstructPredicateForConjunction(preds);
	}

	/**
	 * Given a predicate, return a predicate which is the negation of it.
	 *
	 * @param a
	 *            : The Predicate.
	 */
	protected IPredicate negatePredicate(final IPredicate a) {
		final IPredicate pred = mPredicateUnifier.getPredicateFactory().not(a);
		return mPredicateUnifier.getOrConstructPredicate(pred);
	}

	public CodeCheckSettings getGlobalSettings() {
		return mGlobalSettings;
	}
}
